#!/usr/bin/env python3
"""Confine or trace the commands of a build, for trust-base items 2 and 3.

`wrap(d, mode, work)` rewrites `d/build.ninja` (as `mise gen` wrote it) so
that every command runs under a prefix, and returns the edges it read.

- `sandbox` (macOS only): each command runs under `sandbox-exec` with its
  own profile. The profile kills the command (SIGKILL) when it reads the
  data of a file it may not read, or writes a file it may not write, so the
  build fails. Every command may read the toolchain (`TOOLCHAIN`) and its
  own outputs (a `restat` command reads its old output to decide whether to
  keep it). In the build directory a static command may also read its
  explicit and implicit inputs, as `Sem.exec` does, and a depfile command
  may read what `Graph.DynOK` allows: every path no edge produces, and the
  edge's own inputs, order-only ones included. Ninja's own files
  (`build.ninja`, `.ninja_log`, `.ninja_deps`) and depfiles do not count as
  sources. A command may write its outputs, its depfile, the temporary
  files the compiler renames onto them (`OUT-*.tmp`), and a private
  `TMPDIR`. File metadata (`stat`, existence) and directory listings in the
  build directory are not confined: a compiler's include search stats
  paths that may not exist, and Python lists its script's directory.
- `trace`: each command runs with `test/trace.c` loaded (`DYLD_INSERT_LIBRARIES`
  on macOS, `LD_PRELOAD` on Linux, which is untested), which logs every
  file it opens. `check_trace` then compares each edge's reads with what
  the sandbox would allow and, for a depfile edge, with the dependencies
  Ninja recorded from its depfile (`ninja -t deps`): every file the command
  read in the build directory must be an explicit or implicit input or a
  recorded dependency. Reads outside the build directory must be in the
  toolchain; `-MMD` leaves system headers out of the depfile, so they are
  counted, not compared.
- `explain` (macOS only): the sandbox profile refuses without killing, and
  the tracer logs each refused open, to name what a sandbox kill was for.

The modes need simple commands (one program and its arguments, no shell
operators), since the prefix applies to the first command only. A command
in the DSL's wrapper (`Mise.Frontend.wrapCommand`) is the exception: the
prefix goes on the command inside the wrapper, so the command is confined
or traced exactly as it would be on its own. A sandboxed process cannot
start a second sandbox, so the wrapper's `sh` runs outside one, but in
`sandbox` mode every program it starts is confined: the command by its
profile, and each `mv`, `rm` and `cmp` by a profile of its own
(`wrapper_profile`), which lets it read the toolchain and read and write
only the edge's outputs and their `OUT.mise-old` copies. That profile
refuses without killing, so a refusal shows as "Operation not permitted"
in Ninja's output, which `wrapper_refusals` finds. The `sh` itself runs
only builtins (`set`, `for`, `[`, `echo`, `exit`), which test whether files
exist and write to standard error. In `trace` mode the wrapper's programs
are not traced.

`python3 test/confine.py sandbox|trace|determinism` runs the examples; see
`test/conf-sandbox.sh`, `test/conf-depfiles.sh` and `test/conf-determinism.sh`.
"""
import argparse
import os
import platform
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MISE = ROOT / ".lake" / "build" / "bin" / "mise"
OUT = ROOT / "test" / "out" / "confine"
DARWIN = platform.system() == "Darwin"

# Paths every command may read: the Nix store (compiler, Python, SDK), the
# system libraries and frameworks, time zones, and random devices.
TOOLCHAIN = ["/nix/store", "/usr/lib", "/usr/share", "/dev/null", "/dev/tty", "/dev/urandom", "/dev/random"] + (
    ["/System", "/Library/Developer", "/private/var/db/timezone", "/dev/dtracehelper"] if DARWIN
    else ["/etc", "/lib", "/lib64", "/proc/self", "/sys/devices/system/cpu"])
NINJA_FILES = ["build.ninja", ".ninja_log", ".ninja_deps"]
VAR = "mise_confine"
WVAR = "mise_wconfine"


# ---------------------------------------------------------------- manifests

@dataclass
class Edge:
    outs: list
    iouts: list
    rule: str
    ins: list
    iins: list
    oo: list
    dyn: bool = False
    key: str = ""

    @property
    def all_outs(self):
        return self.outs + self.iouts


def split_paths(s):
    """Split a Ninja path list on unescaped spaces, keeping `|`, `||` and `:`
    as separators and undoing `$ `, `$:` and `$$`."""
    toks, cur, i = [], "", 0
    while i < len(s):
        c = s[i]
        if c == "$" and i + 1 < len(s) and s[i + 1] in " :$":
            cur += s[i + 1]
            i += 2
            continue
        if c in " :":
            if cur:
                toks.append(cur)
            cur = ""
            if c == ":":
                toks.append(":")
        else:
            cur += c
        i += 1
    if cur:
        toks.append(cur)
    return toks


def parse_build(line):
    toks = split_paths(line[len("build "):])
    colon = toks.index(":")
    lhs, rhs = toks[:colon], toks[colon + 1:]
    outs, iouts = (lhs[:lhs.index("|")], lhs[lhs.index("|") + 1:]) if "|" in lhs else (lhs, [])
    rule, rest = rhs[0], rhs[1:]
    groups, cur = {"": [], "|": [], "||": []}, ""
    for t in rest:
        if t in ("|", "||"):
            cur = t
        else:
            groups[cur].append(t)
    return Edge(outs, iouts, rule, groups[""], groups["|"], groups["||"])


def parse(text):
    """The rules' commands, which rules have a depfile, and the edges of a
    manifest in the form `mise gen` writes."""
    commands, dyn, edges, rule = {}, set(), [], None
    for line in text.splitlines():
        if line.startswith("rule "):
            rule = line.split()[1]
        elif line.startswith("build "):
            rule = None
            edges.append(parse_build(line))
        elif rule and line.startswith("  command = "):
            commands[rule] = line[len("  command = "):]
        elif rule and line.startswith("  depfile = "):
            dyn.add(rule)
    for e in edges:
        e.dyn = e.rule in dyn
        e.key = re.sub(r"[^A-Za-z0-9._-]", "_", e.outs[0])
    return commands, edges


def sb_str(p):
    return '"' + str(p).replace("\\", "\\\\").replace('"', '\\"') + '"'


def ninja_escape(s):
    return s.replace("$", "$$")


def real(p):
    return Path(os.path.realpath(p))


# ---------------------------------------------------------------- policy

def generated(edges):
    return {p for e in edges for p in e.all_outs}


def may_read(e, edges, rel):
    """Whether edge `e` may read the build-directory path `rel`."""
    if rel in e.all_outs or rel in e.ins + e.iins:
        return True
    if e.dyn:
        if rel in e.oo:
            return True
        return rel not in generated(edges) and rel not in NINJA_FILES and not rel.endswith(".d")
    return False


def tmp_regex(d, out):
    """The temporary files clang writes and renames onto an output:
    `build/main.o` becomes `build/main-1a2b3c4d.o.tmp`."""
    p = d / out
    stem, suffix = os.path.splitext(p.name)
    return "^" + sb_re(p.parent / stem) + "-[^/]*" + sb_re(suffix) + "[.]tmp$"


def sb_re(s):
    """A regex matching `s` literally, without backslashes, which the sandbox
    profile language and Python read alike."""
    return "".join(c if c.isalnum() or c in "/_" else f"[{c}]" for c in str(s))


def profile(e, edges, d, tmp, extra_reads, extra_writes):
    """A sandbox profile for edge `e` run in build directory `d`."""
    reads = [f"(subpath {sb_str(real(t))})" for t in TOOLCHAIN + [tmp] if os.path.exists(t)]
    # A process opens `/` and its executable's directory at start-up.
    reads += [f"(literal {sb_str(real(p))}) (literal {sb_str(real(p).parent)})" for p in extra_reads]
    reads += ['(literal "/")', f"(require-all (subpath {sb_str(d)}) (vnode-type DIRECTORY))"]
    writes = [f"(literal {sb_str(p)})" for p in ["/dev/null", "/dev/tty", "/dev/dtracehelper"]]
    writes += [f"(subpath {sb_str(real(tmp))})"]
    writes += [f"(literal {sb_str(d / p)})" for p in e.all_outs + list(extra_writes)]
    writes += [f"(regex {sb_str(tmp_regex(d, p))})" for p in e.all_outs]
    if e.dyn:
        writes.append(f"(literal {sb_str(d / (e.outs[0] + '.d'))})")
    lines = ["(version 1)", "(allow default)",
             "(deny file-read-data (with send-signal SIGKILL))",
             "(deny file-write* (with send-signal SIGKILL))",
             "(allow file-read-data " + " ".join(reads) + ")"]
    if e.dyn:
        # Graph.DynOK: anything no edge produces, and the edge's own inputs.
        lines.append(f"(allow file-read-data (subpath {sb_str(d)}))")
        banned = sorted((generated(edges) | set(NINJA_FILES)) - set(e.all_outs + e.ins + e.iins + e.oo))
        lines.append(f"(deny file-read-data (with send-signal SIGKILL) "
                     + " ".join(f"(literal {sb_str(d / p)})" for p in banned)
                     + f" (regex {sb_str('^' + sb_re(d) + '/.*[.]d$')}))")
    lines.append("(allow file-read-data " + " ".join(f"(literal {sb_str(d / p)})"
                                                     for p in e.all_outs + e.ins + e.iins + (e.oo if e.dyn else [])) + ")")
    lines.append("(allow file-write* " + " ".join(writes) + ")")
    return "\n".join(lines) + "\n"


def wrapper_profile(e, d):
    """A sandbox profile for the wrapper's `mv`, `rm` and `cmp` on edge `e`:
    they may read the toolchain and the programs themselves, and read and
    write the edge's outputs and their `OUT.mise-old` copies. It refuses
    without killing, so that the refusal message reaches Ninja's output."""
    progs = [real(shutil.which(p)) for p in ["mv", "rm", "cmp"]]
    reads = [f"(subpath {sb_str(real(t))})" for t in TOOLCHAIN if os.path.exists(t)]
    reads += [f"(literal {sb_str(p)}) (literal {sb_str(p.parent)})" for p in progs]
    files = [f"(literal {sb_str(d / q)})" for o in e.all_outs for q in (o, o + ASIDE)]
    devs = [f"(literal {sb_str(p)})" for p in ["/dev/null", "/dev/tty", "/dev/dtracehelper"]]
    return "\n".join(["(version 1)", "(allow default)", "(deny file-read-data)", "(deny file-write*)",
                      "(allow file-read-data " + " ".join(reads + ['(literal "/")'] + files) + ")",
                      "(allow file-write* " + " ".join(devs + files) + ")"]) + "\n"


def wrapper_refusals(stdout):
    """The lines of Ninja's output in which the sandbox refused a step of the
    wrapper."""
    return [l for l in stdout.splitlines() if "Operation not permitted" in l]


# ---------------------------------------------------------------- wrapping

SHELL_OPS = re.compile(r"[;&|<>`\n]|\$\$")

# The parts of the DSL's wrapper around the command it runs (see `inner`
# in test/MiseTest/Fuzz.lean), the suffix of the copies it moves old
# outputs to, and the programs it runs.
WRAP_OPEN, WRAP_CLOSE = "; if ( ", " ); then "
ASIDE = ".mise-old"
WRAP_PROGS = ["mv -f ", "rm -f ", "cmp -s "]


def split_wrapped(cmd):
    """(head, command, tail) for a command in the DSL's wrapper, so that
    head + command + tail == cmd, or None for any other command."""
    parts = cmd.split(WRAP_OPEN)
    if len(parts) != 2 or not parts[0].startswith("set -- ") or WRAP_CLOSE not in parts[1]:
        return None
    inner, tail = parts[1].split(WRAP_CLOSE, 1)
    return parts[0] + WRAP_OPEN, inner, WRAP_CLOSE + tail


def confine_wrapper(part):
    """`part` of the wrapper with each `mv`, `rm` and `cmp` under the
    wrapper's prefix."""
    for p in WRAP_PROGS:
        part = part.replace(p, "${" + WVAR + "} " + p)
    return part


def tracer(work):
    """Compile test/trace.c into `work` once."""
    lib = work / ("libtrace.dylib" if DARWIN else "libtrace.so")
    if not lib.exists():
        work.mkdir(parents=True, exist_ok=True)
        flags = ["-dynamiclib"] if DARWIN else ["-shared", "-fPIC"]
        subprocess.run(["cc", "-O2", "-Wall", *flags, "-o", lib, ROOT / "test" / "trace.c"]
                       + ([] if DARWIN else ["-ldl"]), check=True)
    return lib


def wrap(d, mode, work, extra_reads=(), extra_writes=()):
    """Rewrite `d/build.ninja` so that every command runs confined or
    traced. Profiles, private temporary directories and trace logs go to
    `work`, outside `d`. Returns the edges."""
    d, work = real(d), Path(work)
    text = (d / "build.ninja").read_text()
    commands, edges = parse(text)
    for name, cmd in commands.items():
        w = split_wrapped(cmd)
        if SHELL_OPS.search(w[1] if w else cmd):
            raise RuntimeError(f"confine: rule {name} is not a simple command: {cmd}")
    for sub in ["sb", "tmp", "trace"]:
        (work / sub).mkdir(parents=True, exist_ok=True)
    prefix, wprefix = {}, {}
    for e in edges:
        tmp = work / "tmp" / e.key
        tmp.mkdir(exist_ok=True)
        var = "DYLD_INSERT_LIBRARIES" if DARWIN else "LD_PRELOAD"
        trace = f"{var}={real(tracer(work))} MISE_TRACE={real(work / 'trace' / e.key)}.log"
        if mode in ("sandbox", "explain"):
            if not DARWIN:
                raise RuntimeError("confine: sandbox mode needs macOS sandbox-exec")
            prof = work / "sb" / f"{e.key}.sb"
            text_sb = profile(e, edges, d, real(tmp), extra_reads, extra_writes)
            pre = f"TMPDIR={real(tmp)} sandbox-exec -f {real(prof)}"
            if mode == "explain":
                # Refuse without killing, and trace the refusals. sandbox-exec
                # is SIP-protected and drops DYLD_*, so `env` sets them again.
                text_sb = text_sb.replace(" (with send-signal SIGKILL)", "")
                text_sb += (f"(allow file-read-data (literal {sb_str(real(tracer(work)))}))\n"
                            f"(allow file-write* (subpath {sb_str(real(work / 'trace'))}))\n")
                pre += f" {shutil.which('env')} {trace}"
            prof.write_text(text_sb)
            prefix[e.key] = pre
            wprof = work / "sb" / f"{e.key}.wrapper.sb"
            wprof.write_text(wrapper_profile(e, d))
            wprefix[e.key] = f"sandbox-exec -f {real(wprof)}"
        else:
            prefix[e.key] = f"TMPDIR={real(tmp)} {trace}"
    out, i = [], 0
    for line in text.splitlines():
        if line.startswith("  command = ") and out and not out[-1].startswith("build "):
            cmd = line[len("  command = "):]
            w = split_wrapped(cmd)
            if w and wprefix:
                w = (confine_wrapper(w[0]), w[1], confine_wrapper(w[2]))
            line = "  command = " + (w[0] + "${" + VAR + "} " + w[1] + w[2] if w else "${" + VAR + "} " + cmd)
        out.append(line)
        if line.startswith("build "):
            out.append(f"  {VAR} = {ninja_escape(prefix[edges[i].key])}")
            if wprefix:
                out.append(f"  {WVAR} = {ninja_escape(wprefix[edges[i].key])}")
            i += 1
    (d / "build.ninja").write_text("\n".join(out) + "\n")
    return edges


def clear_traces(work):
    shutil.rmtree(Path(work) / "trace", ignore_errors=True)
    (Path(work) / "trace").mkdir(parents=True)


def ran(stdout):
    """The trace logs named by the commands that `ninja -v` printed."""
    return set(re.findall(r"MISE_TRACE=(\S+)", stdout))


def recorded_deps(d, out):
    r = subprocess.run(["ninja", "-t", "deps", out], cwd=d, capture_output=True, text=True, check=True)
    return [l.strip() for l in r.stdout.splitlines()[1:] if l.strip()]


@dataclass
class Stats:
    edges: int = 0
    dyn_edges: int = 0
    reads: int = 0
    dyn_reads: int = 0
    toolchain_reads: int = 0
    dirs: set = field(default_factory=set)

    def add(self, o):
        for k in ["edges", "dyn_edges", "reads", "dyn_reads", "toolchain_reads"]:
            setattr(self, k, getattr(self, k) + getattr(o, k))
        self.dirs |= o.dirs

    def __str__(self):
        return (f"{self.edges} commands traced, {self.dyn_edges} with depfiles; "
                f"{self.reads} files read in the build directory, {self.dyn_reads} of them by depfile commands; "
                f"{self.toolchain_reads} toolchain files read")


def under(path, roots):
    return any(path == r or path.startswith(r + "/") for r in roots)


def check_trace(d, edges, work, stdout, extra_reads=(), extra_writes=()):
    """Check the trace logs of the edges that ran in a build, given the
    build's `ninja -v` output; return problems and statistics."""
    d, work = real(d), Path(work)
    toolchain = [str(real(t)) for t in TOOLCHAIN if os.path.exists(t)]
    extra = {str(real(p)) for p in extra_reads}
    logs = ran(stdout)
    # Ninja records no deps for a command that failed, so its reads are
    # compared with the sandbox's rules only.
    failed = {t for l in stdout.splitlines() if l.startswith("FAILED: ")
              for t in l[len("FAILED: "):].split() if not t.startswith("[code=")}
    problems, st = [], Stats()
    for e in edges:
        log = real(work / "trace") / f"{e.key}.log"
        if str(log) not in logs:
            continue
        if not log.exists():
            problems.append(f"{e.outs[0]}: ran but left no trace (a static or SIP-protected program?)")
            continue
        st.edges += 1
        st.dyn_edges += e.dyn
        tmp = str(real(work / "tmp" / e.key))
        tmp_res = [re.compile(tmp_regex(d, p)) for p in e.all_outs]
        reads, writes, outside, refused = set(), set(), set(), False
        for line in log.read_text().splitlines():
            kind, path = line[0], line[2:]
            if kind == "E":
                refused = True
                problems.append(f"{e.outs[0]}: an open of {path} was refused")
            elif path.startswith(str(d) + "/"):
                rel = path[len(str(d)) + 1:]
                {"R": reads, "W": writes, "D": st.dirs}[kind].add(rel)
            elif path == str(d):
                st.dirs.add(".")
            elif under(path, [tmp]) or path in extra:
                pass
            elif under(path, toolchain):
                if kind == "R":
                    outside.add(path)
                elif kind == "W" and not path.startswith("/dev/"):
                    problems.append(f"{e.outs[0]}: wrote {path}, in the toolchain")
            else:
                problems.append(f"{e.outs[0]}: opened {path}, outside the build directory and the toolchain")
        st.reads += len(reads)
        st.dyn_reads += len(reads) if e.dyn else 0
        st.toolchain_reads += len(outside)
        for rel in sorted(reads):
            if not may_read(e, edges, rel):
                problems.append(f"{e.outs[0]}: read {rel}, which it may not read")
        for rel in sorted(writes):
            ok = rel in e.all_outs or rel in extra_writes or (e.dyn and rel == e.outs[0] + ".d") \
                or any(r.match(str(d / rel)) for r in tmp_res)
            if not ok:
                problems.append(f"{e.outs[0]}: wrote {rel}, which is not its output")
        if e.dyn and not refused and e.outs[0] not in failed:  # a refused or failed command leaves no deps
            listed = set(recorded_deps(d, e.outs[0])) | set(e.ins + e.iins)
            for rel in sorted(reads - listed - set(e.all_outs)):
                problems.append(f"{e.outs[0]}: read {rel}, which its depfile does not list")
    return problems, st


# ---------------------------------------------------------------- examples

sys.path.insert(0, str(ROOT / "test"))  # for `import props`, the examples' edits


def run(cmd, cwd, check=True):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if check and r.returncode != 0:
        raise RuntimeError(f"{' '.join(map(str, cmd))} failed in {cwd}:\n{r.stdout}{r.stderr}")
    return r


def gen(d, flag=None):
    run([MISE, "gen", *(["--set", f"cflags={flag}"] if flag else []), d], ROOT)


def states(ex):
    """The example's own files, then each edit of the property harness
    applied in turn, and again in reverse: (files, flag index) pairs."""
    import props
    src = ROOT / "examples" / ex.name
    yield {p.name: p.read_text() for p in src.iterdir() if p.is_file()}, 0
    s = ex.initial()
    for edit in ex.edits() + ex.edits()[::-1]:
        if edit[0] == "bump":
            s[edit[1]] += 1
        elif edit[0] == "toggle":
            s[edit[1]] = not s[edit[1]]
        else:
            s["flag"] = (s["flag"] + 1) % len(props.FLAGS)
        yield ex.render(s), s["flag"]


def build_steps(name, mode):
    """Build an example under `mode` through every state; return trace
    problems and statistics."""
    import props
    ex = props.EXAMPLES[name]()
    d, work = OUT / mode / name / "build", OUT / mode / name / "work"
    shutil.rmtree(d.parent, ignore_errors=True)
    d.mkdir(parents=True)
    problems, st, old, runs = [], Stats(), None, 0
    for i, (files, fl) in enumerate(states(ex)):
        props.write_files(d, files, old)
        old = files
        gen(d, props.FLAGS[fl])
        edges = wrap(d, mode, work)
        clear_traces(work)
        r = run(["ninja", "-v", "-j8"], d, check=False)
        if r.returncode != 0:
            raise RuntimeError(f"{name} step {i}: confined build failed:\n{r.stdout}{r.stderr}")
        if mode == "sandbox" and (refused := wrapper_refusals(r.stdout)):
            raise RuntimeError(f"{name} step {i}: the sandbox refused a step of the wrapper:\n" + "\n".join(refused))
        runs += len(re.findall(r"^\[\d+/\d+\]", r.stdout, re.M))
        if "no work to do" not in run(["ninja", "-n"], d).stdout:
            raise RuntimeError(f"{name} step {i}: ninja -n has work to do")
        if mode == "trace":
            p, s = check_trace(d, edges, work, r.stdout)
            problems += [f"{name} step {i}: {x}" for x in p]
            st.add(s)
    return problems, st, i + 1, runs


def bad_case(name, mode, edit_toml):
    """Build a broken copy of an example plainly and under `mode`. Returns
    [(plain build ok, its FAILED line), (confined build ok, its FAILED line
    or trace problems)]."""
    src = ROOT / "examples" / name
    base = OUT / mode / "bad" / f"{name}-{edit_toml.__name__}"
    shutil.rmtree(base, ignore_errors=True)
    res = []
    # In sandbox mode, a third build refuses without killing and traces
    # the refusals, to name what the sandbox caught.
    for m in ["plain", mode] + (["explain"] if mode == "sandbox" else []):
        d, work = base / m, base / f"{m}-work"
        d.mkdir(parents=True)
        for p in src.iterdir():
            if p.is_file():
                shutil.copy(p, d / p.name)
        (d / "mise.toml").write_text(edit_toml((src / "mise.toml").read_text()))
        gen(d)
        edges = wrap(d, m, work) if m != "plain" else None
        clear_traces(work)
        r = run(["ninja", "-v", "-j1"], d, check=False)
        if m in ("trace", "explain"):
            problems, _ = check_trace(d, edges, work, r.stdout)
            res.append((r.returncode == 0 and not problems, problems))
        else:
            res.append((r.returncode == 0, [l for l in r.stdout.splitlines() if l.startswith("FAILED")]))
    return res


def undeclared_header(t):
    """hello-c: main.c includes greet.h, but the edge no longer declares it."""
    return t.replace('ins = ["main.c"]\nimplicit-ins = ["greet.h"]\n', 'ins = ["main.c"]\n', 1)


def generated_not_input(t):
    """gen-header: util.c includes build/config.h, which is not an input of
    its edge (breaks Graph.DynOK)."""
    return t.replace('ins = ["util.c"]\norder-only = ["build/config.h"]\n', 'ins = ["util.c"]\n', 1)


def undeclared_output(t):
    """hello-c: the compile also writes a depfile its rule does not declare."""
    return t.replace('command = "cc $cflags -c $in -o $out"', 'command = "cc $cflags -MMD -c $in -o $out"', 1)


def system_header(t):
    """gen-header: build/ is a system include directory, so `-MMD` leaves
    build/config.h out of the depfile."""
    return t.replace("-Ibuild", "-isystem build", 1)


def check_edit(f, name):
    t = (ROOT / "examples" / name / "mise.toml").read_text()
    if f(t) == t:
        raise RuntimeError(f"bad case {f.__name__} does not change examples/{name}/mise.toml")


def main_confined(mode):
    import props
    fails = 0
    for name in props.EXAMPLES:
        problems, st, n, runs = build_steps(name, mode)
        print(f"{mode} {name}: {n} builds, {runs} commands" + (f"; {st}" if mode == "trace" else ", all passed under the sandbox"))
        if mode == "trace" and st.dirs:
            print(f"  directories listed: {', '.join(sorted(st.dirs))}")
        for p in problems:
            print("FAIL", p)
        fails += len(problems)
    cases = [("hello-c", undeclared_header), ("gen-header", generated_not_input), ("hello-c", undeclared_output)] \
        if mode == "sandbox" else [("gen-header", system_header)]
    for name, f in cases:
        check_edit(f, name)
        (plain_ok, _), (conf_ok, why), *explained = bad_case(name, mode, f)
        verdict = "caught" if plain_ok and not conf_ok else "NOT CAUGHT"
        print(f"{mode} bad case {name}/{f.__name__}: plain build {'passes' if plain_ok else 'fails'}, "
              f"{mode} build {'passes' if conf_ok else 'fails'}: {verdict}")
        for l in why + (explained[0][1] if explained else []):
            print(f"  {l}")
        fails += verdict != "caught"
    return 1 if fails else 0


# ---------------------------------------------------------------- determinism

DET_FLAGS = ["-O2 -Wall", "-O0", "-O1 -DMISE_FLAG=1", "-O0 -g"]


def main_determinism(flags):
    """Two clean builds of each example per `cflags` value, in different
    directories, at least a second apart, with different `-j` levels, time
    zones and locales. Products must be byte-identical, except that a
    product may differ by the build directory's path where the compiler
    embeds it (`-g`); the two directory names have the same length, so
    substituting one path for the other must then make them identical."""
    import props
    fails = 0
    for name, cls in props.EXAMPLES.items():
        ex = cls()
        src = ROOT / "examples" / name
        seen = set()
        for i, flag in enumerate(flags):
            dirs = []
            for k, (sub, jobs, tz, lang) in enumerate([("first", "-j1", "UTC", "C"),
                                                        ("later", "-j8", "Asia/Tokyo", "en_GB.UTF-8")]):
                d = OUT / "determinism" / name / str(i) / sub
                shutil.rmtree(d, ignore_errors=True)
                d.mkdir(parents=True)
                for p in src.iterdir():
                    if p.is_file():
                        shutil.copy(p, d / p.name)
                gen(d, flag)
                if k:
                    time.sleep(1.1)
                env = dict(os.environ, TZ=tz, LANG=lang, LC_ALL=lang)
                r = subprocess.run(["ninja", jobs], cwd=d, env=env, capture_output=True, text=True)
                if r.returncode != 0:
                    raise RuntimeError(f"{name}: build failed:\n{r.stdout}")
                dirs.append(d)
            a = {p: (dirs[0] / p).read_bytes() for p in ex.products}
            b = {p: (dirs[1] / p).read_bytes() for p in ex.products}
            diff = [p for p in ex.products if a[p] != b[p]]
            pa, pb = str(dirs[0]).encode(), str(dirs[1]).encode()
            by_path, by_hash, other = [], [], []
            for p in diff:
                if pb not in b[p]:
                    other.append(p)
                elif b[p].replace(pb, pa) == a[p]:
                    by_path.append(p)
                elif macho_hashes_masked(b[p].replace(pb, pa)) == macho_hashes_masked(a[p]):
                    by_hash.append(p)
                else:
                    other.append(p)
            size = sum(map(len, a.values()))
            head = f"determinism {name} cflags={flag!r}: {len(ex.products)} products, {size} bytes"
            if other:
                fails += 1
                print(f"{head}: DIFFER {other}")
            elif diff:
                print(f"{head}: they embed the build directory; with it substituted, "
                      + (f"{', '.join(by_path)} identical" if by_path else "")
                      + ("; " if by_path and by_hash else "")
                      + (f"{', '.join(by_hash)} identical except LC_UUID and the code signature, "
                         "which hash the embedded path" if by_hash else ""))
            else:
                print(f"{head}: identical")
    return 1 if fails else 0


def macho_hashes_masked(data):
    """A 64-bit Mach-O file with its LC_UUID and code signature zeroed: the
    linker derives both from the contents, so a path embedded in the
    contents changes them too. Other files come back unchanged."""
    import struct
    if data[:4] != b"\xcf\xfa\xed\xfe":
        return data
    out = bytearray(data)
    ncmds = struct.unpack_from("<I", data, 16)[0]
    off = 32
    for _ in range(ncmds):
        cmd, size = struct.unpack_from("<II", data, off)
        if cmd == 0x1b:  # LC_UUID
            out[off + 8:off + 24] = bytes(16)
        elif cmd == 0x1d:  # LC_CODE_SIGNATURE
            doff, dsize = struct.unpack_from("<II", data, off + 8)
            out[doff:doff + dsize] = bytes(dsize)
        off += size
    return bytes(out)


def main():
    import props
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["sandbox", "trace", "determinism"])
    ap.add_argument("--flag", action="append", dest="flags",
                    help="a cflags value for determinism, as --flag='-O0 -g'; repeatable (default: DET_FLAGS)")
    a = ap.parse_args()
    if a.mode == "determinism":
        return main_determinism(a.flags or DET_FLAGS)
    return main_confined(a.mode)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except RuntimeError as e:
        print(f"FAIL: {e}", file=sys.stderr)
        sys.exit(1)
