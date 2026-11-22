#!/usr/bin/env python3
"""Mutation testing of the definitions the theorems are stated in.

Each mutant is one small edit to a definition that a statement in
`Mise/Theorems.lean` uses, and makes at least one of those theorems weaker:
a hypothesis that holds less often, or a conclusion that says less. A proof
cannot catch such a mutant, because the weaker theorem is still true, so a
test in `test/MiseTest/` must. (Some mutants also make another theorem
false, but the tests should still pin each definition by themselves.)
Mutants that make a theorem stronger or false are the proofs' job and are
not listed. Proofs do not tell the two apart: they break on almost any
change to a definition they unfold, equivalent ones included.

The driver

1. copies the tree to `test/out/trust-mutants/tree`, never touching the real
   tree;
2. in the copy, replaces the body of every theorem in `Mise/` with `sorry`,
   and builds the library with `debug.byAsSorry`, which does the same for
   the `by` proofs inside definitions. A mutant then breaks no proof, and
   the build depends only on the definitions. The copy's tests use
   `#eval!`, because `#eval` refuses a value that depends on `sorry`;
3. builds `MiseTest` on the unmutated copy, which must succeed;
4. builds each mutant in two stages. The first builds only the test modules
   in `KILLERS`, which should kill every mutant; the second builds the rest
   of `MiseTest`, and runs only when the first finds no error. `--jobs`
   builds run at once.

There are two ways to build a mutant. `--via inproc`, the default, starts
one long-lived Lean process per job, `test/trust-mutants.lean`, and feeds it
mutants one at a time. For each mutant it elaborates the mutated module and
the modules that import it from source, in memory, on the modules the
mutated one does not reach, which it loads once per module and reuses. This
saves starting and importing a Lean process for each module: about a fifth
of the CPU time of `--via lake`. All the modules of a stage share one
environment, where Lake gives each module only its own imports, so the
driver also runs the unmutated tree this way, as a control that must pass.
`--via lake` clones the built copy for each mutant, applies the edit to the
clone and runs `lake build` there. It does not depend on Lean's internal
elaboration API, so use it when that API changes or a mutant crashes the
in-process build.

`--generated` adds the mutants that `test/MiseTest/MutantGen.lean`
generates in the prepared copy, after step 3: mechanical edits at every
place a trusted definition states a condition or computes a value, kept
when they weaken at least one theorem or their effect is unknown
(`--all-edits` keeps every edit). The definitions that trust item 1 is
stated in, such as the printer, are targets too, with unknown effect. A generated mutant that gives the same file as an earlier one is
skipped. A generated edit that breaks the library is "stillborn": it does
not type-check, so no theorem is stated about it, and it does not fail the
run.

A mutant is killed when a test fails. The kill is "evaluates" when `decide`
or `#guard` computed a false result, and "elaborates" when a test no longer
type-checks: an unknown constructor, a wrong number of arguments, or a proof
step that fails. A mutant that breaks the library itself is an error, since
the tests never run. With staged builds, a mutant that the first stage
kills reports only the first stage's errors. Each row is appended to
`test/out/trust-mutants/results.md` as its mutant finishes, and the sorted
table with a summary replaces it at the end.

`test/MiseTest/MutantCheck.lean` then triages the mutants that survive, on
`--jobs` processes (see its header). For each survivor it searches for a
witness, an input on which the definition and the mutant differ, and turns
it into a test that kills the mutant. When it finds none, it tries to prove
the two equal; a proved mutant is "equivalent", which no test can kill. The
report lists the survivors by their effect on the theorems, weaker first,
with each triage result, and then the tests. `--samples` sets the number of
random inputs per survivor, `--no-triage` skips the triage, and `--retriage`
triages the survivors of the last run again, from
`test/out/trust-mutants/rows.json`, without building any mutant.

The tests overlap: a test of a caller often kills mutants of the functions
it calls. So when the triage finds distinguished survivors, the run builds
each of them against all of the triage's tests, in a module
`MiseTest.Candidates` in the copy, and chooses a smallest set of tests that
kills them all, the shortest among equals. It writes the set to
`test/out/trust-mutants/cover.lean`, with the mutants each test kills, and
the kill matrix to `kills.json` there. `--no-cover` skips this step, and
`--cover` runs only this step, on the last triage.

The run prints a banner as each stage starts, with the time since the run
started, and a line as each item of a stage finishes: a module of the
control build, a mutant, a triaged survivor, or a survivor of the cover,
with the count, the time in the stage and an estimate of the time left.
At the end it prints the summary; the full report is in `results.md`.

The exit status is 1 when a mutant that is not equivalent survives, or a
mutant is an error.

usage: trust-mutants.py [--via inproc|lake] [-j JOBS] [--generated [--all-edits]]
                        [--samples N] [--no-triage] [--no-cover] [MUTANT...]
       trust-mutants.py --retriage [--no-cover] [MUTANT...]
       trust-mutants.py --cover

JOBS defaults to the number of CPUs, at most one per 4 GB of memory: an
in-process worker holds about 2.5 GB, and up to 4 GB for a few seconds after
its process starts. Workers start 5 seconds apart, so that those peaks do not
coincide. A worker starts a new process for each mutated module, since a
process keeps every module's imports it has loaded.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "test" / "out" / "trust-mutants"
TREE = OUT / "tree"
WORK = OUT / "work"
INPROC = ROOT / "test" / "trust-mutants.lean"
CHECK = ROOT / "test" / "MiseTest" / "MutantCheck.lean"

# The test modules that should kill every mutant (see `CLAUDE.md`). A build
# builds these first, and the rest of `MiseTest` only if they pass.
KILLERS = ["MiseTest.Boundary", "MiseTest.Reachable"]

SOUND = "Mise/Model/Sound.lean"
SPEC = "Mise/Spec/Basic.lean"
THMS = "Mise/Theorems.lean"
BASIC = "Mise/Model/Basic.lean"
GRAPH = "Mise/Frontend/Graph.lean"
TASK = "Mise/Task/Basic.lean"
CMP = "Mise/Model/Cmp.lean"

# (name, definition, file, what it does, old text, new text). Each old text
# occurs exactly once in its file.
MUTANTS = [
    ("reach-no-init", "Reach", SOUND, "no start state, so nothing is reachable",
     "  | init {st : St V} : st.Fresh → (∀ p, st.log p = none) → (∀ p, st.deps p = none) → Reach es st\n", ""),
    ("reach-no-edit", "Reach", SOUND, "drop source edits",
     "  | edit {st : St V} (p : Path) (v : V) : Reach es st → (∀ e ∈ es, p ∉ e.outs) → Reach es (st.edit p v)\n", ""),
    # Deleting `step` would leave `Reach` without `sem`, so Lean would drop
    # that argument and every use of `Reach` would fail to type-check.
    ("reach-no-step", "Reach", SOUND, "no edge can be visited",
     "Reach es st → e ∈ es → Reach es (st.step sem e)", "Reach es st → e ∈ ([] : List MEdge) → Reach es (st.step sem e)"),
    ("reach-clock-0", "Reach", SOUND, "a start state has clock 0",
     "st.Fresh → (∀ p, st.log p = none)", "st.clock = 0 → st.Fresh → (∀ p, st.log p = none)"),
    ("reach-edit-unread", "Reach", SOUND, "only a path no edge reads can be edited",
     "(∀ e ∈ es, p ∉ e.outs) → Reach es (st.edit p v)", "(∀ e ∈ es, p ∉ e.outs ∧ p ∉ e.ins) → Reach es (st.edit p v)"),
    ("reach-step-first", "Reach", SOUND, "only the first edge can be visited",
     "Reach es st → e ∈ es → Reach es (st.step sem e)", "Reach es st → e ∈ es.take 1 → Reach es (st.step sem e)"),
    ("fresh-strict", "St.Fresh", BASIC, "every mtime is earlier than the clock",
     "(∀ p v t, st.fs p = some (v, t) → t ≤ st.clock)", "(∀ p v t, st.fs p = some (v, t) → t < st.clock)"),
    ("correct-src-true", "Correct", SPEC, "sources may hold anything",
     "  (∀ k, b.isSource k = true → R k = S k) ∧\n", "  True ∧\n"),
    ("correct-tgt-true", "Correct", SPEC, "targets may hold anything",
     "  (∀ k, b.isSource k = false → R k = (b.task k).run R)\n", "  True\n"),
    ("spec-self", "Spec", THMS, "compare the result with its own sources",
     "(g.spec sem).Correct st.content (f st).content", "(g.spec sem).Correct (f st).content (f st).content"),
    ("cmdtask-no-ins", "cmdTask", GRAPH, "a static command ignores its inputs",
     "(fetchAll ins).bind fun vs => .pure (sem.exec cmd vs)", ".pure (sem.exec cmd [])"),
    ("cmdtask-static", "cmdTask", GRAPH, "a depfile command is treated as static",
     "  if dyn then sem.dyn cmd else", "  if false then sem.dyn cmd else"),
    ("issource-never", "Graph.isSource", GRAPH, "no path is a source",
     "def Graph.isSource (g : Graph) (k : Path) : Bool := (findOut GEdge.allOuts k g.edges).isNone",
     "def Graph.isSource (_ : Graph) (_ : Path) : Bool := false"),
    ("checks-true", "Checks", THMS, "every path is checked",
     "∃ o ∈ e.outs, ∃ D, st.effIns e o = some D ∧ p ∈ D", "True"),
    ("checks-outs", "Checks", THMS, "an edge's own outputs are checked",
     "st.effIns e o = some D ∧ p ∈ D", "st.effIns e o = some D ∧ (p ∈ D ∨ p ∈ e.outs)"),
    ("checks-oo", "Checks", THMS, "order-only inputs are checked",
     "st.effIns e o = some D ∧ p ∈ D", "st.effIns e o = some D ∧ (p ∈ D ∨ p ∈ e.oo)"),
    ("ran-empty", "ran", THMS, "a build runs no edge",
     "List MEdge := (buildTrace sem (edges g) st).2", "List MEdge := (buildTrace sem (edges g) st).2.take 0"),
    ("ran-first", "ran", THMS, "a build runs at most its first dirty edge",
     "List MEdge := (buildTrace sem (edges g) st).2", "List MEdge := (buildTrace sem (edges g) st).2.take 1"),
    ("edits-ignored", "St.edits", BASIC, "a list of edits changes nothing",
     "  | (p, v) :: es => (st.edit p v).edits es", "  | (_, _) :: es => st.edits es"),
    ("order-exact", "ValidOrder", THMS, "manifest order is the only valid order",
     "es.Perm (edges g) ∧ Sched es", "es = edges g ∧ Sched es"),
    ("sched-no-deps", "Sched", BASIC, "no edge reads an earlier edge's output",
     "Disjoint e.reads e'.outs ∧ Disjoint e.outs e'.outs",
     "Disjoint e.reads e'.outs ∧ Disjoint e'.reads e.outs ∧ Disjoint e.outs e'.outs"),
    ("dynok-no-source", "DynOK", GRAPH, "a depfile command may not read an undeclared source",
     "fun k => g.isSource k = true ∨ k ∈ e.allIns", "fun k => k ∈ e.allIns"),
    ("dynok-no-oo", "DynOK", GRAPH, "a depfile command may not read an order-only input",
     "fun k => g.isSource k = true ∨ k ∈ e.allIns", "fun k => g.isSource k = true ∨ k ∈ e.inputs"),
    ("fetchesonly-pure", "FetchesOnly", TASK, "only a task that fetches nothing qualifies",
     "  | fetch (k : K) (c : V → Task K V α) :\n      P k → (∀ v, FetchesOnly P (c v)) → FetchesOnly P (.fetch k c)\n", ""),
    ("wrapped-noop", "runWrapped", CMP, "a wrapped run changes nothing",
     "  if r.2 then { st.run sem e with fs := r.1 } else { st with fs := r.1 }", "  let _ := r\n  st"),
    ("wrapped-no-log", "runWrapped", CMP, "a successful wrapped run writes no log entry",
     "{ st.run sem e with fs := r.1 }", "{ st with fs := r.1, clock := st.clock + 1 }"),
]

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma|example)\b")
OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
CLOSE = set(OPEN.values())
CHAR = re.compile(r"'(?:\\.|[^\\'])'")
LET = re.compile(r"\b(?:let|have)\b")


def body_start(d):
    """The index in declaration `d` where its proof starts: the first `:=`, or
    the first line that starts with `|`, outside brackets, comments and
    strings."""
    depth, i = 0, 0
    while i < len(d):
        c = d[i]
        if d.startswith("--", i):
            i = d.find("\n", i)
            if i < 0:
                return None
            continue
        if d.startswith("/-", i):
            nest, i = 1, i + 2
            while nest and i < len(d):
                if d.startswith("/-", i):
                    nest, i = nest + 1, i + 2
                elif d.startswith("-/", i):
                    nest, i = nest - 1, i + 2
                else:
                    i += 1
            continue
        if c == '"':
            i += 1
            while i < len(d) and d[i] != '"':
                i += 2 if d[i] == "\\" else 1
        elif c == "'" and (i == 0 or not (d[i - 1].isalnum() or d[i - 1] in "_'!?")) and (m := CHAR.match(d, i)):
            i = m.end() - 1
        elif c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0 and d.startswith(":=", i) and not LET.search(d, d.rfind("\n", 0, i) + 1, i):
            return i
        elif depth == 0 and c == "\n" and d.startswith("  |", i + 1) and not d[:i].rstrip().endswith("with"):
            return i
        i += 1
    return None


def sorry_theorems(text):
    """Replace the proof of every top-level theorem with `sorry`. A
    declaration runs to the next line that starts in column 0."""
    lines = text.split("\n")
    out, i, n = [], 0, 0
    while i < len(lines):
        if not DECL.match(lines[i]):
            out.append(lines[i])
            i += 1
            continue
        j = i + 1
        while j < len(lines) and (not lines[j] or lines[j][0] in " \t"):
            j += 1
        while j > i + 1 and not lines[j - 1].strip():
            j -= 1
        d = "\n".join(lines[i:j])
        k = body_start(d)
        if k is None:
            sys.exit(f"cannot find the proof of: {lines[i]}")
        out.append(d[:k].rstrip() + " := sorry")
        n += 1
        i = j
    return "\n".join(out), n


def sh(cmd, cwd=None):
    return subprocess.run(cmd, cwd=cwd or TREE, capture_output=True, text=True)


def dur(secs):
    """`secs` as `1h02m`, `3m05s` or `42s`."""
    secs = int(secs)
    if secs >= 3600:
        return f"{secs // 3600}h{secs % 3600 // 60:02d}m"
    if secs >= 60:
        return f"{secs // 60}m{secs % 60:02d}s"
    return f"{secs}s"


class Progress:
    """The run's progress, one line at a time, so that it reads the same in
    a terminal and in a CI log: a banner for each stage, with the time since
    the run started, and for each item a stage counts, the count, the time
    in the stage and an estimate of the time left."""

    def __init__(self):
        self.start, self.stages, self.k = time.time(), [], 0
        self.lock = threading.Lock()
        self.total = self.done = 0
        self.t = self.start

    def plan(self, stages):
        self.stages = stages

    def stage(self, name, total=0):
        """Start the stage `name`, which has `total` items to count."""
        with self.lock:
            self.k = self.stages.index(name) + 1 if name in self.stages else self.k
            self.total, self.done, self.t = total, 0, time.time()
            of = f"Stage {self.k}/{len(self.stages)}: " if self.stages else ""
            n = f" ({total})" if total else ""
            print(f"\n== {of}{name}{n} · {dur(self.t - self.start)} in ==", flush=True)

    def item(self, text, done=None, total=None):
        """One item of the stage has finished; `done` and `total` replace
        the stage's own count, for a tool that counts for itself."""
        with self.lock:
            self.done = done if done is not None else self.done + 1
            total = total or self.total
            el = time.time() - self.t
            if total:
                w = len(str(total))
                left = f", ~{dur(el / self.done * (total - self.done))} left" if self.done < total else ""
                print(f"[{self.done:>{w}}/{total} {100 * self.done // total:>3}%] {text}  ({dur(el)}{left})", flush=True)
            else:
                print(f"  {text}  ({dur(el)})", flush=True)

    def note(self, text):
        with self.lock:
            print(f"  {text}", flush=True)

    def skip(self, name, why):
        with self.lock:
            k = self.stages.index(name) + 1 if name in self.stages else self.k
            print(f"\n== Stage {k}/{len(self.stages)}: {name}: skipped, {why} ==", flush=True)


P = Progress()

# The stages of a run.
COPY = "copy the tree and replace the library's proofs with sorry"
CONTROL = "build the unmutated copy"
GENERATE = "generate mutants"
MUTANTS_STAGE = "build the mutants"
TRIAGE = "triage the survivors"
COVER = "choose a smallest set of tests"


def clone(srcs, dst):
    """Copy `srcs` to `dst`, with copy-on-write clones where the file system
    has them. Timestamps are kept, so a clone of a built tree stays built."""
    args = [str(s) for s in srcs] + [str(dst)]
    if sys.platform == "darwin" and sh(["/bin/cp", "-Rc", *args], cwd=ROOT).returncode == 0:
        return
    gnu = sys.platform.startswith("linux")
    subprocess.run(["cp", "-Rp", *(["--reflink=auto"] if gnu else []), *args], check=True)


def copy_tree():
    """Copy the sources and the build directory to `TREE`."""
    shutil.rmtree(TREE, ignore_errors=True)
    (TREE / "test").mkdir(parents=True)
    items = [".lake", "Mise", "Main.lean", "Mise.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json", "fuzz"]
    tests = [p.name for p in (ROOT / "test").iterdir() if p.name != "out"]
    clone([ROOT / s for s in items], TREE)
    clone([ROOT / "test" / t for t in tests], TREE / "test")


def prepare():
    """Turn every proof in the copy's library into `sorry`."""
    lake = TREE / "lakefile.toml"
    cfg = lake.read_text()
    lib = '[[lean_lib]]\nname = "Mise"\n'
    if cfg.count(lib) != 1:
        sys.exit("lakefile.toml: cannot find the Mise library")
    lake.write_text(cfg.replace(lib, lib + 'moreLeanArgs = ["-Ddebug.byAsSorry=true"]\n'))
    total = 0
    for f in sorted((TREE / "Mise").rglob("*.lean")):
        text, n = sorry_theorems(f.read_text())
        f.write_text(text)
        total += n
    # `#eval` refuses a value that depends on `sorry`, which a definition
    # with a proof inside it now does.
    for f in sorted((TREE / "test" / "MiseTest").rglob("*.lean")):
        f.write_text(re.sub(r"^#eval ", "#eval! ", f.read_text(), flags=re.M))
    return total


ERR = re.compile(r"^error: (?:\./)*(\S+?\.lean):(\d+):\d+: ", re.M)


def lake_errors(r):
    """The errors in the output of a `lake build`, as (file, line, message)."""
    text = r.stdout + r.stderr
    marks = list(ERR.finditer(text))
    errs = []
    for a, b in zip(marks, marks[1:] + [None]):
        msg = text[a.end():b.start() if b else len(text)]
        errs.append((a.group(1), int(a.group(2)), msg))
    if r.returncode != 0 and not errs:
        errs.append(("?", 0, text[-1500:]))
    return errs


LAKE_STEP = re.compile(r"\[(\d+)/(\d+)\] Built (\S+)")


def build_watched():
    """`build()` on `TREE`, with a progress line for each module that Lake
    builds."""
    p = subprocess.Popen(["lake", "build", "MiseTest"], cwd=TREE, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True)
    out = []
    for line in p.stdout:
        out.append(line)
        if m := LAKE_STEP.search(line):
            P.item(m.group(3), int(m.group(1)), int(m.group(2)))
    p.wait()
    return lake_errors(subprocess.CompletedProcess(p.args, p.returncode, "".join(out), ""))


def build(tree=TREE, staged=False):
    """The errors of `lake build MiseTest` in `tree`. With `staged`, the
    errors of building `KILLERS` alone, if there are any."""
    if staged and (errs := lake_errors(sh(["lake", "build", *KILLERS], cwd=tree))):
        return errs
    return lake_errors(sh(["lake", "build", "MiseTest"], cwd=tree))


def verdict(errs):
    """(verdict, kind, where) for one mutant's build errors."""
    if not errs:
        return "SURVIVED", "", ""
    lib = [e for e in errs if e[0].startswith("Mise/") or e[0] == "?"]
    if lib:
        f, line, msg = lib[0]
        return "error", "library", f"`{f}:{line}`: {msg.strip().splitlines()[0][:80]}"
    evaluates = any("proved that the proposition" in m or "did not evaluate to `true`" in m for _, _, m in errs)
    where = sorted({f"{f.removeprefix('test/MiseTest/')}:{line}" for f, line, _ in errs})
    return "killed", "evaluates" if evaluates else "elaborates", ", ".join(where[:4]) + (" …" if len(where) > 4 else "")


# The names of the generated mutants.
GENERATED = set()

# The effect of each mutant on the theorems: "weaker" when it weakens at
# least one, else "unknown" or "stronger". A mutant in `MUTANTS` weakens one.
EFFECT = {}
EFFECTS = ["weaker", "unknown", "stronger"]


def mutate(data, m):
    """The bytes `data` of mutant `m`'s file with its edit applied: a text
    replacement for a mutant in `MUTANTS`, a byte range `(start, stop)` for
    a generated one."""
    _, _, _, _, old, new = m
    if isinstance(old, tuple):
        return data[:old[0]] + new.encode() + data[old[1]:]
    return data.replace(old.encode(), new.encode())


def generate(keep_all):
    """The mutants of `MiseTest.MutantGen`, run in the prepared and built
    copy, as `MUTANTS` rows, without those that repeat an earlier mutant."""
    out = OUT / "generated.json"
    r = subprocess.run(["lake", "env", "lean", "test/MiseTest/MutantGen.lean"], cwd=TREE,
                       capture_output=True, text=True, env={**os.environ, "MUTANTS_OUT": str(out)})
    if r.returncode != 0:
        sys.exit(f"MutantGen failed:\n{(r.stdout + r.stderr)[-2000:]}")
    P.note(r.stdout.strip().splitlines()[-1])
    seen = {(m[2], mutate((TREE / m[2]).read_bytes(), m)) for m in MUTANTS}
    rows, repeats = [], 0
    for g in json.loads(out.read_text())["mutants"]:
        if not (g["keep"] or keep_all):
            continue
        m = (g["name"], g["decl"], g["file"], g["what"], (g["start"], g["stop"]), g["text"])
        key = (m[2], mutate((TREE / m[2]).read_bytes(), m))
        if key in seen:
            repeats += 1
            continue
        seen.add(key)
        rows.append(m)
        effs = set(g["effects"].values())
        EFFECT[m[0]] = next((e for e in EFFECTS if e in effs), "unknown")
    P.note(f"{len(rows)} generated mutants, after {repeats} that repeat another")
    return rows


HEADER = ["| Mutant | Definition | Change | Verdict | Kill | Where |", "|---|---|---|---|---|---|"]
RESULTS = OUT / "results.md"
RESULTS_LOCK = threading.Lock()


def table_row(r):
    """The line of results row `r` in the results table."""
    return f"| `{r[0]}` | `{r[1]}` | {r[2].replace('|', chr(92) + '|')} | {r[3]} | {r[4]} | {r[5]} |"


def row(m, errs, secs):
    """The results row of mutant `m`, printed and appended to the results
    table as it finishes, so that a run that stops keeps the rows so far."""
    name, defn, _, what, _, _ = m
    v, kind, where = verdict(errs)
    if v == "error" and name in GENERATED:
        v = "stillborn"
    P.item(f"{name}: {v}{f' ({kind})' if kind else ''}{f'; {where}' if where else ''}; {secs:.0f}s")
    r = name, defn, what, v, kind, where
    with RESULTS_LOCK, RESULTS.open("a") as f:
        f.write(table_row(r) + "\n")
    return r


def via_lake(m):
    """Build mutant `m` in its own clone of `TREE`; its results row."""
    name, _, f, _, _, _ = m
    tree = WORK / name
    clone([TREE], tree)
    (tree / f).write_bytes(mutate((tree / f).read_bytes(), m))
    t = time.time()
    errs = build(tree, staged=True)
    shutil.rmtree(tree)
    return [row(m, errs, time.time() - t)]


def module_of(f):
    """The module name of a file in the tree."""
    return f.removeprefix("test/").removesuffix(".lean").replace("/", ".")


def file_of(mod):
    """The file of a module in the tree, relative to it."""
    return ("test/" if mod.split(".")[0] == "MiseTest" else "") + mod.replace(".", "/") + ".lean"


def module_graph(roots=("MiseTest",)):
    """The imports of each module that `lake build MiseTest` builds, or that
    `roots` reach."""
    imps, todo = {}, list(roots)
    while todo:
        mod = todo.pop()
        if mod in imps or not (TREE / file_of(mod)).exists():
            continue
        imps[mod] = re.findall(r"^import (\S+)", (TREE / file_of(mod)).read_text(), re.M)
        todo += imps[mod]
    return imps


def stages(imps, mod, killers=KILLERS, first_only=False):
    """The stages of the in-process build of a mutant of `mod`: the modules
    that `mod` reaches and that `KILLERS` import, then every module that
    `mod` reaches. Each stage is in import order, with the imports it needs
    from outside itself. A stage is closed under imports within the modules
    `mod` reaches, so the modules outside it are unchanged and come from
    their `.olean` files."""
    reach = {mod}
    while more := {m for m, ii in imps.items() if m not in reach and reach.intersection(ii)}:
        reach |= more
    up, todo = set(), list(killers)
    while todo:
        m = todo.pop()
        if m in imps and m not in up:
            up.add(m)
            todo += imps[m]
    order = []
    def visit(m):
        if m in reach and m not in order:
            for i in imps[m]:
                visit(i)
            order.append(m)
    for m in sorted(reach):
        visit(m)
    out = []
    for part in [reach & up] if first_only else [reach & up, reach]:
        if not part or (out and part == reach & up):
            continue
        mods = [m for m in order if m in part]
        out.append({
            "imports": sorted({i for m in mods for i in imps[m] if i not in part}),
            "modules": [{"name": m, "file": file_of(m), "imports": [i for i in imps[m] if i in part],
                         "byAsSorry": file_of(m).startswith("Mise")} for m in mods]})
    return out


class Worker:
    """One `test/trust-mutants.lean` process, fed one mutant at a time."""

    def __init__(self, plan, tag):
        self.plan, self.log = plan, WORK / f"{tag}.stderr"
        self.p, self.seen = None, set()

    def run(self, mod, m):
        """The errors of mutant `m` of module `mod`, or of the unmutated
        control when `m` is None. A crash is an error, and the next call
        starts a new process."""
        if self.p is not None and mod not in self.seen:
            # The process keeps the imports of every module it has loaded, so
            # a new module gets a new process.
            self.close()
        if self.p is None:
            self.p = subprocess.Popen(["lake", "env", "lean", "--run", str(INPROC), str(self.plan)], cwd=TREE,
                                      stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                      stderr=self.log.open("a"), text=True)
            self.seen = set()
        self.seen.add(mod)
        src = mutate((TREE / m[2]).read_bytes(), m).decode() if m else None
        other = []
        try:
            self.p.stdin.write(json.dumps({"name": m[0] if m else "", "module": mod, "src": src}) + "\n")
            self.p.stdin.flush()
            for line in self.p.stdout:
                if line.startswith("{"):
                    r = json.loads(line)
                    return [(e["file"], e["line"], e["msg"]) for e in r["errors"]], r["secs"]
                other.append(line)
        except BrokenPipeError:
            pass
        self.p.kill()
        self.p.wait()
        self.p = None
        err = " ".join(("".join(other) + self.log.read_text()).split())[:300] or "no output"
        return [("?", 0, f"the in-process build stopped ({err}); rerun with `--via lake`")], 0

    def close(self):
        if self.p:
            self.p.stdin.close()
            self.p.wait()
            self.p = None


# The seconds between the starts of two in-process workers (see the header).
STAGGER = 5


def run_inproc(todo, jobs, ex):
    """Build the mutants in `todo` on `jobs` workers, each a long-lived Lean
    process, with the unmutated control first; the futures of their rows.
    A worker prefers a mutant of the module it has loaded."""
    imps = module_graph()
    plans = {mod: stages(imps, mod) for mod in {module_of(m[2]) for m in todo}}
    plan = WORK / "plan.json"
    plan.write_text(json.dumps([{"module": mod, "stages": st} for mod, st in plans.items()]))
    # The control runs every stage, from the module that reaches the most.
    top = max(plans, key=lambda mod: len(plans[mod][-1]["modules"]))
    pending = [(top, None)] + sorted(((module_of(m[2]), m) for m in todo),
                                     key=lambda x: -len(plans[x[0]][0]["modules"]))
    lock = threading.Lock()

    def work(k):
        time.sleep(k * STAGGER)
        w, rows = Worker(plan, f"worker-{k}"), []
        while True:
            with lock:
                if not pending:
                    break
                mod, m = pending.pop(next((i for i, (mod, _) in enumerate(pending) if mod in w.seen), 0))
            errs, secs = w.run(mod, m)
            rows.append(row(m, errs, secs) if m else ("(unmutated)", errs))
        w.close()
        return rows

    return [ex.submit(work, k) for k in range(jobs)]


# The peak memory of one in-process worker, in GB (see the header).
JOB_GB = 4


def default_jobs():
    """The number of CPUs, at most one per `JOB_GB` of physical memory."""
    mem = os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES") / 2**30
    return max(1, min(os.cpu_count() or 2, int(mem // JOB_GB)))


def edit_of(m):
    """Mutant `m` as `MutantCheck` reads it: a byte range of its file in
    `TREE` and the text that replaces it."""
    name, _, f, _, old, new = m
    if isinstance(old, (tuple, list)):
        start, stop = old
    else:
        start = (TREE / f).read_bytes().find(old.encode())
        stop = start + len(old.encode())
    return {"name": name, "file": f, "start": start, "stop": stop, "text": new}


def triage_poll(tri, k, out):
    """`out` with the triage results that the `k` processes have written
    since, each reported as it arrives."""
    for i in range(k):
        f = tri / f"out-{i}.jsonl"
        if not f.exists():
            continue
        for line in f.read_text().splitlines():
            if not line.endswith("}"):
                continue
            r = json.loads(line)
            if r["name"] in out:
                continue
            out[r["name"]] = r
            why = "" if r["verdict"] != "undecided" else f": {' '.join(r['detail'].split())[:90]}"
            P.item(f"{r['name']}: {r['verdict']}{why}")
    return out


def triage(todo, rows, jobs, samples):
    """The triage of the mutants that survive, by `MutantCheck` on `jobs`
    processes: for each, its `verdict` ("distinguished", "equivalent" or
    "undecided") and the rest of its result."""
    live = {r[0] for r in rows if r[3] == "SURVIVED"}
    edits = sorted((edit_of(m) for m in todo if m[0] in live), key=lambda e: (e["file"], e["start"]))
    if not edits:
        P.skip(TRIAGE, "no survivors")
        return {}
    P.stage(TRIAGE, len(edits))
    tri = OUT / "triage"
    shutil.rmtree(tri, ignore_errors=True)
    tri.mkdir(parents=True)
    # Contiguous chunks, so that each process elaborates few files again.
    k = min(jobs, len(edits))
    procs, out = [], {}
    for i in range(k):
        chunk = edits[len(edits) * i // k:len(edits) * (i + 1) // k]
        (tri / f"in-{i}.json").write_text(json.dumps(chunk))
        (tri / f"out-{i}.jsonl").write_text("")
        procs.append(subprocess.Popen(
            ["lake", "env", "lean", "--run", str(CHECK), str(tri / f"in-{i}.json"), str(tri / f"out-{i}.jsonl")],
            cwd=TREE, stdout=(tri / f"log-{i}.txt").open("w"), stderr=subprocess.STDOUT,
            env={**os.environ, "MUTANT_SAMPLES": str(samples)}))
        time.sleep(STAGGER)
        out = triage_poll(tri, k, out)
    while any(p.poll() is None for p in procs):
        time.sleep(1)
        out = triage_poll(tri, k, out)
    out = triage_poll(tri, k, out)
    for e in edits:
        out.setdefault(e["name"], {"name": e["name"], "verdict": "undecided",
                                   "detail": f"MutantCheck stopped; see {tri.relative_to(ROOT)}/log-*.txt"})
    return out


CANDIDATES = "MiseTest.Candidates"


def min_cover(kills, cost):
    """A smallest set of the tests in `kills` (test -> mutants it kills) that
    kills every mutant some test kills, the cheapest by `cost` among those;
    and whether the search proved it smallest. Each connected group of
    tests is searched exactly, or greedily when the search runs too long."""
    killers = {}
    for t, ms in kills.items():
        for m in ms:
            killers.setdefault(m, set()).add(t)
    # Connected groups: mutants joined by a test that kills both.
    group = {m: m for m in killers}
    def find(m):
        while group[m] != m:
            group[m] = group[group[m]]
            m = group[m]
        return m
    for ms in kills.values():
        ms = list(ms)
        for m in ms[1:]:
            group[find(m)] = find(ms[0])
    parts = {}
    for m in killers:
        parts.setdefault(find(m), set()).add(m)
    chosen, exact = set(), True
    for part in parts.values():
        tests = {t for m in part for t in killers[m]}
        best = None
        nodes = [0]
        def search(left, picked, c):
            nonlocal best
            nodes[0] += 1
            if nodes[0] > 200000:
                raise TimeoutError
            if best and (len(picked), c) >= (len(best[0]), best[1]):
                return
            if not left:
                best = (set(picked), c)
                return
            # Branch on the mutant with the fewest killers.
            m = min(left, key=lambda m: len(killers[m]))
            for t in sorted(killers[m] & tests, key=lambda t: (-len(kills[t] & left), cost[t])):
                picked.append(t)
                search(left - kills[t], picked, c + cost[t])
                picked.pop()
        try:
            search(set(part), [], 0)
        except TimeoutError:
            exact = False
            left, best = set(part), (set(), 0)
            while left:
                t = max(tests, key=lambda t: (len(kills[t] & left), -cost[t]))
                best[0].add(t)
                left -= kills[t]
        chosen |= best[0]
    return chosen, exact


def cover(jobs):
    """Build each distinguished survivor of the last triage against all the
    tests the triage wrote, and choose a smallest set of them that kills
    every one: the kill matrix and the cover, written to `OUT`. Its summary,
    and whether every mutant behaved as expected."""
    last = json.loads((OUT / "rows.json").read_text())
    todo = {m[0]: tuple(m[:4]) + (tuple(m[4]) if isinstance(m[4], list) else m[4], m[5]) for m in last["todo"]}
    tri = {r["name"]: r for f in sorted((OUT / "triage").glob("out-*.jsonl"))
           for r in map(json.loads, f.read_text().splitlines())}
    dist = sorted(n for n, r in tri.items() if r["verdict"] == "distinguished" and n in todo)
    if not dist:
        P.skip(COVER, "no distinguished survivors")
        return None, True
    P.stage(COVER, len(dist))
    # One test per mutant, each in its own range of lines.
    # The library alone, so that a mutant elaborates no other test module.
    lines = ["import Mise", ""]
    span = {}
    for n in dist:
        lines.append(f"-- {n}")
        a = len(lines) + 1
        lines += tri[n]["test"].splitlines()
        span[n] = (a, len(lines))
        lines.append("")
    path = file_of(CANDIDATES)
    (TREE / path).write_text("\n".join(lines) + "\n")
    def test_at(line):
        return next((n for n, (a, b) in span.items() if a <= line <= b), None)

    imps = module_graph(("MiseTest", CANDIDATES))
    mods = {module_of(todo[n][2]) for n in dist}
    plans = {mod: stages(imps, mod, [CANDIDATES], first_only=True) for mod in mods}
    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir()
    plan = WORK / "plan.json"
    plan.write_text(json.dumps([{"module": mod, "stages": st} for mod, st in plans.items()]))
    pending = [(None, None)] + sorted((module_of(todo[n][2]), todo[n]) for n in dist)
    lock = threading.Lock()
    failed = {}

    def work(k):
        time.sleep(k * STAGGER)
        w = Worker(plan, f"cover-{k}")
        while True:
            with lock:
                if not pending:
                    break
                mod, m = pending.pop(next((i for i, (mod, _) in enumerate(pending) if mod in w.seen), 0))
            # The control: the unmutated module that reaches the most.
            if m is None:
                mod = max(plans, key=lambda mod: len(plans[mod][0]["modules"]))
            errs, secs = w.run(mod, m)
            with lock:
                failed[m[0] if m else None] = errs
            n = len({test_at(e[1]) for e in errs if e[0] == path})
            if m:
                P.item(f"{m[0]}: {n} of {len(dist)} tests fail; {secs:.0f}s")
            else:
                P.note(f"the unmutated copy fails {n} tests (must be 0)")
        w.close()

    with ThreadPoolExecutor(jobs) as ex:
        for fu in [ex.submit(work, k) for k in range(jobs)]:
            fu.result()
    if failed[None]:
        f, line, msg = failed[None][0]
        sys.exit(f"the unmutated tree fails a candidate test, {f}:{line}: {msg.strip()[:300]}")
    kills, odd = {n: set() for n in dist}, []
    for n in dist:
        other = [e for e in failed[n] if e[0] != path]
        if other:
            odd.append(f"{n}: an error outside the tests, {other[0][0]}:{other[0][1]}")
        for e in failed[n]:
            if e[0] == path and (t := test_at(e[1])):
                kills[t].add(n)
    for n in dist:
        if n not in kills[n]:
            odd.append(f"{n}: its own test does not kill it")
    cost = {t: len(tri[t]["test"]) for t in dist}
    chosen, exact = min_cover(kills, cost)
    covered = set().union(*(kills[t] for t in chosen)) if chosen else set()
    out = [f"-- {len(chosen)} tests kill the {len(covered)} distinguished survivors that any test kills"
           f"{'' if exact else ' (greedy for some groups, so perhaps not the fewest)'}.", ""]
    for t in sorted(chosen, key=lambda t: (todo[t][1], t)):
        out += [f"-- kills {', '.join(sorted(kills[t]))}", tri[t]["test"], ""]
    (OUT / "cover.lean").write_text("\n".join(out))
    (OUT / "kills.json").write_text(json.dumps({t: sorted(ms) for t, ms in kills.items()}, indent=1))
    summary = (f"{out[0].removeprefix('-- ')} They are in {(OUT / 'cover.lean').relative_to(ROOT)}, "
               f"the kill matrix in {(OUT / 'kills.json').relative_to(ROOT)}.")
    for o in odd:
        P.note(o)
    P.note(summary)
    return summary, not odd


def cell(s):
    """`s` as one cell of a Markdown table."""
    return " ".join(s.split()).replace("|", "\\|")


def report(rows, tri, secs, via, cov=None):
    """The results report: a summary, every mutant, then the survivors by
    effect with their triage, and the tests that kill those with a witness."""
    v = {r[0]: ("equivalent" if r[3] == "SURVIVED" and tri.get(r[0], {}).get("verdict") == "equivalent" else r[3])
         for r in rows}
    n = {x: sum(y == x for y in v.values()) for x in ["killed", "equivalent", "stillborn", "SURVIVED", "error"]}
    live = [r for r in rows if v[r[0]] == "SURVIVED"]
    dist = [r for r in live if tri.get(r[0], {}).get("verdict") == "distinguished"]
    lines = [f"{n['killed']} of {len(rows) - n['stillborn'] - n['equivalent']} mutants killed "
             f"({n['equivalent']} equivalent, {n['stillborn']} stillborn); {len(live)} survive, "
             f"{len(dist)} of them with a witness; {n['error']} errors; {secs:.0f} s, via {via}.", ""]
    if cov:
        lines += [cov, ""]
    lines += HEADER + [table_row((r[0], r[1], r[2], v[r[0]], r[4], r[5])) for r in rows]
    if live:
        lines += ["", "## Survivors", "",
                  "By effect on the theorems, then definition. A witness is an input on which the "
                  "definition and the mutant differ.", "",
                  "| Mutant | Definition | Change | Effect | Triage | Detail |", "|---|---|---|---|---|---|"]
        order = sorted(live, key=lambda r: (EFFECTS.index(EFFECT.get(r[0], "weaker")), r[1], r[0]))
        for r in order:
            t = tri.get(r[0], {})
            lines.append(f"| `{r[0]}` | `{r[1]}` | {cell(r[2])} | {EFFECT.get(r[0], 'weaker')} | "
                         f"{t.get('verdict', '')} | {cell(t.get('detail', ''))[:300]} |")
    if dist:
        lines += ["", "## Tests that kill the survivors", "",
                  "Each test states the unmutated definition's result on a witness, so it passes now "
                  "and fails on its mutant.", "", "```lean"]
        for r in sorted(dist, key=lambda r: (r[1], r[0])):
            lines += [f"-- {r[0]}: {' '.join(r[2].split())}", tri[r[0]]["test"], ""]
        lines[-1:] = ["```"]
    return "\n".join(lines) + "\n", len(live) == 0 and n["error"] == 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("only", nargs="*", help="run only these mutants")
    ap.add_argument("-j", "--jobs", type=int, default=default_jobs(),
                    help=f"builds to run at once (default: the number of CPUs, at most one per {JOB_GB} GB of memory)")
    ap.add_argument("--via", choices=["inproc", "lake"], default="inproc",
                    help="build mutants in long-lived Lean processes (default), or with lake build")
    ap.add_argument("--generated", action="store_true", help="add the mutants of MiseTest.MutantGen")
    ap.add_argument("--all-edits", action="store_true",
                    help="with --generated, also run the edits that only strengthen theorems")
    ap.add_argument("--no-triage", action="store_true", help="do not triage the mutants that survive")
    ap.add_argument("--retriage", action="store_true",
                    help="triage the survivors of the last run again, without building any mutant")
    ap.add_argument("--samples", type=int, default=100000,
                    help="random samples per survivor in the triage (default: 100000)")
    ap.add_argument("--cover", action="store_true",
                    help="only choose a smallest set of the last triage's tests that kills its distinguished survivors")
    ap.add_argument("--no-cover", action="store_true",
                    help="do not choose a smallest set of tests after the triage")
    a = ap.parse_args()
    start = time.time()
    if a.cover:
        P.plan([COVER])
        _, ok = cover(a.jobs)
        return 0 if ok else 1
    after = ([] if a.no_triage else [TRIAGE]) + ([] if a.no_triage or a.no_cover else [COVER])
    if a.retriage:
        P.plan(after)
        last = json.loads((OUT / "rows.json").read_text())
        rows = [tuple(r) for r in last["rows"]]
        todo = [tuple(m[:4]) + (tuple(m[4]) if isinstance(m[4], list) else m[4], m[5]) for m in last["todo"]]
        GENERATED.update(last["generated"])
        EFFECT.update(last["effect"])
        tri = triage([m for m in todo if not a.only or m[0] in a.only], rows, a.jobs, a.samples)
        cov, cok = cover(a.jobs) if COVER in after else (None, True)
        return finish(rows, tri, last["secs"] + time.time() - start, last["via"], cov, cok)
    P.plan([COPY, CONTROL] + ([GENERATE] if a.generated else []) + [MUTANTS_STAGE] + after)
    P.stage(COPY)
    copy_tree()
    for name, _, f, _, old, _ in MUTANTS:
        c = (TREE / f).read_text().count(old)
        if c != 1:
            sys.exit(f"{name}: the text to replace occurs {c} times in {f}")
    n = prepare()
    P.note(f"{n} theorems replaced with sorry")
    P.stage(CONTROL)
    errs = build_watched()
    P.note(f"the unmutated copy {'fails' if errs else 'passes'}")
    if errs:
        for f, line, msg in errs[:5]:
            print(f"  {f}:{line}: {msg.strip()[:300]}")
        sys.exit("the unmutated tests fail; mutant results would mean nothing")
    todo = list(MUTANTS)
    if a.generated:
        P.stage(GENERATE)
        gen = generate(a.all_edits)
        GENERATED.update(m[0] for m in gen)
        todo += gen
    unknown = set(a.only) - {m[0] for m in todo}
    if unknown:
        sys.exit(f"unknown mutants: {sorted(unknown)}")
    todo = [m for m in todo if not a.only or m[0] in a.only]

    shutil.rmtree(WORK, ignore_errors=True)
    WORK.mkdir()
    RESULTS.write_text("\n".join([f"Running {len(todo)} mutants via {a.via}; rows in the order they finish.", ""] + HEADER) + "\n")
    P.stage(MUTANTS_STAGE, len(todo))
    with ThreadPoolExecutor(a.jobs) as ex:
        if a.via == "lake":
            futures = [ex.submit(via_lake, m) for m in todo]
        else:
            futures = run_inproc(todo, a.jobs, ex)
        results = [r for fu in as_completed(futures) for r in fu.result()]
    control = [r[1] for r in results if r[0] == "(unmutated)"]
    if control and control[0]:
        for f, line, msg in control[0][:5]:
            print(f"  {f}:{line}: {msg.strip()[:300]}")
        sys.exit("the unmutated tests fail in the in-process build, though Lake passes them; rerun with `--via lake`")
    done = {r[0]: r for r in results if r[0] != "(unmutated)"}
    rows = [done[m[0]] for m in todo]
    # What `--retriage` needs to triage these survivors again.
    (OUT / "rows.json").write_text(json.dumps({
        "rows": rows, "todo": todo, "generated": sorted(GENERATED), "effect": EFFECT,
        "secs": time.time() - start, "via": a.via}))
    tri = {} if a.no_triage else triage(todo, rows, a.jobs, a.samples)
    cov, cok = cover(a.jobs) if COVER in after else (None, True)
    return finish(rows, tri, time.time() - start, a.via, cov, cok)


def finish(rows, tri, secs, via, cov, cover_ok):
    """Write the report, print its summary, and return the exit status."""
    text, ok = report(rows, tri, secs, via, cov)
    RESULTS.write_text(text)
    print(f"\n== Done in {dur(time.time() - P.start)} ==", flush=True)
    print(text.split("\n")[0])
    if cov:
        print(cov)
    print(f"The full report is in {RESULTS.relative_to(ROOT)}.")
    return 0 if ok and cover_ok else 1


if __name__ == "__main__":
    sys.exit(main())
