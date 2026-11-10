#!/usr/bin/env python3
"""Stage 6 and 7 property harness against real Ninja.

For each example, run sequences of edits. A sequence starts with a clean
build, then applies edits one at a time, running `ninja` after each with a
random `-j` level, so that Ninja runs independent commands in different
orders.

The edit kinds come from a de Bruijn sequence of order K (`--order`, default
3), which contains every ordered run of K edit kinds exactly once. It is cut
into sequences of at most `--length` edits that overlap by K - 1, so every
run appears whole in some sequence. `--repeat` covers it again with the edit
kinds in a different order and fresh values. The edits' values (which
version of a file, which flag) are random. `--random N` instead runs N
sequences of 1 to 6 random edits. Both modes report how many ordered pairs
and triples of edit kinds they covered.
After every build it checks three things:

1. every build product equals, byte for byte, the product of a clean build
   of the same sources in a separate directory;
2. `ninja -n` reports no work;
3. `ninja -t missingdeps` finds nothing.

Edits change a source file, add or remove an `#include`, change the
generator script, add a comment to `config.in` (which leaves the generated
header the same, so the `restat` generator keeps it), or change `cflags` in
the DSL and regenerate the manifest. After a comment edit the harness also
checks that only the generator ran (early cutoff).

Sequences are independent, so they run in parallel, each in its own
directory with its own random generator seeded from the seed, the example and
the sequence number. A run gives the same results whatever the number of
workers. Clean builds are cached on disk by the hash of their sources and
manifest, and shared between workers.

A manifest depends only on `cflags`, so `mise gen` runs once per example and
flag before the sequences start. Compiles go through ccache, which `cc`
resolves to through a symlink on PATH; a cache hit gives the same object and
depfile as a real compile, so a build that skips a needed command still
leaves a stale product. `--no-ccache` runs the compiler directly.

usage: props.py [--order K] [--length L] [--repeat R] [--random N]
                [--seed S] [--workers W] [--no-ccache] [EXAMPLE...]
"""
import argparse
import hashlib
import os
import random
import shutil
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MISE = ROOT / ".lake" / "build" / "bin" / "mise"
OUT = ROOT / "test" / "out" / "props"
CCACHE_DIR = ROOT / "test" / "out" / "ccache"
FLAGS = ["-O2 -Wall", "-O0", "-O1 -DMISE_FLAG=1"]
JOBS = ["-j1", "-j2", "-j8"]


class HelloC:
    name = "hello-c"
    products = ["build/main.o", "build/greet.o", "build/hello"]
    toml = (ROOT / "examples" / "hello-c" / "mise.toml").read_text()

    def initial(self):
        return {"main": 0, "greet": 0, "header": 0, "flag": 0}

    def render(self, s):
        return {
            "mise.toml": self.toml,
            "greet.h": f"#pragma once\n#define GREET_N {s['header']}\nvoid greet(void);\n",
            "greet.c": '#include <stdio.h>\n#include "greet.h"\n'
                       f'void greet(void) {{ printf("Hello %d %d\\n", GREET_N, {s["greet"]}); }}\n',
            "main.c": '#include "greet.h"\n'
                      f'int main(void) {{ greet(); return {s["main"]} * 0; }}\n',
        }

    def edits(self):
        return [("bump", "main"), ("bump", "greet"), ("bump", "header"), ("flag",)]


class GenHeader:
    name = "gen-header"
    products = ["build/config.h", "build/main.o", "build/util.o", "build/app"]
    generator = (ROOT / "examples" / "gen-header" / "gen-config.py").read_text()
    toml = (ROOT / "examples" / "gen-header" / "mise.toml").read_text()

    def initial(self):
        return {"main": 0, "util": 0, "utilh": 0, "extra": 0, "cfg": 0, "gen": 0, "note": 0,
                "main_extra": False, "util_extra": False, "flag": 0}

    @staticmethod
    def c_file(includes, body):
        lines = ["#include <stdio.h>"] + [f'#include "{h}"' for h in includes]
        lines += ["#ifndef EXTRA", "#define EXTRA -1", "#endif", body, ""]
        return "\n".join(lines)

    def render(self, s):
        main_inc = ["config.h"] + (["extra.h"] if s["main_extra"] else []) + ["util.h"]
        util_inc = ["config.h", "util.h"] + (["extra.h"] if s["util_extra"] else [])
        return {
            "mise.toml": self.toml,
            "main.c": self.c_file(main_inc, 'int main(void) { greet("mise", TIMES); '
                                  f'printf("main %d %d\\n", {s["main"]}, EXTRA); return 0; }}'),
            "util.c": self.c_file(util_inc, "void greet(const char *who, int times) { "
                                  'for (int i = 0; i < times; i++) printf("%s, %s! %d %d\\n", '
                                  f'GREETING, who, {s["util"]}, EXTRA); }}'),
            "util.h": f"#pragma once\nvoid greet(const char *who, int times);\n/* {s['utilh']} */\n",
            "extra.h": f"#pragma once\n#define EXTRA {s['extra']}\n",
            "config.in": f'# note {s["note"]}\nGREETING="Hello {s["cfg"]}"\nTIMES={1 + s["cfg"] % 3}\n',
            "gen-config.py": self.generator + f"# version {s['gen']}\n",
        }

    def edits(self):
        return [("bump", k) for k in ["main", "util", "utilh", "extra", "cfg", "gen", "note"]] + \
               [("toggle", "main_extra"), ("toggle", "util_extra"), ("flag",)]


def run(cmd, cwd):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"{' '.join(cmd)} failed in {cwd}:\n{r.stdout}{r.stderr}")
    return r.stdout


def write_files(d, files, old=None):
    for name, text in files.items():
        if old is None or old.get(name) != text:
            (d / name).write_text(text)


def manifests(ex):
    """The manifest for each flag, generated by `mise gen`."""
    ms = []
    for i, flag in enumerate(FLAGS):
        d = OUT / "manifests" / ex.name / str(i)
        d.mkdir(parents=True)
        write_files(d, ex.render(ex.initial()))
        run([str(MISE), "gen", "--set", f"cflags={flag}", str(d)], ROOT)
        ms.append((d / "build.ninja").read_bytes())
    return ms


def products(d, names):
    return {n: (d / n).read_bytes() for n in names}


class Checker:
    def __init__(self, ex):
        self.ex = ex
        self.clean_builds = 0

    def clean(self, files, manifest):
        """The products of a clean build, from the on-disk cache when another
        sequence has already built the same sources and manifest."""
        h = hashlib.sha256()
        for name in sorted(files):
            h.update(name.encode() + b"\0" + files[name].encode() + b"\0")
        h.update(manifest)
        d = OUT / "clean" / self.ex.name / h.hexdigest()
        if not d.exists():
            # Build in a private directory, then rename it into place; if
            # another worker got there first, keep theirs.
            tmp = d.with_name(f"{d.name}.{os.getpid()}")
            shutil.rmtree(tmp, ignore_errors=True)
            tmp.mkdir(parents=True)
            write_files(tmp, files)
            (tmp / "build.ninja").write_bytes(manifest)
            run(["ninja"], tmp)
            try:
                tmp.rename(d)
                self.clean_builds += 1
            except OSError:
                shutil.rmtree(tmp)
        return products(d, self.ex.products)

    def check(self, d, files, where):
        expected = self.clean(files, (d / "build.ninja").read_bytes())
        actual = products(d, self.ex.products)
        for n in self.ex.products:
            if actual[n] != expected[n]:
                raise AssertionError(f"{where}: {n} differs from a clean build")
        if "no work to do" not in run(["ninja", "-n"], d):
            raise AssertionError(f"{where}: ninja -n has work to do")
        md = run(["ninja", "-t", "missingdeps"], d)
        if "No missing dependencies" not in md:
            raise AssertionError(f"{where}: missingdeps reported:\n{md}")


def de_bruijn(n, k):
    """A cyclic sequence over range(n) containing every length-k word once."""
    a, out = [0] * (k + 1), []

    def db(t, p):
        if t > k:
            if k % p == 0:
                out.extend(a[1:p + 1])
        else:
            a[t] = a[t - p]
            db(t + 1, p)
            for j in range(a[t - p] + 1, n):
                a[t] = j
                db(t + 1, t)
    db(1, 1)
    return out


def plan(name, order, length, repeat, seed):
    """Edit-kind indices for each sequence, covering every run of `order` kinds."""
    n = len(EXAMPLES[name]().edits())
    plans = []
    for r in range(repeat):
        perm = list(range(n))
        random.Random(f"{seed}:{name}:perm:{r}").shuffle(perm)
        cyc = de_bruijn(n, order)
        line = [perm[i] for i in cyc + cyc[:order - 1]]
        step = length - (order - 1)
        for i in range(0, max(len(line) - (order - 1), 1), step):
            plans.append(line[i:i + length])
    return plans


def coverage(histories):
    """Distinct ordered pairs and triples of consecutive edit kinds."""
    def runs(k):
        return {tuple(h[i:i + k]) for h in histories for i in range(len(h) - k + 1)}
    return len(runs(2)), len(runs(3))


def sequence(name, seed, idx, ms, kinds=None):
    """Run one sequence of the given edit kinds, or random ones when `kinds` is
    None; return the kinds applied and the number of new clean builds."""
    ex = EXAMPLES[name]()
    checker = Checker(ex)
    rng = random.Random(f"{seed}:{name}:{idx}")
    d = OUT / "inc" / name / str(idx)
    shutil.rmtree(d, ignore_errors=True)
    d.mkdir(parents=True)
    state = ex.initial()
    files = ex.render(state)
    write_files(d, files)
    (d / "build.ninja").write_bytes(ms[state["flag"]])
    run(["ninja", rng.choice(JOBS)], d)
    history = ["clean build"]
    checker.check(d, files, f"sequence {idx}, after {history}")
    applied = []
    steps = kinds if kinds is not None else [None] * rng.randint(1, 6)
    for kind in steps:
        edit = ex.edits()[kind] if kind is not None else rng.choice(ex.edits())
        applied.append(ex.edits().index(edit))
        new = dict(state)
        if edit[0] == "bump":
            new[edit[1]] = rng.choice([v for v in range(5) if v != state[edit[1]]])
        elif edit[0] == "toggle":
            new[edit[1]] = not state[edit[1]]
        else:
            new["flag"] = rng.choice([i for i in range(len(FLAGS)) if i != state["flag"]])
        new_files = ex.render(new)
        write_files(d, new_files, files)
        if new["flag"] != state["flag"]:
            (d / "build.ninja").write_bytes(ms[new["flag"]])
        before = {n: (d / n).stat().st_mtime_ns for n in ex.products}
        out = run(["ninja", rng.choice(JOBS)], d)
        history.append(" ".join(map(str, edit)))
        if edit == ("bump", "note"):
            after = {n: (d / n).stat().st_mtime_ns for n in ex.products}
            if after != before or out.count("GEN ") != 1 or "CC " in out or "LINK " in out:
                raise AssertionError(f"sequence {idx}, after {history}: no early cutoff:\n{out}")
        state, files = new, new_files
        checker.check(d, files, f"sequence {idx}, after {history}")
    shutil.rmtree(d)  # kept only when a check fails
    return applied, checker.clean_builds


EXAMPLES = {"hello-c": HelloC, "gen-header": GenHeader}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--order", type=int, default=3)
    ap.add_argument("--length", type=int, default=6)
    ap.add_argument("--repeat", type=int, default=1)
    ap.add_argument("--random", type=int, metavar="N")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--workers", type=int, default=os.cpu_count())
    ap.add_argument("--no-ccache", action="store_true")
    ap.add_argument("examples", nargs="*", default=list(EXAMPLES))
    args = ap.parse_args()
    if args.length < args.order:
        ap.error("--length must be at least --order")
    shutil.rmtree(OUT, ignore_errors=True)
    if not args.no_ccache:
        ccache = shutil.which("ccache")
        if ccache is None:
            raise RuntimeError("ccache not found; run in the Nix shell or pass --no-ccache")
        shim = OUT / "bin"
        shim.mkdir(parents=True)
        (shim / "cc").symlink_to(ccache)  # ccache then runs the next `cc` on PATH
        os.environ["PATH"] = f"{shim}{os.pathsep}{os.environ['PATH']}"
        os.environ["CCACHE_DIR"] = str(CCACHE_DIR)
        run([ccache, "--zero-stats"], ROOT)
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for name in args.examples:
            kinds = [None] * args.random if args.random else plan(name, args.order, args.length, args.repeat, args.seed)
            n = len(kinds)
            ms = manifests(EXAMPLES[name]())
            try:
                results = list(pool.map(sequence, [name] * n, [args.seed] * n, range(n), [ms] * n, kinds))
            except BaseException:
                pool.shutdown(cancel_futures=True)  # stop at the first failure
                raise
            edits = sum(len(h) for h, _ in results)
            cleans = sum(c for _, c in results)
            k = len(EXAMPLES[name]().edits())
            pairs, triples = coverage([h for h, _ in results])
            print(f"props {name}: {n} sequences, {edits} edits, {cleans} distinct clean builds, "
                  f"{pairs}/{k ** 2} pairs and {triples}/{k ** 3} triples of edit kinds, all checks passed")
    if not args.no_ccache:
        stats = dict(l.split("\t", 1) for l in run(["ccache", "--print-stats"], ROOT).splitlines() if "\t" in l)
        hits = sum(int(stats.get(k, 0)) for k in ["direct_cache_hit", "preprocessed_cache_hit"])
        print(f"props: ccache {hits} hits, {stats.get('cache_miss', '?')} misses")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, RuntimeError) as e:
        print(f"FAIL: {e}", file=sys.stderr)
        sys.exit(1)
