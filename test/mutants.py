#!/usr/bin/env python3
"""Mutation testing of the Ninja model against the random-graph harness.

Each mutant is one small edit to an executable definition in
`Mise/Model/Basic.lean`: the dirtiness test, the deps log, `restat`, the
build log, order-only inputs, the traversal, or the edge translation. For
each mutant the driver

1. applies the edit to a copy of the source tree in `test/out/mutants/tree`,
   never to the real tree;
2. builds only `fuzzgen`, whose closure is the front end and
   `Mise/Model/Basic.lean`. `Basic.lean` holds definitions and no proofs,
   and `test/MiseTest/Fuzz.lean` imports it alone, so the broken proofs in
   `Sound.lean`, `Dsl.lean`, `Minimal.lean` and `Parallel.lean` are never
   rebuilt;
3. runs the mutant generator with its own checks on (a second build runs
   nothing, depfile edges read only what they may), and records the first
   failure;
4. runs it again with those checks off (`FUZZGEN_NO_SELF_CHECK`), replays
   the cases against real Ninja with `test/fuzz.py --no-shrink`, and counts
   the failing cases by check.

A mutant is killed when the generator or a check against Ninja fails. The
unmutated model runs first and must pass both. The results table goes to
`test/out/mutants/results.md`.

usage: mutants.py [--cases N] [--seed S] [--workers W] [MUTANT...]
"""
import argparse
import collections
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "test" / "out" / "mutants"
TREE = OUT / "tree"
BASIC = "Mise/Model/Basic.lean"

TRACE = """\
  | e :: es, st =>
    let r := buildTrace sem es (st.step sem e)
    (r.1, if st.dirty e then e :: r.2 else r.2)
"""

# (name, area, what it does, old text, new text). Each old text occurs
# exactly once in Basic.lean.
MUTANTS = [
    ("mtime-flip", "dirty", "output dirty when newer than its newest input",
     "decide (t < st.newest D)", "decide (st.newest D < t)"),
    ("no-mtime", "dirty", "drop the output mtime test",
     "(!e.restat && decide (t < st.newest D)) || ", ""),
    ("no-logtime", "dirty", "drop the log time test",
     " || decide (lt < st.newest D)", ""),
    ("no-cmd", "dirty", "drop the command test",
     "c != e.cmd || ", ""),
    ("all-outs", "dirty", "edge dirty only when every output is dirty",
     "e.outs.any (st.outDirty e)", "e.outs.all (st.outDirty e)"),
    ("restat-mtime", "restat", "compare a restat output's mtime too",
     "(!e.restat && decide (t < st.newest D))", "decide (t < st.newest D)"),
    ("never-keep", "restat", "a restat run rewrites every output",
     "| some (old, _) => sem.keep old (st.outVal sem e o)", "| some _ => false"),
    ("always-keep", "restat", "a restat run keeps every existing output",
     "| some (old, _) => sem.keep old (st.outVal sem e o)", "| some _ => true"),
    ("keep-all-rules", "restat", "every rule keeps unchanged outputs, not only restat",
     "  e.restat && match st.fs o with", "  match st.fs o with"),
    ("deps-ignored", "deps", "dirtiness ignores the recorded deps",
     "(st.deps o).map (e.ins ++ ·)", "(st.deps o).map (fun _ => e.ins)"),
    ("deps-missing-ok", "deps", "a depfile output without a deps entry is not dirty",
     "if e.dyn then (st.deps o).map (e.ins ++ ·) else some e.ins",
     "if e.dyn then some (e.ins ++ (st.deps o).getD []) else some e.ins"),
    ("deps-stale", "deps", "a deps entry, once written, is never updated",
     "if e.outs.contains p then some D else st.deps p",
     "if e.outs.contains p then some ((st.deps p).getD D) else st.deps p"),
    ("oo-dirty", "order-only", "order-only inputs count for dirtiness",
     "if e.dyn then (st.deps o).map (e.ins ++ ·) else some e.ins",
     "if e.dyn then (st.deps o).map (e.ins ++ e.oo ++ ·) else some (e.ins ++ e.oo)"),
    ("log-skip-kept", "log", "no new log entry for a kept output",
     "log := fun p => if e.outs.contains p then", "log := fun p => if e.outs.contains p && !st.kept sem e p then"),
    ("log-first-out", "log", "log only the first output",
     "log := fun p => if e.outs.contains p then", "log := fun p => if e.outs.head? == some p then"),
    ("log-old-time", "log", "log the time before the run, not the run's time",
     "some (e.cmd, t)", "some (e.cmd, st.clock)"),
    ("trace-reverse", "traversal", "visit the edges in reverse order", TRACE, """\
  | e :: es, st =>
    let r := buildTrace sem es st
    (r.1.step sem e, if r.1.dirty e then e :: r.2 else r.2)
"""),
    ("trace-upfront", "traversal", "decide every edge's dirtiness before running any",
     "def buildTrace (sem : Sem V) : List MEdge → St V → St V × List MEdge\n  | [], st => (st, [])\n" + TRACE,
     "def buildTrace (sem : Sem V) (es : List MEdge) (st : St V) : St V × List MEdge :=\n"
     "  let ran := es.filter st.dirty\n  (ran.foldl (fun s e => s.run sem e) st, ran)\n"),
    ("trace-all", "traversal", "report every visited edge as run",
     "(r.1, if st.dirty e then e :: r.2 else r.2)", "(r.1, e :: r.2)"),
    ("no-implicit", "edge", "drop implicit inputs from the model edge",
     "c.edge.ins ++ c.edge.implicitIns, c.edge.orderOnly", "c.edge.ins, c.edge.orderOnly"),
]


def sh(cmd, cwd=TREE, env=None):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)


def copy_tree():
    """Copy the sources and the build directory, with copy-on-write clones
    where the file system has them."""
    shutil.rmtree(TREE, ignore_errors=True)
    (TREE / "test").mkdir(parents=True)
    items = [".lake", "Mise", "Main.lean", "Mise.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json"]
    tests = [p.name for p in (ROOT / "test").iterdir() if p.name != "out"]
    for src, dst in [(items, TREE), ([f"test/{t}" for t in tests], TREE / "test")]:
        args = [str(ROOT / s) for s in src] + [str(dst)]
        if sys.platform != "darwin" or sh(["/bin/cp", "-Rc", *args], cwd=ROOT).returncode != 0:
            subprocess.run(["cp", "-R", *args], check=True)


def build():
    r = sh(["lake", "build", "fuzzgen", "mise"])
    return None if r.returncode == 0 else (r.stdout + r.stderr)[-2000:]


def generator_check(n, seed):
    """The first failure of the generator's own checks, or None."""
    r = sh([".lake/build/bin/fuzzgen", "test/out/mutants/strict", str(n), str(seed)])
    shutil.rmtree(TREE / "test/out/mutants/strict", ignore_errors=True)
    if r.returncode == 0:
        return None
    line = r.stderr.strip().splitlines()[-1] if r.stderr.strip() else f"exit {r.returncode}"
    m = re.match(r"case (\d+): (.*)", line)
    if not m:
        return line
    msg = m.group(2)
    if "idempotent" in msg:
        msg = "second build runs edges"
    elif "which it may not" in msg:
        msg = "depfile reads a forbidden path"
    return f"{msg} (case {m.group(1)})"


def ninja_checks(n, seed, workers):
    """(cases failed, cases, Counter of failing checks), or an error string."""
    env = dict(os.environ, FUZZGEN_NO_SELF_CHECK="1")
    cases = "test/out/fuzz/cases"
    shutil.rmtree(TREE / cases, ignore_errors=True)
    r = sh([".lake/build/bin/fuzzgen", cases, str(n), str(seed)], env=env)
    if r.returncode != 0:
        return f"generator: {r.stderr.strip()[-300:]}"
    r = sh([sys.executable, "test/fuzz.py", "--no-shrink", "--workers", str(workers), "--seed", str(seed), cases])
    m = re.search(r"fuzz: (\d+)/(\d+) cases passed", r.stdout)
    if not m:
        return f"fuzz.py: {(r.stdout + r.stderr).strip()[-300:]}"
    kinds = collections.Counter(re.findall(r"^FAIL case \d+ \[(\w+)\]", r.stdout, re.M))
    total = int(m.group(2))
    return total - int(m.group(1)), total, kinds


def run_one(name, n, seed, workers):
    t = time.time()
    err = build()
    if err:
        return {"name": name, "error": "does not compile:\n" + err, "time": time.time() - t}
    gen = generator_check(n, seed)
    nin = ninja_checks(n, seed, workers)
    return {"name": name, "gen": gen, "ninja": nin, "time": time.time() - t}


def killed(r):
    return bool(r.get("gen")) or (isinstance(r.get("ninja"), tuple) and r["ninja"][0] > 0)


def fmt_ninja(nin):
    if isinstance(nin, str):
        return nin
    failed, total, kinds = nin
    if not failed:
        return f"0/{total}"
    return f"{failed}/{total}: " + ", ".join(f"{k} {v}" for k, v in kinds.most_common())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("only", nargs="*", help="run only these mutants")
    ap.add_argument("--cases", type=int, default=200)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--workers", type=int, default=os.cpu_count())
    a = ap.parse_args()
    unknown = set(a.only) - {m[0] for m in MUTANTS}
    if unknown:
        sys.exit(f"unknown mutants: {sorted(unknown)}")
    todo = [m for m in MUTANTS if not a.only or m[0] in a.only]
    start = time.time()
    copy_tree()
    basic = (TREE / BASIC).read_text()
    for name, _, _, old, _ in todo:
        if basic.count(old) != 1:
            sys.exit(f"{name}: the text to replace occurs {basic.count(old)} times in {BASIC}")

    base = run_one("(real model)", a.cases, a.seed, a.workers)
    print(f"real model: generator {base.get('gen') or 'ok'}, ninja {fmt_ninja(base.get('ninja', base.get('error')))}, "
          f"{base['time']:.0f}s", flush=True)
    if base.get("error") or killed(base):
        sys.exit("the real model fails; mutant results would mean nothing")

    rows = []
    for name, area, what, old, new in todo:
        (TREE / BASIC).write_text(basic.replace(old, new))
        r = run_one(name, a.cases, a.seed, a.workers)
        r.update(area=area, what=what)
        rows.append(r)
        verdict = "error" if r.get("error") else "killed" if killed(r) else "SURVIVED"
        print(f"{name}: {verdict}; generator {r.get('gen') or 'ok'}; "
              f"ninja {fmt_ninja(r['ninja']) if 'ninja' in r else r['error']}; {r['time']:.0f}s", flush=True)
    (TREE / BASIC).write_text(basic)

    total = time.time() - start
    k = sum(map(killed, rows))
    lines = [f"{k} of {len(rows)} mutants killed; {a.cases} cases, seed {a.seed}, {a.workers} workers, {total:.0f} s.", "",
             "| Mutant | Area | Change | Generator check | Failing cases against Ninja | Killed |",
             "|---|---|---|---|---|---|"]
    for r in rows:
        nin = fmt_ninja(r["ninja"]) if "ninja" in r else r["error"].splitlines()[0]
        lines.append(f"| `{r['name']}` | {r['area']} | {r['what']} | {r.get('gen') or 'passes'} | {nin} | "
                     f"{'yes' if killed(r) else 'no'} |")
    report = "\n".join(lines) + "\n"
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "results.md").write_text(report)
    print()
    print(report)
    return 0 if all(not r.get("error") for r in rows) else 1


if __name__ == "__main__":
    sys.exit(main())
