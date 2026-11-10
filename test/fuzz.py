#!/usr/bin/env python3
"""Random-graph harness: replay cases from `lake exe fuzzgen` against real Ninja.

Each case (`<i>.json`) is a list of steps. For each step the driver writes
the step's files, runs `mise gen` and compares `build.ninja` with the
expected text, then runs `ninja` with a random `-j` level. It then checks:

1. the edges that ran (the helper `fz` logs each run's first output to
   `fz.log`) are exactly the ones the model's `buildTrace` runs, each once;
2. every product holds the contents the model computes;
3. `ninja -n` reports no work.

After the last step it checks that `ninja -t missingdeps` finds nothing.

Edits need fresh mtimes: after writing a file the driver waits until its
mtime is newer than every file in the case directory.

usage: fuzz.py [--workers W] [--seed S] [--keep] CASES_DIR [CASE...]
"""
import argparse
import json
import os
import random
import shutil
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MISE = ROOT / ".lake" / "build" / "bin" / "mise"
OUT = ROOT / "test" / "out" / "fuzz"
FZ = OUT / "fz"
JOBS = ["-j1", "-j2", "-j8"]


class Fail(Exception):
    pass


def run(cmd, cwd):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if r.returncode != 0:
        raise Fail(f"{' '.join(map(str, cmd))} exited {r.returncode}:\n{r.stdout}{r.stderr}")
    return r.stdout


def newest(d):
    m = 0
    for root, _, files in os.walk(d):
        for f in files:
            m = max(m, os.stat(os.path.join(root, f), follow_symlinks=False).st_mtime_ns)
    return m


def write_fresh(d, files):
    """Write files so that each is newer than everything already in `d`."""
    floor = newest(d)
    for rel, text in files.items():
        p = d / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        for _ in range(1000):
            p.write_text(text)
            if p.stat().st_mtime_ns > floor:
                break
            time.sleep(0.001)
        else:
            raise Fail(f"{rel}: mtime does not advance past {floor}")


def replay(case, seed, keep):
    name = case.stem
    d = OUT / "run" / name
    shutil.rmtree(d, ignore_errors=True)
    d.mkdir(parents=True)
    (d / "fz").symlink_to(FZ)
    steps = json.loads(case.read_text())["steps"]
    rng = random.Random(f"{seed}/{name}")
    for i, s in enumerate(steps):
        where = f"case {name} step {i} ({'; '.join(s['edits']) or 'no edits'})"
        try:
            write_fresh(d, s["write"])
            run([MISE, "gen", "."], d)
            if (d / "build.ninja").read_text() != s["ninja"]:
                raise Fail("build.ninja differs from the expected manifest")
            log = d / "fz.log"
            log.unlink(missing_ok=True)
            run(["ninja", rng.choice(JOBS)], d)
            ran = log.read_text().split() if log.exists() else []
            if len(ran) != len(set(ran)):
                raise Fail(f"an edge ran twice: {sorted(ran)}")
            if sorted(ran) != s["ran"]:
                extra = sorted(set(ran) - set(s["ran"]))
                missing = sorted(set(s["ran"]) - set(ran))
                raise Fail(f"ran differs from the model: extra {extra}, missing {missing}")
            for p, v in s["products"].items():
                got = (d / p).read_text() if (d / p).exists() else None
                if got != v:
                    raise Fail(f"{p} holds {got!r}, the model says {v!r}")
            if "no work to do" not in run(["ninja", "-n"], d):
                raise Fail("ninja -n has work to do")
        except Fail as e:
            return f"{where}: {e}"
    md = run(["ninja", "-t", "missingdeps"], d)
    if "No missing dependencies" not in md:
        return f"case {name}: missingdeps reported:\n{md}"
    if not keep:
        shutil.rmtree(d)
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cases")
    ap.add_argument("only", nargs="*")
    ap.add_argument("--workers", type=int, default=os.cpu_count())
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--keep", action="store_true", help="keep the directories of passing cases")
    a = ap.parse_args()
    cases = sorted(Path(a.cases).glob("*.json"), key=lambda p: int(p.stem))
    if a.only:
        cases = [c for c in cases if c.stem in a.only]
    OUT.mkdir(parents=True, exist_ok=True)
    subprocess.run(["cc", "-O2", "-Wall", "-o", FZ, ROOT / "test" / "fz.c"], check=True)
    t = time.time()
    with ProcessPoolExecutor(a.workers) as ex:
        results = list(ex.map(replay, cases, [a.seed] * len(cases), [a.keep] * len(cases)))
    fails = [r for r in results if r]
    steps = sum(len(json.loads(c.read_text())["steps"]) for c in cases)
    for f in fails:
        print("FAIL", f)
    print(f"fuzz: {len(cases) - len(fails)}/{len(cases)} cases passed, {steps} steps, {time.time() - t:.1f}s")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
