#!/usr/bin/env python3
"""Random-graph harness: replay cases from `lake exe fuzzgen` against real Ninja.

Each case (`<i>.json`) holds a description (sources, edges and edits) and
the steps the model computed from it. For each step the driver writes the
step's files, runs `mise gen` and compares `build.ninja` with the expected
text, then runs `ninja` with a random `-j` level. It then checks:

1. the edges that ran (the helper `fz` logs each run's first output to
   `fz.log`) are exactly the ones the model's `buildTrace` runs, each once;
2. every product holds the contents the model computes;
3. `ninja -n` reports no work.

After the last step it checks that `ninja -t missingdeps` finds nothing.

Edits need fresh mtimes: after writing a file the driver waits until its
mtime is newer than every file in the case directory.

A failing case is shrunk: the driver drops steps, edges, edits, inputs,
includes and sources from its description one at a time, asks
`fuzzgen expect` for the model's steps on the smaller description, and
keeps the change when the case still fails the same check with the same
`-j` levels. It repeats until no single change keeps the failure, and
writes the result to `test/out/fuzz/shrunk/<i>.json`, which
`fuzz.py test/out/fuzz/shrunk <i>` replays.

usage: fuzz.py [--workers W] [--seed S] [--keep] [--no-shrink]
               [--shrink-max K] [--fz PATH] CASES_DIR [CASE...]
"""
import argparse
import copy
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
FUZZGEN = ROOT / ".lake" / "build" / "bin" / "fuzzgen"
OUT = ROOT / "test" / "out" / "fuzz"
JOBS = ["-j1", "-j2", "-j8"]


class Fail(Exception):
    def __init__(self, kind, msg):
        super().__init__(msg)
        self.kind = kind


def run(cmd, cwd):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if r.returncode != 0:
        raise Fail("exit", f"{' '.join(map(str, cmd))} exited {r.returncode}:\n{r.stdout}{r.stderr}")
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
            raise Fail("mtime", f"{rel}: mtime does not advance past {floor}")


def replay_steps(d, steps, jobs, fz):
    """Replay steps in a fresh directory `d`. Returns None, or (kind, message)."""
    shutil.rmtree(d, ignore_errors=True)
    d.mkdir(parents=True)
    (d / "fz").symlink_to(fz)
    for i, s in enumerate(steps):
        where = f"step {i} ({'; '.join(s['edits']) or 'no edits'}, {jobs[i]})"
        try:
            write_fresh(d, s["write"])
            run([MISE, "gen", "."], d)
            if (d / "build.ninja").read_text() != s["ninja"]:
                raise Fail("manifest", "build.ninja differs from the expected manifest")
            log = d / "fz.log"
            log.unlink(missing_ok=True)
            run(["ninja", jobs[i]], d)
            ran = log.read_text().split() if log.exists() else []
            if len(ran) != len(set(ran)):
                raise Fail("twice", f"an edge ran twice: {sorted(ran)}")
            if sorted(ran) != s["ran"]:
                extra = sorted(set(ran) - set(s["ran"]))
                missing = sorted(set(s["ran"]) - set(ran))
                raise Fail("ran", f"ran differs from the model: extra {extra}, missing {missing}")
            for p, v in s["products"].items():
                got = (d / p).read_text() if (d / p).exists() else None
                if got != v:
                    raise Fail("contents", f"{p} holds {got!r}, the model says {v!r}")
            if "no work to do" not in run(["ninja", "-n"], d):
                raise Fail("rerun", "ninja -n has work to do")
        except Fail as e:
            return e.kind, f"{where}: {e}"
    try:
        md = run(["ninja", "-t", "missingdeps"], d)
    except Fail as e:
        return e.kind, str(e)
    if "No missing dependencies" not in md:
        return "missingdeps", f"missingdeps reported:\n{md}"
    return None


def expect(desc, tmp):
    """The model's steps for a description, or None if fuzzgen rejects it."""
    src, dst = tmp / "desc.json", tmp / "case.json"
    src.write_text(json.dumps(desc))
    r = subprocess.run([FUZZGEN, "expect", src, dst], capture_output=True, text=True)
    return json.loads(dst.read_text())["steps"] if r.returncode == 0 else None


def refs(desc, path):
    """Whether any edge reads `path` or any source includes it. A source's
    `allowed` list only steers the generator, so it does not count."""
    return any(path in e["ins"] + e["implicitIns"] + e["orderOnly"] for e in desc["edges"]) or any(
        path in s["includes"] for s in desc["srcs"]
    )


def forget(desc, path):
    """Remove `path` from every `allowed` list and every edit that names it."""
    for s in desc["srcs"]:
        s["allowed"] = [a for a in s["allowed"] if a != path]
    desc["steps"] = [[x for x in st if path not in next(iter(x.values())).values()] for st in desc["steps"]]


def set_vars(e):
    """Recompute the `iout` and `imp` variables, which list the implicit
    outputs and inputs, keeping `tag` first as the generator does."""
    vs = [kv for kv in e["vars"] if kv[0] not in ("iout", "imp")]
    if e["implicitOuts"]:
        vs.append(["iout", " ".join(e["implicitOuts"])])
    if e["implicitIns"]:
        vs.append(["imp", " ".join(e["implicitIns"])])
    e["vars"] = vs


def candidates(desc, jobs):
    """Descriptions one change smaller, largest changes first."""
    steps = desc["steps"]
    for k in reversed(range(len(steps))):
        c = copy.deepcopy(desc)
        del c["steps"][k]
        yield c, jobs[: k + 1] + jobs[k + 2 :]
    for i in reversed(range(len(desc["edges"]))):
        e = desc["edges"][i]
        outs = e["outs"] + e["implicitOuts"]
        c = copy.deepcopy(desc)
        del c["edges"][i]
        if any(refs(c, o) for o in outs):
            continue
        for o in outs:
            forget(c, o)
        yield c, jobs
    for k, st in enumerate(steps):
        for j in range(len(st)):
            c = copy.deepcopy(desc)
            del c["steps"][k][j]
            yield c, jobs
    for i, e in enumerate(desc["edges"]):
        for key in ["ins", "implicitIns", "orderOnly"]:
            for x in e[key]:
                c = copy.deepcopy(desc)
                ce = c["edges"][i]
                ce[key].remove(x)
                if not ce["ins"]:
                    if not ce["implicitIns"]:
                        continue
                    ce["ins"] = [ce["implicitIns"].pop(0)]
                set_vars(ce)
                yield c, jobs
        # Outputs other than the first, which names the edge in `retag` edits.
        for key, xs in [("outs", e["outs"][1:]), ("implicitOuts", e["implicitOuts"])]:
            for x in xs:
                c = copy.deepcopy(desc)
                c["edges"][i][key].remove(x)
                if refs(c, x):
                    continue
                forget(c, x)
                set_vars(c["edges"][i])
                yield c, jobs
    for i, s in enumerate(desc["srcs"]):
        for x in s["includes"]:
            c = copy.deepcopy(desc)
            c["srcs"][i]["includes"].remove(x)
            yield c, jobs
    for i, s in enumerate(desc["srcs"]):
        p = s["path"]
        c = copy.deepcopy(desc)
        del c["srcs"][i]
        if refs(c, p):
            continue
        forget(c, p)
        yield c, jobs


def size(desc):
    return f"{len(desc['edges'])} edges, {len(desc['srcs'])} sources, {len(desc['steps'])} edit steps, " \
        f"{sum(map(len, desc['steps']))} edits"


def shrink(name, desc, jobs, kind, fz):
    tmp = OUT / "shrink" / name
    tmp.mkdir(parents=True, exist_ok=True)
    trials = 0
    progress = True
    while progress:
        progress = False
        for c, cj in candidates(desc, jobs):
            trials += 1
            steps = expect(c, tmp)
            if steps is None:
                continue
            r = replay_steps(tmp / "run", steps, cj, fz)
            if r and r[0] == kind:
                desc, jobs, progress = c, cj, True
                break
    steps = expect(desc, tmp)
    r = replay_steps(OUT / "shrunk-run" / name, steps, jobs, fz)
    shrunk = OUT / "shrunk"
    shrunk.mkdir(parents=True, exist_ok=True)
    (shrunk / f"{name}.json").write_text(json.dumps({"desc": desc, "jobs": jobs, "steps": steps}))
    shutil.rmtree(tmp, ignore_errors=True)
    return desc, trials, r


def replay(case, seed, keep, fz, do_shrink):
    name = case.stem
    data = json.loads(case.read_text())
    steps = data["steps"]
    rng = random.Random(f"{seed}/{name}")
    jobs = data.get("jobs") or [rng.choice(JOBS) for _ in steps]
    d = OUT / "run" / name
    r = replay_steps(d, steps, jobs, fz)
    if r is None:
        if not keep:
            shutil.rmtree(d)
        return None
    kind, msg = r
    report = f"case {name}: {msg}"
    if do_shrink:
        t = time.time()
        small, trials, r2 = shrink(name, data["desc"], jobs, kind, fz)
        report += f"\n  shrunk from {size(data['desc'])}\n  to {size(small)} in {trials} trials, {time.time() - t:.1f}s"
        report += f"\n  {r2[1] if r2 else 'the shrunk case passes on replay (flaky?)'}"
        report += f"\n  replay: test/fuzz.py test/out/fuzz/shrunk {name}"
    return report


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cases")
    ap.add_argument("only", nargs="*")
    ap.add_argument("--workers", type=int, default=os.cpu_count())
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--keep", action="store_true", help="keep the directories of passing cases")
    ap.add_argument("--no-shrink", action="store_true")
    ap.add_argument("--shrink-max", type=int, default=3, help="shrink at most this many failing cases")
    ap.add_argument("--fz", help="use this helper binary instead of compiling test/fz.c")
    a = ap.parse_args()
    cases = sorted(Path(a.cases).glob("*.json"), key=lambda p: int(p.stem))
    if a.only:
        cases = [c for c in cases if c.stem in a.only]
    OUT.mkdir(parents=True, exist_ok=True)
    fz = Path(a.fz).resolve() if a.fz else OUT / "fz"
    if not a.fz:
        subprocess.run(["cc", "-O2", "-Wall", "-o", fz, ROOT / "test" / "fz.c"], check=True)
    t = time.time()
    n = len(cases)
    with ProcessPoolExecutor(a.workers) as ex:
        results = list(ex.map(replay, cases, [a.seed] * n, [a.keep] * n, [fz] * n, [False] * n))
        fails = [(c, r) for c, r in zip(cases, results) if r]
        steps = sum(len(json.loads(c.read_text())["steps"]) for c in cases)
        print(f"fuzz: {n - len(fails)}/{n} cases passed, {steps} steps, {time.time() - t:.1f}s")
        if fails and not a.no_shrink:
            todo = [c for c, _ in fails[: a.shrink_max]]
            k = len(todo)
            shrunk = dict(zip(todo, ex.map(replay, todo, [a.seed] * k, [True] * k, [fz] * k, [True] * k)))
            fails = [(c, shrunk.get(c, r)) for c, r in fails]
    for _, f in fails:
        print("FAIL", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
