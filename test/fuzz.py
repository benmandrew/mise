#!/usr/bin/env python3
"""Random-graph harness: replay cases from `lake exe fuzzgen` against real Ninja.

Each case (`<i>.json`) holds a description (sources, edges and edits) and
the steps the model computed from it. For each step the driver writes the
step's files, runs `mise gen` and compares `build.ninja` with the expected
text, then runs `ninja` with a random `-j` level. It then checks:

1. the edges that ran (the helper `fz` logs each run's first output to
   `fz.log`) are exactly the ones the model's `buildTrace` runs, each once;
2. the runs form a schedule, as `parallel_equiv` assumes (see
   `check_schedule`);
3. every product holds the contents the model computes;
4. `ninja -n` reports no work.

After the last step it checks that `ninja -t missingdeps` finds nothing.

`--missing-ok` is for cases generated with `fuzzgen ... absent`, whose
commands leave out some outputs. Ninja then reruns an edge with a missing
output in every build, which the model does not (see `Mise/Model/NOTES.md`).
The option lets such edges run in addition to the model's, and replaces
check 4: a second build may run only such edges, must pass check 2 and
must leave the same contents (`ninja -n` does not restat, so it would list
their dependents).

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
               [--shrink-max K] [--fz PATH] [--delay US] [--missing-ok] CASES_DIR [CASE...]
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
JOBS = ["-j1", "-j2", "-j8", "-j64"]


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


def parse_log(text):
    """The first output of each run in log order, and for each run with
    timestamps its six times and the files it read (see test/fz.c)."""
    order, runs = [], {}
    for line in text.splitlines():
        f = line.split()
        order.append(f[0])
        if len(f) >= 7:
            runs[f[0]] = ([int(x) for x in f[1:7]], f[7:])
    return order, runs


def check_schedule(desc, order, runs, stats):
    """Check the assumptions behind `parallel_equiv` (Mise/Model/Parallel.lean).

    The theorem treats a parallel run as the sequence of its commands by
    start time, each reading its inputs at the start and writing its outputs
    at the end, and assumes that sequence is a `Sched`. With the times `fz`
    logs:

    (b) within each run, entry <= first read <= last read <= first write <=
        last write <= exit, so all reads come before all writes;
    (a) every run starts after every edge producing one of its inputs is
        done. Inputs are explicit, implicit and order-only inputs and the
        files the run read, so discovered deps count. A producer that ran
        is done when it exits; one that did not run is done when all of its
        own producers are, which is the earliest Ninja could have found it
        clean;
    (s) the edges sorted by start time (edges that did not run at their
        done time, ties broken by depth) form a `Sched`: no edge reads its
        own outputs or a later edge's outputs, and outputs are unique.

    (a) gives the second conjunct of `Sched` for the sequence in (s); (s)
    checks it directly, together with the first and third conjuncts, which
    hold for every emitted manifest (`sched_emit`). (a) is the stronger
    claim: a producer has ended, not just started, before a reader starts,
    so with (b) two runs that overlap in time never read what the other
    writes, and the sequence by start time has the parallel run's effect."""
    if len(runs) != len(order):
        return  # a helper without timestamps (--fz)
    edges = {e["outs"][0]: e for e in desc["edges"]}
    outs = {k: e["outs"] + e["implicitOuts"] for k, e in edges.items()}
    prod = {o: k for k, os in outs.items() for o in os}
    reads = {k: e["ins"] + e["implicitIns"] + e["orderOnly"] for k, e in edges.items()}
    for k, (t, _) in runs.items():
        if t != sorted(t):
            raise Fail("rw-order", f"{k}: times entry, read, read, write, write, exit are out of order: {t}")
    done, depth = {}, {}

    def visit(k):
        if k not in done:
            ps = [visit(prod[p]) for p in reads[k] if p in prod]
            done[k] = runs[k][0][5] if k in runs else max((p[0] for p in ps), default=0)
            depth[k] = 1 + max((p[1] for p in ps), default=0)
        return done[k], depth[k]

    for k in edges:
        visit(k)
    for k, (t, rd) in runs.items():
        for p in reads[k] + rd:
            q = prod.get(p)
            if q is not None and done[q] >= t[0]:
                raise Fail("sched", f"{k} started at {t[0]}, before {q}, which produces {p}, was done at {done[q]}")
    seq = sorted(edges, key=lambda k: (runs[k][0][0] if k in runs else done[k], depth[k]))
    seen = set()
    for i in reversed(range(len(seq))):
        k = seq[i]
        if set(outs[k]) & seen or len(set(outs[k])) != len(outs[k]):
            raise Fail("sched", f"start order {seq}: an output of {k} is not unique")
        seen |= set(outs[k])
        bad = set(reads[k] + (runs[k][1] if k in runs else [])) & seen
        if bad:
            raise Fail("sched", f"start order {seq}: {k} reads {sorted(bad)}, written by itself or a later edge")
    # Overlap statistics: pairs of runs whose intervals intersect, and the
    # most runs at once.
    ev = sorted([(t[0], 1) for t, _ in runs.values()] + [(t[5], -1) for t, _ in runs.values()])
    cur = 0
    for _, x in ev:
        cur += x
        stats["max"] = max(stats["max"], cur)
    iv = sorted(t[0:6:5] for t, _ in runs.values())
    pairs = sum(1 for i in range(len(iv)) for j in range(i + 1, len(iv)) if iv[j][0] < iv[i][1])
    stats["pairs"] += pairs
    stats["steps"] += pairs > 0


def new_stats():
    return {"max": 0, "pairs": 0, "steps": 0, "multi": 0}


def with_missing(d, desc):
    """The first outputs of the edges with a missing output."""
    return {e["outs"][0] for e in desc["edges"] if not all((d / o).exists() for o in e["outs"] + e["implicitOuts"])}


def check_products(d, s):
    for p, v in s["products"].items():
        # A missing file reads as empty, as in the model.
        got = (d / p).read_text() if (d / p).exists() else ""
        if got != v:
            raise Fail("contents", f"{p} holds {got!r}, the model says {v!r}")


def ran_edges(d, jobs):
    """Run `ninja` and return `parse_log` of the runs it made."""
    log = d / "fz.log"
    log.unlink(missing_ok=True)
    run(["ninja", jobs], d)
    ran, runs = parse_log(log.read_text()) if log.exists() else ([], {})
    if len(ran) != len(set(ran)):
        raise Fail("twice", f"an edge ran twice: {sorted(ran)}")
    return ran, runs


def replay_steps(d, steps, jobs, fz, desc, stats=None, missing_ok=False):
    """Replay steps in a fresh directory `d`. Returns None, or (kind, message).
    With `missing_ok`, allow the differences `--missing-ok` describes."""
    stats = stats if stats is not None else new_stats()
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
            ok = with_missing(d, desc) if missing_ok and i > 0 else set()
            ran, runs = ran_edges(d, jobs[i])
            extra = sorted(set(ran) - set(s["ran"]) - ok)
            missing = sorted(set(s["ran"]) - set(ran))
            if extra or missing:
                raise Fail("ran", f"ran differs from the model: extra {extra}, missing {missing}")
            stats["multi"] += jobs[i] != "-j1" and len(ran) > 1
            check_schedule(desc, ran, runs, stats)
            check_products(d, s)
            if not missing_ok:
                if "no work to do" not in run(["ninja", "-n"], d):
                    raise Fail("rerun", "ninja -n has work to do")
            else:
                again, again_runs = ran_edges(d, jobs[i])
                # Check the second build's schedule too, but keep it out of the overlap statistics.
                check_schedule(desc, again, again_runs, new_stats())
                again = sorted(set(again) - with_missing(d, desc))
                if again:
                    raise Fail("rerun", f"a second build ran {again}, which have every output")
                check_products(d, s)
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


def shrink(name, desc, jobs, kind, fz, missing_ok):
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
            r = replay_steps(tmp / "run", steps, cj, fz, c, missing_ok=missing_ok)
            if r and r[0] == kind:
                desc, jobs, progress = c, cj, True
                break
    steps = expect(desc, tmp)
    r = replay_steps(OUT / "shrunk-run" / name, steps, jobs, fz, desc, missing_ok=missing_ok)
    shrunk = OUT / "shrunk"
    shrunk.mkdir(parents=True, exist_ok=True)
    (shrunk / f"{name}.json").write_text(json.dumps({"desc": desc, "jobs": jobs, "steps": steps}))
    shutil.rmtree(tmp, ignore_errors=True)
    return desc, trials, r


def replay(case, seed, keep, fz, do_shrink, missing_ok):
    name = case.stem
    data = json.loads(case.read_text())
    steps = data["steps"]
    rng = random.Random(f"{seed}/{name}")
    jobs = data.get("jobs") or [rng.choice(JOBS) for _ in steps]
    d = OUT / "run" / name
    stats = new_stats()
    r = replay_steps(d, steps, jobs, fz, data["desc"], stats, missing_ok)
    if r is None:
        if not keep:
            shutil.rmtree(d)
        return None, stats
    kind, msg = r
    report = f"case {name}: {msg}"
    if do_shrink:
        t = time.time()
        small, trials, r2 = shrink(name, data["desc"], jobs, kind, fz, missing_ok)
        report += f"\n  shrunk from {size(data['desc'])}\n  to {size(small)} in {trials} trials, {time.time() - t:.1f}s"
        report += f"\n  {r2[1] if r2 else 'the shrunk case passes on replay (flaky?)'}"
        report += f"\n  replay: test/fuzz.py test/out/fuzz/shrunk {name}"
    return report, stats


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
    ap.add_argument("--delay", type=int, default=20000,
                    help="each command sleeps up to this many microseconds twice, so that runs overlap (0: off)")
    ap.add_argument("--missing-ok", action="store_true",
                    help="allow reruns of edges with a missing output (for `absent` cases)")
    a = ap.parse_args()
    cases = sorted(Path(a.cases).glob("*.json"), key=lambda p: int(p.stem))
    if a.only:
        cases = [c for c in cases if c.stem in a.only]
    OUT.mkdir(parents=True, exist_ok=True)
    fz = Path(a.fz).resolve() if a.fz else OUT / "fz"
    if not a.fz:
        subprocess.run(["cc", "-O2", "-Wall", "-o", fz, ROOT / "test" / "fz.c"], check=True)
    os.environ["FZ_DELAY"] = str(a.delay)
    t = time.time()
    n = len(cases)
    with ProcessPoolExecutor(a.workers) as ex:
        mo = [a.missing_ok] * n
        results = list(ex.map(replay, cases, [a.seed] * n, [a.keep] * n, [fz] * n, [False] * n, mo))
        fails = [(c, r) for c, (r, _) in zip(cases, results) if r]
        steps = sum(len(json.loads(c.read_text())["steps"]) for c in cases)
        print(f"fuzz: {n - len(fails)}/{n} cases passed, {steps} steps, {time.time() - t:.1f}s")
        st = [s for _, s in results]
        print(f"fuzz: of {sum(s['multi'] for s in st)} builds with -j above 1 that ran two or more edges, "
              f"{sum(s['steps'] for s in st)} ran edges at the same time; "
              f"{sum(s['pairs'] for s in st)} overlapping pairs, at most {max(s['max'] for s in st)} at once")
        if fails and not a.no_shrink:
            todo = [c for c, _ in fails[: a.shrink_max]]
            k = len(todo)
            shrunk = dict(zip(todo, (r for r, _ in ex.map(replay, todo, [a.seed] * k, [True] * k, [fz] * k, [True] * k,
                                                          [a.missing_ok] * k))))
            fails = [(c, shrunk.get(c, r)) for c, r in fails]
    for _, f in fails:
        print("FAIL", f)
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
