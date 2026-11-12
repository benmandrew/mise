#!/usr/bin/env python3
"""Decide which CI jobs need to run.

A job runs only when a file it depends on differs between the commit under
test and the last commit on which the job succeeded. For each job this
script finds that commit in the workflow's run history, diffs the two
trees, and matches the changed paths against the job's dependencies.

A job's dependencies are the files in COMMON (the toolchain, the flake, the
CI setup), the workflow file that defines it, its own paths in JOBS, and
the import closure of its Lean roots within this package. Paths are fnmatch patterns over repository paths, so
`*` also matches `/`.

The history searched, newest first:
- a push or a scheduled run: earlier runs of the same workflow on the same
  branch, from any event;
- a pull request: earlier runs for the pull request's branch, then runs on
  the base branch.

A job with no earlier success, or whose earlier commit cannot be fetched,
runs. A job that was skipped did not run, so it does not count; neither
does a failed one, except for an informational job, which counts whenever
it finished. A matrix job counts only when every entry with its name
succeeded.

Usage: affected.py WORKFLOW_FILE JOB...   (or --all JOB... to run every job)

Writes `JOB=true|false` lines to $GITHUB_OUTPUT (stdout without it) and a
table to $GITHUB_STEP_SUMMARY. Needs `gh` with `actions: read`, a full
clone (fetch-depth 0), and GH_REPO, SHA, EVENT, BRANCH and BASE_BRANCH in
the environment (BASE_BRANCH only for pull requests).
"""

import fnmatch
import json
import os
import re
import subprocess
import sys
from pathlib import Path

# Every job depends on these.
COMMON = [
    "flake.nix",
    "flake.lock",
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    ".github/actions/*",
    ".github/scripts/*",
]

# Lake executables and the Lean module each one is built from.
EXE = {
    "mise": "Main",
    "difftest": "MiseTest.DiffTest",
    "fuzzgen": "MiseTest.Fuzz",
    "tomljson": "MiseTest.TomlJson",
}

# The random-graph harness and its helpers, which several jobs share.
FUZZ = ["test/fuzz.sh", "test/fuzz.py", "test/confine.py", "test/fz.c"]
# The confinement harnesses' helpers.
CONFINE = FUZZ + ["test/trace.c", "examples/*"]

# For each job: its paths, and the Lean modules whose import closures it
# depends on. A job key matches the job's id in the workflow; `names` is
# the regular expression its run names match, for matrix jobs whose names
# carry the matrix values.
JOBS = {
    # scripts/check.sh builds every default target and regenerates the
    # trusted-base docs, so it depends on every Lean file.
    "proofs": {"paths": ["*.lean", "scripts/*", "docs/trusted.md", "docs/headline.typ"]},
    "ninja": {
        "names": r"ninja \S+ \(.*\)",
        "paths": ["test/ninja-matrix.sh", "test/stage3-diff.sh", "test/stage4-hello.sh",
                  "test/stage6-props.sh", "test/props.py", "examples/*"] + FUZZ,
        "exes": ["mise", "fuzzgen", "difftest"],
    },
    "extras": {
        "names": r"command wrapper and TOML front end",
        "paths": ["test/restat-cmp.sh", "test/wrap-outputs.sh", "test/sugar.sh",
                  "test/toml-diff.sh", "test/toml_diff.py"],
        "exes": ["mise", "tomljson"],
    },
    "fuzz": {"names": r"fuzz \(.*\)", "paths": FUZZ, "exes": ["mise", "fuzzgen"]},
    "props": {"paths": ["test/stage6-props.sh", "test/props.py"], "exes": ["mise"]},
    "conf-sandbox": {"paths": ["test/conf-sandbox.sh"] + CONFINE, "exes": ["mise", "fuzzgen"]},
    "conf-depfiles": {"paths": ["test/conf-depfiles.sh"] + CONFINE, "exes": ["mise", "fuzzgen"]},
    "conf-determinism": {"paths": ["test/conf-determinism.sh"] + CONFINE, "exes": ["mise", "fuzzgen"]},
    "toml-diff": {"paths": ["test/toml-diff.sh", "test/toml_diff.py"], "exes": ["tomljson"]},
    "parser-fuzz": {
        "paths": ["test/parser-fuzz.sh", "test/parser_fuzz.cc", "test/parser-fuzz.dict"],
        "exes": ["difftest"],
        "lean": ["MiseTest.ParseFuzz"],
    },
    "mutants": {"paths": ["test/mutants.sh", "test/mutants.py"] + FUZZ, "exes": ["mise", "fuzzgen"]},
    "mtime-faults": {"paths": ["test/mtime-faults.sh"], "exes": ["mise"], "informational": True},
}


def sh(*args, check=True):
    r = subprocess.run(args, capture_output=True, text=True)
    if check and r.returncode != 0:
        sys.exit(f"{' '.join(args)}: {r.stderr.strip()}")
    return r


def module_path(m):
    """The source file of a module of this package, or None."""
    top = m.split(".")[0]
    if top == "MiseTest":
        return Path("test") / (m.replace(".", "/") + ".lean")
    if top == "MiseFuzz":
        return Path("fuzz/build") / (m.replace(".", "/") + ".lean")
    if top in ("Mise", "Main"):
        return Path(m.replace(".", "/") + ".lean")
    return None


IMPORT = re.compile(r"^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?(\S+)", re.M)


def closure(roots):
    """The source files of `roots` and everything they import, transitively,
    within this package, read from the working tree."""
    todo, seen = list(roots), set()
    while todo:
        p = module_path(todo.pop())
        if p is None or str(p) in seen or not p.exists():
            continue
        seen.add(str(p))
        todo += IMPORT.findall(p.read_text())
    return seen


def deps(workflow, key):
    job = JOBS[key]
    roots = [EXE[e] for e in job.get("exes", [])] + job.get("lean", [])
    return COMMON + [f".github/workflows/{workflow}"] + job["paths"], closure(roots)


def affected(workflow, key, changed):
    """The changed paths the job depends on."""
    patterns, files = deps(workflow, key)
    return [f for f in changed if f in files or any(fnmatch.fnmatchcase(f, p) for p in patterns)]


def runs(workflow, branch):
    out = sh("gh", "run", "list", "--workflow", workflow, "--branch", branch, "--limit", "40",
             "--json", "databaseId,headSha,status").stdout
    return [r for r in json.loads(out) if r["status"] == "completed"]


def jobs_of(run_id):
    out = sh("gh", "api", f"repos/{os.environ['GH_REPO']}/actions/runs/{run_id}/jobs?per_page=100",
             "--jq", "[.jobs[] | {name, conclusion}]").stdout
    return json.loads(out)


def counts(key, run_jobs):
    """Whether this run counts as a run of the job on its commit."""
    job = JOBS[key]
    pat = re.compile(job.get("names", re.escape(key)) + r"\Z")
    mine = [j["conclusion"] for j in run_jobs if pat.match(j["name"])]
    ok = ("success", "failure") if job.get("informational") else ("success",)
    return bool(mine) and all(c in ok for c in mine)


def have(sha):
    if sh("git", "cat-file", "-e", f"{sha}^{{commit}}", check=False).returncode == 0:
        return True
    return sh("git", "fetch", "--quiet", "origin", sha, check=False).returncode == 0


def main():
    args = sys.argv[1:]
    run_all = args[:1] == ["--all"]
    if run_all:
        args = args[1:]
    workflow, keys = args[0], args[1:]
    for k in keys:
        if k not in JOBS:
            sys.exit(f"unknown job {k}")
    sha = os.environ["SHA"]
    branches = [os.environ["BRANCH"]]
    if os.environ.get("EVENT") == "pull_request":
        branches.append(os.environ["BASE_BRANCH"])

    result = {}
    if run_all:
        result = {k: (True, "run by hand", []) for k in keys}
    else:
        history = [r for b in branches for r in runs(workflow, b)]
        cache = {}
        for k in keys:
            base = None
            for r in history:
                if r["databaseId"] not in cache:
                    cache[r["databaseId"]] = jobs_of(r["databaseId"])
                if counts(k, cache[r["databaseId"]]) and have(r["headSha"]):
                    base = r["headSha"]
                    break
            if base is None:
                result[k] = (True, "no earlier success", [])
                continue
            changed = sh("git", "diff", "--name-only", base, sha).stdout.split()
            hit = affected(workflow, k, changed)
            why = f"since {base[:7]}: " + (f"{len(hit)} relevant files changed" if hit else "nothing relevant changed")
            result[k] = (bool(hit), why, hit)

    lines = [f"{k}={'true' if run else 'false'}" for k, (run, _, _) in result.items()]
    out = os.environ.get("GITHUB_OUTPUT")
    if out:
        with open(out, "a") as f:
            f.write("\n".join(lines) + "\n")
    else:
        print("\n".join(lines))
    table = ["| job | runs | why |", "| --- | --- | --- |"]
    for k, (run, why, hit) in result.items():
        shown = ", ".join(hit[:5]) + (" ..." if len(hit) > 5 else "")
        table.append(f"| {k} | {'yes' if run else 'no'} | {why}{': ' + shown if hit else ''} |")
    print("\n".join(table), file=sys.stderr)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as f:
            f.write("\n".join(table) + "\n")


if __name__ == "__main__":
    main()
