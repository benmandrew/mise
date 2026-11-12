#!/usr/bin/env python3
"""Mutation testing of the Ninja model against the in-process harness.

The mutants are those of `test/mutants.py`. For each one the driver applies
the edit to a copy of the tree in `test/out/mutants-inproc/tree`, builds the
standalone harness there (`fuzz/build/build.sh standalone`), and replays N
cases with the model's own checks off (`MISE_FUZZ_NO_SELF_CHECK`), so that
only the comparison with Ninja can kill the mutant. It prints, per mutant,
how many cases failed and by which check.

usage: fuzz/build/mutants.py [--cases N] [--seed S] [MUTANT...]
Run from the repository root inside `nix develop`.
"""
import argparse
import collections
import importlib.util
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
OUT = ROOT / "test" / "out" / "mutants-inproc"
TREE = OUT / "tree"

spec = importlib.util.spec_from_file_location("mutants", ROOT / "test" / "mutants.py")
mutants = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mutants)


def copy_tree():
    shutil.rmtree(TREE, ignore_errors=True)
    TREE.mkdir(parents=True)
    items = [".lake", "Mise", "Main.lean", "Mise.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json", "fuzz"]
    args = [str(ROOT / s) for s in items] + [str(TREE)]
    if sys.platform != "darwin" or subprocess.run(["/bin/cp", "-Rc", *args]).returncode != 0:
        subprocess.run(["cp", "-R", *args], check=True)
    (TREE / "test").mkdir()
    for p in (ROOT / "test").iterdir():
        if p.name != "out":
            (shutil.copytree if p.is_dir() else shutil.copy2)(p, TREE / "test" / p.name)


def run(n, seed, env):
    r = subprocess.run(["fuzz/build/build.sh", "standalone"], cwd=TREE, env=env, capture_output=True, text=True)
    if r.returncode != 0:
        return f"does not build: {(r.stdout + r.stderr)[-500:]}"
    out = TREE / "test" / "out" / "fuzz" / "inproc"
    shutil.rmtree(out, ignore_errors=True)
    r = subprocess.run([".lake/build/fuzz/mise-buildfuzz-standalone", str(n), str(seed)], cwd=TREE,
                       env=dict(env, MISE_FUZZ_NO_SELF_CHECK="1", MISE_FUZZ_OUT=str(out)),
                       capture_output=True, text=True)
    kinds = collections.Counter(re.findall(r"^mise-fuzz: (\w+): ", r.stderr, re.M))
    m = re.search(r"(\d+) mismatches", r.stdout)
    if not m:
        return f"harness: {(r.stdout + r.stderr)[-500:]}"
    failed = int(m.group(1))
    return f"{failed}/{n}" + (": " + ", ".join(f"{k} {v}" for k, v in kinds.most_common()) if failed else "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=200)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("names", nargs="*")
    a = ap.parse_args()
    src = subprocess.run(["nix", "build", "--no-link", "--print-out-paths", ".#ninja-1_13_2.src"], cwd=ROOT,
                         capture_output=True, text=True, check=True).stdout.strip()
    env = dict(os.environ, NINJA_SRC=src)
    copy_tree()
    basic = TREE / mutants.BASIC
    orig = basic.read_text()
    todo = [("original", "", "", "", "")] + [m for m in mutants.MUTANTS if not a.names or m[0] in a.names]
    for name, _, what, old, new in todo:
        t = time.time()
        if old:
            assert orig.count(old) == 1, name
        basic.write_text(orig.replace(old, new) if old else orig)
        print(f"{name:16} {run(a.cases, a.seed, env)}  ({time.time() - t:.0f} s)", flush=True)
    basic.write_text(orig)


if __name__ == "__main__":
    main()
