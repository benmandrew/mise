#!/usr/bin/env bash
# Mutation testing of the Ninja model against the random-graph harness:
# apply each mutant in test/mutants.py to a copy of the tree, rebuild only
# fuzzgen, and record which check kills it. With --via inproc, rebuild the
# in-process build fuzzer instead (fuzz/build.sh build standalone) and
# check against Ninja's own code.
# Usage: test/mutants.sh [--via real|inproc] [--cases N] [--seed S] [--workers W] [MUTANT...]
set -euo pipefail
cd "$(dirname "$0")/.."
lake build mise fuzzgen >/dev/null
python3 test/mutants.py "$@"
