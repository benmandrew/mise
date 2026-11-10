#!/usr/bin/env bash
# Random-graph harness: generate N cases with SEED (see test/MiseTest/Fuzz.lean)
# and replay them against real Ninja (see test/fuzz.py).
# Usage: test/fuzz.sh [N] [SEED] [-- FUZZ_PY_ARGS...]
set -euo pipefail
cd "$(dirname "$0")/.."
n=${1:-500}
seed=${2:-1}
shift $(( $# < 2 ? $# : 2 ))
[ "${1:-}" = "--" ] && shift
cases=test/out/fuzz/cases
lake build mise fuzzgen >/dev/null
rm -rf "$cases"
lake exe fuzzgen "$cases" "$n" "$seed"
python3 test/fuzz.py --seed "$seed" "$cases" "$@"
