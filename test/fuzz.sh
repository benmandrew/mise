#!/usr/bin/env bash
# Random-graph harness: generate N cases with SEED (see test/MiseTest/Fuzz.lean)
# and replay them against real Ninja (see test/fuzz.py). OPTS are generator
# flags, comma-separated; the only one is `absent` (see `Opts` in Fuzz.lean).
# Usage: test/fuzz.sh [--opts OPTS] [N] [SEED] [-- FUZZ_PY_ARGS...]
set -euo pipefail
cd "$(dirname "$0")/.."
opts=()
if [ "${1:-}" = "--opts" ]; then
  opts=("$2")
  shift 2
fi
n=${1:-500}
seed=${2:-1}
shift $(( $# < 2 ? $# : 2 ))
[ "${1:-}" = "--" ] && shift
cases=test/out/fuzz/cases
lake build mise fuzzgen >/dev/null
rm -rf "$cases"
lake exe fuzzgen "$cases" "$n" "$seed" ${opts[@]+"${opts[@]}"}
python3 test/fuzz.py --seed "$seed" "$cases" "$@"
