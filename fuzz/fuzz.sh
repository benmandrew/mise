#!/usr/bin/env bash
# Build one of the fuzzers in fuzz/ with fuzz/build.sh and run it.
#
# Usage: fuzz/fuzz.sh parser|build [--engine libfuzzer|afl|standalone]
#          [--time SECONDS] [--mode text|gen] [--cases N] [--seed S]
#          [--repro FILE...] [-- ENGINE_ARGS...]
#
#   --engine  default libfuzzer
#   --time    how long libFuzzer or AFL++ runs, default 60 seconds
#   --mode    parser only: text (default) feeds the input to both parsers
#             as a manifest; gen turns it into a generated manifest first
#   --cases   standalone only: the number of pseudo-random inputs, default 500
#   --seed    standalone only: the seed of the first input, default 1
#   --repro   replay the inputs in the files instead of fuzzing
#
# ENGINE_ARGS go to libFuzzer or afl-fuzz; for the standalone engine, a
# number sets the bytes per input (default 4096).
#
# The corpus lives in test/out/fuzz-TARGET[-MODE]/corpus, failing inputs in
# its crash directory. The build fuzzer also writes each mismatching case
# as JSON to $MISE_FUZZ_OUT (default test/out/fuzz/inproc), which
# `test/fuzz.py DIR N` replays against real Ninja. The last line says pass
# or FAIL, and the exit status is 1 on a failure.
set -euo pipefail
cd "$(dirname "$0")/.."

usage() { sed -n '4,6p' "$0" | sed 's/^# //' >&2; exit 2; }
[ $# -ge 1 ] || usage
target=$1
shift
case "$target" in parser|build) ;; *) usage ;; esac
engine=libfuzzer secs=60 mode= cases=500 seed=1 repro=()
while [ $# -gt 0 ]; do
  case "$1" in
    --engine) engine=$2; shift 2 ;;
    --time) secs=$2; shift 2 ;;
    --mode) mode=$2; shift 2 ;;
    --cases) cases=$2; shift 2 ;;
    --seed) seed=$2; shift 2 ;;
    --repro)
      shift
      while [ $# -gt 0 ] && [ "$1" != -- ] && [ "${1#--}" = "$1" ]; do repro+=("$1"); shift; done
      [ ${#repro[@]} -gt 0 ] || usage ;;
    --) shift; break ;;
    *) usage ;;
  esac
done
case "$engine" in libfuzzer|afl|standalone) ;; *) usage ;; esac
if [ "$target" = parser ]; then
  mode=${mode:-text}
  case "$mode" in text|gen) ;; *) usage ;; esac
  export MISE_FUZZ_MODE=$mode
elif [ -n "$mode" ]; then
  echo "$0: --mode applies to the parser fuzzer only" >&2
  exit 2
fi

bin=$(fuzz/build.sh "$target" "$engine")
name=$target${mode:+ $mode}
dir=test/out/fuzz-$target${mode:+-$mode}
corpus=$dir/corpus crash=$dir/crash
mkdir -p "$corpus" "$crash"
export ASAN_OPTIONS=${ASAN_OPTIONS:-detect_leaks=0}

pass() { echo "fuzz $name ($engine): pass; $*"; exit 0; }
fail() { echo "fuzz $name ($engine): FAIL; $*" >&2; exit 1; }

if [ ${#repro[@]} -gt 0 ]; then
  if [ "$engine" = standalone ]; then set -- "${repro[@]}"; else set -- "$@" "${repro[@]}"; fi
  "$bin" "$@" || fail "an input fails"
  pass "${#repro[@]} inputs replayed"
fi

# The standalone engine's own argument is the number of bytes per input.
if [ "$engine" = standalone ]; then
  "$bin" "$cases" "$seed" "$@" || fail "see the failures above"
  pass "$cases inputs from seed $seed"
fi

# Seeds for the parser's text mode: generated manifests the model accepts,
# and the negative cases. Other modes start from the corpus alone.
seeds=()
if [ "$target" = parser ] && [ "$mode" = text ]; then
  rm -rf "$dir/seeds"
  lake exe difftest "$dir/seeds/gen" 200 1 >/dev/null
  lake exe difftest negative "$dir/seeds/neg" >/dev/null
  mkdir -p "$dir/seeds/flat"
  for f in "$dir"/seeds/gen/*/build.ninja "$dir"/seeds/neg/*/build.ninja; do
    cp "$f" "$dir/seeds/flat/$(basename "$(dirname "$f")")-$(basename "$(dirname "$(dirname "$f")")")"
  done
  seeds=("$dir/seeds/flat")
fi
dict=()
[ "$target" = parser ] && [ "$mode" = text ] && dict=(fuzz/parser/parser.dict)
max_len=4096

if [ "$engine" = libfuzzer ]; then
  set +e
  "$bin" ${dict:+-dict="${dict[0]}"} -max_len=$max_len -max_total_time="$secs" -print_final_stats=1 \
    -artifact_prefix="$crash/" "$@" "$corpus" "${seeds[@]}" 2>&1 |
    grep -v '^#[0-9]*[[:space:]]*\(NEW\|REDUCE\|pulse\)'
  status=${PIPESTATUS[0]}
  set -e
  [ "$status" -eq 0 ] || fail "inputs in $crash; replay with $0 $target${mode:+ --mode $mode} --repro FILE"
  pass "${secs}s against Ninja; corpus $(ls "$corpus" | wc -l | tr -d ' ') inputs"
fi

# AFL++. Untested on macOS, where nixpkgs has no AFL++.
if [ ${#seeds[@]} -eq 0 ]; then
  if [ -z "$(ls "$corpus")" ]; then head -c 64 /dev/urandom > "$corpus/random"; fi
  seeds=("$corpus")
fi
afl=$dir/afl
AFL_SKIP_CPUFREQ=1 AFL_NO_UI=1 afl-fuzz -i "${seeds[0]}" -o "$afl" ${dict:+-x "${dict[0]}"} -G $max_len \
  -V "$secs" "$@" -- "$bin" || fail "afl-fuzz stopped"
found=$(find "$afl" -path '*/crashes/id:*' | wc -l | tr -d ' ')
[ "$found" -eq 0 ] || fail "$found inputs in $afl/*/crashes; replay with $0 $target${mode:+ --mode $mode} --repro FILE"
pass "${secs}s against Ninja; queue in $afl"
