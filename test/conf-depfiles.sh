#!/usr/bin/env bash
# Trust-base item 3: trace the files every command opens (test/trace.c,
# loaded with DYLD_INSERT_LIBRARIES or LD_PRELOAD) on the examples and on N
# random-graph cases, and check that each depfile command read in the build
# directory only its inputs and the dependencies Ninja recorded from its
# depfile. Then check that the trace catches a broken example and a helper
# whose depfile drops its last file. Usage: test/conf-depfiles.sh [N] [SEED]
set -euo pipefail
cd "$(dirname "$0")/.."
n=${1:-500}
seed=${2:-1}
lake build mise >/dev/null
python3 test/confine.py trace
test/fuzz.sh "$n" "$seed" -- --confine trace

mut=test/out/conf-depfiles
mkdir -p "$mut"
sed 's/for (int k = 0; k < n; k++) fprintf(f, " %s", reads\[k\]);/for (int k = 0; k < n - 1; k++) fprintf(f, " %s", reads[k]);/' \
  test/fz.c > "$mut/fz-drop-last.c"
if cmp -s test/fz.c "$mut/fz-drop-last.c"; then
  echo "FAIL: the depfile mutant no longer applies to test/fz.c" >&2
  exit 1
fi
cc -O2 -Wall -o "$mut/fz-drop-last" "$mut/fz-drop-last.c"
out=$(python3 test/fuzz.py --seed "$seed" --confine trace --no-shrink --fz "$mut/fz-drop-last" \
  test/out/fuzz/cases || true)
fails=$(echo "$out" | grep -c '^FAIL case' || true)
caught=$(echo "$out" | grep '^FAIL case' | grep -c 'which its depfile does not list' || true)
if [ "$fails" -eq 0 ] || [ "$fails" -ne "$caught" ]; then
  echo "FAIL: the helper whose depfile drops its last file was not caught by the trace:" >&2
  echo "$out" | head -20 >&2
  exit 1
fi
echo "conf-depfiles: the helper whose depfile drops its last file fails $fails of $n cases, each on an unlisted read"
