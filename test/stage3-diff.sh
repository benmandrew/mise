#!/usr/bin/env bash
# Differential test: real Ninja must read every generated manifest exactly as
# its AST says (Stage 3), and evaluate every command as the Stage 4 model
# says. Usage: test/stage3-diff.sh [N] [SEED]
set -euo pipefail
cd "$(dirname "$0")/.."
n=${1:-100}
seed=${2:-1}
out=test/out/stage3
rm -rf "$out"
lake build difftest >/dev/null
lake exe difftest "$out" "$n" "$seed"
fail=0
for d in "$out"/*/; do
  targets=()
  while IFS= read -r t; do targets+=("$t"); done < "$d/targets"
  if ! (cd "$d" && ninja -f build.ninja -t query "${targets[@]}") > "$d/actual" 2> "$d/stderr"; then
    echo "FAIL $d: ninja exited non-zero: $(cat "$d/stderr")"
    fail=1
  elif ! cmp -s "$d/expected" "$d/actual"; then
    echo "FAIL $d: query output differs"
    diff "$d/expected" "$d/actual" | head -20
    fail=1
  fi
  cmds=()
  while IFS= read -r t; do cmds+=("$t"); done < "$d/cmd-targets"
  if [ "${#cmds[@]}" -gt 0 ]; then
    (cd "$d" && ninja -f build.ninja -t commands -s "${cmds[@]}") > "$d/actual-commands"
    if ! cmp -s "$d/expected-commands" "$d/actual-commands"; then
      echo "FAIL $d: evaluated commands differ"
      diff "$d/expected-commands" "$d/actual-commands" | head -20
      fail=1
    fi
  fi
done
neg=test/out/stage3-negative
rm -rf "$neg"
lake exe difftest negative "$neg"
for d in "$neg"/*/; do
  if (cd "$d" && ninja -f build.ninja -t targets all) >/dev/null 2>&1; then
    echo "FAIL $d: ninja accepts a manifest the parser model rejects"
    fail=1
  fi
done
if [ "$fail" -eq 0 ]; then
  echo "stage3-diff: $n manifests agree with $(ninja --version); $(ls "$neg" | wc -l | tr -d ' ') negative cases rejected by both"
fi
exit "$fail"
