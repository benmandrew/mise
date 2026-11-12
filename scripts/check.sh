#!/usr/bin/env bash
# Acceptance checks shared by every stage:
#   1. lake build succeeds;
#   2. no `sorry` or `admit` in Lean sources;
#   3. headline theorems use only propext, Classical.choice and Quot.sound;
#   4. docs/trusted.md and docs/headline.typ match the definitions the
#      headline theorems use, and docs/headline.typ compiles with Typst;
#   5. every one of those definitions has a docstring.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build

if grep -rnwE 'sorry|admit' --include='*.lean' Mise test Main.lean; then
  echo "check: found sorry/admit" >&2
  exit 1
fi

out=$(lake env lean test/MiseTest/Axioms.lean)
echo "$out"
bad=$(echo "$out" | grep 'depends on axioms' \
  | sed -E 's/.*depends on axioms: \[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ' \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [ -n "$bad" ]; then
  echo "check: unexpected axioms: $bad" >&2
  exit 1
fi
n=$(echo "$out" | grep -c 'axiom' || true)
# Checks 4 and 5.
scripts/trusted.sh --check
echo "check: ok ($n theorems checked)"
