#!/usr/bin/env bash
# Acceptance checks shared by every stage:
#   1. lake build succeeds;
#   2. no `sorry` or `admit` in Lean sources;
#   3. headline theorems use only propext, Classical.choice and Quot.sound;
#   4. each example's mise.toml emits the same manifest as its Lean description.
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

# Elaborated fresh on every run: Lake cannot see that it reads the TOML files.
lake env lean test/MiseTest/Toml.lean

echo "check: ok ($n theorems checked, TOML examples agree)"
