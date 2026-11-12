#!/usr/bin/env bash
# Run the shell harnesses against several Ninja releases and print a table.
# Each release is the flake package `ninja-X_Y_Z`, built from its upstream
# tag; it goes first on PATH, and the rest comes from the shell this runs in.
# Logs go to test/out/matrix/<release>/<harness>.log.
#
# Usage: test/ninja-matrix.sh [--workers W] [--fuzz N] [--seed S] [RELEASE...]
#   --workers W  workers for the property and random-graph harnesses
#                (default: one per core)
#   --fuzz N     random-graph cases per release (default 500)
#   --seed S     seed for every harness (default 1)
# With no RELEASE, it runs every release in the flake.
set -euo pipefail
cd "$(dirname "$0")/.."

all=(1.10.2 1.11.1 1.12.1 1.13.2)
workers=$(getconf _NPROCESSORS_ONLN)
fuzz=500
seed=1
releases=()
while [ $# -gt 0 ]; do
  case "$1" in
    --workers) workers=$2; shift 2 ;;
    --fuzz) fuzz=$2; shift 2 ;;
    --seed) seed=$2; shift 2 ;;
    -h|--help) sed -n '2,12p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*) echo "unknown option $1" >&2; exit 2 ;;
    *) releases+=("$1"); shift ;;
  esac
done
[ ${#releases[@]} -gt 0 ] || releases=("${all[@]}")

command -v lake >/dev/null || { echo "run this in the Nix shell (nix develop)" >&2; exit 2; }
lake build mise fuzzgen difftest >/dev/null

harnesses=(stage3 stage4 props fuzz)
run_harness() {
  case "$1" in
    stage3) test/stage3-diff.sh 100 "$seed" ;;
    stage4) test/stage4-hello.sh ;;
    props) test/stage6-props.sh --order 2 --seed "$seed" --workers "$workers" ;;
    fuzz) test/fuzz.sh "$fuzz" "$seed" -- --workers "$workers" ;;
  esac
}

out=test/out/matrix
mkdir -p "$out"
rows=()
fail=0
for r in "${releases[@]}"; do
  attr="ninja-${r//./_}"
  bin=$(nix build --no-link --print-out-paths ".#$attr")/bin
  got=$(PATH="$bin:$PATH" ninja --version)
  [ "$got" = "$r" ] || { echo "$attr reports Ninja $got, not $r" >&2; exit 1; }
  mkdir -p "$out/$r"
  row=$(printf '%-8s' "$r")
  for h in "${harnesses[@]}"; do
    log="$out/$r/$h.log"
    start=$(date +%s)
    if PATH="$bin:$PATH" run_harness "$h" >"$log" 2>&1; then res=pass; else res=FAIL; fail=1; fi
    secs=$(( $(date +%s) - start ))
    echo "ninja $r $h: $res in ${secs}s ($log)"
    row+=$(printf ' | %-10s' "$res ${secs}s")
  done
  rows+=("$row")
done

echo
printf '%-8s' release
for h in "${harnesses[@]}"; do printf ' | %-10s' "$h"; done
echo
printf -- '-%.0s' $(seq 1 60); echo
for row in "${rows[@]}"; do echo "$row"; done
exit "$fail"
