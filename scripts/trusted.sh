#!/usr/bin/env bash
# Write docs/trusted.md: the definitions each theorem in Mise/Headline.lean
# depends on (see test/MiseTest/Trusted.lean). `--check` fails if it is stale.
set -euo pipefail
cd "$(dirname "$0")/.."
out=$(lake env lean test/MiseTest/Trusted.lean)
if [ "${1:-}" = "--check" ]; then
  if ! diff -q <(echo "$out") docs/trusted.md >/dev/null; then
    echo "check: docs/trusted.md is out of date; run scripts/trusted.sh" >&2
    exit 1
  fi
else
  echo "$out" > docs/trusted.md
fi
