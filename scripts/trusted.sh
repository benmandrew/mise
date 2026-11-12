#!/usr/bin/env bash
# Write docs/trusted.md and docs/headline.typ from the theorems in
# Mise/Headline.lean (see test/MiseTest/Trusted.lean). Run after `lake build`.
#
#   scripts/trusted.sh          write both files
#   scripts/trusted.sh --pdf    write both files and build docs/headline.pdf
#   scripts/trusted.sh --check  fail if either file is out of date, if a
#                               trusted declaration has no docstring, or if
#                               docs/headline.typ does not compile with Lean
#                               highlighting
#
# docs/headline.pdf is not committed; docs/headline.typ is.
set -euo pipefail
cd "$(dirname "$0")/.."
mode=${1:-}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

TRUSTED_OUT=$tmp lake env lean test/MiseTest/Trusted.lean > "$tmp/report"
cat "$tmp/report"

if [ "$mode" = "--check" ]; then
  for f in trusted.md headline.typ; do
    if ! diff -q "$tmp/$f" "docs/$f" >/dev/null; then
      echo "check: docs/$f is out of date; run scripts/trusted.sh" >&2
      exit 1
    fi
  done
  if grep -q '^missing docstring' "$tmp/report"; then
    echo "check: every trusted declaration needs a docstring" >&2
    exit 1
  fi
  typst compile --ignore-system-fonts docs/headline.typ "$tmp/headline.pdf"
  # A grammar that does not match `lang: "lean"` leaves code in one colour
  # without an error, so count the colours in a highlighted probe.
  cat > "$tmp/probe.typ" <<EOF
#import "$PWD/docs/headline-style.typ": lean-code
#show: lean-code
#raw(lang: "lean", block: true, "/-- Doc. -/\ntheorem t : ∀ x : Nat, x = x := by\n  -- comment\n  rfl")
EOF
  typst compile --ignore-system-fonts --root / "$tmp/probe.typ" "$tmp/probe.svg"
  colours=$(grep -o 'fill="#[0-9a-fA-F]*"' "$tmp/probe.svg" | sort -u | grep -vic 'fill="#ffffff"' || true)
  if [ "$colours" -lt 4 ]; then
    echo "check: Lean code in docs/headline.typ is not highlighted ($colours colours)" >&2
    exit 1
  fi
else
  cp "$tmp/trusted.md" "$tmp/headline.typ" docs/
  if [ "$mode" = "--pdf" ]; then
    typst compile --ignore-system-fonts docs/headline.typ docs/headline.pdf
    echo "wrote docs/headline.pdf"
  fi
fi
