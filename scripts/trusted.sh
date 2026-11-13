#!/usr/bin/env bash
# Write docs/trusted.md and docs/theorems.typ from the theorems in
# Mise/Theorems.lean (see test/MiseTest/Trusted.lean). Run after `lake build`.
#
#   scripts/trusted.sh          write both files
#   scripts/trusted.sh --pdf    write both files and build docs/theorems.pdf
#   scripts/trusted.sh --check  fail if either file is out of date, if a
#                               trusted declaration has no docstring, or if
#                               docs/theorems.typ does not compile with Lean
#                               highlighting
#
# docs/theorems.pdf is not committed; docs/theorems.typ is.
set -euo pipefail
cd "$(dirname "$0")/.."
mode=${1:-}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

TRUSTED_OUT=$tmp lake env lean test/MiseTest/Trusted.lean > "$tmp/report"
cat "$tmp/report"

if [ "$mode" = "--check" ]; then
  for f in trusted.md theorems.typ; do
    if ! diff -q "$tmp/$f" "docs/$f" >/dev/null; then
      echo "check: docs/$f is out of date; run scripts/trusted.sh" >&2
      exit 1
    fi
  done
  if grep -q '^missing docstring' "$tmp/report"; then
    echo "check: every trusted declaration needs a docstring" >&2
    exit 1
  fi
  # Typst silently falls back to another font for a character the Iosevka
  # subset lacks, so check every character against the subset's ranges.
  python3 - docs/fonts/charset.txt docs/theorems.typ docs/theorems-style.typ <<'EOF'
import re, sys
ranges = []
for line in open(sys.argv[1], encoding="utf-8"):
    m = re.match(r"U\+([0-9A-F]+)-([0-9A-F]+)", line.split("#")[0].strip())
    if m:
        ranges.append((int(m[1], 16), int(m[2], 16)))
bad = sorted({c for f in sys.argv[2:] for c in open(f, encoding="utf-8").read()
              if ord(c) > 0x7E and not any(a <= ord(c) <= b for a, b in ranges)})
if bad:
    print("check: docs/fonts/charset.txt does not cover "
          + " ".join(f"{c} U+{ord(c):04X}" for c in bad)
          + "; add the range and run scripts/subset-fonts.sh", file=sys.stderr)
    sys.exit(1)
EOF
  typst compile --ignore-system-fonts --font-path docs/fonts docs/theorems.typ "$tmp/theorems.pdf"
  # A grammar that does not match `lang: "lean"` leaves code in one colour
  # without an error, so count the colours in a highlighted probe.
  cat > "$tmp/probe.typ" <<EOF
#import "$PWD/docs/theorems-style.typ": lean-code
#show: lean-code
#raw(lang: "lean", block: true, "/-- Doc. -/\ntheorem t : ∀ x : Nat, x = x := by\n  -- comment\n  rfl")
EOF
  typst compile --ignore-system-fonts --font-path docs/fonts --root / "$tmp/probe.typ" "$tmp/probe.svg"
  colours=$(grep -o 'fill="#[0-9a-fA-F]*"' "$tmp/probe.svg" | sort -u | grep -vic 'fill="#ffffff"' || true)
  if [ "$colours" -lt 4 ]; then
    echo "check: Lean code in docs/theorems.typ is not highlighted ($colours colours)" >&2
    exit 1
  fi
else
  cp "$tmp/trusted.md" "$tmp/theorems.typ" docs/
  if [ "$mode" = "--pdf" ]; then
    typst compile --ignore-system-fonts --font-path docs/fonts docs/theorems.typ docs/theorems.pdf
    echo "wrote docs/theorems.pdf"
  fi
fi
