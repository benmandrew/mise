#!/usr/bin/env bash
# Build docs/theorems.pdf from docs/theorems.typ, its style, fonts and Lean
# syntax. The creation date is fixed, so the same inputs and Typst give the
# same bytes, and the committed PDF can be checked against its inputs.
#
#   scripts/theorems-pdf.sh           write docs/theorems.pdf
#   scripts/theorems-pdf.sh --staged  fail if the staged docs/theorems.pdf
#                                     differs from a build of the staged
#                                     inputs (.githooks/pre-commit runs this)
#
# scripts/trusted.sh writes docs/theorems.typ, and scripts/check.sh fails if
# that file is out of date.
set -euo pipefail
cd "$(dirname "$0")/.."

# Typst stamps the PDF with the build time unless given one. This is
# 1980-01-01, the time the Nix shell's SOURCE_DATE_EPOCH gives.
build() {
  typst compile --ignore-system-fonts --font-path "$1/fonts" \
    --creation-timestamp 315532800 "$1/theorems.typ" "$2"
}

if [ "${1:-}" != "--staged" ]; then
  build docs docs/theorems.pdf
  echo "wrote docs/theorems.pdf"
  exit 0
fi

inputs=(docs/theorems.typ docs/theorems-style.typ docs/lean4.sublime-syntax docs/fonts docs/theorems.pdf)
git diff --cached --quiet -- "${inputs[@]}" && exit 0
fail() { echo "pre-commit: $*" >&2; exit 1; }
command -v typst >/dev/null || fail "typst not found; commit from the Nix shell (nix develop)"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
git ls-files -z -- docs | git checkout-index -z --stdin --prefix="$tmp/"
[ -f "$tmp/docs/theorems.pdf" ] || fail "docs/theorems.pdf is not staged; run scripts/theorems-pdf.sh and git add it"
build "$tmp/docs" "$tmp/built.pdf"
cmp -s "$tmp/built.pdf" "$tmp/docs/theorems.pdf" \
  || fail "the staged docs/theorems.pdf does not match the staged docs/theorems.typ; run scripts/theorems-pdf.sh and git add docs/theorems.pdf"
