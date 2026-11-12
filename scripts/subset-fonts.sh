#!/usr/bin/env bash
# Write docs/fonts/IosevkaExtended-{Regular,Bold}.ttf, the code font of
# docs/headline.pdf, as subsets of Iosevka Extended from nixpkgs' iosevka-bin.
#
# The full package is 486 MB, so the repository keeps only these subsets
# (about 90 KB each). They hold the ranges in docs/fonts/charset.txt and drop
# every layout feature, ligatures included, and the hinting. Run this only to
# change those ranges or the Iosevka version.
set -euo pipefail
cd "$(dirname "$0")/.."

nixpkgs='(builtins.getFlake (toString ./.)).inputs.nixpkgs.legacyPackages.${builtins.currentSystem}'
iosevka=$(nix build --no-link --print-out-paths --impure --expr "$nixpkgs.iosevka-bin")
for w in Regular Bold; do
  # Face 3 of each collection is Iosevka Extended.
  nix shell --impure --expr "$nixpkgs.python3.withPackages (p: [ p.fonttools ])" -c \
    pyftsubset "$iosevka/share/fonts/truetype/Iosevka-$w.ttc" --font-number=3 \
      --unicodes-file=docs/fonts/charset.txt --layout-features= --no-layout-closure \
      --no-hinting --name-IDs='*' --notdef-outline \
      --output-file="docs/fonts/IosevkaExtended-$w.ttf"
  echo "wrote docs/fonts/IosevkaExtended-$w.ttf ($(wc -c < "docs/fonts/IosevkaExtended-$w.ttf") bytes)"
done
