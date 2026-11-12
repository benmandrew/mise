#!/usr/bin/env bash
# Trust-base item 2, determinism: two clean builds of each example per
# cflags value, in different directories, a second apart, with different
# -j levels, time zones and locales, give byte-identical products (with
# `-g`, identical once the embedded build directory is substituted; see
# test/confine.py). Arguments pass through, e.g. --flag='-O3'.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build mise >/dev/null
python3 test/confine.py determinism "$@"
