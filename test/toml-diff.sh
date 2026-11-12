#!/usr/bin/env bash
# Differential test: the mise.toml parser (Mise/Frontend/Toml.lean) against
# Python's tomllib on N random documents of each kind (see test/toml_diff.py).
# Usage: test/toml-diff.sh [N] [SEED]
set -euo pipefail
cd "$(dirname "$0")/.."
n=${1:-2500}
seed=${2:-1}
lake build tomljson >/dev/null
python3 test/toml_diff.py --seed "$seed" test/out/toml "$n"
