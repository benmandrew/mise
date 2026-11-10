#!/usr/bin/env bash
# Stage 6 acceptance: edit sequences on both examples against real Ninja
# (see test/props.py). Arguments pass through, e.g. --order 2.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build mise >/dev/null
python3 test/props.py "$@"
