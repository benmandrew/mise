#!/usr/bin/env bash
# Trust-base item 2: run every command of the examples and of N random-graph
# cases under a sandbox-exec profile that kills it on a read of anything
# but its declared inputs (for depfile rules, what Graph.DynOK allows) and
# the toolchain, or a write of anything but its outputs. Then check that
# three broken examples fail under the sandbox and pass without it.
# macOS only (see test/confine.py). Usage: test/conf-sandbox.sh [N] [SEED]
set -euo pipefail
cd "$(dirname "$0")/.."
if [ "$(uname)" != Darwin ] || ! command -v sandbox-exec >/dev/null; then
  echo "conf-sandbox: needs macOS sandbox-exec; skipped" >&2
  exit 0
fi
lake build mise >/dev/null
python3 test/confine.py sandbox
test/fuzz.sh "${1:-500}" "${2:-1}" -- --confine sandbox
