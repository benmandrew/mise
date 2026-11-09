#!/usr/bin/env bash
# Stage 4 acceptance: generate examples/hello-c/build.ninja from the DSL,
# build it with real Ninja, run the binary, and check that Ninja evaluates
# every command to the one the DSL means.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build gen >/dev/null
lake exe gen examples/hello-c >/dev/null
mkdir -p test/out
lake exe gen --commands examples/hello-c | sort > test/out/hello-c-expected-commands
cd examples/hello-c
rm -rf build .ninja_log .ninja_deps
ninja >/dev/null
out=$(./build/hello)
[ "$out" = "Hello, mise!" ] || { echo "FAIL: binary printed: $out"; exit 1; }
ninja -n | grep -q 'no work to do' || { echo "FAIL: second build has work to do"; exit 1; }
ninja -t commands build/hello | sort > ../../test/out/hello-c-actual-commands
cmp -s ../../test/out/hello-c-expected-commands ../../test/out/hello-c-actual-commands ||
  { echo "FAIL: commands differ"; diff ../../test/out/hello-c-{expected,actual}-commands; exit 1; }
echo "stage4-hello: built, ran, no-op rebuild, $(wc -l < ../../test/out/hello-c-actual-commands | tr -d ' ') commands agree"
