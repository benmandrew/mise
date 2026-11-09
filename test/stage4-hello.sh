#!/usr/bin/env bash
# Stage 4 acceptance: build examples/hello-c with `mise build`, run the
# binary, check that a second `mise build` has no work and leaves build.ninja
# alone, and check that Ninja evaluates every command to the one the DSL means.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build mise >/dev/null
mise=$PWD/.lake/build/bin/mise
mkdir -p test/out
"$mise" gen --commands examples/hello-c | sort > test/out/hello-c-expected-commands
cd examples/hello-c
rm -rf build build.ninja .ninja_log .ninja_deps
"$mise" build >/dev/null
out=$(./build/hello)
[ "$out" = "Hello, mise!" ] || { echo "FAIL: binary printed: $out"; exit 1; }
before=$(ls -l --time-style=full-iso build.ninja 2>/dev/null || stat -f %Fm build.ninja)
again=$("$mise" build)
[ "$again" = "ninja: no work to do." ] || { echo "FAIL: second build: $again"; exit 1; }
after=$(ls -l --time-style=full-iso build.ninja 2>/dev/null || stat -f %Fm build.ninja)
[ "$before" = "$after" ] || { echo "FAIL: second build rewrote build.ninja"; exit 1; }
ninja -t commands build/hello | sort > ../../test/out/hello-c-actual-commands
cmp -s ../../test/out/hello-c-expected-commands ../../test/out/hello-c-actual-commands ||
  { echo "FAIL: commands differ"; diff ../../test/out/hello-c-{expected,actual}-commands; exit 1; }
echo "stage4-hello: built, ran, no-op rebuild, $(wc -l < ../../test/out/hello-c-actual-commands | tr -d ' ') commands agree"
