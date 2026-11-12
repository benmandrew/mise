#!/usr/bin/env bash
# The command wrapper on a rule without `restat`, against real Ninja. One
# generator edge writes two explicit outputs and an implicit one whose name
# has a space; each output is copied by a downstream edge. The checks: a
# command that exits 0 without writing an output fails the build loudly,
# leaves every old output with its mtime and no `.mise-old` files, runs no
# copy, and is retried by the next build; so is a command that fails after a
# partial write; a first build that fails leaves no outputs and removes a
# stale `.mise-old` file; and with `wrap = false` the same command "succeeds"
# but leaves Ninja with work on every later build.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build mise >/dev/null
mise=$PWD/.lake/build/bin/mise
dir=test/out/wrap-outputs
rm -rf "$dir"
mkdir -p "$dir"
cd "$dir"

cat > gen.sh <<'EOF'
# gen.sh IN MODE A B C: line 1 of IN to A, line 2 to B, line 3 to C. Mode
# `fail` exits 1 after writing A; mode `skip` does not write B and exits 0.
mode=$(cat "$2")
sed -n 1p "$1" > "$3"
[ "$mode" = fail ] && exit 1
[ "$mode" = skip ] || sed -n 2p "$1" > "$4"
sed -n 3p "$1" > "$5"
exit 0
EOF
cat > mise.toml <<'EOF'
sources = ["gen.sh", "in.txt", "mode"]

[[rule]]
name = "gen"
command = "sh gen.sh $in $out 'out/c d.txt'"
description = "GEN"

[[rule]]
name = "copy"
command = "cp $in $out"
description = "COPY $out"

[[build]]
rule = "gen"
outs = ["out/a.txt", "out/b.txt"]
implicit-outs = ["out/c d.txt"]
ins = ["in.txt", "mode"]
implicit-ins = ["gen.sh"]

[[build]]
rule = "copy"
outs = ["copy/a.txt"]
ins = ["out/a.txt"]

[[build]]
rule = "copy"
outs = ["copy/b.txt"]
ins = ["out/b.txt"]

[[build]]
rule = "copy"
outs = ["copy/c.txt"]
ins = ["out/c d.txt"]
EOF
mkdir -p out copy
printf 'a1\nb1\nc1\n' > in.txt

fail() { echo "FAIL: $*"; exit 1; }
mtimes() { for f in out/a.txt out/b.txt "out/c d.txt"; do stat -c %y "$f" 2>/dev/null || stat -f %Fm "$f"; done; }
# Run a build; print the descriptions of the edges that ran, sorted.
ran() { "$mise" build . -- "$@" 2>&1 | sed -nE 's/^\[[0-9]+\/[0-9]+\] //p' | sort | tr '\n' ' '; }
contents() { cat out/a.txt out/b.txt "out/c d.txt" copy/a.txt copy/b.txt copy/c.txt | tr '\n' ' '; }
no_old() { [ -z "$(find . -name '*.mise-old')" ] || fail "$1: left $(find . -name '*.mise-old')"; }
# Build, expecting failure; print the output.
failing() { if out=$("$mise" build . 2>&1); then fail "$1: build succeeded"; fi; echo "$out"; }
tick() { sleep 0.05; }

# A first build whose command leaves an output missing: nothing is left
# behind, not even a stale `.mise-old` file from before.
echo skip > mode
echo stale > out/b.txt.mise-old
out=$(failing "first build")
echo "$out" | grep -q "mise: out/b.txt was not written" || fail "first build: no message"
[ -z "$(ls out)" ] || fail "first build: left $(ls out)"
no_old "first build"

echo ok > mode
[ "$(ran)" = "COPY copy/a.txt COPY copy/b.txt COPY copy/c.txt GEN " ] || fail "clean build"
[ "$(contents)" = "a1 b1 c1 a1 b1 c1 " ] || fail "clean contents: $(contents)"
"$mise" build . -- -n | grep -q "no work to do" || fail "no-op build has work"
no_old "clean build"

# Exit 0 without writing out/b.txt, after rewriting out/a.txt: the build
# fails loudly, every old output keeps its contents and mtime, and no copy
# runs.
before=$(mtimes); tick
printf 'a2\nb2\nc2\n' > in.txt; echo skip > mode
out=$(failing "missing output")
echo "$out" | grep -q "mise: out/b.txt was not written" || fail "missing output: no message"
echo "$out" | grep -q "FAILED: .*out/a.txt out/b.txt" || fail "missing output: Ninja did not report the edge"
echo "$out" | grep -q "COPY" && fail "missing output: a copy ran"
[ "$(contents)" = "a1 b1 c1 a1 b1 c1 " ] || fail "missing output: outputs changed: $(contents)"
[ "$(mtimes)" = "$before" ] || fail "missing output: an mtime changed"
no_old "missing output"

# The next build retries the edge, with no edit in between.
out=$(failing "retry")
echo "$out" | grep -q "\] GEN" || fail "retry: the generator did not run"
[ "$(mtimes)" = "$before" ] || fail "retry: an mtime changed"
no_old "retry"

# A command that fails after a partial write behaves the same.
echo fail > mode
failing "failing command" >/dev/null
[ "$(contents)" = "a1 b1 c1 a1 b1 c1 " ] || fail "failing command: outputs changed: $(contents)"
[ "$(mtimes)" = "$before" ] || fail "failing command: an mtime changed"
no_old "failing command"

# Recovery: the edge is still dirty, and the new contents reach every copy.
echo ok > mode
[ "$(ran)" = "COPY copy/a.txt COPY copy/b.txt COPY copy/c.txt GEN " ] || fail "recovery: wrong edges ran"
[ "$(contents)" = "a2 b2 c2 a2 b2 c2 " ] || fail "recovery contents: $(contents)"
"$mise" build . -- -n | grep -q "no work to do" || fail "after recovery: work left"
no_old "recovery"

# Without a `restat` rule, every successful run writes every output afresh.
before=$(mtimes); tick
printf 'a2\nb2\nc2\nignored\n' > in.txt
[ "$(ran)" = "COPY copy/a.txt COPY copy/b.txt COPY copy/c.txt GEN " ] || fail "rewrite: wrong edges ran"
[ "$(mtimes | sed -n 1p)" != "$(echo "$before" | sed -n 1p)" ] || fail "rewrite: a.txt kept its mtime"

# `wrap = false`: the same command exits 0 without out/b.txt, a build of
# out/a.txt succeeds, and Ninja has work on every build after it.
awk '{ print } /^description = "GEN"$/ { print "wrap = false" }' mise.toml > mise.toml.new
mv mise.toml.new mise.toml
[ "$("$mise" gen --commands . | head -1)" = "sh gen.sh in.txt mode out/a.txt out/b.txt 'out/c d.txt'" ] ||
  fail "wrap = false still wraps"
"$mise" build . >/dev/null
rm out/b.txt; echo skip > mode
"$mise" build . -- out/a.txt >/dev/null 2>&1 || fail "wrap = false: build failed"
[ "$(ran out/a.txt)" = "GEN " ] || fail "wrap = false: second build did not rerun the generator"
"$mise" build . -- -n out/a.txt | grep -q "no work to do" && fail "wrap = false: no work left"
echo "wrap-outputs: missing output, retry, failure, recovery and the unwrapped contrast all pass"
