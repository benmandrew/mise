#!/usr/bin/env bash
# The `cmp` wrapper on `restat` rules, against real Ninja. One generator edge
# writes two explicit outputs and an implicit one whose name has a space;
# each output is copied by a downstream edge. The checks: an edit that leaves
# the outputs the same reruns only the generator and keeps every mtime; an
# edit to one output's contents reruns only its copy; a failed command and a
# missing output fail the build and leave the old outputs, mtimes and no
# `.mise-old` files; and the build after a failure recovers. The commands
# always write, so any early cutoff comes from the wrapper.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build mise >/dev/null
mise=$PWD/.lake/build/bin/mise
dir=test/out/restat-cmp
rm -rf "$dir"
mkdir -p "$dir"
cd "$dir"

cat > gen.sh <<'EOF'
# gen.sh IN MODE A B C: line 1 of IN to A, line 2 to B, line 3 to C. Mode
# `fail` exits 1 after writing A; mode `skip` does not write B.
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
restat = true

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
echo ok > mode

fail() { echo "FAIL: $*"; exit 1; }
mtimes() { for f in out/a.txt out/b.txt "out/c d.txt"; do stat -c %y "$f" 2>/dev/null || stat -f %Fm "$f"; done; }
# Run a build; print the descriptions of the edges that ran, sorted.
ran() { "$mise" build . -- "$@" 2>&1 | sed -nE 's/^\[[0-9]+\/[0-9]+\] //p' | sort | tr '\n' ' '; }
contents() { cat out/a.txt out/b.txt "out/c d.txt" copy/a.txt copy/b.txt copy/c.txt | tr '\n' ' '; }
no_old() { [ -z "$(find . -name '*.mise-old')" ] || fail "$1: left $(find . -name '*.mise-old')"; }
# Ninja's mtimes have nanoseconds, but make sure each edit is visibly newer.
tick() { sleep 0.05; }

[ "$(ran)" = "COPY copy/a.txt COPY copy/b.txt COPY copy/c.txt GEN " ] || fail "clean build"
[ "$(contents)" = "a1 b1 c1 a1 b1 c1 " ] || fail "clean contents: $(contents)"
"$mise" build . -- -n | grep -q "no work to do" || fail "no-op build has work"
no_old "clean build"

# A line the generator ignores: early cutoff, every mtime kept.
before=$(mtimes); tick
printf 'a1\nb1\nc1\nignored\n' > in.txt
[ "$(ran)" = "GEN " ] || fail "ignored line: ran more than GEN"
[ "$(mtimes)" = "$before" ] || fail "ignored line: an mtime changed"
"$mise" build . -- -n | grep -q "no work to do" || fail "after cutoff: work left"
no_old "cutoff"

# A change to one output propagates to its copy only.
before=$(mtimes); tick
printf 'a1\nb2\nc1\n' > in.txt
[ "$(ran)" = "COPY copy/b.txt GEN " ] || fail "edit b: wrong edges ran"
[ "$(contents)" = "a1 b2 c1 a1 b2 c1 " ] || fail "edit b contents: $(contents)"
[ "$(mtimes | sed -n 1p)" = "$(echo "$before" | sed -n 1p)" ] || fail "edit b: a.txt rewritten"
[ "$(mtimes | sed -n 2p)" != "$(echo "$before" | sed -n 2p)" ] || fail "edit b: b.txt not rewritten"

# The implicit output, whose name needs quoting, propagates too.
tick
printf 'a1\nb2\nc3\n' > in.txt
[ "$(ran)" = "COPY copy/c.txt GEN " ] || fail "edit c: wrong edges ran"
[ "$(contents)" = "a1 b2 c3 a1 b2 c3 " ] || fail "edit c contents: $(contents)"

# A failing command after a partial write: the build fails, old outputs stay.
before=$(mtimes); tick
printf 'a9\nb9\nc9\n' > in.txt; echo fail > mode
if "$mise" build . >/dev/null 2>&1; then fail "failing command: build succeeded"; fi
[ "$(contents)" = "a1 b2 c3 a1 b2 c3 " ] || fail "failing command: outputs changed: $(contents)"
[ "$(mtimes)" = "$before" ] || fail "failing command: an mtime changed"
no_old "failing command"

# A missing output is a failure too.
echo skip > mode
out=$("$mise" build . 2>&1 || true)
echo "$out" | grep -q "mise: out/b.txt was not written" || fail "missing output: no message"
echo "$out" | grep -q "FAILED" || fail "missing output: build did not fail"
[ "$(contents)" = "a1 b2 c3 a1 b2 c3 " ] || fail "missing output: outputs changed: $(contents)"
[ "$(mtimes)" = "$before" ] || fail "missing output: an mtime changed"
no_old "missing output"

# Recovery: the edge is still dirty, and the new contents reach every copy.
echo ok > mode
[ "$(ran)" = "COPY copy/a.txt COPY copy/b.txt COPY copy/c.txt GEN " ] || fail "recovery: wrong edges ran"
[ "$(contents)" = "a9 b9 c9 a9 b9 c9 " ] || fail "recovery contents: $(contents)"

# Back to the old inputs after a failure: the generator runs and rewrites.
tick
printf 'a9\nb9\nc9\n' > in.txt; echo fail > mode
"$mise" build . >/dev/null 2>&1 && fail "second failure: build succeeded"
echo ok > mode
[ "$(ran)" = "GEN " ] || fail "after failure, same contents: ran more than GEN"
no_old "end"

# `restat-cmp = false` emits the command as written.
awk '{ print } /^restat = true$/ { print "restat-cmp = false" }' mise.toml > mise.toml.new
mv mise.toml.new mise.toml
[ "$("$mise" gen --commands . | head -1)" = "sh gen.sh in.txt mode out/a.txt out/b.txt 'out/c d.txt'" ] ||
  fail "restat-cmp = false still wraps"
echo "restat-cmp: cutoff, propagation, failure, missing output and recovery all pass"
