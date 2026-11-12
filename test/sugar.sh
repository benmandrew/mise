#!/usr/bin/env bash
# The TOML conveniences against real Ninja: `source-globs`, `foreach`, `%`
# inputs, builds out of order, and aliases. Builds a small C program whose
# sources a glob finds, checks that an alias builds its targets and nothing
# else, that a new source file is compiled and linked by the next
# `mise build`, and that Ninja evaluates every command as the DSL means it.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build mise >/dev/null
mise=$PWD/.lake/build/bin/mise
d=test/out/sugar
rm -rf "$d"
mkdir -p "$d/src/sub" "$d/inc" "$d/src/.hidden"
cd "$d"
fail() { echo "FAIL: $*"; exit 1; }

printf '#define BASE 40\n' > inc/x.h
printf '#include "x.h"\nint a(void) { return BASE; }\n' > src/a.c
printf 'int b(void) { return 2; }\n' > src/sub/b.c
printf '#include <stdio.h>\nint a(void); int b(void);\nint main(void) { printf("%%d\\n", a() + b()); return 0; }\n' > src/main.c
printf 'not C\n' > src/.hidden/skip.c

# The link comes first and reads every object through a `%` input.
cat > mise.toml <<'EOF'
source-globs = ["src/**/*.c", "inc/*.h"]
defaults = ["all"]

[[build]]
rule = "link"
outs = ["build/app"]
ins = ["build/%.o"]

[[build]]
rule = "cc"
foreach = "src/%.c"
outs = ["build/%.o"]
ins = ["src/%.c"]

[[rule]]
name = "cc"
command = "cc -MMD -MF $out.d -Iinc -c $in -o $out"
description = "CC $out"
depfile = true

[[rule]]
name = "link"
command = "cc $in -o $out"
description = "LINK $out"

[aliases]
objs = ["build/a.o", "build/sub/b.o", "build/main.o"]
all = ["build/app", "objs"]
EOF

out=$("$mise" build)
[ "$(./build/app)" = 42 ] || fail "app printed $(./build/app)"
[ "$(grep -c '^\[.*\] CC ' <<<"$out")" = 3 ] || fail "first build: $out"
grep -q '^build objs: phony build/a.o build/sub/b.o build/main.o$' build.ninja || fail "no objs alias"
grep -q '^default all$' build.ninja || fail "no default alias"
[ "$("$mise" build)" = "ninja: no work to do." ] || fail "second build has work"
[ "$("$mise" build -- objs)" = "ninja: no work to do." ] || fail "objs has work"

# An alias builds its targets and nothing more.
rm build/a.o
out=$("$mise" build -- objs)
grep -q 'CC build/a.o' <<<"$out" || fail "objs did not rebuild a.o: $out"
grep -q LINK <<<"$out" && fail "objs linked: $out"
out=$("$mise" build)
grep -q 'LINK build/app' <<<"$out" || fail "all did not relink: $out"
grep -q CC <<<"$out" && fail "all recompiled: $out"

# A header edit found by the depfile rebuilds only its reader.
printf '#define BASE 50\n' > inc/x.h
out=$("$mise" build)
[ "$(grep -c CC <<<"$out")" = 1 ] && grep -q 'CC build/a.o' <<<"$out" || fail "header edit: $out"
[ "$(./build/app)" = 52 ] || fail "app printed $(./build/app) after the header edit"

# A new source is found by the glob, compiled and linked.
printf 'int c(void) { return 7; }\n' > src/sub/c.c
out=$("$mise" build)
grep -q 'CC build/sub/c.o' <<<"$out" || fail "new source not compiled: $out"
grep -q 'LINK build/app' <<<"$out" || fail "new source not linked: $out"
nm build/app | grep -q ' _\?c$' || fail "app has no symbol c"
[ "$("$mise" build)" = "ninja: no work to do." ] || fail "build after the new source has work"

# Removing it relinks without it.
rm src/sub/c.c
out=$("$mise" build)
grep -q 'LINK build/app' <<<"$out" || fail "removed source not unlinked: $out"
nm build/app | grep -q ' _\?c$' && fail "app still has symbol c"

"$mise" gen --commands . | sort > ../sugar-expected-commands
ninja -t commands all | sort > ../sugar-actual-commands
cmp -s ../sugar-expected-commands ../sugar-actual-commands ||
  { diff ../sugar-{expected,actual}-commands; fail "commands differ"; }
echo "sugar: globs, foreach, % inputs, any order and aliases agree with Ninja ($(wc -l < ../sugar-actual-commands | tr -d ' ') commands)"
