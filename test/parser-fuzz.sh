#!/usr/bin/env bash
# Differential fuzzer for Ninja's manifest parser against the Lean parser
# model, with libFuzzer: test/parser_fuzz.cc links Ninja's parser from the
# flake's pinned source and the Lean model (test/MiseTest/ParseFuzz.lean)
# into one process, both instrumented for coverage. See "Parser fuzzer" in
# docs/testing.md.
#
# Usage: test/parser-fuzz.sh [text|gen] [SECONDS] [-- LIBFUZZER_ARGS...]
#        test/parser-fuzz.sh repro text|gen FILE...
# NINJA_RELEASE picks the Ninja release (default 1.13.2; any key of
# ninjaReleases in flake.nix from 1.12.1 on). It needs clang with libFuzzer
# (CC and CXX override clang and clang++): on Linux run it in
# `nix develop .#fuzz`, whose clang has it; macOS's default shell does too.
set -euo pipefail
cd "$(dirname "$0")/.."
root=$PWD
release=${NINJA_RELEASE:-1.13.2}

repro=0
if [ "${1:-}" = repro ]; then repro=1; shift; fi
mode=${1:-text}
case "$mode" in text|gen) ;; *) echo "usage: $0 [repro] text|gen ..." >&2; exit 2 ;; esac
shift || true

# --- build
lake build MiseTest.ParseFuzz difftest >/dev/null
base=test/out/parser-fuzz
ninja_src=$(nix build --no-link --print-out-paths ".#ninja-${release//./_}.src")
# The Lean modules the harness needs: the import closure of
# MiseTest.ParseFuzz within this package.
lean_mods=$(python3 - <<'EOF'
import re, pathlib
todo, seen = ["MiseTest.ParseFuzz"], []
while todo:
    m = todo.pop()
    if m in seen: continue
    seen.append(m)
    top = m.split(".")[0]
    src = pathlib.Path("test" if top == "MiseTest" else ".") / (m.replace(".", "/") + ".lean")
    for line in src.read_text().splitlines():
        r = re.match(r"import\s+(\S+)", line)
        if r and r.group(1).split(".")[0] in ("Mise", "MiseTest"):
            todo.append(r.group(1))
print(" ".join(sorted(seen)))
EOF
)
# AddressSanitizer is on by default except on macOS, where clang 21's ASan
# deadlocks while it starts (in dyld_shared_cache_iterate_text_swift).
# MISE_FUZZ_ASAN=1 or 0 overrides.
asan=${MISE_FUZZ_ASAN:-$([ "$(uname)" = Darwin ] && echo 0 || echo 1)}
if [ "$asan" = 1 ]; then san="-fsanitize=fuzzer-no-link,address" link_san="-fsanitize=fuzzer,address"
else san="-fsanitize=fuzzer-no-link" link_san="-fsanitize=fuzzer"; fi
out=$base/build$([ "$asan" = 1 ] && echo -asan || true)
mkdir -p "$out"
{
  echo "ninja_required_version = 1.10"
  echo "cxxflags = -std=c++17 -O1 -g $san -fno-omit-frame-pointer -I$ninja_src/src $(leanc --print-cflags)"
  echo "cflags = $(leanc --print-cflags) -O1 -g $san"
  # Only the runtime and Init: libleancpp and libLean define the Lean
  # compiler's own `main`, which would take the place of libFuzzer's.
  echo "ldflags = $(leanc --print-ldflags | sed -E 's/ -l(leancpp|Lean|Lake|LeanExport|Std)( |$)/ /g; s/ -l(leancpp|Lean|Lake|LeanExport|Std)( |$)/ /g')"
  echo "rule cxx"
  echo "  command = ${CXX:-clang++} \$cxxflags -MMD -MF \$out.d -c \$in -o \$out"
  echo "  depfile = \$out.d"
  echo "  deps = gcc"
  echo "  description = CXX \$out"
  echo "rule cc"
  echo "  command = ${CC:-clang} \$cflags -c \$in -o \$out"
  echo "  description = CC \$out"
  echo "rule link"
  echo "  command = ${CXX:-clang++} $link_san \$in -o \$out \$ldflags"
  echo "  description = LINK \$out"
  objs=()
  for f in "$ninja_src"/src/*.cc; do
    b=$(basename "$f" .cc)
    case "$b" in
      *_test|*_perftest|*-win32|*.in|ninja|browse|hash_collision_bench|test) continue ;;
    esac
    echo "build ninja-$release/$b.o: cxx $f"
    objs+=("ninja-$release/$b.o")
  done
  for m in $lean_mods; do
    echo "build lean/$m.o: cc $root/.lake/build/ir/${m//.//}.c"
    objs+=("lean/$m.o")
  done
  echo "build harness-$release.o: cxx $root/test/parser_fuzz.cc"
  echo "build parser-fuzz-$release: link harness-$release.o ${objs[*]}"
  echo "default parser-fuzz-$release"
} > "$out/build.ninja"
ninja -C "$out" > "$out/build.log" || { grep -v "^\[" "$out/build.log"; exit 1; }
bin=$out/parser-fuzz-$release
out=$base
export MISE_FUZZ_MODE=$mode ASAN_OPTIONS=detect_leaks=0

if [ "$repro" = 1 ]; then
  exec "$bin" "$@"
fi

# --- run
secs=${1:-60}
shift || true
[ "${1:-}" = -- ] && shift
corpus=$out/corpus-$mode
mkdir -p "$corpus" "$out/crash"
seeds=()
if [ "$mode" = text ]; then
  # Seeds: generated manifests the model accepts, and the negative cases.
  rm -rf "$out/seeds"
  lake exe difftest "$out/seeds/gen" 200 1
  lake exe difftest negative "$out/seeds/neg"
  mkdir -p "$out/seeds/flat"
  for f in "$out"/seeds/gen/*/build.ninja "$out"/seeds/neg/*/build.ninja; do
    cp "$f" "$out/seeds/flat/$(basename "$(dirname "$f")")-$(basename "$(dirname "$(dirname "$f")")")"
  done
  seeds=("$out/seeds/flat")
fi
set +e
"$bin" -dict=test/parser-fuzz.dict -max_len=4096 -max_total_time="$secs" -print_final_stats=1 \
  -artifact_prefix="$out/crash/$mode-" "$@" "$corpus" "${seeds[@]}" 2>&1 |
  grep -v '^#[0-9]*[[:space:]]*\(NEW\|REDUCE\|pulse\)'
status=${PIPESTATUS[0]}
set -e
if [ "$status" -ne 0 ]; then
  echo "parser-fuzz $mode: FAIL; inputs in $out/crash, replay with $0 repro $mode FILE" >&2
  exit 1
fi
echo "parser-fuzz $mode: no difference from Ninja $release in ${secs}s; corpus $(ls "$corpus" | wc -l | tr -d ' ') inputs"
