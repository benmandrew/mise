#!/usr/bin/env bash
# Build a fuzzer that links Ninja's own code and the Lean model into one
# process, and print the path of the binary.
#
# Usage: fuzz/build.sh TARGET ENGINE
#   TARGET  parser  Ninja's manifest parser against the parser model
#                   (fuzz/parser/harness.cc, fuzz/MiseFuzz/Parser.lean)
#           build   Ninja's build logic against the build model, in memory
#                   (fuzz/build/harness.cc, fuzz/MiseFuzz/Build.lean)
#   ENGINE  libfuzzer   clang's libFuzzer, with coverage
#           afl         AFL++ through afl-clang-fast, with coverage (Linux)
#           standalone  fuzz/standalone.cc, without coverage
#
# Ninja's sources come from NINJA_SRC, or else from the flake's release
# NINJA_RELEASE (default 1.13.2). MISE_FUZZ_ASAN=1 or 0 turns
# AddressSanitizer on or off; it is on by default except on macOS, where
# clang 21's ASan deadlocks while it starts. MISE_FUZZ_CC and
# MISE_FUZZ_CXX override the compilers: clang and clang++, or afl-clang-fast
# and afl-clang-fast++ for afl. Plain CC and CXX are ignored, since the
# Linux dev shells set them to gcc, which has no libFuzzer. libFuzzer and AFL++ need clang from `nix develop .#fuzz` on Linux;
# macOS's default shell has libFuzzer too.
#
# The build goes to .lake/build/fuzz/TARGET-ENGINE[-asan], through a
# generated build.ninja.
set -euo pipefail
cd "$(dirname "$0")/.."
root=$PWD

usage() { echo "usage: $0 parser|build libfuzzer|afl|standalone" >&2; exit 2; }
[ $# -eq 2 ] || usage
target=$1 engine=$2
case "$target" in
  parser) module=MiseFuzz.Parser ;;
  build) module=MiseFuzz.Build ;;
  *) usage ;;
esac
case "$engine" in
  libfuzzer) cc=${MISE_FUZZ_CC:-clang} cxx=${MISE_FUZZ_CXX:-clang++} ;;
  afl) cc=${MISE_FUZZ_CC:-afl-clang-fast} cxx=${MISE_FUZZ_CXX:-afl-clang-fast++} ;;
  standalone) cc=${MISE_FUZZ_CC:-clang} cxx=${MISE_FUZZ_CXX:-clang++} ;;
  *) usage ;;
esac
asan=${MISE_FUZZ_ASAN:-$([ "$(uname)" = Darwin ] && echo 0 || echo 1)}
out=.lake/build/fuzz/$target-$engine$([ "$asan" = 1 ] && echo -asan || true)
mkdir -p "$out"

# --- the Lean side: its C, and the import closure within this package
if ! lake build "$module" > "$out/lake.log" 2>&1; then
  cat "$out/lake.log" >&2
  exit 1
fi
lean_mods=$(python3 -I - "$module" <<'EOF'
import re, sys, pathlib
dirs = {"Mise": ".", "MiseTest": "test", "MiseFuzz": "fuzz"}
todo, seen = [sys.argv[1]], set()
while todo:
    m = todo.pop()
    if m in seen:
        continue
    seen.add(m)
    src = pathlib.Path(dirs[m.split(".")[0]]) / (m.replace(".", "/") + ".lean")
    for line in src.read_text().splitlines():
        r = re.match(r"import\s+(\S+)", line)
        if r and r.group(1).split(".")[0] in dirs:
            todo.append(r.group(1))
print(" ".join(sorted(seen)))
EOF
)

if [ -n "${NINJA_SRC:-}" ]; then
  ninja_src=$NINJA_SRC
else
  release=${NINJA_RELEASE:-1.13.2}
  ninja_src=$(nix build --no-link --print-out-paths ".#ninja-${release//./_}.src")
fi

# --- flags
case "$engine" in
  libfuzzer) san=fuzzer-no-link link_san=fuzzer ;;
  # afl-clang-fast instruments by itself; at link time it reads
  # -fsanitize=fuzzer as "link AFL++'s libFuzzer driver".
  afl) san= link_san=fuzzer ;;
  standalone) san= link_san= ;;
esac
if [ "$asan" = 1 ]; then
  san=${san:+$san,}address link_san=${link_san:+$link_san,}address
fi
san=${san:+-fsanitize=$san} link_san=${link_san:+-fsanitize=$link_san}
lean_cflags=$(leanc --print-cflags)
ninja_defs=$([ "$(uname)" = Linux ] && echo -DUSE_PPOLL || true)
# The Lean libraries the closure needs, in place of leanc's whole list.
# libLeanExport holds the Lean compiler's own `main`, which would take the
# place of the engine's, and libLake is not used. The build model's case
# generator writes JSON with Lean.Json, which is in libLean, and a module
# that imports Lean starts through `lean_initialize`, in libleancpp.
case "$target" in
  parser) lean_libs="-lInit -lleanrt" ;;
  build) lean_libs="-lleancpp -lInit -lStd -lLean -lleanrt" ;;
esac
ldflags=
for w in $(leanc --print-ldflags); do
  case "$w" in
    -lleancpp|-lInit|-lStd|-lLean|-lleanrt|-lLake|-lLeanExport) ;;
    -lc++) ldflags+=" $lean_libs -lc++" ;;
    *) ldflags+=" $w" ;;
  esac
done

{
  echo "ninja_required_version = 1.10"
  echo "common = -O2 -g -fno-omit-frame-pointer $san"
  echo "cxxflags = -std=c++17 \$common $ninja_defs -I$ninja_src/src $lean_cflags"
  echo "cflags = \$common $lean_cflags"
  echo "ldflags = $ldflags"
  echo "rule cxx"
  echo "  command = $cxx \$cxxflags -MMD -MF \$out.d -c \$in -o \$out"
  echo "  depfile = \$out.d"
  echo "  deps = gcc"
  echo "  description = CXX \$out"
  # A module whose source defines `main` gets a C `main`, which would take
  # the place of the engine's, so it is renamed in every module.
  echo "rule cc"
  echo "  command = $cc \$cflags -Dmain=\$main -c \$in -o \$out"
  echo "  description = CC \$out"
  echo "rule link"
  echo "  command = $cxx $link_san \$in -o \$out \$ldflags"
  echo "  description = LINK \$out"
  objs=()
  for f in "$ninja_src"/src/*.cc; do
    b=$(basename "$f" .cc)
    case "$b" in
      *_test|*_perftest|*-win32|*.in|ninja|browse|hash_collision_bench|test) continue ;;
    esac
    echo "build ninja/$b.o: cxx $f"
    objs+=("ninja/$b.o")
  done
  for m in $lean_mods; do
    echo "build lean/$m.o: cc $root/.lake/build/ir/${m//.//}.c"
    echo "  main = lean_main_${m//./_}"
    objs+=("lean/$m.o")
  done
  echo "build harness.o: cxx $root/fuzz/$target/harness.cc"
  objs+=(harness.o)
  if [ "$engine" = standalone ]; then
    echo "build standalone.o: cxx $root/fuzz/standalone.cc"
    objs+=(standalone.o)
  fi
  echo "build $target: link ${objs[*]}"
  echo "default $target"
} > "$out/build.ninja"
if ! ninja -C "$out" > "$out/build.log" 2>&1; then
  grep -v "^\[" "$out/build.log" >&2
  exit 1
fi
echo "$root/$out/$target"
