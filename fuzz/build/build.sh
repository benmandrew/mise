#!/usr/bin/env bash
# Build the in-process build fuzzer (see harness.cc).
#
#   fuzz/build/build.sh [libfuzzer|afl|standalone]
#
# libfuzzer (the default) links libFuzzer's driver; afl compiles with
# afl-clang-fast++ (AFL++, Linux only), whose driver calls the same entry
# point; standalone has a main of its own that replays input files or
# counts up seeds and prints the rate. Ninja's sources come from the
# flake's ninja-1_13_2 package, or from $NINJA_SRC; $MISE_FUZZ_CFLAGS adds
# compiler flags (say -fsanitize=address). Prints the path of the binary.
# Run from the repository root inside `nix develop`.
set -euo pipefail
mode=${1:-libfuzzer}
root=$(pwd)
out=$root/.lake/build/fuzz/$mode
mkdir -p "$out"
src=${NINJA_SRC:-$(nix build --no-link --print-out-paths .#ninja-1_13_2.src)}

case $mode in
  libfuzzer) CXX=${CXX:-clang++}; cov=-fsanitize=fuzzer-no-link; link=-fsanitize=fuzzer ;;
  afl) CXX=afl-clang-fast++; cov=-fsanitize=fuzzer-no-link; link=-fsanitize=fuzzer ;;
  standalone) CXX=${CXX:-c++}; cov=; link= ;;
  *) echo "unknown mode $mode" >&2; exit 2 ;;
esac
extra=${MISE_FUZZ_CFLAGS:-}

# The Lean side: the model, the case generator and MiseFuzz.lean. fuzzgen's
# link line names every object and library they need. MiseTest.Fuzz
# defines `main`, which would clash with the fuzzer's, so its C is compiled
# again with `main` renamed.
lake build fuzzgen MiseFuzz:static >/dev/null
ir=$root/.lake/build/ir
prefix=$(lean --print-prefix)
cc -c -O3 -DNDEBUG -DLEAN_EXPORTING -fvisibility=hidden -I"$prefix/include" -Dmain=mise_fuzzgen_main \
  "$ir/MiseTest/Fuzz.c" -o "$out/Fuzz.o"
lean_link=()
while IFS= read -r a; do
  case $a in
    */MiseTest/Fuzz.c.o.export) lean_link+=("$out/Fuzz.o" "$ir/MiseFuzz.c.o.export") ;;
    # These hold a `main` of their own, which the linker would otherwise
    # take over the fuzzer driver's; nothing here needs them.
    -lLake | -lLeanExport) ;;
    *) lean_link+=("$a") ;;
  esac
done < <(python3 -I -c 'import shlex, sys; print("\n".join(shlex.split(open(sys.argv[1]).read())))' \
           "$root/.lake/build/bin/fuzzgen.rsp")

# Ninja without its main and its tests, with coverage instrumentation.
flags=(-O2 -g -DNDEBUG -std=c++17 -fno-exceptions -Wno-deprecated $cov $extra)
if [ "$(uname)" = Linux ]; then flags+=(-DUSE_PPOLL); fi
objs=()
for n in build build_log clean clparser debug_flags deps_log disk_interface dyndep dyndep_parser \
         edit_distance elide_middle eval_env graph graphviz jobserver json line_printer manifest_parser \
         metrics missing_deps parser real_command_runner state status_printer string_piece_util util \
         version jobserver-posix subprocess-posix depfile_parser lexer; do
  o=$out/ninja-$n.o
  objs+=("$o")
  if [ "$o" -nt "$src/src/$n.cc" ] && [ "$o" -nt "$0" ]; then continue; fi
  "$CXX" "${flags[@]}" -c "$src/src/$n.cc" -o "$o" &
done
wait

def=
if [ "$mode" = standalone ]; then def=-DMISE_FUZZ_STANDALONE; fi
"$CXX" "${flags[@]}" $def -I"$src/src" -I"$prefix/include" -c fuzz/build/harness.cc -o "$out/harness.o"
bin=$root/.lake/build/fuzz/mise-buildfuzz-$mode
"$CXX" $link $extra -o "$bin" "$out/harness.o" "${objs[@]}" "${lean_link[@]}"
echo "$bin"
