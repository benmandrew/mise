#!/usr/bin/env bash
# Run the shell harnesses against several Ninja releases and print a table.
# Each release is the flake package `ninja-X_Y_Z`, built from its upstream
# tag; it goes first on PATH, and the rest comes from the shell this runs in.
# Logs go to test/out/matrix/<release>/<harness>.log.
#
# Usage: test/ninja-matrix.sh [--workers W] [--fuzz N] [--seed S] [RELEASE...]
#        test/ninja-matrix.sh --refuse-only [RELEASE...]
#   --workers W  workers for the property and random-graph harnesses
#                (default: one per core)
#   --fuzz N     random-graph cases per release (default 500)
#   --seed S     seed for every harness (default 1)
#   --refuse-only  only check that each RELEASE (default: the unsupported
#                releases) refuses an emitted manifest with Ninja's version
#                error, and exit nonzero if one does not
# With no RELEASE, it runs the supported releases. First it checks that each
# unsupported release refuses an emitted manifest. An unsupported release can
# be named, and is known to fail; its harnesses then run through a `ninja`
# shim that lowers the manifest's `ninja_required_version` to that release.
set -euo pipefail
cd "$(dirname "$0")/.."

supported=(1.12.1 1.13.2)
unsupported=(1.10.2 1.11.1)
refuse_only=0
workers=$(getconf _NPROCESSORS_ONLN)
fuzz=500
seed=1
releases=()
while [ $# -gt 0 ]; do
  case "$1" in
    --workers) workers=$2; shift 2 ;;
    --fuzz) fuzz=$2; shift 2 ;;
    --seed) seed=$2; shift 2 ;;
    --refuse-only) refuse_only=1; shift ;;
    -h|--help) sed -n '2,19p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    -*) echo "unknown option $1" >&2; exit 2 ;;
    *) releases+=("$1"); shift ;;
  esac
done
refuse=("${unsupported[@]}")
if [ "$refuse_only" = 1 ]; then
  [ ${#releases[@]} -eq 0 ] || refuse=("${releases[@]}")
  releases=()
elif [ ${#releases[@]} -eq 0 ]; then
  releases=("${supported[@]}")
fi

command -v lake >/dev/null || { echo "run this in the Nix shell (nix develop)" >&2; exit 2; }
if [ "$refuse_only" = 1 ]; then
  lake build mise >/dev/null
else
  lake build mise fuzzgen difftest >/dev/null
fi

harnesses=(stage3 stage4 props fuzz)
run_harness() {
  case "$1" in
    stage3) test/stage3-diff.sh 100 "$seed" ;;
    stage4) test/stage4-hello.sh ;;
    props) test/stage6-props.sh --order 2 --seed "$seed" --workers "$workers" ;;
    fuzz) test/fuzz.sh "$fuzz" "$seed" -- --workers "$workers" ;;
  esac
}

# The bin directory of the flake's Ninja release $1.
ninja_bin() {
  local attr="ninja-${1//./_}" bin got
  bin=$(nix build --no-link --print-out-paths ".#$attr")/bin
  got=$(PATH="$bin:$PATH" ninja --version)
  [ "$got" = "$1" ] || { echo "$attr reports Ninja $got, not $1" >&2; exit 1; }
  echo "$bin"
}

out=test/out/matrix
mkdir -p "$out"
fail=0

# Every emitted manifest starts with `ninja_required_version = MIN`, and each
# release in `refuse` must refuse it with Ninja's version error.
d=$out/refuse
rm -rf "$d"
mkdir -p "$d"
# `mise gen` expands the source globs, so the sources come too.
cp examples/hello-c/mise.toml examples/hello-c/*.c examples/hello-c/*.h "$d/"
.lake/build/bin/mise gen "$d" >/dev/null
# The first line is the printer's comment; the binding is the first statement.
min=$(sed -n '2s/^ninja_required_version = //p' "$d/build.ninja")
[ -n "$min" ] || { echo "build.ninja does not start with ninja_required_version" >&2; exit 1; }
older() { [ "$1" != "$min" ] && [ "$(printf '%s\n' "$1" "$min" | sort -V | head -n 1)" = "$1" ]; }
for r in "${refuse[@]}"; do
  bin=$(ninja_bin "$r")
  log="$d/$r.log"
  # `-t targets` parses the manifest and needs none of the sources.
  if (cd "$d" && PATH="$bin:$PATH" ninja -t targets all) >"$log" 2>&1; then
    res="FAIL (accepted the manifest)"; fail=1
  elif grep -q "incompatible with build file ninja_required_version version ($min)" "$log"; then
    res=pass
  else
    res="FAIL (another error)"; fail=1
  fi
  echo "ninja $r refuses ninja_required_version = $min: $res ($log)"
done
[ "$refuse_only" = 0 ] || exit "$fail"

rows=()
for r in "${releases[@]}"; do
  bin=$(ninja_bin "$r")
  mkdir -p "$out/$r"
  if older "$r"; then
    # Ninja $r refuses every emitted manifest, so the shim gives it a copy of
    # build.ninja whose version binding names $r. A manifest named with `-f`
    # (the Stage 3 differential test writes its own) passes through unchanged.
    mkdir -p "$out/$r/shim"
    cat >"$out/$r/shim/ninja" <<EOF
#!/bin/sh
real='$bin/ninja'
dir=.
[ "\$1" = -C ] && dir=\$2
case " \$* " in *" -f "*) exec "\$real" "\$@" ;; esac
m=\$dir/build.ninja
[ "\$(sed -n 2p "\$m" 2>/dev/null)" = "ninja_required_version = $min" ] || exec "\$real" "\$@"
tmp=\$(mktemp) || exit 1
sed '2s/.*/ninja_required_version = $r/' "\$m" >"\$tmp"
"\$real" -f "\$tmp" "\$@"
s=\$?
rm -f "\$tmp"
exit \$s
EOF
    chmod +x "$out/$r/shim/ninja"
    bin="$PWD/$out/$r/shim:$bin"
    echo "ninja $r is older than $min, unsupported and known to fail: the harnesses run through $out/$r/shim/ninja"
  fi
  row=$(printf '%-8s' "$r")
  for h in "${harnesses[@]}"; do
    log="$out/$r/$h.log"
    start=$(date +%s)
    if PATH="$bin:$PATH" run_harness "$h" >"$log" 2>&1; then res=pass; else res=FAIL; fail=1; fi
    secs=$(( $(date +%s) - start ))
    echo "ninja $r $h: $res in ${secs}s ($log)"
    row+=$(printf ' | %-10s' "$res ${secs}s")
  done
  rows+=("$row")
done

echo
printf '%-8s' release
for h in "${harnesses[@]}"; do printf ' | %-10s' "$h"; done
echo
printf -- '-%.0s' $(seq 1 60); echo
for row in "${rows[@]}"; do echo "$row"; done
exit "$fail"
