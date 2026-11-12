#!/usr/bin/env bash
# mtime fault injection: break trust-base item 5 (docs/trust.md) on purpose
# and record what Ninja does. This is not a pass/fail test and is not part
# of scripts/check.sh; it prints one line per fault and writes the same
# table to test/out/mtime-faults/report.txt.
#
# The project is a small mise.toml: a.txt -> build/mid -> build/out (plain
# copies), a.txt -> build/kept -> build/after (the first a restat copy), and
# s.txt -> build/slow, a copy that reads at the start, sleeps and writes at
# the end. Every product must equal its source. After each fault the script
# runs `ninja`, then classifies the state:
#
#   ok        products correct and `ninja -n` has no work;
#   hidden    a product is stale and `ninja -n` has no work, so no later
#             build repairs it until the source changes again;
#   repaired  a product is stale after the build, but `ninja -n` has work
#             and one more build makes the products correct;
#   loop      products correct, but every build has work again.
#
# The coarse-mtime faults need a filesystem with one-second mtimes: on macOS
# the script makes and mounts an HFS+ disk image with hdiutil, elsewhere it
# skips them. The clock-skew fault with libfaketime needs `faketime` on the
# PATH; without it the script skips that fault.
#
# Usage: test/mtime-faults.sh
#   or, with libfaketime, inside the Nix shell:
#   nix shell --inputs-from . nixpkgs#libfaketime -c test/mtime-faults.sh
set -uo pipefail
cd "$(dirname "$0")/.."
lake build mise >/dev/null || exit 1
mise=$PWD/.lake/build/bin/mise
out=$PWD/test/out/mtime-faults
hfs=$out/hfs
mount | grep -qF " on $hfs " && hdiutil detach -quiet "$hfs"
rm -rf "$out"
mkdir -p "$out"
report=$out/report.txt
: >"$report"

cat >"$out/mise.toml" <<'EOF'
sources = ["a.txt", "s.txt"]

[[rule]]
name = "copy"
command = "cat $in > $out"

[[rule]]
name = "keep"
command = "cat $in > $out.tmp && if cmp -s $out.tmp $out; then rm $out.tmp; else mv $out.tmp $out; fi"
restat = true

[[rule]]
name = "slow"
command = "cat $in > $out.tmp && sleep 0.5 && mv $out.tmp $out"

[[build]]
rule = "copy"
outs = ["build/mid"]
ins = ["a.txt"]

[[build]]
rule = "copy"
outs = ["build/out"]
ins = ["build/mid"]

[[build]]
rule = "keep"
outs = ["build/kept"]
ins = ["a.txt"]

[[build]]
rule = "copy"
outs = ["build/after"]
ins = ["build/kept"]

[[build]]
rule = "slow"
outs = ["build/slow"]
ins = ["s.txt"]
EOF

# mk DIR: a fresh project in DIR, built from clean.
mk() {
  rm -rf "$1"
  mkdir -p "$1"
  cp "$out/mise.toml" "$1/"
  echo a0 >"$1/a.txt"
  echo s0 >"$1/s.txt"
  (cd "$1" && "$mise" gen . >/dev/null && ninja >/dev/null)
}

# stale DIR: the products that differ from their source, or nothing.
stale() {
  local a s p bad=""
  a=$(cat "$1/a.txt")
  s=$(cat "$1/s.txt")
  for p in mid out kept after; do
    [ "$(cat "$1/build/$p" 2>/dev/null)" = "$a" ] || bad="$bad build/$p"
  done
  [ "$(cat "$1/build/slow" 2>/dev/null)" = "$s" ] || bad="$bad build/slow"
  echo "${bad# }"
}

has_work() { ! (cd "$1" && ninja -n) | grep -q "no work to do"; }

# verdict NAME DIR NOTE: classify DIR after the fault's build and record it.
verdict() {
  local v s1 s2
  s1=$(stale "$2")
  if [ -z "$s1" ] && ! has_work "$2"; then
    v="ok"
  elif [ -n "$s1" ] && ! has_work "$2"; then
    v="hidden ($s1 stale)"
  else
    (cd "$2" && ninja >/dev/null)
    s2=$(stale "$2")
    if [ -n "$s1" ] && [ -z "$s2" ] && ! has_work "$2"; then
      v="repaired ($s1 stale after the build)"
    elif [ -z "$s2" ] && has_work "$2"; then
      v="loop"
    else
      v="other (stale after build: ${s1:-none}; after a second build: ${s2:-none})"
    fi
  fi
  printf '%-14s %s\n    %s\n' "$1" "$v" "$3" | tee -a "$report"
}

# logged_start DIR OUTPUT: the command start time Ninja logged for OUTPUT.
logged_start() { awk -v o="$2" '$4 == o { t = $3 } END { print t }' "$1/.ninja_log"; }

# at_ns FILE NS: set FILE's mtime to NS nanoseconds since the epoch.
at_ns() { touch -m -d "@${2:0:${#2}-9}.${2: -9}" "$1"; }

# Wait until 50 ms past the start of the next second.
next_second() { python3 -c 'import time; time.sleep(1.05 - time.time() % 1)'; }

# --- Control: a normal edit. ---
d=$out/control
mk "$d"
echo a1 >"$d/a.txt"
(cd "$d" && ninja >/dev/null)
verdict control "$d" "edit a.txt with a fresh mtime, then build"

# --- 1. An edit in the same mtime tick as the build. ---
# Ninja logs each command's start time, read from the mtime of .ninja_lock,
# and an output is dirty when an input is newer than that. An edit whose
# mtime equals the start time of a command that read the old contents is
# not newer.
d=$out/same-tick-sim
mk "$d"
echo a1 >"$d/a.txt"
at_ns "$d/a.txt" "$(logged_start "$d" build/mid)"
(cd "$d" && ninja >/dev/null)
verdict same-tick-sim "$d" "edit a.txt after the build, stamped with build/mid's logged start time (APFS, simulated tick)"

if command -v hdiutil >/dev/null &&
  hdiutil create -quiet -size 20m -fs HFS+ -volname mtime-faults "$out/hfs.dmg" &&
  mkdir -p "$hfs" && hdiutil attach -quiet -nobrowse -mountpoint "$hfs" "$out/hfs.dmg"; then
  trap 'hdiutil detach -quiet "$hfs"' EXIT

  d=$hfs/same-tick
  mk "$d"
  next_second
  echo a1 >"$d/a.txt"
  (cd "$d" && ninja >/dev/null)
  echo a2 >"$d/a.txt"
  verdict same-tick-hfs "$d" "on HFS+ (1 s mtimes): edit, build, edit again within the same second"

  d=$hfs/during
  mk "$d"
  # Each step in its own second, so that only the edit during the build
  # shares a tick with a command start.
  next_second
  echo s1 >"$d/s.txt"
  next_second
  (cd "$d" && ninja >/dev/null) &
  sleep 0.2
  echo s2 >"$d/s.txt"
  wait
  verdict during-hfs "$d" "on HFS+: edit s.txt while build/slow runs, in the second its command started"
else
  printf '%-14s skipped: no HFS+ image (hdiutil missing or failed)\n' same-tick-hfs | tee -a "$report"
  printf '%-14s skipped: no HFS+ image (hdiutil missing or failed)\n' during-hfs | tee -a "$report"
fi

# --- 2. A source mtime set backwards. ---
d=$out/backwards
mk "$d"
echo a1 >"$d/a.txt"
touch -m -t 200001010000 "$d/a.txt"
(cd "$d" && ninja >/dev/null)
verdict backwards "$d" "edit a.txt, then touch -t 200001010000 a.txt"

d=$out/restore
mk "$d"
cp -p "$d/a.txt" "$d/a.bak"
sleep 0.01
echo a1 >"$d/a.txt"
(cd "$d" && ninja >/dev/null)
cp -p "$d/a.bak" "$d/a.txt"
(cd "$d" && ninja >/dev/null)
verdict restore "$d" "edit a.txt and build, then restore the old a.txt with cp -p (its old mtime)"

# --- 3. A file edited while a build runs. ---
d=$out/during
mk "$d"
echo s1 >"$d/s.txt"
(cd "$d" && ninja >/dev/null) &
sleep 0.2
echo s2 >"$d/s.txt"
wait
verdict during "$d" "edit s.txt while build/slow runs, after it read s.txt (APFS)"

# --- 4. Clock skew. ---
# A source written through a clock that is ahead of, or behind, the clock
# that stamps the build directory (another host's clock with cp -p, tar or
# rsync -t, or a network filesystem whose server clock is skewed).
d=$out/skew-ahead
mk "$d"
echo a1 >"$d/a.txt"
touch -m -d '+1 hour' "$d/a.txt"
(cd "$d" && ninja >/dev/null)
verdict skew-ahead "$d" "edit a.txt and stamp it one hour ahead"

d=$out/skew-behind
mk "$d"
echo a1 >"$d/a.txt"
touch -m -d '-1 hour' "$d/a.txt"
(cd "$d" && ninja >/dev/null)
verdict skew-behind "$d" "edit a.txt and stamp it one hour behind"

d=$out/out-ahead
mk "$d"
touch -m -d '+1 hour' "$d/build/mid" "$d/build/kept"
echo a1 >"$d/a.txt"
(cd "$d" && ninja >/dev/null)
verdict out-ahead "$d" "stamp build/mid and build/kept one hour ahead, then edit a.txt"

if command -v faketime >/dev/null; then
  skew=$(($(faketime -f '+1h' date +%s) - $(date +%s)))
  d=$out/faketime
  mk "$d"
  echo a1 >"$d/a.txt"
  (cd "$d" && faketime -f '+1h' ninja >/dev/null)
  echo a2 >"$d/a.txt"
  (cd "$d" && faketime -f '-1h' ninja >/dev/null)
  verdict faketime "$d" "build under libfaketime +1h, edit, build under -1h (date under +1h is ${skew} s ahead)"
else
  printf '%-14s skipped: faketime not on the PATH (nix shell nixpkgs#libfaketime)\n' faketime | tee -a "$report"
fi
