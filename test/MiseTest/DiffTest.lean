import MiseTest.DiffGen

/-!
# Stage 3 differential test

`lake exe difftest DIR N SEED` writes `N` random well-formed manifests to
`DIR/<i>/build.ninja`. Next to each it writes `targets` (one path per line)
and `expected`, the output `ninja -t query` should print for those targets
if real Ninja reads the manifest as the AST says. `test/stage3-diff.sh`
runs Ninja and compares. `lake exe difftest bytes FILE DIR` writes one
manifest generated from the bytes of `FILE` instead, as the parser fuzzer
does (`test/parser-fuzz.sh`).
-/

open MiseTest.DiffTest Mise.Syntax in
/-- Check a generated manifest and write it with its expected outputs. -/
def writeCase (what d : String) (m : Manifest) : IO Bool := do
  if !decide m.WellFormed then
    IO.eprintln s!"{what} is not well formed"; return false
  if parse (print m) != some m then
    IO.eprintln s!"{what} does not round-trip through the parser model"; return false
  IO.FS.createDirAll d
  IO.FS.writeFile s!"{d}/build.ninja" (print m)
  let ts := allPaths m
  IO.FS.writeFile s!"{d}/targets" (String.join (ts.map (· ++ "\n")))
  IO.FS.writeFile s!"{d}/expected" (String.join (ts.map (expectedQuery m)))
  let cs := commandTargets m
  IO.FS.writeFile s!"{d}/cmd-targets" (String.join (cs.map (·.1 ++ "\n")))
  IO.FS.writeFile s!"{d}/expected-commands" (String.join (cs.map (·.2 ++ "\n")))
  return true

open MiseTest.DiffTest Mise.Syntax in
def main (args : List String) : IO UInt32 := do
  if let ["negative", dir] := args then
    for (name, text) in negatives do
      if (parse text).isSome then
        IO.eprintln s!"negative case {name} is accepted by the parser model"; return 1
      IO.FS.createDirAll s!"{dir}/{name}"
      IO.FS.writeFile s!"{dir}/{name}/build.ninja" text
    return 0
  if let ["bytes", file, dir] := args then
    let m := genManifest.runBytes (← IO.FS.readBinFile file)
    return if ← writeCase s!"the manifest from {file}" dir m then 0 else 1
  let (dir, n, seed) := match args with
    | [d, n, s] => (d, n.toNat!, s.toNat!)
    | _ => ("test/out/stage3", 100, 1)
  let mut g : MiseTest.Rng := .ofSeed seed.toUInt64
  for i in [0:n] do
    let (m, g') := genManifest.run g
    g := g'
    unless ← writeCase s!"manifest {i}" s!"{dir}/{i}" m do return 1
  return 0
