import Mise.Syntax.Print
import Mise.Syntax.Parse

/-!
# Stage 3 differential test generator

`lake exe difftest DIR N SEED` writes `N` random well-formed manifests to
`DIR/<i>/build.ninja`. Next to each it writes `targets` (one path per line)
and `expected`, the output `ninja -t query` should print for those targets
if real Ninja reads the manifest as the AST says. `test/stage3-diff.sh`
runs Ninja and compares.
-/

namespace MiseTest.DiffTest
open Mise.Syntax

/-- A 64-bit linear congruential generator, so runs are reproducible. -/
structure Rng where
  state : UInt64

def Rng.next (g : Rng) : Nat × Rng :=
  let s := g.state * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat, ⟨s⟩)

abbrev GenM := StateM Rng

def rand (n : Nat) : GenM Nat := do
  let (x, g) := (← get).next
  set g
  pure (if n = 0 then 0 else x % n)

def pick {α} [Inhabited α] (xs : List α) : GenM α := do
  pure (xs[← rand xs.length]!)

def chance (num den : Nat) : GenM Bool := do pure ((← rand den) < num)

/-- Path components chosen to exercise escaping: spaces, `$`, `:`, unicode. -/
def components : List String :=
  ["a", "b", "src", "out.o", "x y", "d$e", "f:g", "ü", "日本", "sp ace$:", "$$", "c:", " lead", "trail "]

def genPath : GenM Path := do
  let n := (← rand 3) + 1
  let mut cs : List String := []
  for _ in [0:n] do
    cs := cs ++ [← pick components]
  pure (String.intercalate "/" cs)

/-- Fresh paths: distinct from everything in `avoid` and from each other. -/
def genFresh (k : Nat) (avoid : List Path) : GenM (List Path) := do
  let mut out : List Path := []
  let mut tries := 0
  while out.length < k && tries < 50 do
    tries := tries + 1
    let p ← genPath
    if !(avoid.contains p) && !(out.contains p) then out := out ++ [p]
  pure out

def identChars : List Char := "abcxyz_-.09".toList

def genIdent : GenM String := do
  let n := (← rand 6) + 1
  let mut cs : List Char := ['v']
  for _ in [0:n] do
    cs := cs ++ [← pick identChars]
  pure (String.ofList cs)

def litPieces : List String := ["cc", " ", "-o", "$", ":", "|", "ü", "  ", "#", "{", "}", "x=y"]

/-- A random value, normalised so no two literals are adjacent. -/
def genEval (vars : List String) : GenM EvalString := do
  let n ← rand 5
  let mut segs : EvalString := []
  for _ in [0:n] do
    if (← chance 1 3) && !vars.isEmpty then
      segs := segs ++ [.var (← pick vars)]
    else
      let s ← pick litPieces
      segs := match segs.getLast? with
        | some (.lit t) => segs.dropLast ++ [.lit (t ++ s)]
        | _ => segs ++ [.lit s]
  pure segs

def subset (xs : List Path) (maxN : Nat) : GenM (List Path) := do
  let mut out : List Path := []
  for x in xs do
    if out.length < maxN && (← chance 1 3) then out := out ++ [x]
  pure out

def genManifest : GenM Manifest := do
  let mut stmts : List Stmt := [.binding "ninja_required_version" [.lit "1.10"]]
  let mut topVars : List String := []
  for _ in [0:(← rand 3)] do
    let k ← genIdent
    stmts := stmts ++ [.binding k (← genEval topVars)]
    topVars := topVars ++ [k]
  -- rules
  let mut rules : List String := []
  for _ in [0:(← rand 3) + 1] do
    let name ← genIdent
    if rules.contains name then continue
    let vars := topVars ++ ["in", "out"]
    let mut cmd ← genEval vars
    if cmd.isEmpty then cmd := [.var "in"]
    let mut bs : List Binding := [("command", cmd)]
    if ← chance 1 2 then bs := bs ++ [("description", ← genEval vars)]
    if ← chance 1 3 then bs := bs ++ [("depfile", [.var "out", .lit ".d"]), ("deps", [.lit "gcc"])]
    if ← chance 1 4 then bs := bs ++ [("restat", [.lit "1"])]
    stmts := stmts ++ [.rule ⟨name, bs⟩]
    rules := rules ++ [name]
  -- edges
  let sources ← genFresh 6 []
  let mut known : List Path := []
  let mut outs : List Path := []
  for _ in [0:(← rand 8) + 1] do
    let rule ← if ← chance 1 5 then pure "phony" else pick rules
    let avail := sources ++ outs
    let ins ← subset avail 3
    let rest := avail.filter (!ins.contains ·)
    let iins ← subset rest 2
    let rest := rest.filter (!iins.contains ·)
    let oo ← subset rest 2
    let newOuts ← genFresh ((← rand 2) + 1) (sources ++ known ++ outs)
    if newOuts.isEmpty then continue
    let iouts ← genFresh (← rand 2) (sources ++ known ++ outs ++ newOuts)
    let mut ebs : List Binding := []
    if ← chance 1 3 then ebs := ebs ++ [(← genIdent, ← genEval topVars)]
    let e : Edge := { outs := newOuts, implicitOuts := iouts, rule, ins, implicitIns := iins,
                      orderOnly := oo, bindings := ebs }
    stmts := stmts ++ [.edge e]
    outs := outs ++ e.allOuts
    known := known ++ e.allPaths
  let defs ← subset known 3
  if !defs.isEmpty then stmts := stmts ++ [.default defs]
  pure ⟨stmts⟩

/-- What `ninja -t query t` prints, computed from the AST. -/
def expectedQuery (m : Manifest) (t : Path) : String := Id.run do
  let edges := m.stmts.filterMap fun | .edge e => some e | _ => none
  let mut out := t ++ ":\n"
  match edges.find? (·.allOuts.contains t) with
  | some e =>
    out := out ++ "  input: " ++ e.rule ++ "\n"
    for i in e.ins do out := out ++ "    " ++ i ++ "\n"
    for i in e.implicitIns do out := out ++ "    | " ++ i ++ "\n"
    for i in e.orderOnly do out := out ++ "    || " ++ i ++ "\n"
  | none => pure ()
  out := out ++ "  outputs:\n"
  -- Ninja records the edge once per occurrence of `t` among its inputs.
  for e in edges do
    for i in e.allIns do
      if i == t then
        for o in e.allOuts do out := out ++ "    " ++ o ++ "\n"
  pure out

def allPaths (m : Manifest) : List Path :=
  (m.stmts.flatMap fun | .edge e => e.allPaths | _ => []).foldl
    (fun acc p => if acc.contains p then acc else acc ++ [p]) []

/-- Manifests that both the parser model and real Ninja must reject. -/
def negatives : List (String × String) := [
  ("dup-output", "rule r\n  command = x\nbuild o: r\nbuild o: r\n"),
  ("dup-output-in-edge", "rule r\n  command = x\nbuild o o: r\n"),
  ("unknown-default", "rule r\n  command = x\nbuild o: r a\ndefault zz\n"),
  ("unknown-rule", "build o: r\n"),
  ("rule-before-def", "build o: r\nrule r\n  command = x\n"),
  ("no-command", "rule r\n  description = x\nbuild o: r\n"),
  ("empty-command", "rule r\n  command = x\n  command = \nbuild o: r\n"),
  ("unknown-rule-key", "rule r\n  command = x\n  foo = 1\nbuild o: r\n"),
  ("redefine-phony", "rule phony\n  command = x\n"),
  ("dup-rule", "rule r\n  command = x\nrule r\n  command = y\n"),
  ("keyword-binding", "build = 1\n"),
  ("indent-after-blank", "rule r\n  command = x\n\n  description = y\n"),
  ("indent-at-top", "  x = 1\n"),
  ("no-outputs", "rule r\n  command = x\nbuild : r\n"),
  ("bad-escape", "rule r\n  command = x\nbuild o$!: r\n"),
  ("missing-colon", "rule r\n  command = x\nbuild o r\n"),
  ("pipe-before-colon", "rule r\n  command = x\nbuild o ||: r\n")
]

end MiseTest.DiffTest

open MiseTest.DiffTest Mise.Syntax in
def main (args : List String) : IO UInt32 := do
  if let ["negative", dir] := args then
    for (name, text) in negatives do
      if (parse text).isSome then
        IO.eprintln s!"negative case {name} is accepted by the parser model"; return 1
      IO.FS.createDirAll s!"{dir}/{name}"
      IO.FS.writeFile s!"{dir}/{name}/build.ninja" text
    return 0
  let (dir, n, seed) := match args with
    | [d, n, s] => (d, n.toNat!, s.toNat!)
    | _ => ("test/out/stage3", 100, 1)
  let mut g : Rng := ⟨seed.toUInt64⟩
  for i in [0:n] do
    let (m, g') := genManifest.run g
    g := g'
    if !decide m.WellFormed then
      IO.eprintln s!"manifest {i} is not well formed"; return 1
    if parse (print m) != some m then
      IO.eprintln s!"manifest {i} does not round-trip through the parser model"; return 1
    let d := s!"{dir}/{i}"
    IO.FS.createDirAll d
    IO.FS.writeFile s!"{d}/build.ninja" (print m)
    let ts := allPaths m
    IO.FS.writeFile s!"{d}/targets" (String.join (ts.map (· ++ "\n")))
    IO.FS.writeFile s!"{d}/expected" (String.join (ts.map (expectedQuery m)))
  return 0
