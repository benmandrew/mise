import Lean.Data.Json
import Mise.Model.Dsl
import Mise.Frontend.Toml
import MiseTest.Rng

/-!
# Random-graph harness: case generator

`lake exe fuzzgen DIR N SEED` writes `N` random cases to `DIR/<i>.json`, and
`test/fuzz.py` replays them against real Ninja.

A case is a random valid graph and a sequence of steps. Every edge runs the
helper `test/fz.c`, and `sem` below computes the same contents and reads, so
the model predicts what real Ninja must do. Each step lists the files to
write (sources and `mise.toml`), the `build.ninja` that `mise gen` must
produce, the edges the model's `buildTrace` runs, and every product's
contents afterwards.

Depfile commands read only their own private main source, shared headers,
their declared inputs, and generated files named as order-only inputs. That
keeps `Graph.DynOK`, so the model's theorems apply, and no include names a
missing file, where the model and Ninja differ.
-/

namespace MiseTest.Fuzz
open Mise Mise.Syntax Mise.Frontend Mise.Model Lean

/-! ## What the helper computes -/

def fnvOffset : UInt64 := 14695981039346656037

/-- FNV-1a over the UTF-8 bytes of `s`. -/
def feed (h : UInt64) (s : String) : UInt64 :=
  s.toUTF8.data.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) h

def hex16 (h : UInt64) : String :=
  let d := Nat.toDigits 16 h.toNat
  String.ofList (List.replicate (16 - d.length) '0' ++ d)

/-- The command's arguments after the program name, as the shell splits them. -/
def args (cmd : String) : List String := ((cmd.splitOn " ").filter (· != "")).drop 1

def outsOf (cmd : String) : List String := ((args cmd).drop 2).takeWhile (· != "--")

def insOf (cmd : String) : List String := ((args cmd).dropWhile (· != "--")).drop 1

def lines (v : String) : List String := v.splitOn "\n"

/-- The contents the helper writes to each output, from the contents of the
files it read, in order. Lines starting with `#` do not count. -/
def fzContent (cmd : String) (vs : List String) : List String :=
  let key := feed fnvOffset (" ".intercalate (args cmd) ++ "\n")
  let file (h : UInt64) (v : String) : UInt64 :=
    feed ((lines v).foldl (fun h l => if l.startsWith "#" then h else feed (feed h l) "\n") h) "\x00"
  (List.range (outsOf cmd).length).map fun i => hex16 (vs.foldl file (feed key (toString i ++ "\n"))) ++ "\n"

def includes (v : String) : List Path :=
  (lines v).filterMap fun l =>
    if l.startsWith "include " && l.length > 8 then some (String.ofList (l.toList.drop 8)) else none

def dedup (ps : List Path) : List Path := ps.foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []

/-- Read `queue` breadth first, queueing every included path not yet seen. -/
def bfs : Nat → List Path → List Path → List String → Task Path String (List String)
  | 0, _, _, acc => .pure acc
  | _, _, [], acc => .pure acc
  | f + 1, seen, p :: q, acc => .fetch p fun v =>
    let (seen', new) := (includes v).foldl
      (fun (s, n) k => if s.contains k then (s, n) else (s ++ [k], n ++ [k])) (seen, [])
    bfs f seen' (q ++ new) (acc ++ [v])

def fzDyn (cmd : String) : Task Path String (List String) :=
  let ins := dedup (insOf cmd)
  (bfs 10000 ins ins []).bind fun vs => .pure (fzContent cmd vs)

/-- The helper as command semantics. A `restat` run leaves an output alone
when its contents would not change. -/
def sem : Sem String :=
  { exec := fzContent, dyn := fzDyn, keep := (· == ·), keep_eq := fun _ _ h => by simpa using h }

/-! ## Random graphs -/

/-- `(name, mode, depfile, restat)`; the mode tells the helper what to do. -/
def ruleSpecs : List (String × String × Bool × Bool) :=
  [("st", "s", false, false), ("str", "sr", false, true), ("dy", "d", true, false), ("dyr", "dr", true, true)]

def ruleCmd (mode : String) : String := "./fz " ++ mode ++ " ${tag} $out ${iout} -- $in ${imp}"

def rules : List GRule :=
  ruleSpecs.map fun (name, mode, depfile, restat) =>
    { name, command := (readValue (ruleCmd mode).toList).getD [], depfile, restat }

structure Src where
  path : Path
  version : Nat := 0
  includes : List Path := []
  comments : Nat := 0
  /-- What this source may include. -/
  allowed : List Path := []
  deriving Inhabited

def Src.text (s : Src) : String :=
  s!"{s.path} v{s.version}\n" ++ String.join (s.includes.map fun p => s!"include {p}\n") ++
    String.join ((List.range s.comments).map fun k => s!"# note {k}\n")

structure Case where
  srcs : List Src
  edges : List GEdge

def Case.graph (c : Case) : Graph := { sources := c.srcs.map (·.path), rules, edges := c.edges }

/-- `k` distinct elements of `xs`, in random order. -/
def sample {α} [Inhabited α] (k : Nat) (xs : List α) : GenM (List α) := do
  let mut rest := xs
  let mut out := []
  for _ in [0:k] do
    if rest.isEmpty then break
    let i ← rand rest.length
    out := out ++ [rest[i]!]
    rest := rest.eraseIdx i
  pure out

def edgeVars (tag : String) (iouts imps : List Path) : List (String × String) :=
  [("tag", tag)] ++ (if iouts.isEmpty then [] else [("iout", " ".intercalate iouts)]) ++
    (if imps.isEmpty then [] else [("imp", " ".intercalate imps)])

def genCase : GenM Case := do
  let nh := 1 + (← rand 3)
  let np := 1 + (← rand 3)
  let ne := 2 + (← rand 9)
  let hs := (List.range nh).map fun k => s!"inc/h{k}.h"
  let mut headers : List Src := []
  for h in hs do
    let allowed := hs.filter (· != h)
    headers := headers ++ [{ path := h, allowed, includes := ← sample (← rand 2) allowed }]
  let plains : List Src := (List.range np).map fun k => { path := s!"src/p{k}.txt" }
  let mut mains : List Src := []
  let mut edges : List GEdge := []
  let mut gens : List Path := []
  for i in [0:ne] do
    let restat ← chance 1 2
    let fresh (xs : List Path) (avoid : List Path) := xs.filter fun x => !avoid.contains x
    if ← chance 2 5 then
      let main := s!"src/m{i}.c"
      let extra ← sample (← rand 2) gens
      let imp ← sample (← rand 2) (fresh (plains.map (·.path) ++ hs ++ gens) extra)
      let oo ← sample (← rand 3) (fresh gens (extra ++ imp))
      let allowed := hs ++ oo
      mains := mains ++ [{ path := main, allowed, includes := ← sample (← rand 3) allowed }]
      let out := s!"out/e{i}.o"
      edges := edges ++ [{ rule := if restat then "dyr" else "dy", outs := [out], ins := main :: extra,
                           implicitIns := imp, orderOnly := oo, vars := edgeVars "t0" [] imp }]
      gens := gens ++ [out]
    else
      let pool := plains.map (·.path) ++ hs ++ gens
      let ins ← sample (1 + (← rand 3)) pool
      let imp ← sample (← rand 2) (fresh pool ins)
      let oo ← sample (← rand 2) (fresh gens (ins ++ imp))
      let outs := (List.range (1 + (← rand 2))).map fun k => s!"out/e{i}_{k}"
      let iouts := if ← chance 1 3 then [s!"out/e{i}_i"] else []
      edges := edges ++ [{ rule := if restat then "str" else "st", outs, implicitOuts := iouts, ins,
                           implicitIns := imp, orderOnly := oo, vars := edgeVars "t0" iouts imp }]
      gens := gens ++ outs ++ iouts
  pure { srcs := plains ++ headers ++ mains, edges }

/-! ## Edits -/

inductive Edit where
  | bump (src : Nat)
  | comment (src : Nat)
  | addInc (src : Nat) (p : Path)
  | rmInc (src : Nat) (p : Path)
  | retag (edge : Nat)
  deriving Inhabited

def Case.describe (c : Case) : Edit → String
  | .bump i => s!"bump {c.srcs[i]!.path}"
  | .comment i => s!"comment {c.srcs[i]!.path}"
  | .addInc i p => s!"include {p} in {c.srcs[i]!.path}"
  | .rmInc i p => s!"drop include {p} from {c.srcs[i]!.path}"
  | .retag e => s!"retag {c.edges[e]!.outs.headD ""}"

def bumpTag (vs : List (String × String)) : List (String × String) :=
  vs.map fun (k, v) => if k == "tag" then (k, "t" ++ toString ((String.ofList (v.toList.drop 1)).toNat! + 1)) else (k, v)

def Case.apply (c : Case) : Edit → Case
  | .bump i => { c with srcs := c.srcs.modify i fun s => { s with version := s.version + 1 } }
  | .comment i => { c with srcs := c.srcs.modify i fun s => { s with comments := s.comments + 1 } }
  | .addInc i p => { c with srcs := c.srcs.modify i fun s => { s with includes := s.includes ++ [p] } }
  | .rmInc i p => { c with srcs := c.srcs.modify i fun s => { s with includes := s.includes.erase p } }
  | .retag e => { c with edges := c.edges.modify e fun g => { g with vars := bumpTag g.vars } }

/-- Every edit possible now, grouped by kind. -/
def Case.candidates (c : Case) : List (List Edit) :=
  let idx := List.range c.srcs.length
  let adds := idx.flatMap fun i =>
    let s := c.srcs[i]!
    (s.allowed.filter fun p => !s.includes.contains p).map (.addInc i)
  let rms := idx.flatMap fun i => c.srcs[i]!.includes.map (.rmInc i)
  [idx.map .bump, idx.map .comment, adds, rms, (List.range c.edges.length).map .retag].filter (!·.isEmpty)

def genEdit (c : Case) : GenM Edit := do pick (← pick c.candidates)

/-! ## TOML -/

def tstr (s : String) : String := "\"" ++ s ++ "\""
def tarr (xs : List String) : String := "[" ++ ", ".intercalate (xs.map tstr) ++ "]"

def tomlOf (g : Graph) : String := Id.run do
  let mut t := s!"sources = {tarr g.sources}\n"
  for (name, mode, depfile, restat) in ruleSpecs do
    t := t ++ s!"\n[[rule]]\nname = {tstr name}\ncommand = {tstr (ruleCmd mode)}\n"
    if depfile then t := t ++ "depfile = true\n"
    if restat then t := t ++ "restat = true\n"
  for e in g.edges do
    t := t ++ s!"\n[[build]]\nrule = {tstr e.rule}\nouts = {tarr e.outs}\n"
    for (k, v) in [("implicit-outs", e.implicitOuts), ("ins", e.ins), ("implicit-ins", e.implicitIns),
                   ("order-only", e.orderOnly)] do
      if !v.isEmpty then t := t ++ s!"{k} = {tarr v}\n"
    t := t ++ "vars = { " ++ ", ".intercalate (e.vars.map fun (k, v) => s!"{k} = {tstr v}") ++ " }\n"
  t

/-! ## Running the model -/

def products (g : Graph) : List Path := g.edges.flatMap (·.allOuts)

def jsonMap (kvs : List (String × String)) : Json := Json.mkObj (kvs.map fun (k, v) => (k, Json.str v))

def sortStrs (xs : List String) : List String := (xs.toArray.qsort (· < ·)).toList

/-- The same state as a table over `paths`. Model states are chains of
closures, and a lookup in one re-runs every command behind it, so the
generator flattens the state after each step. The flat state agrees with
the original on every path the case uses, which is all the model reads. -/
def flatten (paths : List Path) (st : St String) : St String :=
  let fs := paths.map fun p => (p, st.fs p)
  let log := paths.map fun p => (p, st.log p)
  let deps := paths.map fun p => (p, st.deps p)
  { fs := fun p => (fs.lookup p).bind id, log := fun p => (log.lookup p).bind id,
    deps := fun p => (deps.lookup p).bind id, clock := st.clock }

/-- One step: write the changed files, check the manifest, build, and record
what the model runs and the contents it leaves. -/
def step (edits : List String) (old : Option Case) (c : Case) (st : St String) :
    Except String (Json × St String) := do
  let g := c.graph
  unless g.check do throw "the graph is not valid"
  let toml := tomlOf g
  let ninja := print (emit g)
  match Toml.load toml with
  | .error e => throw s!"mise.toml does not load: {e}"
  | .ok vg => unless print (emit vg.1) == ninja do throw "mise.toml does not read back as the graph"
  let changed := c.srcs.filter fun s => match old with
    | some o => (o.srcs.find? (·.path == s.path)).map (·.text) != some s.text
    | none => true
  let tomlChanged := match old with
    | some o => tomlOf o.graph != toml
    | none => true
  let st := st.edits (changed.map fun s => (s.path, s.text))
  let es := (emit g).medges
  let (st', ran) := buildTrace sem es st
  let st' := flatten (g.sources ++ products g) st'
  unless (buildTrace sem es st').2.isEmpty do throw "the model is not idempotent"
  for e in es do
    if e.dyn then
      for o in e.outs do
        for k in (st'.deps o).getD [] do
          unless g.isSource k || e.reads.contains k do throw s!"{o} read {k}, which it may not"
  let write := changed.map (fun s => (s.path, s.text)) ++ (if tomlChanged then [("mise.toml", toml)] else [])
  let j := Json.mkObj [("edits", toJson edits), ("write", jsonMap write), ("ninja", Json.str ninja),
    ("ran", toJson (sortStrs (ran.map (·.outs.headD "")))),
    ("products", jsonMap ((products g).map fun p => (p, st'.content p)))]
  pure (j, st')

def empty : St String := { fs := fun _ => none, log := fun _ => none, clock := 0 }

def genSteps (c0 : Case) (n : Nat) : GenM (List (List Edit)) := do
  let mut c := c0
  let mut out := []
  for _ in [0:n] do
    let k ← if ← chance 1 10 then pure 0 else pure (1 + (← rand 3))
    let mut es := []
    for _ in [0:k] do
      let e ← genEdit c
      c := c.apply e
      es := es ++ [e]
    out := out ++ [es]
  pure out

def runCase (c0 : Case) (steps : List (List Edit)) : Except String Json := do
  let (j0, st0) ← step [] none c0 empty
  let mut st := st0
  let mut c := c0
  let mut js := #[j0]
  for es in steps do
    let mut c' := c
    let mut ds := []
    for e in es do
      ds := ds ++ [c'.describe e]
      c' := c'.apply e
    let (j, st') ← step ds (some c) c' st
    js := js.push j
    st := st'
    c := c'
  pure (Json.mkObj [("steps", Json.arr js)])

def seeded (seed i : Nat) : Rng := Id.run do
  let mut g : Rng := ⟨(seed * 1000003 + i * 7919 + 1).toUInt64⟩
  for _ in [0:4] do g := g.next.2
  g

def genOne (seed i : Nat) : Case × List (List Edit) :=
  let gen : GenM (Case × List (List Edit)) := do
    let c ← genCase
    let n := 3 + (← rand 6)
    pure (c, ← genSteps c n)
  (gen.run (seeded seed i)).1

end MiseTest.Fuzz

open MiseTest.Fuzz in
def main (args : List String) : IO UInt32 := do
  let (dir, n, seed) := match args with
    | [d, n, s] => (d, n.toNat!, s.toNat!)
    | _ => ("test/out/fuzz/cases", 100, 1)
  IO.FS.createDirAll dir
  for i in [0:n] do
    let (c, steps) := genOne seed i
    match runCase c steps with
    | .error e => IO.eprintln s!"case {i}: {e}"; return 1
    | .ok j => IO.FS.writeFile s!"{dir}/{i}.json" j.compress
  return 0
