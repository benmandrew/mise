import Lean.Data.Json
import Mise.Model.Dsl
import Mise.Frontend.Toml
import MiseTest.Rng

/-!
# Random-graph harness: case generator

`lake exe fuzzgen DIR N SEED [OPTS]` writes `N` random cases to
`DIR/<i>.json`, and `test/fuzz.py` replays them against real Ninja. `OPTS`
is a comma-separated list of `Opts` flags; the only one is `absent`.
`lake exe fuzzgen expect IN OUT` reads a case description from `IN` and
writes its case to `OUT`.

A case is a random valid graph and a sequence of steps. Every edge runs the
helper `test/fz.c`, and `sem` below computes the same contents and reads, so
the model predicts what real Ninja must do. Each step lists the files to
write (sources and `mise.toml`), the `build.ninja` that `mise gen` must
produce, the edges the model's `buildTrace` runs, and every product's
contents afterwards.

Depfile commands read only their own private main source, shared headers,
their declared inputs, and generated files named as order-only inputs. That
keeps `Graph.DynOK`, so the model's theorems apply, and no include names a
missing file, where the model and Ninja differ. A depfile edge has one
explicit output and up to two implicit ones, so that Ninja keys its deps by
the first of several outputs.
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

/-- The command inside the DSL's `cmp` wrapper (`cmpWrap`), or the command
itself when it is not wrapped. The wrapper does not change what the helper
computes, only which outputs keep their old file. -/
def inner (cmd : String) : String :=
  match cmd.splitOn "; if ( " with
  | [_, rest] => (rest.splitOn " ); then ").headD rest
  | _ => cmd

/-- The command's arguments after the program name, as the shell splits them. -/
def args (cmd : String) : List String := (((inner cmd).splitOn " ").filter (· != "")).drop 1

def outsOf (cmd : String) : List String := ((args cmd).drop 2).takeWhile (· != "--")

def insOf (cmd : String) : List String := ((args cmd).dropWhile (· != "--")).drop 1

def lines (v : String) : List String := v.splitOn "\n"

/-- Whether a helper in mode `x` leaves out an output with hash `h`. -/
def absent (h : UInt64) : Bool := h % 3 == 0

/-- The contents the helper writes to each output, from the contents of the
files it read, in order. Lines starting with `#` do not count. In mode `x`
the helper leaves out some outputs; a missing file reads as empty, so the
model gives such an output the empty string. -/
def fzContent (cmd : String) (vs : List String) : List String :=
  let key := feed fnvOffset (" ".intercalate (args cmd) ++ "\n")
  let skip := ((args cmd).headD "").contains 'x'
  let file (h : UInt64) (v : String) : UInt64 :=
    feed ((lines v).foldl (fun h l => if l.startsWith "#" then h else feed (feed h l) "\n") h) "\x00"
  (List.range (outsOf cmd).length).map fun i =>
    let h := vs.foldl file (feed key (toString i ++ "\n"))
    if skip && absent h then "" else hex16 h ++ "\n"

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
when its contents would not change, whether the helper decides that (mode
`r`) or the `cmp` wrapper does, as `Sem.withCmp` says. -/
def sem : Sem String := Sem.withCmp { exec := fzContent, dyn := fzDyn }

/-! ## Random graphs -/

/-- `(name, mode, depfile, restat, wrapped)`; the mode tells the helper what
to do. A `restat` rule either has the helper keep unchanged outputs itself
(mode `r`, emitted with `restat-cmp = false`) or goes through the DSL's
`cmp` wrapper with a helper that always writes. The `x` rules leave out
some outputs, are never wrapped, and only `Opts.absent` uses them. -/
def ruleSpecs : List (String × String × Bool × Bool × Bool) :=
  [("st", "s", false, false, false), ("str", "sr", false, true, false), ("stw", "s", false, true, true),
   ("dy", "d", true, false, false), ("dyr", "dr", true, true, false), ("dyw", "d", true, true, true),
   ("stx", "srx", false, true, false), ("dyx", "drx", true, true, false)]

def ruleCmd (mode : String) : String := "./fz " ++ mode ++ " ${tag} $out ${iout} -- $in ${imp}"

def rules : List GRule :=
  ruleSpecs.map fun (name, mode, depfile, restat, wrapped) =>
    { name, command := (readValue (if wrapped then cmpWrap (ruleCmd mode) else ruleCmd mode).toList).getD [],
      depfile, restat }

def wrapped (rule : String) : Bool := ruleSpecs.any fun (n, _, _, _, w) => n == rule && w

/-- The edge as the DSL's `edge` makes it: a wrapped edge's implicit outputs
also go to the wrapper in `mise_iouts`. -/
def withIouts (e : GEdge) : GEdge :=
  if wrapped e.rule && !e.implicitOuts.isEmpty then
    { e with vars := e.vars ++ [(cmpOutsVar, shellList " " e.implicitOuts)] }
  else e

structure Src where
  path : Path
  version : Nat := 0
  includes : List Path := []
  comments : Nat := 0
  /-- What this source may include. -/
  allowed : List Path := []
  deriving Inhabited, ToJson, FromJson

def Src.text (s : Src) : String :=
  s!"{s.path} v{s.version}\n" ++ String.join (s.includes.map fun p => s!"include {p}\n") ++
    String.join ((List.range s.comments).map fun k => s!"# note {k}\n")

structure Case where
  srcs : List Src
  edges : List GEdge

def Case.graph (c : Case) : Graph := { sources := c.srcs.map (·.path), rules, edges := c.edges.map withIouts }

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

/-- Generator options. `absent` gives half the `restat` edges a command that
leaves out some outputs (`test/fz.c`, mode `x`), which the model cannot
express; see "Where the model differs from Ninja" in `Mise/Model/NOTES.md`. -/
structure Opts where
  absent : Bool := false

def Opts.parse (s : String) : Opts := { absent := (s.splitOn ",").contains "absent" }

def genCase (o : Opts) : GenM Case := do
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
    let skip ← if o.absent && restat then chance 1 2 else pure false
    let fresh (xs : List Path) (avoid : List Path) := xs.filter fun x => !avoid.contains x
    if ← chance 2 5 then
      let main := s!"src/m{i}.c"
      let extra ← sample (← rand 2) gens
      let imp ← sample (← rand 2) (fresh (plains.map (·.path) ++ hs ++ gens) extra)
      let oo ← sample (← rand 3) (fresh gens (extra ++ imp))
      let allowed := hs ++ oo
      mains := mains ++ [{ path := main, allowed, includes := ← sample (← rand 3) allowed }]
      -- One explicit output, as `Graph.check` demands of depfile edges.
      let outs := [s!"out/e{i}.o"]
      let iouts := (List.range (← rand 3)).map fun k => s!"out/e{i}_i{k}"
      edges := edges ++ [{ rule := if skip then "dyx" else if restat then (if i % 2 == 0 then "dyw" else "dyr")
                                   else "dy",
                           outs, implicitOuts := iouts, ins := main :: extra, implicitIns := imp, orderOnly := oo,
                           vars := edgeVars "t0" iouts imp }]
      gens := gens ++ outs ++ iouts
    else
      let pool := plains.map (·.path) ++ hs ++ gens
      let ins ← sample (1 + (← rand 3)) pool
      let imp ← sample (← rand 2) (fresh pool ins)
      let oo ← sample (← rand 2) (fresh gens (ins ++ imp))
      let outs := (List.range (1 + (← rand 2))).map fun k => s!"out/e{i}_{k}"
      let iouts := if ← chance 1 3 then [s!"out/e{i}_i"] else []
      edges := edges ++ [{ rule := if skip then "stx" else if restat then (if i % 2 == 0 then "stw" else "str")
                                   else "st",
                           outs, implicitOuts := iouts, ins,
                           implicitIns := imp, orderOnly := oo, vars := edgeVars "t0" iouts imp }]
      gens := gens ++ outs ++ iouts
  pure { srcs := plains ++ headers ++ mains, edges }

/-! ## Edits -/

/-- An edit names its source by path and its edge by first output, so it
still means the same after the shrinker drops other edits or edges. An edit
whose source or edge is gone does nothing. -/
inductive Edit where
  | bump (src : Path)
  | comment (src : Path)
  | addInc (src : Path) (p : Path)
  | rmInc (src : Path) (p : Path)
  | retag (out : Path)
  deriving Inhabited, ToJson, FromJson

def Edit.describe : Edit → String
  | .bump s => s!"bump {s}"
  | .comment s => s!"comment {s}"
  | .addInc s p => s!"include {p} in {s}"
  | .rmInc s p => s!"drop include {p} from {s}"
  | .retag o => s!"retag {o}"

def bumpTag (vs : List (String × String)) : List (String × String) :=
  vs.map fun (k, v) => if k == "tag" then (k, "t" ++ toString ((String.ofList (v.toList.drop 1)).toNat! + 1)) else (k, v)

def Case.modSrc (c : Case) (p : Path) (f : Src → Src) : Case :=
  { c with srcs := c.srcs.map fun s => if s.path == p then f s else s }

def Case.apply (c : Case) : Edit → Case
  | .bump p => c.modSrc p fun s => { s with version := s.version + 1 }
  | .comment p => c.modSrc p fun s => { s with comments := s.comments + 1 }
  | .addInc p q => c.modSrc p fun s => { s with includes := s.includes ++ [q] }
  | .rmInc p q => c.modSrc p fun s => { s with includes := s.includes.erase q }
  | .retag o => { c with edges := c.edges.map fun g => if g.outs.headD "" == o then { g with vars := bumpTag g.vars } else g }

/-- Every edit possible now, grouped by kind. -/
def Case.candidates (c : Case) : List (List Edit) :=
  let ps := c.srcs.map (·.path)
  let adds := c.srcs.flatMap fun s => (s.allowed.filter fun p => !s.includes.contains p).map (.addInc s.path)
  let rms := c.srcs.flatMap fun s => s.includes.map (.rmInc s.path)
  [ps.map .bump, ps.map .comment, adds, rms, c.edges.map fun e => .retag (e.outs.headD "")].filter (!·.isEmpty)

def genEdit (c : Case) : GenM Edit := do pick (← pick c.candidates)

/-! ## TOML -/

def tstr (s : String) : String := "\"" ++ s ++ "\""
def tarr (xs : List String) : String := "[" ++ ", ".intercalate (xs.map tstr) ++ "]"

def tomlOf (g : Graph) : String := Id.run do
  let mut t := s!"sources = {tarr g.sources}\n"
  for (name, mode, depfile, restat, wrapped) in ruleSpecs do
    t := t ++ s!"\n[[rule]]\nname = {tstr name}\ncommand = {tstr (ruleCmd mode)}\n"
    if depfile then t := t ++ "depfile = true\n"
    if restat then t := t ++ "restat = true\n"
    if restat && !wrapped then t := t ++ "restat-cmp = false\n"
  for e in g.edges do
    t := t ++ s!"\n[[build]]\nrule = {tstr e.rule}\nouts = {tarr e.outs}\n"
    for (k, v) in [("implicit-outs", e.implicitOuts), ("ins", e.ins), ("implicit-ins", e.implicitIns),
                   ("order-only", e.orderOnly)] do
      if !v.isEmpty then t := t ++ s!"{k} = {tarr v}\n"
    let vars := e.vars.filter (·.1 != cmpOutsVar)
    t := t ++ "vars = { " ++ ", ".intercalate (vars.map fun (k, v) => s!"{k} = {tstr v}") ++ " }\n"
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

/-! ## Case descriptions

A description is a case before the model runs: the sources, the edges and
the edits. `fuzzgen` writes it into every case file, and `fuzzgen expect`
reads one back and recomputes the expectations, so `test/fuzz.py` can
shrink a failing case by editing its description. -/

/-- `GEdge` with JSON instances. -/
structure EdgeD where
  rule : String
  outs : List Path
  implicitOuts : List Path
  ins : List Path
  implicitIns : List Path
  orderOnly : List Path
  vars : List (String × String)
  deriving ToJson, FromJson

def EdgeD.ofEdge (e : GEdge) : EdgeD := ⟨e.rule, e.outs, e.implicitOuts, e.ins, e.implicitIns, e.orderOnly, e.vars⟩
def EdgeD.toEdge (e : EdgeD) : GEdge := ⟨e.rule, e.outs, e.implicitOuts, e.ins, e.implicitIns, e.orderOnly, e.vars⟩

structure Desc where
  srcs : List Src
  edges : List EdgeD
  steps : List (List Edit)
  deriving ToJson, FromJson

def runCase (c0 : Case) (steps : List (List Edit)) : Except String Json := do
  let (j0, st0) ← step [] none c0 empty
  let mut st := st0
  let mut c := c0
  let mut js := #[j0]
  for es in steps do
    let mut c' := c
    let mut ds := []
    for e in es do
      ds := ds ++ [e.describe]
      c' := c'.apply e
    let (j, st') ← step ds (some c) c' st
    js := js.push j
    st := st'
    c := c'
  let desc : Desc := ⟨c0.srcs, c0.edges.map .ofEdge, steps⟩
  pure (Json.mkObj [("desc", toJson desc), ("steps", Json.arr js)])

def seeded (seed i : Nat) : Rng := Id.run do
  let mut g : Rng := ⟨(seed * 1000003 + i * 7919 + 1).toUInt64⟩
  for _ in [0:4] do g := g.next.2
  g

def genOne (o : Opts) (seed i : Nat) : Case × List (List Edit) :=
  let gen : GenM (Case × List (List Edit)) := do
    let c ← genCase o
    let n := 3 + (← rand 6)
    pure (c, ← genSteps c n)
  (gen.run (seeded seed i)).1

end MiseTest.Fuzz

open MiseTest.Fuzz Lean in
def main (args : List String) : IO UInt32 := do
  if let ["expect", src, dst] := args then
    let d ← match Json.parse (← IO.FS.readFile src) >>= fromJson? (α := Desc) with
      | .ok d => pure d
      | .error e => IO.eprintln s!"{src}: {e}"; return 2
    match runCase ⟨d.srcs, d.edges.map (·.toEdge)⟩ d.steps with
    | .error e => IO.eprintln s!"{src}: {e}"; return 1
    | .ok j => IO.FS.writeFile dst j.compress; return 0
  let (dir, n, seed, o) := match args with
    | [d, n, s] => (d, n.toNat!, s.toNat!, ({} : Opts))
    | [d, n, s, f] => (d, n.toNat!, s.toNat!, Opts.parse f)
    | _ => ("test/out/fuzz/cases", 100, 1, ({} : Opts))
  IO.FS.createDirAll dir
  for i in [0:n] do
    let (c, steps) := genOne o seed i
    match runCase c steps with
    | .error e => IO.eprintln s!"case {i}: {e}"; return 1
    | .ok j => IO.FS.writeFile s!"{dir}/{i}.json" j.compress
  return 0
