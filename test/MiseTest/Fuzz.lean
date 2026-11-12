import Lean.Data.Json
import Mise.Model.Basic
import Mise.Frontend.Toml
import MiseTest.Rng

/-!
# Random-graph harness: case generator

`lake exe fuzzgen DIR N SEED [OPTS]` writes `N` random cases to
`DIR/<i>.json`, and `test/fuzz.py` replays them against real Ninja. `OPTS`
is a comma-separated list of `Opts` flags: `absent`, and `nowrap` with it.
`lake exe fuzzgen expect IN OUT` reads a case description from `IN` and
writes its case to `OUT`.

A case is a random valid graph and a sequence of steps. Every edge runs the
helper `test/fz.c`, and `sem` below computes the same contents and reads, so
the model predicts what real Ninja must do. Each step lists the files to
write (sources and `mise.toml`), to delete (products, `.ninja_log`,
`.ninja_deps`) and to age (products whose mtime goes back to the distant
past), the `build.ninja` that `mise gen` must produce, how to
build (every edge, some targets or aliases, or with one edge failing), the edges the
model runs, and the contents of every output the case has had afterwards.

Edits that touch a source, delete both logs, or build some targets or with
a failure stay within `Reach`. Deleting one log keeps `Inv`, since every
edge that used it becomes dirty, and so does removing an edge that nothing
reads, though no theorem states either. Deleting a product or adding an
edge goes outside what the theorems cover, so there the harness tests only
the model's dirtiness rule against Ninja.

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

/-- The command inside the DSL's wrapper (`wrapCommand`), or the command
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
`r`) or the wrapper's `cmp` does, as `Sem.withCmp` says. -/
def sem : Sem String := Sem.withCmp { exec := fzContent, dyn := fzDyn }

/-! ## Random graphs -/

/-- `(name, mode, depfile, restat, wrapped)`; the mode tells the helper what
to do. Rules without `restat` go through the DSL's wrapper. A `restat` rule
either has the helper keep unchanged outputs itself (mode `r`, emitted with
`wrap = false`) or goes through the wrapper, which compares with `cmp`, with
a helper that always writes. The `x` rules leave out some outputs, are never
wrapped, and only `Opts.absent` uses them: `stx` and `dyx` are unwrapped
`restat` rules whose helper also keeps unchanged outputs (for `nowrap`), and
`sx`, `sxr`, `dx` and `dxr` are wrapped, so that a run that leaves out an
output fails (see `natFail`). -/
def ruleSpecs : List (String × String × Bool × Bool × Bool) :=
  [("st", "s", false, false, true), ("str", "sr", false, true, false), ("stw", "s", false, true, true),
   ("dy", "d", true, false, true), ("dyr", "dr", true, true, false), ("dyw", "d", true, true, true),
   ("stx", "srx", false, true, false), ("dyx", "drx", true, true, false),
   ("sx", "sx", false, false, true), ("sxr", "sx", false, true, true),
   ("dx", "dx", true, false, true), ("dxr", "dx", true, true, true)]

def ruleCmd (mode : String) : String := "./fz " ++ mode ++ " ${tag} $out ${iout} -- $in ${imp}"

def rules : List GRule :=
  ruleSpecs.map fun (name, mode, depfile, restat, wrapped) =>
    { name, command := (readValue (if wrapped then wrapCommand restat (ruleCmd mode) else ruleCmd mode).toList).getD [],
      depfile, restat }

def wrapped (rule : String) : Bool := ruleSpecs.any fun (n, _, _, _, w) => n == rule && w

/-- The edge as the DSL's `edge` makes it: a wrapped edge's implicit outputs
also go to the wrapper in `mise_iouts`. -/
def withIouts (e : GEdge) : GEdge :=
  if wrapped e.rule && !e.implicitOuts.isEmpty then
    { e with vars := e.vars ++ [(wrapOutsVar, shellList " " e.implicitOuts)] }
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

structure Case where
  srcs : List Src
  edges : List GEdge
  /-- Edges removed by `rmEdge`, which `addEdge` may put back. -/
  removed : List GEdge := []
  /-- How many edges `addEdge` has made, which names the next one. -/
  fresh : Nat := 0

/-- Aliases derived from the edges, so that every edit keeps them valid:
`al-even` builds the first outputs of the even-numbered edges, and `al-odd`
those of the odd-numbered edges and the first source. An alias with no
targets is left out. -/
def aliasesOf (srcs : List Path) (es : List GEdge) : List GAlias :=
  let firsts := es.zipIdx.map fun (e, i) => (e.outs.headD "", i)
  let even := (firsts.filter (·.2 % 2 == 0)).map (·.1)
  let odd := (firsts.filter (·.2 % 2 == 1)).map (·.1) ++ srcs.take 1
  [({ name := "al-even", targets := even } : GAlias), { name := "al-odd", targets := odd }].filter
    (!·.targets.isEmpty)

def Case.graph (c : Case) : Graph :=
  { sources := c.srcs.map (·.path), rules, edges := c.edges.map withIouts,
    aliases := aliasesOf (c.srcs.map (·.path)) c.edges }

def products (g : Graph) : List Path := g.edges.flatMap (·.allOuts)

/-- What `ninja` may be asked to build: products and aliases. -/
def targetsOf (g : Graph) : List Path := products g ++ g.aliases.map (·.name)

/-- The paths a list of targets builds, with each alias replaced by its
targets. -/
def expandTargets (g : Graph) (ts : List Path) : List Path :=
  ts.flatMap fun t => match g.aliases.find? (·.name == t) with
    | some a => a.targets
    | none => [t]

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

def without (xs avoid : List Path) : List Path := xs.filter fun x => !avoid.contains x

/-- A static edge named `name` that reads from `pool`, with order-only
inputs from `gens`. -/
def genStatic (name : String) (rule : String) (pool gens : List Path) : GenM GEdge := do
  let ins ← sample (1 + (← rand 3)) pool
  let imp ← sample (← rand 2) (without pool ins)
  let oo ← sample (← rand 2) (without gens (ins ++ imp))
  let outs := (List.range (1 + (← rand 2))).map fun k => s!"out/{name}_{k}"
  let iouts := if ← chance 1 3 then [s!"out/{name}_i"] else []
  pure { rule, outs, implicitOuts := iouts, ins, implicitIns := imp, orderOnly := oo,
         vars := edgeVars "t0" iouts imp }

/-- Generator options. `absent` gives a quarter of the edges a command that
leaves out some outputs (`test/fz.c`, mode `x`) in the DSL's wrapper, which
turns such a run into a failure that changes no file (`natFail`). With
`nowrap` as well, half the `restat` edges get such a command outside the
wrapper instead, so outputs go missing, which the model cannot express; see
"Where the model differs from Ninja" in `Mise/Model/NOTES.md`. -/
structure Opts where
  absent : Bool := false
  nowrap : Bool := false

def Opts.parse (s : String) : Opts :=
  let fs := s.splitOn ","
  { absent := fs.contains "absent", nowrap := fs.contains "nowrap" }

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
    let skip ← if !o.absent then pure false else if o.nowrap then (if restat then chance 1 2 else pure false)
      else chance 1 4
    if ← chance 2 5 then
      let main := s!"src/m{i}.c"
      let extra ← sample (← rand 2) gens
      let imp ← sample (← rand 2) (without (plains.map (·.path) ++ hs ++ gens) extra)
      let oo ← sample (← rand 3) (without gens (extra ++ imp))
      let allowed := hs ++ oo
      mains := mains ++ [{ path := main, allowed, includes := ← sample (← rand 3) allowed }]
      -- One explicit output, as `Graph.check` demands of depfile edges.
      let outs := [s!"out/e{i}.o"]
      let iouts := (List.range (← rand 3)).map fun k => s!"out/e{i}_i{k}"
      edges := edges ++ [{ rule := if skip then (if o.nowrap then "dyx" else if restat then "dxr" else "dx") else if restat then (if i % 2 == 0 then "dyw" else "dyr")
                                   else "dy",
                           outs, implicitOuts := iouts, ins := main :: extra, implicitIns := imp, orderOnly := oo,
                           vars := edgeVars "t0" iouts imp }]
      gens := gens ++ outs ++ iouts
    else
      let rule := if skip then (if o.nowrap then "stx" else if restat then "sxr" else "sx") else if restat then (if i % 2 == 0 then "stw" else "str") else "st"
      let e ← genStatic s!"e{i}" rule (plains.map (·.path) ++ hs ++ gens) gens
      edges := edges ++ [e]
      gens := gens ++ e.allOuts
  pure { srcs := plains ++ headers ++ mains, edges }

/-! ## Edits -/

/-- An edit names its source by path and its edge by first output, so it
still means the same after the shrinker drops other edits or edges. An edit
whose source or edge is gone, or that would make the graph invalid, does
nothing. -/
inductive Edit where
  | bump (src : Path)
  | comment (src : Path)
  | addInc (src : Path) (p : Path)
  | rmInc (src : Path) (p : Path)
  | retag (out : Path)
  /-- Write a source again with the same contents, so only its mtime changes. -/
  | touch (src : Path)
  /-- Delete a product. -/
  | delOut (out : Path)
  /-- Delete `.ninja_log`. -/
  | delLog
  /-- Delete `.ninja_deps`. -/
  | delDeps
  /-- Remove the edge with this first output, when no edge reads its outputs.
  The outputs stay on disk. -/
  | rmEdge (out : Path)
  /-- Append an edge, when its inputs exist and its outputs are new. -/
  | addEdge (e : EdgeD)
  /-- Set a product's mtime to the distant past, as restoring it from a
  backup would. The case does not change, only the state. -/
  | age (out : Path)
  deriving Inhabited, ToJson, FromJson

def Edit.describe : Edit → String
  | .bump s => s!"bump {s}"
  | .comment s => s!"comment {s}"
  | .addInc s p => s!"include {p} in {s}"
  | .rmInc s p => s!"drop include {p} from {s}"
  | .retag o => s!"retag {o}"
  | .touch s => s!"touch {s}"
  | .delOut o => s!"delete {o}"
  | .delLog => "delete .ninja_log"
  | .delDeps => "delete .ninja_deps"
  | .rmEdge o => s!"remove edge {o}"
  | .addEdge e => s!"add edge {e.outs.headD ""}"
  | .age o => s!"age {o}"

def bumpTag (vs : List (String × String)) : List (String × String) :=
  vs.map fun (k, v) => if k == "tag" then (k, "t" ++ toString ((String.ofList (v.toList.drop 1)).toNat! + 1)) else (k, v)

def Case.modSrc (c : Case) (p : Path) (f : Src → Src) : Case :=
  { c with srcs := c.srcs.map fun s => if s.path == p then f s else s }

/-- Whether another edge reads one of the edge's outputs. -/
def Case.read (c : Case) (e : GEdge) : Bool :=
  c.edges.any fun g => g != e && g.allIns.any e.allOuts.contains

/-- Whether `e` can be appended: its inputs exist and its outputs are new. -/
def Case.canAdd (c : Case) (e : GEdge) : Bool :=
  let used := c.srcs.map (·.path) ++ products c.graph
  e.allIns.all used.contains && e.allOuts.all (!used.contains ·)

def Case.apply (c : Case) : Edit → Case
  | .bump p => c.modSrc p fun s => { s with version := s.version + 1 }
  | .comment p => c.modSrc p fun s => { s with comments := s.comments + 1 }
  | .addInc p q => c.modSrc p fun s => { s with includes := s.includes ++ [q] }
  | .rmInc p q => c.modSrc p fun s => { s with includes := s.includes.erase q }
  | .retag o => { c with edges := c.edges.map fun g => if g.outs.headD "" == o then { g with vars := bumpTag g.vars } else g }
  | .touch _ | .delOut _ | .delLog | .delDeps | .age _ => c
  | .rmEdge o => match c.edges.find? (·.outs.headD "" == o) with
    | some e => if c.read e then c else { c with edges := c.edges.erase e, removed := c.removed ++ [e] }
    | none => c
  | .addEdge d =>
    let e := d.toEdge
    if c.canAdd e then { c with edges := c.edges ++ [e], removed := c.removed.erase e, fresh := c.fresh + 1 } else c

/-- Every edit possible now, grouped by kind, except new edges. -/
def Case.candidates (c : Case) : List (List Edit) :=
  let ps := c.srcs.map (·.path)
  let adds := c.srcs.flatMap fun s => (s.allowed.filter fun p => !s.includes.contains p).map (.addInc s.path)
  let rms := c.srcs.flatMap fun s => s.includes.map (.rmInc s.path)
  let firsts := c.edges.map (·.outs.headD "")
  [ps.map .bump, ps.map .comment, adds, rms, firsts.map .retag, ps.map .touch,
   (products c.graph).map .delOut, [.delLog, .delDeps],
   ((c.edges.filter fun e => !c.read e).map (·.outs.headD "")).map .rmEdge,
   ((c.removed.filter c.canAdd).map EdgeD.ofEdge).map .addEdge, (products c.graph).map .age].filter (!·.isEmpty)

/-- A new static edge reading sources and products. -/
def genAdd (c : Case) : GenM Edit := do
  let gens := products c.graph
  let pool := ((c.srcs.filter fun s => !s.path.startsWith "src/m").map (·.path)) ++ gens
  let rule := if ← chance 1 2 then (if c.fresh % 2 == 0 then "stw" else "str") else "st"
  let e ← genStatic s!"a{c.fresh}" rule pool gens
  pure (.addEdge (.ofEdge e))

def genEdit (c : Case) : GenM Edit := do
  if ← chance 1 12 then genAdd c else pick (← pick c.candidates)

/-! ## TOML -/

def tstr (s : String) : String := "\"" ++ s ++ "\""
def tarr (xs : List String) : String := "[" ++ ", ".intercalate (xs.map tstr) ++ "]"

def tomlOf (g : Graph) : String := Id.run do
  let mut t := s!"sources = {tarr g.sources}\n"
  for (name, mode, depfile, restat, wrapped) in ruleSpecs do
    t := t ++ s!"\n[[rule]]\nname = {tstr name}\ncommand = {tstr (ruleCmd mode)}\n"
    if depfile then t := t ++ "depfile = true\n"
    if restat then t := t ++ "restat = true\n"
    if !wrapped then t := t ++ "wrap = false\n"
  for e in g.edges do
    t := t ++ s!"\n[[build]]\nrule = {tstr e.rule}\nouts = {tarr e.outs}\n"
    for (k, v) in [("implicit-outs", e.implicitOuts), ("ins", e.ins), ("implicit-ins", e.implicitIns),
                   ("order-only", e.orderOnly)] do
      if !v.isEmpty then t := t ++ s!"{k} = {tarr v}\n"
    let vars := e.vars.filter (·.1 != wrapOutsVar)
    t := t ++ "vars = { " ++ ", ".intercalate (vars.map fun (k, v) => s!"{k} = {tstr v}") ++ " }\n"
  unless g.aliases.isEmpty do
    t := t ++ "\n[aliases]\n"
    for a in g.aliases do t := t ++ s!"{tstr a.name} = {tarr a.targets}\n"
  t

/-! ## Running the model -/

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

/-- The edges Ninja visits to build `ts`: those whose outputs the targets
need, through explicit, implicit and order-only inputs, in manifest order.
In a schedule every reader follows the edges it reads from, so one pass
from the end finds them all. Building them with `buildTrace` is a sequence
of `Reach` steps. -/
def closure (es : List MEdge) (ts : List Path) : List MEdge :=
  (es.foldr (fun e (acc, need) => if e.outs.any need.contains then (e :: acc, need ++ e.reads) else (acc, need))
    ([], ts)).1

/-- Whether a run of `e` from `st` fails on its own: a wrapped command in
mode `x` that leaves out an output, which the wrapper turns into a failure
that changes no file (`Mise.Model.St.runWrapped`). The helper still runs and
logs the run. A written output is never empty, so an empty value is one the
helper left out. -/
def natFailRule (e : MEdge) : Bool :=
  (e.cmd.splitOn "; if ( ").length == 2 && ((args e.cmd).headD "").contains 'x'

def natFail (st : St String) (e : MEdge) : Bool :=
  natFailRule e && e.outs.any fun o => st.outVal sem e o == ""

/-- A build under `ninja -k 0` in which the edge with first output `f`, if
any, fails before it reads or writes anything, and each edge for which
`natFail` holds fails after its helper ran. Ninja runs every edge that does
not depend on a failed one, and none that does. The edges that finish are a
sublist of the manifest, and a failed run leaves the state as it was
(`Mise.Headline.wrapped_run`), so this too is a sequence of `Reach` steps.
Returns the state, the edges whose helper ran (failed ones included),
whether `f` was tried, and whether any edge failed. -/
def failTrace (f : Option Path) : List MEdge → List Path → St String → St String × List MEdge × Bool × Bool
  | [], _, st => (st, [], false, false)
  | e :: es, bad, st =>
    if e.reads.any bad.contains then failTrace f es (bad ++ e.outs) st
    else if some (e.outs.headD "") == f && st.dirty e then
      let r := failTrace f es (bad ++ e.outs) st
      (r.1, r.2.1, true, true)
    else if st.dirty e && natFail st e then
      let r := failTrace f es (bad ++ e.outs) st
      (r.1, e :: r.2.1, r.2.2.1, true)
    else
      let r := failTrace f es bad (st.step sem e)
      (r.1, if st.dirty e then e :: r.2.1 else r.2.1, r.2.2)

/-- A build that Ninja stopped when the edge with first output `f` failed,
under the default `-k 1`: Ninja starts no new edge after the failure, and
which edges finished first depends on its scheduling, which the model does
not fix. Ninja also stops at the first edge for which `natFail` holds. So
the driver tells the model which edges ran (`fin`) and whether `f` was
tried, and the model runs exactly those edges in manifest order, a sequence
of `Reach` steps in which a run for which `natFail` holds changes nothing.
It checks that each one was dirty on its turn and read no output that an
unfinished or failed dirty edge, or `f`, had yet to write. Also returns
whether an edge failed and the first dirty edge Ninja left unstarted, which
the caller accepts only when an edge failed. -/
def stopTrace (f : Path) (fin : List Path) (tried : Bool) :
    List MEdge → List Path → St String → Except String (St String × List MEdge × Bool × Option Path)
  | [], _, st => pure (st, [], tried, none)
  | e :: es, bad, st => do
    let o := e.outs.headD ""
    if fin.contains o then
      unless st.dirty e do throw s!"Ninja ran {o}, which the model says is clean"
      if let some p := e.reads.find? bad.contains then throw s!"Ninja ran {o} before {p} was up to date"
      if natFail st e then
        let (st', ran, _, left) ← stopTrace f fin tried es (bad ++ e.outs) st
        pure (st', e :: ran, true, left)
      else
        let (st', ran, failed, left) ← stopTrace f fin tried es bad (st.run sem e)
        pure (st', e :: ran, failed, left)
    else if st.dirty e then
      if o == f && tried && e.reads.any bad.contains then throw s!"Ninja tried {o} before its inputs were up to date"
      let (st', ran, failed, _) ← stopTrace f fin tried es (bad ++ e.outs) st
      pure (st', ran, failed, some o)
    else
      if o == f && tried then throw s!"Ninja tried {o}, which the model says is clean"
      stopTrace f fin tried es bad st

/-- How a step builds. -/
structure StepD where
  edits : List Edit := []
  /-- Build only these targets; every edge when empty. -/
  targets : List Path := []
  /-- The edge with this first output fails, and Ninja runs with `-k 0`, or
  stops at the failure when `stop` holds. -/
  fail : Option Path := none
  stop : Bool := false
  /-- For a `stop` step, what the driver saw: the edges that finished and
  whether the failing edge was tried. Without it the model guesses as for
  `-k 0`, and the driver recomputes the case once it has seen the build. -/
  finished : Option (List Path) := none
  tried : Bool := false
  deriving ToJson, FromJson, Inhabited

/-- Product `p` with mtime 0, older than every source and every run. The
driver sets the real file's mtime to one second after the epoch. -/
def age (st : St String) (p : Path) : St String :=
  { st with fs := fun q => if q = p then (st.fs p).map fun (v, _) => (v, 0) else st.fs q }

/-- One step: write the changed files and apply the other edits, check the
manifest, build, and record what the model runs and the contents it
leaves. `known` lists every path the case has used, so that the state keeps
the outputs of removed edges. With `strict`, also check that a second
build runs nothing and that depfile edges read only what they may. -/
def step (strict : Bool) (sd : StepD) (old : Option Case) (c : Case) (known : List Path) (st : St String) :
    Except String (Json × St String × List Path) := do
  let g := c.graph
  unless g.check do throw "the graph is not valid"
  let toml := tomlOf g
  let ninja := print (emit g)
  match Toml.load toml with
  | .error e => throw s!"mise.toml does not load: {e}"
  | .ok vg => unless print (emit vg.1) == ninja do throw "mise.toml does not read back as the graph"
  let touched := sd.edits.filterMap fun | .touch p => some p | _ => none
  let changed := c.srcs.filter fun s => touched.contains s.path || match old with
    | some o => (o.srcs.find? (·.path == s.path)).map (·.text) != some s.text
    | none => true
  let tomlChanged := match old with
    | some o => tomlOf o.graph != toml
    | none => true
  let known := dedup (known ++ g.sources ++ products g)
  let outs := known.filter (!g.isSource ·)
  let dels := dedup (sd.edits.filterMap fun | .delOut p => some p | _ => none) |>.filter outs.contains
  let delLog := sd.edits.any fun | .delLog => true | _ => false
  let delDeps := sd.edits.any fun | .delDeps => true | _ => false
  let ages := dedup (sd.edits.filterMap fun | .age p => some p | _ => none) |>.filter (products g).contains
  let st := ages.foldl age (st.edits (changed.map fun s => (s.path, s.text)))
  let st := { st with fs := fun p => if dels.contains p then none else st.fs p }
  let st := if delLog then { st with log := fun _ => none } else st
  let st := if delDeps then { st with deps := fun _ => none } else st
  let es := (emit g).medges
  let fail := sd.fail.filter fun f => es.any (·.outs.headD "" == f)
  let targets := sd.targets.filter (targetsOf g).contains
  let visit := if targets.isEmpty then es else closure es (expandTargets g targets)
  let (st', ran, tried, failed) ← match fail, sd.stop, sd.finished with
    | some f, true, some fin => do
      let (st', ran, failed, left) ← stopTrace f fin sd.tried es [] st
      if let some o := left then
        unless failed do throw s!"Ninja stopped without running {o}, which the model says is dirty"
      pure (st', ran, sd.tried, failed)
    | some f, _, _ => pure (failTrace (some f) es [] st)
    | none, _, _ =>
      -- `failTrace none` is `buildTrace` when no edge fails; keep the
      -- model's own trace where none can.
      if es.any natFailRule then pure (failTrace none visit [] st)
      else let r := buildTrace sem visit st; pure (r.1, r.2, false, false)
  let st' := flatten known st'
  if strict then
    if !failed then
      unless (buildTrace sem visit st').2.isEmpty do
        throw "the model is not idempotent"
    for e in es do
      if e.dyn then
        for o in e.outs do
          for k in (st'.deps o).getD [] do
            unless g.isSource k || e.reads.contains k do throw s!"{o} read {k}, which it may not"
  let write := changed.map (fun s => (s.path, s.text)) ++ (if tomlChanged then [("mise.toml", toml)] else [])
  let delete := dels ++ (if delLog then [".ninja_log"] else []) ++ (if delDeps then [".ninja_deps"] else [])
  let j := Json.mkObj [("edits", toJson (sd.edits.map (·.describe))), ("write", jsonMap write),
    ("delete", toJson delete), ("age", toJson ages), ("ninja", Json.str ninja), ("targets", toJson targets),
    ("fail", toJson fail), ("stop", toJson (fail.isSome && sd.stop)), ("tried", toJson tried), ("failed", toJson failed),
    ("edges", toJson (c.edges.map EdgeD.ofEdge)), ("ran", toJson (sortStrs (ran.map (·.outs.headD "")))),
    ("products", Json.mkObj (outs.map fun p => (p, match st'.fs p with
      | some (v, _) => Json.str v
      | none => Json.null)))]
  pure (j, st', known)

def empty : St String := { fs := fun _ => none, log := fun _ => none, clock := 0 }

/-- `n` steps of edits. All but the last build may build some targets only
(one in five), have an edge fail under `-k 0` (one in ten), or stop at a
failing edge (one in ten). Under `Opts.nowrap` no edge is made to fail. -/
def genSteps (o : Opts) (c0 : Case) (n : Nat) : GenM (List StepD) := do
  let mut c := c0
  let mut out := []
  for i in [0:n] do
    let k ← if ← chance 1 10 then pure 0 else pure (1 + (← rand 3))
    let mut es := []
    for _ in [0:k] do
      let e ← genEdit c
      c := c.apply e
      es := es ++ [e]
    let r ← rand 10
    let mut sd : StepD := { edits := es }
    -- Under `nowrap`, Ninja reruns every edge with a missing output, so it
    -- tries a failing edge, and finishes edges before a stop, that the model
    -- finds clean; those cases build fully instead.
    if i + 1 == n || r ≥ 4 || c.edges.isEmpty || (o.nowrap && r ≥ 2) then pure ()
    else if r < 2 then sd := { sd with targets := ← sample (1 + (← rand 2)) (targetsOf c.graph) }
    else
      -- Ninja schedules an edge with readers early, so a stop there leaves
      -- more edges unstarted.
      let read := c.edges.filter c.read
      let pool := if r == 3 && !read.isEmpty then read else c.edges
      sd := { sd with fail := some (← pick (pool.map (·.outs.headD ""))), stop := r == 3 }
    out := out ++ [sd]
  pure out

/-! ## Case descriptions

A description is a case before the model runs: the sources, the edges and
the steps. `fuzzgen` writes it into every case file, and `fuzzgen expect`
reads one back and recomputes the expectations, so `test/fuzz.py` can
shrink a failing case by editing its description. -/

structure Desc where
  srcs : List Src
  edges : List EdgeD
  steps : List StepD
  deriving ToJson, FromJson

def runCase (strict : Bool) (c0 : Case) (steps : List StepD) : Except String Json := do
  let (j0, st0, k0) ← step strict {} none c0 [] empty
  let mut st := st0
  let mut known := k0
  let mut c := c0
  let mut js := #[j0]
  for sd in steps do
    let c' := sd.edits.foldl Case.apply c
    let (j, st', known') ← step strict sd (some c) c' known st
    js := js.push j
    st := st'
    known := known'
    c := c'
  let desc : Desc := ⟨c0.srcs, c0.edges.map .ofEdge, steps⟩
  pure (Json.mkObj [("desc", toJson desc), ("steps", Json.arr js)])

def seeded (seed i : Nat) : Rng := Id.run do
  let mut g : Rng := ⟨(seed * 1000003 + i * 7919 + 1).toUInt64⟩
  for _ in [0:4] do g := g.next.2
  g

def genOne (o : Opts) (seed i : Nat) : Case × List StepD :=
  let gen : GenM (Case × List StepD) := do
    let c ← genCase o
    let n := 3 + (← rand 6)
    pure (c, ← genSteps o c n)
  (gen.run (seeded seed i)).1

end MiseTest.Fuzz

open MiseTest.Fuzz Lean in
def main (args : List String) : IO UInt32 := do
  -- `test/mutants.py` turns the model's own checks off, to see what the
  -- checks against Ninja catch.
  let strict := (← IO.getEnv "FUZZGEN_NO_SELF_CHECK").isNone
  if let ["expect", src, dst] := args then
    let d ← match Json.parse (← IO.FS.readFile src) >>= fromJson? (α := Desc) with
      | .ok d => pure d
      | .error e => IO.eprintln s!"{src}: {e}"; return 2
    match runCase strict { srcs := d.srcs, edges := d.edges.map (·.toEdge) } d.steps with
    | .error e => IO.eprintln s!"{src}: {e}"; return 1
    | .ok j => IO.FS.writeFile dst j.compress; return 0
  let (dir, n, seed, o) := match args with
    | [d, n, s] => (d, n.toNat!, s.toNat!, ({} : Opts))
    | [d, n, s, f] => (d, n.toNat!, s.toNat!, Opts.parse f)
    | _ => ("test/out/fuzz/cases", 100, 1, ({} : Opts))
  IO.FS.createDirAll dir
  for i in [0:n] do
    let (c, steps) := genOne o seed i
    match runCase strict c steps with
    | .error e => IO.eprintln s!"case {i}: {e}"; return 1
    -- Under `nowrap` an output can go missing, which `fuzz.py` then allows
    -- as `--missing-ok` describes.
    | .ok j => IO.FS.writeFile s!"{dir}/{i}.json" (j.setObjVal! "missingOk" (toJson (o.absent && o.nowrap))).compress
  return 0
