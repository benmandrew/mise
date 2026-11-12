import Mise.Frontend.Emit

/-!
# Stages 5 to 7: an abstract model of Ninja

The state holds file contents with modification times, the build log, the
deps log, and a clock. `ninjaBuild` visits the manifest's edges in order and
runs each edge that is dirty. Dirtiness follows Ninja's
`DependencyScan::RecomputeOutputDirty` for edges without `generator`. An
output's inputs are the edge's explicit and implicit inputs, plus for a
depfile edge the deps recorded for that output. The output is
dirty when it is missing, older than the newest input, has no log entry, has
a log entry with a different command, has a log entry older than the newest
input, or belongs to a depfile edge and has no deps entry. For a `restat`
edge the output's own mtime is not compared, only the logged time, as Ninja
does when the output has a log entry.

Dirtiness is decided when the edge is visited, from the current state. An
edge with an input rebuilt earlier in the same run is therefore dirty by the
mtime check (`outDirty_of_newer`), which is Ninja's dirty propagation.
-/

namespace Mise.Model
open Mise Mise.Syntax Mise.Frontend

/-- What the model needs from an edge: all outputs, the inputs that count
for dirtiness and for a static command (explicit and implicit), the
order-only inputs, the evaluated command, whether it has a depfile, and
whether it has `restat`.
Gloss: model edges -/
structure MEdge where
  /-- All outputs, explicit and implicit.
  Gloss: the outputs of {self} -/
  outs : List Path
  ins : List Path
  oo : List Path := []
  cmd : String
  dyn : Bool := false
  restat : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Every input Ninja builds before the edge. -/
def MEdge.reads (e : MEdge) : List Path := e.ins ++ e.oo

/-- The edge's command as a task returning all its outputs. -/
def MEdge.task {V : Type} (sem : Sem V) (e : MEdge) : Task Path V (List V) := cmdTask sem e.dyn e.cmd e.ins

/-- An edge as Ninja stores it, in the model's form: all outputs, explicit and
implicit inputs, order-only inputs, and the command, `deps` and `restat`
bindings as Ninja evaluates them with the final file scope `file`. -/
def toMEdge (file : Scope) (c : EdgeInfo) : MEdge :=
  ⟨c.edge.allOuts, c.edge.ins ++ c.edge.implicitIns, c.edge.orderOnly, c.command file, c.isDyn file,
    c.isRestat file⟩

end Mise.Model

namespace Mise.Syntax.Manifest
/-- The manifest's edges as the model sees them, in manifest order. -/
def medges (m : Manifest) : List Mise.Model.MEdge := m.elab.edges.map (Mise.Model.toMEdge m.elab.file)
end Mise.Syntax.Manifest

namespace Mise.Model
open Mise Mise.Syntax Mise.Frontend

/-- File system, build log, deps log and clock. A log entry is the command
and the time recorded for the output; a deps entry is the list of paths the
command read.
Gloss: model states over {V} -/
structure St (V : Type) where
  fs : Path → Option (V × Nat)
  log : Path → Option (String × Nat)
  deps : Path → Option (List Path) := fun _ => none
  /-- The current time. Every edit and every command run advances it by
  one, and stamps what it writes with the new time.
  Gloss: the clock of {self} -/
  clock : Nat

variable {V : Type} [Inhabited V]

namespace St

/-- Contents; a missing file reads as `default`.
Gloss: the contents of {p} in {st}
Gloss.fun: the file contents of {st} -/
def content (st : St V) (p : Path) : V := ((st.fs p).map (·.1)).getD default

/-- Modification time; a missing file has time 0.
Gloss: the mtime of {p} in {st} -/
def mtime (st : St V) (p : Path) : Nat := ((st.fs p).map (·.2)).getD 0

/-- The newest mtime among some inputs. -/
def newest (st : St V) : List Path → Nat
  | [] => 0
  | p :: ps => max (st.mtime p) (st.newest ps)

/-- The inputs Ninja checks for an output: the static inputs, and for a
depfile edge the recorded deps. `none` when a depfile edge has no entry. -/
def effIns (st : St V) (e : MEdge) (o : Path) : Option (List Path) :=
  if e.dyn then (st.deps o).map (e.ins ++ ·) else some e.ins

/-- Whether output `o` of `e` is dirty: true when the file is missing, has no
log entry, or (for a depfile edge) has no deps entry; when the logged
command differs from the edge's; when the log time is older than the
newest input Ninja checks; or, for an edge without `restat`, when the
file is older than that input. -/
def outDirty (st : St V) (e : MEdge) (o : Path) : Bool :=
  match st.fs o, st.log o, st.effIns e o with
  | some (_, t), some (c, lt), some D =>
    (!e.restat && decide (t < st.newest D)) || c != e.cmd || decide (lt < st.newest D)
  | _, _, _ => true

/-- Whether Ninja runs the edge: some output is dirty (`outDirty`).
Gloss: whether {e} is dirty in {st} -/
def dirty (st : St V) (e : MEdge) : Bool := e.outs.any (st.outDirty e)

/-- The contents a run writes to output `o`. -/
def outVal (sem : Sem V) (st : St V) (e : MEdge) (o : Path) : V :=
  ((e.task sem).run st.content).getD (e.outs.idxOf o) default

/-- A `restat` command leaves output `o` untouched (Stage 7).
Gloss: whether running {e} in {st} leaves its output {o} untouched -/
def kept (sem : Sem V) (st : St V) (e : MEdge) (o : Path) : Bool :=
  e.restat && match st.fs o with
    | some (old, _) => sem.keep old (st.outVal sem e o)
    | none => false

/-- Run an edge's command: write every output it does not keep, its log
entry and its deps entry at a fresh time. Writes are atomic.
Gloss: the state after running {e} in {st} -/
def run (sem : Sem V) (st : St V) (e : MEdge) : St V :=
  let t := st.clock + 1
  let D := (e.task sem).deps st.content
  { fs := fun p => if e.outs.contains p && !st.kept sem e p then some (st.outVal sem e p, t) else st.fs p
    log := fun p => if e.outs.contains p then some (e.cmd, t) else st.log p
    deps := fun p => if e.outs.contains p then some D else st.deps p
    clock := t }

/-- Ninja's visit to an edge: run it if it is dirty, otherwise change nothing. -/
def step (sem : Sem V) (st : St V) (e : MEdge) : St V :=
  if st.dirty e then st.run sem e else st

/-- A source edit: new contents at a fresh time. -/
def edit (st : St V) (p : Path) (v : V) : St V :=
  { st with fs := fun q => if q = p then some (v, st.clock + 1) else st.fs q, clock := st.clock + 1 }

/-- Apply source edits in list order, each with `edit`.
Gloss: {#1} after the edits {#2} -/
def edits (st : St V) : List (Path × V) → St V
  | [] => st
  | (p, v) :: es => (st.edit p v).edits es

/-- Every recorded mtime and log time is at most the clock. -/
def Fresh (st : St V) : Prop :=
  (∀ p v t, st.fs p = some (v, t) → t ≤ st.clock) ∧ ∀ p c t, st.log p = some (c, t) → t ≤ st.clock

/-- The edge's outputs hold what its command computes now, and the inputs
Ninja checks cover everything the command reads now. -/
def Consistent (sem : Sem V) (st : St V) (e : MEdge) : Prop :=
  ∀ o ∈ e.outs, st.content o = ((e.task sem).run st.content).getD (e.outs.idxOf o) default ∧
    ∀ D, st.effIns e o = some D → ∀ k ∈ (e.task sem).deps st.content, k ∈ D

/-- An edge Ninja would skip is consistent. -/
def EdgeOK (sem : Sem V) (st : St V) (e : MEdge) : Prop :=
  st.dirty e = false → st.Consistent sem e

end St

/-- Visit edges in order, running the dirty ones. Also returns the edges run.
Gloss: the final state and the edges run when Ninja visits {#2} in order from {#3}
Gloss.fst: the state after Ninja visits {#2} in order from {#3}
Gloss.snd: the edges that run when Ninja visits {#2} in order from {#3} -/
def buildTrace (sem : Sem V) : List MEdge → St V → St V × List MEdge
  | [], st => (st, [])
  | e :: es, st =>
    let r := buildTrace sem es (st.step sem e)
    (r.1, if st.dirty e then e :: r.2 else r.2)

/-- One `ninja` run on a manifest: visit the edges in manifest order, running
the dirty ones, and return the final state. -/
def ninjaBuild (sem : Sem V) (m : Manifest) (st : St V) : St V :=
  (buildTrace sem m.medges st).1

/-- A path an edge may read: a source of the whole list, or an input Ninja
builds before the edge. -/
def Allowed (es : List MEdge) (e : MEdge) (k : Path) : Prop := (∀ e' ∈ es, k ∉ e'.outs) ∨ k ∈ e.reads

/-- The static-ancestor condition: every depfile command reads only allowed
paths. Static commands read their inputs and satisfy it by construction. -/
def Reads (sem : Sem V) (es : List MEdge) : Prop :=
  ∀ e ∈ es, e.dyn = true → (sem.dyn e.cmd).FetchesOnly (Allowed es e)

/-- Every deps entry of a depfile edge names only allowed paths. -/
def DepsOK (es : List MEdge) (st : St V) : Prop :=
  ∀ e ∈ es, e.dyn = true → ∀ o ∈ e.outs, ∀ D, st.deps o = some D → ∀ k ∈ D, Allowed es e k

/-- The model's invariant: mtimes are fresh, deps entries name allowed
paths, and every skipped edge is consistent. -/
def Inv (sem : Sem V) (es : List MEdge) (st : St V) : Prop :=
  st.Fresh ∧ DepsOK es st ∧ ∀ e ∈ es, st.EdgeOK sem e

/-- No path is in both lists.
Gloss: no path is in both {a} and {b} -/
def Disjoint (a b : List Path) : Prop := ∀ p ∈ a, p ∉ b

/-- Edges in a schedulable order: no edge reads its own outputs or a later
edge's outputs, order-only inputs included, and no two edges share an
output. -/
def Sched : List MEdge → Prop
  | [] => True
  | e :: es => Disjoint e.reads e.outs ∧ (∀ e' ∈ es, Disjoint e.reads e'.outs ∧ Disjoint e.outs e'.outs) ∧ Sched es

/-- The build specification of a list of model edges. -/
def specOf (sem : Sem V) (es : List MEdge) : BuildSpec Path V where
  isSource k := (findOut MEdge.outs k es).isNone
  task k := match findOut MEdge.outs k es with
    | some (_, e) => outTask (e.task sem) (e.outs.idxOf k)
    | none => .pure default

end Mise.Model
