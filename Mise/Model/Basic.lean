import Mise.Frontend.Emit

/-!
# Stage 5: an abstract model of Ninja

The state holds file contents with modification times, the build log, and a
clock. `ninjaBuild` visits the manifest's edges in order and runs each edge
that is dirty. Dirtiness follows Ninja's `DependencyScan::RecomputeOutputDirty`
for edges without `restat`, `generator` or a depfile: an output is dirty when
it is missing, older than the newest input, has no log entry, has a log entry
with a different command, or has a log entry older than the newest input.

Dirtiness is decided when the edge is visited, from the current state. An
edge with an input rebuilt earlier in the same run is therefore dirty by the
mtime check (`dirty_of_input_rebuilt`), which is Ninja's dirty propagation.
-/

namespace Mise.Model
open Mise Mise.Syntax Mise.Frontend

/-- What the model needs from an edge: all outputs, the inputs that count
for dirtiness and for the command (explicit and implicit), and the evaluated
command. -/
structure MEdge where
  outs : List Path
  ins : List Path
  cmd : String
  deriving DecidableEq, Repr, Inhabited

def toMEdge (file : Scope) (c : EdgeInfo) : MEdge :=
  ⟨c.edge.allOuts, c.edge.ins ++ c.edge.implicitIns, c.command file⟩

end Mise.Model

namespace Mise.Syntax.Manifest
/-- The manifest's edges as the model sees them, in manifest order. -/
def medges (m : Manifest) : List Mise.Model.MEdge := m.elab.edges.map (Mise.Model.toMEdge m.elab.file)
end Mise.Syntax.Manifest

namespace Mise.Model
open Mise Mise.Syntax Mise.Frontend

/-- File system, build log and clock. A log entry is the command and the
time recorded for the output. -/
structure St (V : Type) where
  fs : Path → Option (V × Nat)
  log : Path → Option (String × Nat)
  clock : Nat

variable {V : Type} [Inhabited V]

namespace St

/-- Contents; a missing file reads as `default`. -/
def content (st : St V) (p : Path) : V := ((st.fs p).map (·.1)).getD default

/-- Modification time; a missing file has time 0. -/
def mtime (st : St V) (p : Path) : Nat := ((st.fs p).map (·.2)).getD 0

/-- The newest mtime among some inputs. -/
def newest (st : St V) : List Path → Nat
  | [] => 0
  | p :: ps => max (st.mtime p) (st.newest ps)

def outDirty (st : St V) (e : MEdge) (o : Path) : Bool :=
  match st.fs o, st.log o with
  | some (_, t), some (c, lt) => decide (t < st.newest e.ins) || c != e.cmd || decide (lt < st.newest e.ins)
  | _, _ => true

def dirty (st : St V) (e : MEdge) : Bool := e.outs.any (st.outDirty e)

/-- Run an edge's command: write every output and its log entry at a fresh
time. Writes are atomic. -/
def run (exec : String → List V → List V) (st : St V) (e : MEdge) : St V :=
  let t := st.clock + 1
  let vs := exec e.cmd (e.ins.map st.content)
  { fs := fun p => if e.outs.contains p then some (vs.getD (e.outs.idxOf p) default, t) else st.fs p
    log := fun p => if e.outs.contains p then some (e.cmd, t) else st.log p
    clock := t }

def step (exec : String → List V → List V) (st : St V) (e : MEdge) : St V :=
  if st.dirty e then st.run exec e else st

/-- A source edit: new contents at a fresh time. -/
def edit (st : St V) (p : Path) (v : V) : St V :=
  { st with fs := fun q => if q = p then some (v, st.clock + 1) else st.fs q, clock := st.clock + 1 }

def edits (st : St V) : List (Path × V) → St V
  | [] => st
  | (p, v) :: es => (st.edit p v).edits es

/-- Every recorded mtime is at most the clock. -/
def Fresh (st : St V) : Prop := ∀ p v t, st.fs p = some (v, t) → t ≤ st.clock

/-- The edge's outputs hold what its command computes from its inputs now. -/
def Consistent (exec : String → List V → List V) (st : St V) (e : MEdge) : Prop :=
  ∀ o ∈ e.outs, st.content o = (exec e.cmd (e.ins.map st.content)).getD (e.outs.idxOf o) default

/-- An edge Ninja would skip is consistent. -/
def EdgeOK (exec : String → List V → List V) (st : St V) (e : MEdge) : Prop :=
  st.dirty e = false → st.Consistent exec e

end St

/-- Visit edges in order, running the dirty ones. Also returns the edges run. -/
def buildTrace (exec : String → List V → List V) : List MEdge → St V → St V × List MEdge
  | [], st => (st, [])
  | e :: es, st =>
    let r := buildTrace exec es (st.step exec e)
    (r.1, if st.dirty e then e :: r.2 else r.2)

def ninjaBuild (exec : String → List V → List V) (m : Manifest) (st : St V) : St V :=
  (buildTrace exec m.medges st).1

/-- The model's invariant: mtimes are fresh and every skipped edge is
consistent. -/
def Inv (exec : String → List V → List V) (es : List MEdge) (st : St V) : Prop :=
  st.Fresh ∧ ∀ e ∈ es, st.EdgeOK exec e

def Disjoint (a b : List Path) : Prop := ∀ p ∈ a, p ∉ b

/-- Edges in a schedulable order: no edge reads its own outputs or a later
edge's outputs, and no two edges share an output. -/
def Sched : List MEdge → Prop
  | [] => True
  | e :: es => Disjoint e.ins e.outs ∧ (∀ e' ∈ es, Disjoint e.ins e'.outs ∧ Disjoint e.outs e'.outs) ∧ Sched es

/-- The build specification of a list of model edges. -/
def specOf (exec : String → List V → List V) (es : List MEdge) : BuildSpec Path V where
  isSource k := (findOut MEdge.outs k es).isNone
  task k := match findOut MEdge.outs k es with
    | some (_, e) => edgeTask exec e.cmd e.ins (e.outs.idxOf k)
    | none => .pure default

end Mise.Model
