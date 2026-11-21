import Mise.Model.Cmp
import Mise.Model.Minimal
import Mise.Model.Parallel

/-!
# End-to-end theorems, restated for reading

`mise` is a Lean 4 front end for Ninja. A user describes a build in a
*domain-specific language* (DSL), and `mise` writes it out as a Ninja manifest.
The theorems show that the manifest is well formed, and that Ninja, as
modelled in Lean, builds what the user described. One run leaves correct
contents, and a second run does nothing. A run executes only the edges it
must, and any parallel order gives the same result. Lean checks every proof,
but a theorem means only what the definitions in its statement mean, so those
definitions follow the theorems.
-/

namespace Mise.Theorems
open Mise Mise.Syntax Mise.Frontend Mise.Model

variable {V : Type} [Inhabited V] (sem : Sem V)

/-! ## Names used in the statements -/

/-- The edges of the manifest that `mise` emits for `g`, in the model's form
and in manifest order (`Manifest.medges`). `phony` edges are left out.
Gloss: the manifest edges of {g} -/
abbrev edges (g : Graph) : List MEdge := (emit g).medges

/-- `st` can arise from a start state through any sequence of source edits
and edge visits (`Reach`). The start state has empty build and deps logs,
and no mtime or log time in it is later than its clock. An edit changes a path that no
edge in `edges g` writes. A visit to an edge in `edges g` runs it if it is
dirty and otherwise changes nothing, as Ninja does. Full builds, builds of
some targets and interrupted builds are all such sequences.
Gloss: {st} is reachable for {g} -/
abbrev Reachable (g : Graph) (st : St V) : Prop := Reach sem (edges g) st

/-- The state after one modelled `ninja` run from `st` on the manifest
emitted for `g`, which visits every edge in manifest order. When `g` has
default targets, `ninja` with no arguments builds only those. That is a
partial build, which `Reachable` covers and `build` does not describe.
Gloss: the state after building {g} from {st}
Gloss.fun: building {g} -/
abbrev build (g : Graph) (st : St V) : St V := (buildTrace sem (edges g) st).1

/-- The edges that one modelled `ninja` run from `st` executes, in the order
it runs them.
Gloss: the edges run by building {g} from {st} -/
abbrev ran (g : Graph) (st : St V) : List MEdge := (buildTrace sem (edges g) st).2

/-- `es` is an order in which a parallel Ninja could run the edges. It is a
permutation of `edges g` in which no edge reads an output of itself or of a
later edge, order-only inputs included, and no two edges share an output.
Gloss: {es} is a valid parallel order for {g} -/
abbrev ValidOrder (g : Graph) (es : List MEdge) : Prop := es.Perm (edges g) ∧ Sched es

/-- `p` is an input that Ninja checks for some output of `e` in state `st`:
an explicit or implicit input of `e`, or, for a depfile edge, a path in that
output's deps log entry. A depfile output with no deps entry has no checked
inputs.
Gloss: Ninja checks input {p} of {e} in {st} -/
abbrev Checks (st : St V) (e : MEdge) (p : Path) : Prop :=
  ∃ o ∈ e.outs, ∃ D, st.effIns e o = some D ∧ p ∈ D

/-- From every reachable state `st`, the state `f st` has contents that are
correct for the sources in `st`. `build_correct` and `any_order` state their
conclusions with it, so a test of `Spec` is a test of those conclusions.
Gloss: {f} meets the specification of {g} -/
abbrev Spec (g : Graph) (f : St V → St V) : Prop :=
  ∀ {st}, Reachable sem g st → (g.spec sem).Correct st.content (f st).content

/-! ## The manifest -/

/-- For a valid graph, the manifest that `mise` emits is well formed. The
text `mise` writes is `print (emit g)` (`ValidGraph.ninja`), and trust item 1
assumes that Ninja reads `print m` as `m` for every well-formed manifest `m`.
So Ninja reads the text as `emit g`, the manifest the theorems below run.
Review: core -/
theorem well_formed (g : Graph) (valid : g.Valid) : (emit g).WellFormed :=
  emit_wellFormed g valid

/-- Take a valid graph whose depfile commands read only allowed inputs. For
any sources, the build it describes has at most one correct result.
`Correct` is the correctness predicate of *Build Systems à la Carte*:
sources keep their values, and every target holds what its task computes
from the result. -/
theorem correct_unique (g : Graph) (valid : g.Valid) (depfilesOK : g.DynOK sem)
    {sources result₁ result₂ : Path → V} (correct₁ : (g.spec sem).Correct sources result₁)
    (correct₂ : (g.spec sem).Correct sources result₂) : result₁ = result₂ :=
  BuildSpec.correct_unique (g.acyclic sem valid depfilesOK) correct₁ correct₂

/-! ## Incremental builds -/

/-- Take a valid graph whose *depfile* commands read only allowed inputs. From
any reachable state, one `ninja` run leaves contents that are correct for
the current sources.
Review: core -/
theorem build_correct (g : Graph) (valid : g.Valid) (depfilesOK : g.DynOK sem) :
    Spec sem g (build sem g) := by
  intro st reachable
  have hc := (reach_sound sem (sched_emit g valid) (reads_emit sem g valid depfilesOK) reachable).1
  rwa [denote_emit sem g valid] at hc

/-- Take a valid graph whose depfile commands read only allowed inputs. After
one `ninja` run from any reachable state, a second run executes no edge and
leaves the state unchanged.
Review: core -/
theorem rebuild_noop (g : Graph) (valid : g.Valid) (depfilesOK : g.DynOK sem) {st : St V}
    (reachable : Reachable sem g st) :
    ran sem g (build sem g st) = [] ∧ build sem g (build sem g st) = build sem g st := by
  have hi := (dsl_sound sem g valid depfilesOK reachable).2
  have h1 := congrArg Prod.snd hi
  have h2 := congrArg Prod.fst hi
  exact ⟨h1, h2⟩

/-- Take a valid graph whose depfile commands read only allowed inputs and a
reachable state. Build, apply `edits` to sources, and build again. Every edge
`e` that the second build runs has a reason: an input `p` that Ninja checks
for `e` in the state the first build left. When the second build reaches
`e`, the modification time (mtime) of `p` is later than the clock at the end
of the first build. And `p` is either a path in `edits` or an output of an
edge that ran earlier in the second build. So an edge does not run when no
edit and no earlier edge touched its checked inputs. A `restat` edge that
kept its output did not touch that output.
Review: core -/
theorem rebuild_minimal (g : Graph) (valid : g.Valid) (depfilesOK : g.DynOK sem) {st₀ : St V}
    (reachable : Reachable sem g st₀) (edits : List (Path × V))
    (editsSources : ∀ edit ∈ edits, g.isSource edit.1 = true) {e : MEdge}
    (eRan : e ∈ ran sem g ((build sem g st₀).edits edits)) :
    ∃ before after, edges g = before ++ e :: after ∧ ∃ p, Checks (build sem g st₀) e p ∧
      (build sem g st₀).clock < (buildTrace sem before ((build sem g st₀).edits edits)).1.mtime p ∧
      (p ∈ edits.map (·.1) ∨
        ∃ e' ∈ (buildTrace sem before ((build sem g st₀).edits edits)).2, p ∈ e'.outs) := by
  have hclean := (dsl_parallel sem g valid depfilesOK (List.Perm.refl _) (sched_emit g valid)
    reachable).2
  obtain ⟨pre, post, hsplit, o, ho, D, hD, p, hp, hnew, hwhy⟩ :=
    build_minimal_clean sem (sched_emit g valid) hclean edits
      (fun edit h => source_emit g valid (editsSources edit h)) eRan
  exact ⟨pre, post, hsplit, p, ⟨o, ho, D, hD, hp⟩, hnew, hwhy⟩

/-! ## Parallel builds -/

/-- Take a valid graph whose depfile commands read only allowed inputs and a
reachable state. Running the edges in any valid `order` leaves contents that
are correct for the current sources. It runs the same edges as a run in
manifest order, up to order, and a run in manifest order executes each edge
at most once.
Review: core -/
theorem any_order (g : Graph) (valid : g.Valid) (depfilesOK : g.DynOK sem) {order : List MEdge}
    (validOrder : ValidOrder g order) :
    Spec sem g (fun st => (buildTrace sem order st).1) ∧
      ∀ {st}, Reachable sem g st →
        (buildTrace sem order st).2.Perm (ran sem g st) ∧ (ran sem g st).Nodup := by
  refine ⟨fun {st} reachable => ?_, fun {st} reachable =>
    ⟨dsl_same_edges sem g valid depfilesOK validOrder.1 validOrder.2 reachable,
      trace_nodup_sched sem _ st (sched_emit g valid)⟩⟩
  rw [(dsl_parallel sem g valid depfilesOK validOrder.1 validOrder.2 reachable).1]
  exact BuildSpec.cleanBuild_correct _ _

/-! ## Failed commands -/

/-- **Failed commands.** The DSL wraps every command, unless its rule opts
out, in a script that `Mise.Model.script` models. Take a valid graph, a
state reachable under `Sem.withCmp`, and a dirty edge `e` in `edges g`. The
command of `e` leaves `written` at the outputs, every value it writes is the
one `sem` gives (`writesSem`), and `exitedZero` says whether it exited 0. If
it fails or leaves an output missing, the state after the run is the state
before it. A successful run is the model's run under `Sem.withCmp`
(`runWrapped_ok`). In both cases the state after the run is reachable under
`Sem.withCmp`, so the theorems above apply to it. `Sem.withCmp` keeps a
`restat` output exactly when `cmp` finds it unchanged. The script needs two
conditions: no output's `.mise-old` file is an output (`asideNotOutput`),
and no `.mise-old` file of an output exists (`asideMissing`). -/
theorem wrapped_run [DecidableEq V] (g : Graph) (valid : g.Valid) {st : St V}
    (reachable : Reachable sem.withCmp g st) {e : MEdge} (inManifest : e ∈ edges g)
    (isDirty : st.dirty e = true) (written : Path → Option V) (exitedZero : Bool)
    (writesSem : ∀ o ∈ e.outs, ∀ v, written o = some v → v = st.outVal sem e o)
    (asideNotOutput : ∀ o ∈ e.outs, aside o ∉ e.outs)
    (asideMissing : ∀ o ∈ e.outs, st.fs (aside o) = none) :
    ((exitedZero = false ∨ ∃ o ∈ e.outs, written o = none) →
        st.runWrapped sem e written exitedZero = st) ∧
      Reachable sem.withCmp g (st.runWrapped sem e written exitedZero) :=
  ⟨runWrapped_fail sem st e written exitedZero (outs_nodup_emit valid inManifest) asideNotOutput
     asideMissing,
   reach_runWrapped sem st e written exitedZero reachable inManifest isDirty
     (outs_nodup_emit valid inManifest) asideNotOutput asideMissing writesSem⟩

end Mise.Theorems
