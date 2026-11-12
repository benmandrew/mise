import Mise.Model.Cmp
import Mise.Model.Minimal
import Mise.Model.Parallel
import Mise.Syntax.RoundTrip

/-!
# Headline theorems, restated for reading

`mise` is a Lean 4 front end for Ninja. A user describes a build in a
*domain-specific language* (DSL), and `mise` writes it out as a Ninja manifest.
The theorems show that the manifest means the build the user described, and
that Ninja, as modelled in Lean, runs it correctly. One run leaves correct
contents, and a second run does nothing. A run executes only the edges it
must, and any parallel order gives the same result. Lean checks every proof,
but a theorem means only what the definitions in its statement mean, so those
definitions follow the theorems.
-/

namespace Mise.Headline
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
emitted for `g`.
Gloss: the state after building {g} from {st} -/
abbrev build (g : Graph) (st : St V) : St V := ninjaBuild sem (emit g) st

/-- The edges that one modelled `ninja` run from `st` executes, in the order
it runs them.
Gloss: the edges run by building {g} from {st} -/
abbrev ran (g : Graph) (st : St V) : List MEdge := (buildTrace sem (edges g) st).2

/-- No edge in `edges g` writes `p`. That list leaves out `phony` edges, so
in a valid graph an alias name also counts as a source.
Gloss: {p} is a source of {g} -/
abbrev IsSource (g : Graph) (p : Path) : Prop := ∀ e ∈ edges g, p ∉ e.outs

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

/-! ## What the manifest means -/

/-- For a valid graph, the parser model reads the text that `mise` writes as
the manifest that `mise` emitted. Read through the model of Ninja's variable
evaluation, that manifest means the build the DSL describes (`Graph.spec`).
Review: core -/
theorem meaning (g : Graph) (valid : g.Valid) :
    parse (print (emit g)) = some (emit g) ∧ denote sem (emit g) = g.spec sem :=
  ⟨parse_print _ (emit_wellFormed g valid), denote_emit sem g valid⟩

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
theorem build_correct (g : Graph) (valid : g.Valid) (depfilesOK : g.DynOK sem) {st : St V}
    (reachable : Reachable sem g st) :
    (g.spec sem).Correct st.content (build sem g st).content := by
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

/-- For a valid graph, one `ninja` run from any state executes each edge at
most once. -/
theorem ran_nodup (g : Graph) (valid : g.Valid) (st : St V) : (ran sem g st).Nodup :=
  trace_nodup_sched sem _ st (sched_emit g valid)

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
    (editsSources : ∀ edit ∈ edits, IsSource g edit.1) {e : MEdge}
    (eRan : e ∈ ran sem g ((build sem g st₀).edits edits)) :
    ∃ before after, edges g = before ++ e :: after ∧ ∃ p, Checks (build sem g st₀) e p ∧
      (build sem g st₀).clock < (buildTrace sem before ((build sem g st₀).edits edits)).1.mtime p ∧
      (p ∈ edits.map (·.1) ∨
        ∃ e' ∈ (buildTrace sem before ((build sem g st₀).edits edits)).2, p ∈ e'.outs) := by
  have hclean := (dsl_parallel sem g valid depfilesOK (List.Perm.refl _) (sched_emit g valid)
    reachable).2
  obtain ⟨pre, post, hsplit, o, ho, D, hD, p, hp, hnew, hwhy⟩ :=
    build_minimal_clean sem (sched_emit g valid) hclean edits editsSources eRan
  exact ⟨pre, post, hsplit, p, ⟨o, ho, D, hD, hp⟩, hnew, hwhy⟩

/-- **Early cutoff.** Running a `restat` edge `e` that keeps every output
leaves the dirtiness of each edge `e'` unchanged, when `e'` shares no output
with `e`. So no such edge is rebuilt on account of `e`. -/
theorem restat_cutoff {st : St V} {e e' : MEdge} (disjoint : Disjoint e'.outs e.outs)
    (allKept : ∀ o ∈ e.outs, st.kept sem e o = true) : (st.run sem e).dirty e' = st.dirty e' :=
  Mise.Model.restat_cutoff sem disjoint allKept

/-! ## Parallel builds -/

/-- Take a valid graph whose depfile commands read only allowed inputs and a
reachable state. Running the edges in any valid `order` leaves contents that
are correct for the current sources. It runs the same edges as a run in
manifest order, up to order, so each at most once (`ran_nodup`).
Review: core -/
theorem any_order (g : Graph) (valid : g.Valid) (depfilesOK : g.DynOK sem) {order : List MEdge}
    (validOrder : ValidOrder g order) {st : St V} (reachable : Reachable sem g st) :
    (g.spec sem).Correct st.content (buildTrace sem order st).1.content ∧
      (buildTrace sem order st).2.Perm (ran sem g st) := by
  refine ⟨?_, dsl_same_edges sem g valid depfilesOK validOrder.1 validOrder.2 reachable⟩
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

end Mise.Headline
