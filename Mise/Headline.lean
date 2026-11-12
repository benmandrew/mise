import Mise.Model.Dsl
import Mise.Model.Minimal
import Mise.Model.Parallel
import Mise.Syntax.RoundTrip

/-!
# Headline theorems, restated for reading

This file is the place to start when checking what `mise` proves. Every
theorem here restates a result proved elsewhere, in terms of the DSL graph
`g` that a user writes, and each proof is one or two lines that apply the
original. Lean checks the proofs, so a reader needs to check only two
things:

1. that each statement below says what its docstring says, and
2. that the definitions the statements use mean what their names suggest.

`docs/trusted.md` lists those definitions for every theorem, with their
locations. `scripts/check.sh` fails if that list is out of date.

The statements share these hypotheses:

* `hg : g.Valid`, the decidable well-formedness check on the graph;
* `hd : g.DynOK sem`, that every depfile command reads only sources and the
  edge's own inputs. It holds for any graph without depfile rules
  (`Mise.Model.dynOK_static`).

`sem : Sem V` says what each command computes. It is a parameter, so the
theorems hold for every choice of command meanings.
-/

namespace Mise.Headline
open Mise Mise.Syntax Mise.Frontend Mise.Model

variable {V : Type} [Inhabited V] (sem : Sem V)

/-! ## Names used in the statements -/

/-- The edges of the manifest `mise` emits for `g`, as the Ninja model sees
them. -/
abbrev edges (g : Graph) : List MEdge := (emit g).medges

/-- `st` can arise from empty build and deps logs by any sequence of source
edits and of edges run or skipped as Ninja would. Full builds, builds of some
targets and interrupted builds are all such sequences. -/
abbrev Reachable (g : Graph) (st : St V) : Prop := Reach sem (edges g) st

/-- The state after one `ninja` run on the emitted manifest. -/
abbrev build (g : Graph) (st : St V) : St V := ninjaBuild sem (emit g) st

/-- The edges that one `ninja` run executes, in order. -/
abbrev ran (g : Graph) (st : St V) : List MEdge := (buildTrace sem (edges g) st).2

/-- No edge of the manifest writes `p`. -/
abbrev IsSource (g : Graph) (p : Path) : Prop := ∀ e ∈ edges g, p ∉ e.outs

/-- `es` is an order a parallel Ninja could run the edges in: the same edges
as the manifest, where each edge reads no output of itself or of a later
edge. -/
abbrev ValidOrder (g : Graph) (es : List MEdge) : Prop := es.Perm (edges g) ∧ Sched es

/-- `p` is an input Ninja checks for some output of `e` in state `st`: a
static input, or for a depfile edge a path its deps log entry records. -/
abbrev Checks (st : St V) (e : MEdge) (p : Path) : Prop :=
  ∃ o ∈ e.outs, ∃ D, st.effIns e o = some D ∧ p ∈ D

/-! ## What the manifest means -/

/-- The text `mise` writes parses, under the parser model, to the manifest it
emitted, and that manifest, read through the model of Ninja's variable
evaluation, means the build the DSL describes. -/
theorem meaning (g : Graph) (hg : g.Valid) :
    parse (print (emit g)) = some (emit g) ∧ denote sem (emit g) = g.spec sem :=
  ⟨parse_print _ (emit_wellFormed g hg), denote_emit sem g hg⟩

/-- A build described by a valid graph has at most one correct result for
any sources. `Correct` is the correctness predicate of *Build Systems à la
Carte*: sources keep their values, and every target holds what its task
computes from the result. -/
theorem correct_unique (g : Graph) (hg : g.Valid) (hd : g.DynOK sem) {S R₁ R₂ : Path → V}
    (h₁ : (g.spec sem).Correct S R₁) (h₂ : (g.spec sem).Correct S R₂) : R₁ = R₂ :=
  BuildSpec.correct_unique (g.acyclic sem hg hd) h₁ h₂

/-! ## Incremental builds -/

/-- After any history, one `ninja` run leaves correct contents for the
current sources. -/
theorem build_correct (g : Graph) (hg : g.Valid) (hd : g.DynOK sem) {st : St V}
    (h : Reachable sem g st) : (g.spec sem).Correct st.content (build sem g st).content := by
  have hc := (reach_sound sem (sched_emit g hg) (reads_emit sem g hg hd) h).1
  rwa [denote_emit sem g hg] at hc

/-- After any history, a second `ninja` run executes nothing and changes
nothing. -/
theorem rebuild_noop (g : Graph) (hg : g.Valid) (hd : g.DynOK sem) {st : St V}
    (h : Reachable sem g st) :
    ran sem g (build sem g st) = [] ∧ build sem g (build sem g st) = build sem g st := by
  have hi := (dsl_sound sem g hg hd h).2
  have h1 := congrArg Prod.snd hi
  have h2 := congrArg Prod.fst hi
  exact ⟨h1, h2⟩

/-- One `ninja` run executes each edge at most once. -/
theorem ran_nodup (g : Graph) (hg : g.Valid) (st : St V) : (ran sem g st).Nodup :=
  trace_nodup_sched sem _ st (sched_emit g hg)

/-- Build, edit some sources, build again. Every edge the second build runs
has a reason: an input `p` that Ninja checks for it, whose mtime is newer
than anything the first build left, and that was either edited or written by
an edge that ran earlier in the second build. An edge whose inputs were left
untouched, including by a `restat` edge that kept its output, does not
run. -/
theorem rebuild_minimal (g : Graph) (hg : g.Valid) (hd : g.DynOK sem) {st₀ : St V}
    (h : Reachable sem g st₀) (E : List (Path × V)) (hE : ∀ pv ∈ E, IsSource g pv.1) {e : MEdge}
    (he : e ∈ ran sem g ((build sem g st₀).edits E)) :
    ∃ pre post, edges g = pre ++ e :: post ∧ ∃ p, Checks (build sem g st₀) e p ∧
      (build sem g st₀).clock < (buildTrace sem pre ((build sem g st₀).edits E)).1.mtime p ∧
      (p ∈ E.map (·.1) ∨ ∃ e' ∈ (buildTrace sem pre ((build sem g st₀).edits E)).2, p ∈ e'.outs) := by
  have hclean := (dsl_parallel sem g hg hd (List.Perm.refl _) (sched_emit g hg) h).2
  obtain ⟨pre, post, hsplit, o, ho, D, hD, p, hp, hnew, hwhy⟩ :=
    build_minimal_clean sem (sched_emit g hg) hclean E hE he
  exact ⟨pre, post, hsplit, p, ⟨o, ho, D, hD, hp⟩, hnew, hwhy⟩

/-- **Early cutoff.** A `restat` edge that keeps every output changes no
other edge's dirtiness, so nothing is rebuilt on its account. -/
theorem restat_cutoff {st : St V} {e e' : MEdge} (hdis : Disjoint e'.outs e.outs)
    (hk : ∀ o ∈ e.outs, st.kept sem e o = true) : (st.run sem e).dirty e' = st.dirty e' :=
  Mise.Model.restat_cutoff sem hdis hk

/-! ## Parallel builds -/

/-- After any history, running the edges in any valid order leaves the same
correct contents and runs the same edges, each at most once, as manifest
order. -/
theorem any_order (g : Graph) (hg : g.Valid) (hd : g.DynOK sem) {es : List MEdge}
    (ho : ValidOrder g es) {st : St V} (h : Reachable sem g st) :
    (g.spec sem).Correct st.content (buildTrace sem es st).1.content ∧
      (buildTrace sem es st).2.Perm (ran sem g st) := by
  refine ⟨?_, dsl_same_edges sem g hg hd ho.1 ho.2 h⟩
  rw [(dsl_parallel sem g hg hd ho.1 ho.2 h).1]
  exact BuildSpec.cleanBuild_correct _ _

end Mise.Headline
