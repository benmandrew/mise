import Mise.Model.Cmp
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
locations. `scripts/trusted.sh --pdf` builds `docs/headline.pdf`, which adds a
mechanical English translation of each statement and the source of every
definition. `scripts/check.sh` fails if either is out of date.

The statements share these hypotheses:

* `valid : g.Valid`, the decidable well-formedness check on the graph;
* `depfilesOK : g.DynOK sem`, that every depfile command reads only
  sources and the edge's own inputs. It holds for any graph without depfile
  rules (`Mise.Model.dynOK_static`).

`sem : Sem V` says what each command computes. It is a parameter, so the
theorems hold for every choice of command meanings.

The model has no failing commands: a run writes every output. The DSL
makes that hold by wrapping each command in a script that restores the old
outputs when the command fails or leaves an output missing. `wrapped_run`
shows the state after such a run is reachable, so the other theorems also
cover histories with failed commands.
-/

namespace Mise.Headline
open Mise Mise.Syntax Mise.Frontend Mise.Model

variable {V : Type} [Inhabited V] (sem : Sem V)

/-! ## Names used in the statements -/

/-- The edges of the manifest `mise` emits for `g`, as the Ninja model sees
them.
Gloss: the edges of the manifest for {g} -/
abbrev edges (g : Graph) : List MEdge := (emit g).medges

/-- `st` can arise from empty build and deps logs by any sequence of source
edits and of edges run or skipped as Ninja would. Full builds, builds of some
targets and interrupted builds are all such sequences.
Gloss: {st} can arise for {g} from empty logs by source edits and Ninja edge visits -/
abbrev Reachable (g : Graph) (st : St V) : Prop := Reach sem (edges g) st

/-- The state after one `ninja` run on the emitted manifest.
Gloss: the state after one `ninja` run for {g} from {st} -/
abbrev build (g : Graph) (st : St V) : St V := ninjaBuild sem (emit g) st

/-- The edges that one `ninja` run executes, in order.
Gloss: the edges one `ninja` run for {g} executes from {st} -/
abbrev ran (g : Graph) (st : St V) : List MEdge := (buildTrace sem (edges g) st).2

/-- No edge of the manifest writes `p`.
Gloss: no edge of the manifest for {g} writes {p} -/
abbrev IsSource (g : Graph) (p : Path) : Prop := ∀ e ∈ edges g, p ∉ e.outs

/-- `es` is an order a parallel Ninja could run the edges in: the same edges
as the manifest, where each edge reads no output of itself or of a later
edge.
Gloss: {es} is an order in which a parallel Ninja could run the edges for {g} -/
abbrev ValidOrder (g : Graph) (es : List MEdge) : Prop := es.Perm (edges g) ∧ Sched es

/-- `p` is an input Ninja checks for some output of `e` in state `st`: a
static input, or for a depfile edge a path its deps log entry records.
Gloss: {p} is an input Ninja checks for some output of {e} in {st} -/
abbrev Checks (st : St V) (e : MEdge) (p : Path) : Prop :=
  ∃ o ∈ e.outs, ∃ D, st.effIns e o = some D ∧ p ∈ D

/-! ## What the manifest means -/

/-- The text `mise` writes parses, under the parser model, to the manifest it
emitted, and that manifest, read through the model of Ninja's variable
evaluation, means the build the DSL describes. -/
theorem meaning (g : Graph) (valid : g.Valid) :
    parse (print (emit g)) = some (emit g) ∧ denote sem (emit g) = g.spec sem :=
  ⟨parse_print _ (emit_wellFormed g valid), denote_emit sem g valid⟩

/-- A build described by a valid graph has at most one correct result for
any sources. `Correct` is the correctness predicate of *Build Systems à la
Carte*: sources keep their values, and every target holds what its task
computes from the result. -/
theorem correct_unique (g : Graph) (valid : g.Valid) (depfilesOK : g.DynOK sem)
    {sources result₁ result₂ : Path → V} (correct₁ : (g.spec sem).Correct sources result₁)
    (correct₂ : (g.spec sem).Correct sources result₂) : result₁ = result₂ :=
  BuildSpec.correct_unique (g.acyclic sem valid depfilesOK) correct₁ correct₂

/-! ## Incremental builds -/

/-- After any history, one `ninja` run leaves correct contents for the
current sources. -/
theorem build_correct (g : Graph) (valid : g.Valid) (depfilesOK : g.DynOK sem) {st : St V}
    (reachable : Reachable sem g st) :
    (g.spec sem).Correct st.content (build sem g st).content := by
  have hc := (reach_sound sem (sched_emit g valid) (reads_emit sem g valid depfilesOK) reachable).1
  rwa [denote_emit sem g valid] at hc

/-- After any history, a second `ninja` run executes nothing and changes
nothing. -/
theorem rebuild_noop (g : Graph) (valid : g.Valid) (depfilesOK : g.DynOK sem) {st : St V}
    (reachable : Reachable sem g st) :
    ran sem g (build sem g st) = [] ∧ build sem g (build sem g st) = build sem g st := by
  have hi := (dsl_sound sem g valid depfilesOK reachable).2
  have h1 := congrArg Prod.snd hi
  have h2 := congrArg Prod.fst hi
  exact ⟨h1, h2⟩

/-- One `ninja` run executes each edge at most once. -/
theorem ran_nodup (g : Graph) (valid : g.Valid) (st : St V) : (ran sem g st).Nodup :=
  trace_nodup_sched sem _ st (sched_emit g valid)

/-- Build, edit some sources, build again. Every edge `e` the second build
runs has a reason: an input `p` that Ninja checks for it, whose mtime is
newer than anything the first build left, and that was either among the
`edits` or written by an edge that ran earlier in the second build. An edge
whose inputs were left untouched, including by a `restat` edge that kept its
output, does not run. -/
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

/-- **Early cutoff.** A `restat` edge that keeps every output changes no
other edge's dirtiness, so nothing is rebuilt on its account. -/
theorem restat_cutoff {st : St V} {e e' : MEdge} (disjoint : Disjoint e'.outs e.outs)
    (allKept : ∀ o ∈ e.outs, st.kept sem e o = true) : (st.run sem e).dirty e' = st.dirty e' :=
  Mise.Model.restat_cutoff sem disjoint allKept

/-! ## Parallel builds -/

/-- After any history, running the edges in any valid `order` leaves the same
correct contents and runs the same edges, each at most once, as manifest
order. -/
theorem any_order (g : Graph) (valid : g.Valid) (depfilesOK : g.DynOK sem) {order : List MEdge}
    (validOrder : ValidOrder g order) {st : St V} (reachable : Reachable sem g st) :
    (g.spec sem).Correct st.content (buildTrace sem order st).1.content ∧
      (buildTrace sem order st).2.Perm (ran sem g st) := by
  refine ⟨?_, dsl_same_edges sem g valid depfilesOK validOrder.1 validOrder.2 reachable⟩
  rw [(dsl_parallel sem g valid depfilesOK validOrder.1 validOrder.2 reachable).1]
  exact BuildSpec.cleanBuild_correct _ _

/-! ## Failed commands -/

/-- **Failed commands.** The DSL wraps every command, unless its rule opts
out, in a script that `Mise.Model.script` models. The command leaves
`written` at the outputs, writing what `sem` says (`writesSem`), and exits 0
when `exitedZero`. If it fails or leaves an output missing, the state after
the run is the state before it; otherwise the run is the model's run. In both
cases the state after the run is reachable under `Sem.withCmp`, which keeps a
`restat` output exactly when `cmp` finds it unchanged, so the theorems above
apply to it. The script needs that no output is another output's `.mise-old`
file (`asideNotOutput`) and that no `.mise-old` file of an output exists
(`asideMissing`). -/
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
