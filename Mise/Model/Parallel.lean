import Mise.Model.Dsl

/-!
# Stage 7: parallel equivalence

Ninja runs independent commands at the same time. A command reads its
inputs when it starts and its outputs appear when it finishes, and Ninja
starts a command only after every command producing one of its inputs has
finished. Two commands that overlap therefore never read what the other
writes, and they write disjoint outputs, so a parallel run has the effect of
running the commands one at a time in order of start time. That order lists
every producer before the commands that read its outputs, which makes it a
`Sched`: a permutation of the manifest's edges consistent with the
dependency order.

`parallel_equiv` shows that every such order gives the same contents as the
manifest order and leaves every edge clean. The proof needs no
step-by-step comparison of the two runs. Both results are correct for the
same specification, and a schedule makes that specification acyclic
(`schedAcyclic`), so `correct_unique` from Stage 2 makes them equal.

The two final states agree on contents and on which edges are dirty, which
is all that later builds observe through the theorems of Stages 5 and 6.
They differ in mtimes and log times, because the clock advances in the order
commands run.
-/

namespace Mise.Model
open Mise Mise.Syntax Mise.Frontend

variable {V : Type} [Inhabited V] (sem : Sem V)

/-! ## Same edges, another order -/

theorem inv_same {es es' : List MEdge} (h : ∀ e, e ∈ es ↔ e ∈ es') {st : St V} (hi : Inv sem es st) :
    Inv sem es' st :=
  ⟨hi.1, depsOK_mono (fun e he => (h e).2 he) hi.2.1, fun e he => hi.2.2 e ((h e).2 he)⟩

/-! ## A schedule's specification is acyclic -/

/-- One more than the position of the edge producing `k`; sources rank 0. -/
def schedRank (es : List MEdge) (k : Path) : Nat :=
  match findOut MEdge.outs k es with
  | some (i, _) => i + 1
  | none => 0

/-- In a schedule, an edge's producers come before it. -/
theorem Sched.idx_lt : ∀ {es : List MEdge} {i i' : Nat} {e a : MEdge} {j : Path}, Sched es →
    es[i]? = some e → es[i']? = some a → j ∈ e.reads → j ∈ a.outs → i' < i
  | [], _, _, _, _, _, _, h, _, _, _ => by simp at h
  | b :: es, 0, 0, e, a, j, hs, he, ha, hj, hja => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he ha
    subst he; subst ha
    exact absurd hja (hs.1 j hj)
  | b :: es, 0, i' + 1, e, a, j, hs, he, ha, hj, hja => by
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at he ha
    subst he
    exact absurd hja ((hs.2.1 a (List.mem_of_getElem? ha)).1 j hj)
  | _ :: _, _ + 1, 0, _, _, _, _, _, _, _, _ => Nat.succ_pos _
  | b :: es, i + 1, i' + 1, e, a, j, hs, he, ha, hj, hja => by
    simp only [List.getElem?_cons_succ] at he ha
    exact Nat.succ_lt_succ (Sched.idx_lt hs.2.2 he ha hj hja)

/-- The specification of a schedule is acyclic, with edge positions as
ranks, provided every depfile command reads only allowed paths. -/
def schedAcyclic {es : List MEdge} (hs : Sched es) (hr : Reads sem es) : (specOf sem es).Acyclic where
  rank := schedRank es
  fetches k hk := by
    simp only [specOf] at hk ⊢
    cases hf : findOut MEdge.outs k es with
    | none => simp [hf] at hk
    | some p =>
      obtain ⟨i, e⟩ := p
      have hrk : schedRank es k = i + 1 := by simp [schedRank, hf]
      obtain ⟨hei, -⟩ := findOut_some hf
      have hlt : ∀ j, Allowed es e j → schedRank es j < schedRank es k := by
        intro j hj
        rw [hrk]
        unfold schedRank
        cases hf' : findOut MEdge.outs j es with
        | none => exact Nat.succ_pos i
        | some q =>
          obtain ⟨i', a⟩ := q
          obtain ⟨hai, hja⟩ := findOut_some hf'
          rcases hj with hj | hj
          · exact absurd (by simpa using hja) (hj a (List.mem_of_getElem? hai))
          · exact Nat.succ_lt_succ (Sched.idx_lt hs hei hai hj (by simpa using hja))
      exact outTask_fetchesOnly (cmdTask_fetchesOnly sem _ _ _
        (fun _ j hj => hlt j (.inr (List.mem_append_left _ hj)))
        (fun hd => (hr e (List.mem_of_getElem? hei) hd).mono hlt)) _

/-! ## Parallel equivalence -/

/-- After a build under the invariant, every edge is consistent. -/
theorem build_consistent {es : List MEdge} (hs : Sched es) (hr : Reads sem es) {st : St V}
    (h : Inv sem es st) : ∀ e ∈ es, (buildTrace sem es st).1.Consistent sem e :=
  fun e he => (build_inv sem hs hr es (fun _ h => h) h).2.2 e he (build_clean sem es hs hr h.1 h.2.1 e he)

/-- **Parallel equivalence.** Under the invariant, building the edges in
any order consistent with the dependency order gives the same contents as
building them in manifest order, and leaves every edge clean. -/
theorem parallel_equiv {es es' : List MEdge} (hs : Sched es) (hr : Reads sem es) (hp : es'.Perm es)
    (hs' : Sched es') {st : St V} (h : Inv sem es st) :
    (buildTrace sem es' st).1.content = (buildTrace sem es st).1.content ∧
      ∀ e ∈ es, (buildTrace sem es' st).1.dirty e = false := by
  have hmem : ∀ e, e ∈ es ↔ e ∈ es' := fun e => hp.mem_iff.symm
  have hr' : Reads sem es' := reads_mono sem (fun e he => (hmem e).2 he) hr
  have h' : Inv sem es' st := inv_same sem hmem h
  have c1 : (specOf sem es).Correct st.content (buildTrace sem es' st).1.content :=
    correct_of_consistent sem (fun e he => build_consistent sem hs' hr' h' e ((hmem e).1 he)) _
      fun k hk => by
        simp only [St.content,
          (build_other sem es' fun e he => source_not_out sem hk e ((hmem e).2 he)).1]
  have c2 : (specOf sem es).Correct st.content (buildTrace sem es st).1.content :=
    correct_of_consistent sem (build_consistent sem hs hr h) _
      fun k hk => by simp only [St.content, (build_other sem es (source_not_out sem hk)).1]
  exact ⟨BuildSpec.correct_unique (schedAcyclic sem hs hr) c1 c2,
    fun e he => build_clean sem es' hs' hr' h'.1 h'.2.1 e ((hmem e).1 he)⟩

/-- Parallel equivalence after any history from empty logs. -/
theorem parallel_equiv_reach {es es' : List MEdge} (hs : Sched es) (hr : Reads sem es) (hp : es'.Perm es)
    (hs' : Sched es') {st : St V} (h : Reach sem es st) :
    (buildTrace sem es' st).1.content = (buildTrace sem es st).1.content ∧
      ∀ e ∈ es, (buildTrace sem es' st).1.dirty e = false :=
  parallel_equiv sem hs hr hp hs' (inv_of_reach sem hs hr h)

/-- For an emitted manifest: any order of its edges consistent with the
dependency order builds the clean build of the DSL's meaning. -/
theorem dsl_parallel (g : Graph) (hg : g.Valid) (hd : g.DynOK sem) {es' : List MEdge}
    (hp : es'.Perm (emit g).medges) (hs' : Sched es') {st : St V} (h : Reach sem (emit g).medges st) :
    (buildTrace sem es' st).1.content = BuildSpec.cleanBuild (g.acyclic sem hg hd) st.content ∧
      ∀ e ∈ (emit g).medges, (buildTrace sem es' st).1.dirty e = false := by
  obtain ⟨hc, hclean⟩ := parallel_equiv_reach sem (sched_emit g hg) (reads_emit sem g hg hd) hp hs' h
  exact ⟨hc.trans (dsl_sound sem g hg hd h).1, hclean⟩

end Mise.Model
