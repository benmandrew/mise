import Mise.Model.Dsl
import Mise.Model.Minimal

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

`parallel_same_edges` shows that the two orders also run the same edges,
each at most once. An edge runs when it was dirty before the build or when
an input it checks was written during the build. That input is a source, or
the output of an earlier edge in both orders, since both are schedules. The
output was written when its edge ran and did not keep it, and with `restat`
the keep depends only on the edge's old output and the contents it reads,
which the two orders share. So early cutoff is the same in both orders, and
induction along the manifest order gives the same edges.
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

/-! ## Same edges run -/

/-- `St.kept` with the contents the command reads given separately: a
`restat` run of `e` against contents `c` leaves output `o` of `st` untouched. -/
def St.keptWith (st : St V) (c : Path → V) (e : MEdge) (o : Path) : Bool :=
  e.restat && match st.fs o with
    | some (old, _) => sem.keep old (((e.task sem).run c).getD (e.outs.idxOf o) default)
    | none => false

/-- An edge a build runs has an output. -/
theorem trace_outs {l : List MEdge} {s : St V} {e : MEdge} (h : e ∈ (buildTrace sem l s).2) :
    e.outs ≠ [] := by
  obtain ⟨_, _, _, hd⟩ := trace_split sem l s h
  intro he
  simp [St.dirty, he] at hd

/-- In a schedule, the first edge runs exactly when it is dirty on its turn. -/
theorem trace_head {a : MEdge} {l : List MEdge} (hs : Sched (a :: l)) (s : St V) :
    a ∈ (buildTrace sem (a :: l) s).2 ↔ s.dirty a = true := by
  have hn : a ∉ (buildTrace sem l (s.step sem a)).2 := fun h => by
    obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ (trace_outs sem h)
    exact (hs.2.1 a ((trace_sublist sem l _).subset h)).2 o ho ho
  by_cases hd : s.dirty a = true <;> simp [buildTrace, hd, hn]

theorem trace_tail {a e : MEdge} {l : List MEdge} (hne : e ≠ a) (s : St V) :
    e ∈ (buildTrace sem (a :: l) s).2 ↔ e ∈ (buildTrace sem l (s.step sem a)).2 := by
  by_cases hd : s.dirty a = true <;> simp [buildTrace, hd, hne]

/-- Each edge of a schedule runs at most once, edges without outputs
included, since those never run. -/
theorem trace_nodup_sched : ∀ (l : List MEdge) (s : St V), Sched l → (buildTrace sem l s).2.Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, s, hs => by
    have ih := trace_nodup_sched l (s.step sem a) hs.tail
    simp only [buildTrace]
    split
    · refine List.nodup_cons.mpr ⟨fun h => ?_, ih⟩
      obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ (trace_outs sem h)
      exact (hs.2.1 a ((trace_sublist sem l _).subset h)).2 o ho ho
    · exact ih

namespace St

/-- During a build from `st`, an output untouched since `st` is dirty when it
was dirty in `st`, or when an input Ninja checks was written since. -/
theorem outDirty_iff_written {st s : St V} (hf : st.Fresh) {W : Path → Prop} (htr : Track st s W)
    {e : MEdge} {o : Path} (h1 : s.fs o = st.fs o) (h2 : s.log o = st.log o) (h3 : s.deps o = st.deps o) :
    s.outDirty e o = true ↔ st.outDirty e o = true ∨
      ∃ D, st.effIns e o = some D ∧ ∃ p ∈ D, st.clock < s.mtime p := by
  have he : s.effIns e o = st.effIns e o := by simp only [effIns, h3]
  have hmono : ∀ D : List Path, st.newest D ≤ s.newest D := fun D => st.newest_le fun p hp => by
    refine Nat.le_trans ?_ (s.le_newest hp)
    rcases htr.2 p with h | ⟨h, -⟩
    · simp only [mtime, h]; exact Nat.le_refl _
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (mtime_le_clock hf p) h)
  constructor
  · intro hd
    cases hst : st.outDirty e o
    · right
      obtain ⟨-, -, -, D, -, -, a3, -, -⟩ := outDirty_false_iff.mp hst
      refine ⟨D, a3, Classical.byContradiction fun hc => ?_⟩
      have : s.outDirty e o = st.outDirty e o := outDirty_congr h1 h2 h3 fun D' hD' p hp => by
        rw [he, a3, Option.some.injEq] at hD'
        subst hD'
        rcases htr.2 p with h | ⟨h, -⟩
        · exact h
        · exact absurd ⟨p, hp, h⟩ hc
      rw [this, hst] at hd; cases hd
    · exact .inl rfl
  · intro hd
    cases hs : s.outDirty e o
    · obtain ⟨v, t, lt, D, a1, a2, a3, a4, a5⟩ := outDirty_false_iff.mp hs
      rcases hd with hd | ⟨D', hD', p, hp, hlt⟩
      · have : st.outDirty e o = false := outDirty_false_iff.mpr
          ⟨v, t, lt, D, by rw [← h1]; exact a1, by rw [← h2]; exact a2, by rw [← he]; exact a3,
            fun hr => Nat.le_trans (hmono D) (a4 hr), Nat.le_trans (hmono D) a5⟩
        rw [this] at hd; cases hd
      · rw [he, hD', Option.some.injEq] at a3
        subst a3
        have hl : lt ≤ st.clock := hf.2 o e.cmd lt (by rw [← h2]; exact a2)
        have := s.le_newest hp
        omega
    · rfl

theorem dirty_iff_written {st s : St V} (hf : st.Fresh) {W : Path → Prop} (htr : Track st s W)
    {e : MEdge} (hout : Agree s st e.outs) :
    s.dirty e = true ↔ st.dirty e = true ∨
      ∃ o ∈ e.outs, ∃ D, st.effIns e o = some D ∧ ∃ p ∈ D, st.clock < s.mtime p := by
  have key := fun o (ho : o ∈ e.outs) => outDirty_iff_written (e := e) hf htr (hout o ho).1 (hout o ho).2.1 (hout o ho).2.2
  simp only [dirty, List.any_eq_true]
  constructor
  · rintro ⟨o, ho, hd⟩
    rcases (key o ho).mp hd with h | h
    · exact .inl ⟨o, ho, h⟩
    · exact .inr ⟨o, ho, h⟩
  · rintro (⟨o, ho, h⟩ | ⟨o, ho, h⟩)
    · exact ⟨o, ho, (key o ho).mpr (.inl h)⟩
    · exact ⟨o, ho, (key o ho).mpr (.inr h)⟩

end St

/-- During a build from `st`, an edge runs exactly when it was dirty in `st`
or an input Ninja checks for one of its outputs ends the build newer than
`st.clock`. -/
theorem trace_mem_iff : ∀ (l : List MEdge) {st s : St V} {W : Path → Prop}, Sched l → st.Fresh →
    DepsOK l st → St.Track st s W → (∀ e ∈ l, St.Agree s st e.outs) → ∀ e ∈ l,
    (e ∈ (buildTrace sem l s).2 ↔ st.dirty e = true ∨ ∃ o ∈ e.outs, ∃ D, st.effIns e o = some D ∧
      ∃ p ∈ D, st.clock < (buildTrace sem l s).1.mtime p)
  | [], _, _, _, _, _, _, _, _, e, he => by simp at he
  | a :: l, st, s, W, hs, hf, hdo, htr, hag, e, he => by
    by_cases hea : e = a
    · subst hea
      rw [trace_head sem hs s, St.dirty_iff_written hf htr (hag e (by simp))]
      have hfin : ∀ o ∈ e.outs, ∀ D, st.effIns e o = some D → ∀ p ∈ D,
          (buildTrace sem (e :: l) s).1.mtime p = s.mtime p := by
        intro o ho D hD p hp
        have hal := effIns_allowed hdo (by simp) ho hD p hp
        simp only [buildTrace, St.mtime]
        rw [(build_other sem l (allowed_later hs hal)).1, (St.step_other sem (allowed_self hs (by simp) hal)).1]
      constructor <;> rintro (h | ⟨o, ho, D, hD, p, hp, hlt⟩)
      · exact .inl h
      · exact .inr ⟨o, ho, D, hD, p, hp, by rw [hfin o ho D hD p hp]; exact hlt⟩
      · exact .inl h
      · exact .inr ⟨o, ho, D, hD, p, hp, by rw [← hfin o ho D hD p hp]; exact hlt⟩
    · have he' : e ∈ l := by simpa [hea] using he
      have hsub : ∀ e ∈ l, e ∈ a :: l := fun e he => by simp [he]
      rw [trace_tail sem hea]
      exact trace_mem_iff l hs.tail hf (depsOK_mono hsub hdo) (htr.step sem a) (fun e' he' o ho => by
        obtain ⟨a1, a2, a3⟩ := St.step_other sem (st := s) (e := a) fun hoa => (hs.2.1 e' he').2 o hoa ho
        obtain ⟨b1, b2, b3⟩ := hag e' (hsub e' he') o ho
        exact ⟨a1.trans b1, a2.trans b2, a3.trans b3⟩) e he'

/-- During a build from `st`, an output ends the build newer than `st.clock`
exactly when its edge ran and did not keep it. Whether a run keeps it
depends only on the final contents. -/
theorem written_iff : ∀ (l : List MEdge) {st s : St V} {W : Path → Prop}, Sched l → Reads sem l →
    st.Fresh → St.Track st s W → (∀ e ∈ l, St.Agree s st e.outs) → ∀ a ∈ l, ∀ p ∈ a.outs,
    (st.clock < (buildTrace sem l s).1.mtime p ↔
      a ∈ (buildTrace sem l s).2 ∧ st.keptWith sem (buildTrace sem l s).1.content a p = false)
  | [], _, _, _, _, _, _, _, _, a, ha, _, _ => by simp at ha
  | b :: l, st, s, W, hs, hr, hf, htr, hag, a, ha, p, hp => by
    by_cases hab : a = b
    · subst hab
      rw [trace_head sem hs s]
      have hsp := (hag a (by simp) p hp).1
      have hfin : (buildTrace sem (a :: l) s).1.fs p = (s.step sem a).fs p :=
        (build_other sem l fun e' he' hpe => (hs.2.1 e' he').2 p hp hpe).1
      have hk : s.kept sem a p = st.keptWith sem (buildTrace sem (a :: l) s).1.content a p := by
        have hrun : (a.task sem).run s.content = (a.task sem).run (buildTrace sem (a :: l) s).1.content :=
          (Task.run_eq_of_agree _ _ _ fun k hk => by
            have hal := deps_allowed sem hr (by simp) _ k hk
            simp only [St.content]
            rw [show (buildTrace sem (a :: l) s).1.fs k = s.fs k from
              (build_other sem l (allowed_later hs hal)).1.trans
                (St.step_other sem (allowed_self hs (by simp) hal)).1]).1
        simp only [St.kept, St.keptWith, St.outVal, hrun, hsp]; rfl
      have hle := St.mtime_le_clock hf p
      have hcl := htr.1
      unfold St.step at hfin
      by_cases hd : s.dirty a = true
      · rw [ite_eq_left hd] at hfin
        simp only [hd, true_and, ← hk]
        cases hkp : s.kept sem a p
        · have : (buildTrace sem (a :: l) s).1.mtime p = s.clock + 1 := by
            simp [St.mtime, hfin, St.run, hp, hkp]
          rw [this]; simp only [iff_true]; omega
        · have : (buildTrace sem (a :: l) s).1.mtime p = st.mtime p := by
            simp [St.mtime, hfin, St.run, hp, hkp, hsp]
          rw [this]; simp only [Bool.true_eq_false, iff_false]; omega
      · rw [ite_eq_right hd] at hfin
        have : (buildTrace sem (a :: l) s).1.mtime p = st.mtime p := by simp only [St.mtime, hfin, hsp]
        simp only [hd, Bool.false_eq_true, false_and, iff_false]; rw [this]; omega
    · have ha' : a ∈ l := by simpa [hab] using ha
      have hsub : ∀ e ∈ l, e ∈ b :: l := fun e he => by simp [he]
      rw [trace_tail sem hab]
      exact written_iff l hs.tail (reads_mono sem hsub hr) hf (htr.step sem b) (fun e' he' o ho => by
        obtain ⟨a1, a2, a3⟩ := St.step_other sem (st := s) (e := b) fun hob => (hs.2.1 e' he').2 o hob ho
        obtain ⟨b1, b2, b3⟩ := hag e' (hsub e' he') o ho
        exact ⟨a1.trans b1, a2.trans b2, a3.trans b3⟩) a ha' p hp

/-- **Same edges.** Under the invariant, building the edges in any order
consistent with the dependency order runs the same edges as building them in
manifest order, each at most once: the two traces are permutations of each
other. -/
theorem parallel_same_edges {es es' : List MEdge} (hs : Sched es) (hr : Reads sem es) (hp : es'.Perm es)
    (hs' : Sched es') {st : St V} (h : Inv sem es st) :
    (buildTrace sem es' st).2.Perm (buildTrace sem es st).2 := by
  have hmem : ∀ e, e ∈ es ↔ e ∈ es' := fun e => hp.mem_iff.symm
  have hr' : Reads sem es' := reads_mono sem (fun e he => (hmem e).2 he) hr
  have h' : Inv sem es' st := inv_same sem hmem h
  have hc := (parallel_equiv sem hs hr hp hs' h).1
  have htr := St.Track.refl st fun _ => False
  have hag : ∀ (l : List MEdge), ∀ e ∈ l, St.Agree st st e.outs := fun _ _ _ _ _ => ⟨rfl, rfl, rfl⟩
  have B1 := trace_mem_iff sem es' hs' h'.1 h'.2.1 htr (hag es')
  have B2 := trace_mem_iff sem es hs h.1 h.2.1 htr (hag es)
  have C1 := written_iff sem es' hs' hr' h.1 htr (hag es')
  have C2 := written_iff sem es hs hr h.1 htr (hag es)
  -- A path is written in one build exactly when it is written in the other,
  -- provided its producer, if any, runs in both or in neither.
  have hw : ∀ q, (∀ a ∈ es, q ∈ a.outs → (a ∈ (buildTrace sem es' st).2 ↔ a ∈ (buildTrace sem es st).2)) →
      (st.clock < (buildTrace sem es' st).1.mtime q ↔ st.clock < (buildTrace sem es st).1.mtime q) := by
    intro q hq
    by_cases hex : ∃ a ∈ es, q ∈ a.outs
    · obtain ⟨a, ha, hqa⟩ := hex
      rw [C1 a ((hmem a).1 ha) q hqa, C2 a ha q hqa, hc, hq a ha hqa]
    · have hn : ∀ a ∈ es, q ∉ a.outs := fun a ha hqa => hex ⟨a, ha, hqa⟩
      simp only [St.mtime, (build_other sem es hn).1,
        (build_other sem es' fun a ha => hn a ((hmem a).2 ha)).1]
  have hind : ∀ n i : Nat, i < n → ∀ a, es[i]? = some a →
      (a ∈ (buildTrace sem es' st).2 ↔ a ∈ (buildTrace sem es st).2) := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi a hai
      have ha : a ∈ es := List.mem_of_getElem? hai
      have hin : ∀ o ∈ a.outs, ∀ D, st.effIns a o = some D → ∀ q ∈ D,
          (st.clock < (buildTrace sem es' st).1.mtime q ↔ st.clock < (buildTrace sem es st).1.mtime q) := by
        intro o ho D hD q hq
        refine hw q fun a' ha' hqa' => ?_
        obtain ⟨i', hai'⟩ := List.mem_iff_getElem?.mp ha'
        rcases effIns_allowed h.2.1 ha ho hD q hq with hal | hal
        · exact absurd hqa' (hal a' ha')
        · exact ih i' (by have := Sched.idx_lt hs hai hai' hal hqa'; omega) a' hai'
      rw [B1 a ((hmem a).1 ha), B2 a ha]
      constructor <;> rintro (hd | ⟨o, ho, D, hD, q, hq, hlt⟩)
      · exact .inl hd
      · exact .inr ⟨o, ho, D, hD, q, hq, (hin o ho D hD q hq).1 hlt⟩
      · exact .inl hd
      · exact .inr ⟨o, ho, D, hD, q, hq, (hin o ho D hD q hq).2 hlt⟩
  refine (List.perm_ext_iff_of_nodup (trace_nodup_sched sem es' st hs')
    (trace_nodup_sched sem es st hs)).mpr fun e => ?_
  by_cases he : e ∈ es
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp he
    exact hind (i + 1) i (Nat.lt_succ_self i) e hi
  · have h1 : e ∉ (buildTrace sem es' st).2 := fun h1 =>
      he ((hmem e).2 ((trace_sublist sem es' st).subset h1))
    have h2 : e ∉ (buildTrace sem es st).2 := fun h2 => he ((trace_sublist sem es st).subset h2)
    simp only [h1, h2]

/-- The same edges run after any history from empty logs. -/
theorem parallel_same_edges_reach {es es' : List MEdge} (hs : Sched es) (hr : Reads sem es)
    (hp : es'.Perm es) (hs' : Sched es') {st : St V} (h : Reach sem es st) :
    (buildTrace sem es' st).2.Perm (buildTrace sem es st).2 :=
  parallel_same_edges sem hs hr hp hs' (inv_of_reach sem hs hr h)

/-- For an emitted manifest: any order of its edges consistent with the
dependency order runs the same edges as manifest order. -/
theorem dsl_same_edges (g : Graph) (hg : g.Valid) (hd : g.DynOK sem) {es' : List MEdge}
    (hp : es'.Perm (emit g).medges) (hs' : Sched es') {st : St V} (h : Reach sem (emit g).medges st) :
    (buildTrace sem es' st).2.Perm (buildTrace sem (emit g).medges st).2 :=
  parallel_same_edges_reach sem (sched_emit g hg) (reads_emit sem g hg hd) hp hs' h

end Mise.Model

