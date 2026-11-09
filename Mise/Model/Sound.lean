import Mise.Model.Basic

/-!
# Stage 5: incremental soundness of the Ninja model

The proofs rest on the invariant `Inv`: every mtime is at most the clock,
and every edge Ninja would skip is consistent. Running any edge and editing
any source preserve `Inv`. A full pass in schedule order leaves every edge
clean, and a clean edge under `Inv` is consistent, so the contents are
correct.
-/

set_option linter.unusedSectionVars false

namespace Mise.Model
open Mise Mise.Syntax Mise.Frontend

variable {V : Type} [Inhabited V] (exec : String → List V → List V)

theorem any_congr {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) : l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.any_cons, h a (by simp), ih fun b hb => h b (by simp [hb])]

theorem Disjoint.symm {a b : List Path} (h : Disjoint a b) : Disjoint b a := fun p hb ha => h p ha hb

namespace St

/-! ## Frames -/

theorem newest_congr {st st' : St V} {ps : List Path} (h : ∀ p ∈ ps, st.fs p = st'.fs p) :
    st.newest ps = st'.newest ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [newest, mtime, h p (by simp), ih fun q hq => h q (by simp [hq])]

theorem le_newest (st : St V) {p : Path} {ps : List Path} (h : p ∈ ps) : st.mtime p ≤ st.newest ps := by
  induction ps with
  | nil => simp at h
  | cons q ps ih =>
    simp only [List.mem_cons] at h
    simp only [newest]
    rcases h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem newest_le (st : St V) {ps : List Path} {b : Nat} (h : ∀ p ∈ ps, st.mtime p ≤ b) :
    st.newest ps ≤ b := by
  induction ps with
  | nil => exact Nat.zero_le _
  | cons q ps ih => exact Nat.max_le.mpr ⟨h q (by simp), ih fun p hp => h p (by simp [hp])⟩

theorem mtime_le_clock {st : St V} (hf : st.Fresh) (p : Path) : st.mtime p ≤ st.clock := by
  unfold mtime
  cases h : st.fs p with
  | none => exact Nat.zero_le _
  | some vt => exact hf p vt.1 vt.2 h

/-- Two states agree on some paths. -/
def Agree (st st' : St V) (ps : List Path) : Prop := ∀ p ∈ ps, st.fs p = st'.fs p ∧ st.log p = st'.log p

theorem dirty_congr {st st' : St V} {e : MEdge} (h : Agree st st' (e.ins ++ e.outs)) :
    st.dirty e = st'.dirty e := by
  have hn : st.newest e.ins = st'.newest e.ins := newest_congr fun p hp => (h p (by simp [hp])).1
  unfold dirty
  refine any_congr fun o ho => ?_
  obtain ⟨h1, h2⟩ := h o (by simp [ho])
  unfold outDirty
  rw [h1, h2, hn]

theorem consistent_congr {st st' : St V} {e : MEdge} (h : ∀ p ∈ e.ins ++ e.outs, st.fs p = st'.fs p) :
    st.Consistent exec e ↔ st'.Consistent exec e := by
  have hc : ∀ p ∈ e.ins ++ e.outs, st.content p = st'.content p := fun p hp => by
    simp only [content, h p hp]
  have hm : e.ins.map st.content = e.ins.map st'.content :=
    List.map_congr_left fun p hp => hc p (by simp [hp])
  unfold Consistent
  rw [hm]
  constructor
  · intro H o ho; rw [← hc o (by simp [ho])]; exact H o ho
  · intro H o ho; rw [hc o (by simp [ho])]; exact H o ho

theorem edgeOK_congr {st st' : St V} {e : MEdge} (h : Agree st st' (e.ins ++ e.outs)) :
    st.EdgeOK exec e ↔ st'.EdgeOK exec e := by
  unfold EdgeOK
  rw [dirty_congr h, consistent_congr exec fun p hp => (h p hp).1]

/-! ## Dirtiness -/

theorem dirty_false {st : St V} {e : MEdge} (h : st.dirty e = false) {o : Path} (ho : o ∈ e.outs) :
    st.outDirty e o = false := by
  unfold dirty at h
  rw [List.any_eq_false] at h
  simpa using h o ho

/-- An input newer than an output makes the output dirty. -/
theorem outDirty_of_newer {st : St V} {e : MEdge} {i o : Path} (hi : i ∈ e.ins)
    (h : st.mtime o < st.mtime i) : st.outDirty e o = true := by
  have hlt := Nat.lt_of_lt_of_le h (st.le_newest hi)
  unfold outDirty
  cases hfs : st.fs o with
  | none => simp
  | some vt =>
    obtain ⟨v, t⟩ := vt
    have : st.mtime o = t := by simp [mtime, hfs]
    rw [this] at hlt
    cases hlog : st.log o with
    | none => simp
    | some cl => simp [hlt]

/-- A log entry with another command makes the output dirty. -/
def Stale (st : St V) (e : MEdge) (o : Path) : Prop := ∀ c lt, st.log o = some (c, lt) → c ≠ e.cmd

theorem outDirty_of_stale {st : St V} {e : MEdge} {o : Path} (h : st.Stale e o) : st.outDirty e o = true := by
  unfold outDirty
  split
  · rename_i c _ _ hlog
    have := h c _ hlog
    simp [this]
  · rfl

theorem log_of_clean {st : St V} {e : MEdge} {o : Path} (h : st.outDirty e o = false) :
    ∃ lt, st.log o = some (e.cmd, lt) := by
  unfold outDirty at h
  split at h
  · rename_i c lt _ hlog
    simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at h
    exact ⟨lt, by rw [hlog, h.1.2]⟩
  · cases h

/-! ## Writes -/

/-- Writing fresh files outside an edge's outputs keeps the edge's
invariant: either the edge reads a written file, and is then dirty, or it
sees no change. -/
theorem edgeOK_of_write {st st' : St V} {W : List Path} {e : MEdge} (hf : st.Fresh)
    (hag : ∀ p, p ∉ W → st'.fs p = st.fs p ∧ st'.log p = st.log p)
    (hnew : ∀ p ∈ W, st.clock < st'.mtime p) (hdis : Disjoint e.outs W) (hok : st.EdgeOK exec e) :
    st'.EdgeOK exec e := by
  by_cases hi : ∃ i ∈ e.ins, i ∈ W
  · obtain ⟨i, hi, hiW⟩ := hi
    intro hclean o ho
    exfalso
    have hd := dirty_false hclean ho
    have hoW := hdis o ho
    have hmo : st'.mtime o = st.mtime o := by simp [mtime, (hag o hoW).1]
    have : st'.mtime o < st'.mtime i := by
      rw [hmo]; exact Nat.lt_of_le_of_lt (mtime_le_clock hf o) (hnew i hiW)
    rw [outDirty_of_newer hi this] at hd
    cases hd
  · have hag' : Agree st' st (e.ins ++ e.outs) := by
      intro p hp
      simp only [List.mem_append] at hp
      rcases hp with hp | hp
      · exact hag p fun hpW => hi ⟨p, hp, hpW⟩
      · exact hag p (hdis p hp)
    exact (edgeOK_congr exec hag').mpr hok

theorem run_other {st : St V} {e : MEdge} {p : Path} (hp : p ∉ e.outs) :
    (st.run exec e).fs p = st.fs p ∧ (st.run exec e).log p = st.log p := by
  simp [run, hp]

theorem fresh_run {st : St V} (hf : st.Fresh) (e : MEdge) : (st.run exec e).Fresh := by
  intro p v t h
  show t ≤ st.clock + 1
  simp only [run] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
  · exact Nat.le_succ_of_le (hf p v t h)

theorem run_self {st : St V} {e : MEdge} (hf : st.Fresh) (hd : Disjoint e.ins e.outs) :
    (st.run exec e).dirty e = false ∧ (st.run exec e).Consistent exec e := by
  have hag : ∀ p ∈ e.ins, (st.run exec e).fs p = st.fs p := fun p hp => (run_other exec (hd p hp)).1
  have hn : (st.run exec e).newest e.ins = st.newest e.ins := newest_congr hag
  have hle : st.newest e.ins ≤ st.clock := st.newest_le fun p _ => mtime_le_clock hf p
  have hc : e.ins.map (st.run exec e).content = e.ins.map st.content :=
    List.map_congr_left fun p hp => by simp only [content, hag p hp]
  constructor
  · unfold dirty
    rw [List.any_eq_false]
    intro o ho
    have hlt : ¬ (st.clock + 1 < st.newest e.ins) := by omega
    have hfs : ∃ v, (st.run exec e).fs o = some (v, st.clock + 1) :=
      ⟨(exec e.cmd (e.ins.map st.content)).getD (e.outs.idxOf o) default, by simp [run, ho]⟩
    have hlog : (st.run exec e).log o = some (e.cmd, st.clock + 1) := by simp [run, ho]
    obtain ⟨v, hfs⟩ := hfs
    simp only [outDirty, hfs, hlog, hn]
    simp [hlt]
  · intro o ho
    rw [hc]
    simp [content, run, ho]

theorem edgeOK_run_other {st : St V} {e e' : MEdge} (hf : st.Fresh) (hdis : Disjoint e'.outs e.outs)
    (hok : st.EdgeOK exec e') : (st.run exec e).EdgeOK exec e' :=
  edgeOK_of_write exec hf (fun p hp => run_other exec hp)
    (fun p hp => by simp [mtime, run, hp]) hdis hok

theorem fresh_step {st : St V} (hf : st.Fresh) (e : MEdge) : (st.step exec e).Fresh := by
  unfold step; split
  · exact fresh_run exec hf e
  · exact hf

theorem step_other {st : St V} {e : MEdge} {p : Path} (hp : p ∉ e.outs) :
    (st.step exec e).fs p = st.fs p ∧ (st.step exec e).log p = st.log p := by
  unfold step; split
  · exact run_other exec hp
  · exact ⟨rfl, rfl⟩

theorem fresh_edit {st : St V} (hf : st.Fresh) (p : Path) (v : V) : (st.edit p v).Fresh := by
  intro q w t h
  show t ≤ st.clock + 1
  simp only [edit] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
  · exact Nat.le_succ_of_le (hf q w t h)

end St

/-! ## Schedules -/

theorem Sched.self {es : List MEdge} {e : MEdge} (hs : Sched es) (he : e ∈ es) : Disjoint e.ins e.outs := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact hs.1
    · exact ih hs.2.2 he

theorem Sched.tail {e : MEdge} {es : List MEdge} (hs : Sched (e :: es)) : Sched es := hs.2.2

theorem Sched.disjoint {es : List MEdge} {e e' : MEdge} (hs : Sched es) (he : e ∈ es) (he' : e' ∈ es)
    (hne : e ≠ e') : Disjoint e.outs e'.outs := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
    simp only [List.mem_cons] at he he'
    rcases he with rfl | he <;> rcases he' with rfl | he'
    · exact absurd rfl hne
    · exact (hs.2.1 e' he').2
    · exact (hs.2.1 e he).2.symm
    · exact ih hs.2.2 he he'

/-! ## The invariant -/

theorem inv_step {es : List MEdge} {e : MEdge} {st : St V} (hs : Sched es) (he : e ∈ es)
    (h : Inv exec es st) : Inv exec es (st.step exec e) := by
  refine ⟨St.fresh_step exec h.1 e, fun e' he' => ?_⟩
  unfold St.step
  split
  · by_cases hee : e' = e
    · subst hee
      exact fun _ => (St.run_self exec h.1 (hs.self he)).2
    · exact St.edgeOK_run_other exec h.1 (hs.disjoint he' he hee) (h.2 e' he')
  · exact h.2 e' he'

/-- Source edits keep the invariant. -/
theorem inv_edit {es : List MEdge} {st : St V} {p : Path} (v : V) (hp : ∀ e ∈ es, p ∉ e.outs)
    (h : Inv exec es st) : Inv exec es (st.edit p v) := by
  refine ⟨St.fresh_edit h.1 p v, fun e he => ?_⟩
  refine St.edgeOK_of_write exec (W := [p]) h.1 (fun q hq => ?_) (fun q hq => ?_) ?_ (h.2 e he)
  · simp only [List.mem_singleton] at hq; simp [St.edit, hq]
  · simp only [List.mem_singleton] at hq; subst hq; simp [St.mtime, St.edit]
  · intro o ho hop; simp only [List.mem_singleton] at hop; subst hop; exact hp e he ho

theorem inv_edits {es : List MEdge} (edits : List (Path × V)) (hp : ∀ pv ∈ edits, ∀ e ∈ es, pv.1 ∉ e.outs) :
    ∀ {st : St V}, Inv exec es st → Inv exec es (st.edits edits) := by
  induction edits with
  | nil => exact id
  | cons pv edits ih =>
    intro st h
    exact ih (fun q hq => hp q (by simp [hq])) (inv_edit exec pv.2 (hp pv (by simp)) h)

/-! ## Builds -/

theorem build_fresh : ∀ (l : List MEdge) {st : St V}, st.Fresh → (buildTrace exec l st).1.Fresh
  | [], _, h => h
  | e :: l, _, h => build_fresh l (St.fresh_step exec h e)

theorem build_other : ∀ (l : List MEdge) {st : St V} {p : Path}, (∀ e ∈ l, p ∉ e.outs) →
    (buildTrace exec l st).1.fs p = st.fs p ∧ (buildTrace exec l st).1.log p = st.log p
  | [], _, _, _ => ⟨rfl, rfl⟩
  | e :: l, st, p, h => by
    have h1 := build_other l (st := st.step exec e) fun e' he' => h e' (by simp [he'])
    have h2 := St.step_other exec (st := st) (h e (by simp))
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem build_inv {es : List MEdge} (hs : Sched es) :
    ∀ (l : List MEdge) {st : St V}, (∀ e ∈ l, e ∈ es) → Inv exec es st → Inv exec es (buildTrace exec l st).1
  | [], _, _, h => h
  | e :: l, _, hl, h => build_inv hs l (fun e' he' => hl e' (by simp [he'])) (inv_step exec hs (hl e (by simp)) h)

/-- After a full pass in schedule order, Ninja would skip every edge. -/
theorem build_clean : ∀ (l : List MEdge) {st : St V}, Sched l → st.Fresh →
    ∀ e ∈ l, (buildTrace exec l st).1.dirty e = false
  | [], _, _, _, e, he => by simp at he
  | a :: l, st, hs, hf, e, he => by
    have ih := build_clean l hs.tail (St.fresh_step exec hf a)
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · -- `e` is clean right after its step, and later steps do not touch it.
      have h1 : (st.step exec e).dirty e = false := by
        unfold St.step; split
        · exact (St.run_self exec hf hs.1).1
        · rename_i hd; simpa using hd
      have hag : St.Agree (buildTrace exec l (st.step exec e)).1 (st.step exec e) (e.ins ++ e.outs) := by
        intro p hp
        refine build_other exec l fun e' he' hpo => ?_
        simp only [List.mem_append] at hp
        rcases hp with hp | hp
        · exact (hs.2.1 e' he').1 p hp hpo
        · exact (hs.2.1 e' he').2 p hp hpo
      show (buildTrace exec l (st.step exec e)).1.dirty e = false
      rw [St.dirty_congr hag]; exact h1
    · exact ih e he

theorem trace_clean : ∀ (l : List MEdge) {st : St V}, (∀ e ∈ l, st.dirty e = false) →
    buildTrace exec l st = (st, [])
  | [], _, _ => rfl
  | e :: l, st, h => by
    have he := h e (by simp)
    have hs : st.step exec e = st := by simp [St.step, he]
    simp only [buildTrace, hs, he, Bool.false_eq_true, ite_false]
    rw [trace_clean l fun e' he' => h e' (by simp [he'])]

/-- An edge whose log entry records another command is run. -/
theorem trace_mem_of_stale : ∀ (l : List MEdge) {st : St V} {e : MEdge} {o : Path}, Sched l → e ∈ l →
    o ∈ e.outs → st.Stale e o → e ∈ (buildTrace exec l st).2
  | [], _, _, _, _, he, _, _ => by simp at he
  | a :: l, st, e, o, hs, he, ho, hst => by
    simp only [buildTrace]
    by_cases hea : e = a
    · subst hea
      have : st.dirty e = true := List.any_eq_true.mpr ⟨o, ho, St.outDirty_of_stale hst⟩
      simp [this]
    · have he' : e ∈ l := by simpa [hea] using he
      have hoa : o ∉ a.outs := fun h => (hs.2.1 e he').2 o h ho
      have hst' : (st.step exec a).Stale e o := by
        intro c lt h; rw [(St.step_other exec hoa).2] at h; exact hst c lt h
      have := trace_mem_of_stale l hs.tail he' ho hst'
      split <;> simp [this]

/-! ## Correctness -/

omit [Inhabited V] in
theorem fetchAll_run (R : Store Path V) : ∀ ks : List Path, (fetchAll ks : Task Path V (List V)).run R = ks.map R
  | [] => rfl
  | k :: ks => by simp [fetchAll, Task.run, fetchAll_run R ks]

theorem edgeTask_run (R : Store Path V) (cmd : String) (ins : List Path) (i : Nat) :
    (edgeTask exec cmd ins i).run R = (exec cmd (ins.map R)).getD i default := by
  simp [edgeTask, fetchAll_run]

theorem findOut_none_iff {α : Type} {outs : α → List Path} {k : Path} {l : List α}
    (h : findOut outs k l = none) : ∀ a ∈ l, k ∉ outs a := by
  induction l with
  | nil => simp
  | cons b l ih =>
    unfold findOut at h
    split at h
    · cases h
    · rename_i hb
      have : findOut outs k l = none := by cases hh : findOut outs k l <;> simp_all
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simpa using hb
      · exact ih this a ha

theorem findOut_sched {es : List MEdge} {e : MEdge} {o : Path} (hs : Sched es) (he : e ∈ es)
    (ho : o ∈ e.outs) : ∃ i, findOut MEdge.outs o es = some (i, e) := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
    unfold findOut
    by_cases hoa : o ∈ a.outs
    · have : e = a := by
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · rfl
        · exact absurd ho ((hs.2.1 e he).2 o hoa)
      subst this
      exact ⟨0, by simp [hoa]⟩
    · have he' : e ∈ es := by
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact absurd ho hoa
        · exact he
      obtain ⟨i, hi⟩ := ih hs.tail he'
      exact ⟨i + 1, by simp [hoa, hi]⟩

theorem source_not_out {es : List MEdge} {k : Path} (h : (specOf exec es).isSource k = true) :
    ∀ e ∈ es, k ∉ e.outs := by
  simp only [specOf, Option.isNone_iff_eq_none] at h
  exact findOut_none_iff h

theorem correct_of_consistent {es : List MEdge} {st : St V} (hc : ∀ e ∈ es, st.Consistent exec e)
    (S : Store Path V) (hS : ∀ k, (specOf exec es).isSource k = true → st.content k = S k) :
    (specOf exec es).Correct S st.content := by
  refine ⟨hS, fun k hk => ?_⟩
  simp only [specOf] at hk ⊢
  cases hf : findOut MEdge.outs k es with
  | none => simp [hf] at hk
  | some p =>
    obtain ⟨i, e⟩ := p
    obtain ⟨-, hke⟩ := findOut_some hf
    simp only [edgeTask_run]
    exact hc e (findOut_mem hf) k (by simpa using hke)

theorem consistent_of_correct {es : List MEdge} {st : St V} {S : Store Path V} (hs : Sched es)
    (hc : (specOf exec es).Correct S st.content) : ∀ e ∈ es, st.Consistent exec e := by
  intro e he o ho
  obtain ⟨i, hi⟩ := findOut_sched hs he ho
  have := hc.2 o (by simp [specOf, hi])
  simp only [specOf, hi, edgeTask_run] at this
  exact this

omit [Inhabited V] in
theorem outs_toMEdge (file : Scope) : (MEdge.outs ∘ toMEdge file) = fun c => c.edge.allOuts := rfl

theorem denote_eq (m : Manifest) : denote exec m = specOf exec m.medges := by
  unfold denote specOf Manifest.medges
  simp only [findOut_map, outs_toMEdge]
  congr 1
  · funext k; cases findOut _ k m.elab.edges <;> rfl
  · funext k; cases findOut _ k m.elab.edges <;> rfl

/-! ## Theorems -/

section
variable {m : Manifest}

/-- Under the invariant, a build makes the contents correct. -/
theorem sound_of_inv (hs : Sched m.medges) {st : St V} (h : Inv exec m.medges st) :
    (denote exec m).Correct st.content (ninjaBuild exec m st).content := by
  rw [denote_eq]
  have hinv := build_inv exec hs m.medges (fun _ h => h) h
  have hclean := build_clean exec m.medges hs h.1
  refine correct_of_consistent exec (fun e he => hinv.2 e he (hclean e he)) _ fun k hk => ?_
  simp only [St.content, (build_other exec m.medges (source_not_out exec hk)).1]

/-- From an empty build log, a build is correct. -/
theorem ninjaBuild_clean_correct (hs : Sched m.medges) {st : St V} (hf : st.Fresh)
    (hlog : ∀ p, st.log p = none) :
    (denote exec m).Correct st.content (ninjaBuild exec m st).content := by
  refine sound_of_inv exec hs ⟨hf, fun e _ hclean o ho => ?_⟩
  obtain ⟨lt, h⟩ := St.log_of_clean (St.dirty_false hclean ho)
  rw [hlog] at h; cases h

/-- **Headline.** Start from correct contents, edit any sources, and build:
the contents are correct for the new sources. -/
theorem ninjaBuild_sound (hs : Sched m.medges) {st : St V} (hf : st.Fresh)
    (hc : (denote exec m).Correct st.content st.content) (edits : List (Path × V))
    (he : ∀ pv ∈ edits, (denote exec m).isSource pv.1 = true) :
    (denote exec m).Correct (st.edits edits).content (ninjaBuild exec m (st.edits edits)).content := by
  rw [denote_eq] at hc he
  have h0 : Inv exec m.medges st :=
    ⟨hf, fun e he' _ => consistent_of_correct exec hs hc e he'⟩
  exact sound_of_inv exec hs (inv_edits exec edits (fun pv hpv => source_not_out exec (he pv hpv)) h0)

/-- The contents after an incremental build equal a clean build's. -/
theorem ninjaBuild_eq_cleanBuild (hs : Sched m.medges) (ha : (denote exec m).Acyclic) {st : St V}
    (hf : st.Fresh) (hc : (denote exec m).Correct st.content st.content) (edits : List (Path × V))
    (he : ∀ pv ∈ edits, (denote exec m).isSource pv.1 = true) :
    (ninjaBuild exec m (st.edits edits)).content = BuildSpec.cleanBuild ha (st.edits edits).content := by
  funext k
  exact congrFun (BuildSpec.correct_eq_cleanBuild ha (ninjaBuild_sound exec hs hf hc edits he)) k

/-- A second build runs no edges and changes nothing. -/
theorem ninjaBuild_idem (hs : Sched m.medges) {st : St V} (hf : st.Fresh) :
    buildTrace exec m.medges (ninjaBuild exec m st) = (ninjaBuild exec m st, []) :=
  trace_clean exec m.medges (build_clean exec m.medges hs hf)

/-- An interrupted build, one that stops after any prefix of the schedule,
keeps the invariant, so the next build is correct. -/
theorem ninjaBuild_after_interrupt (hs : Sched m.medges) {st : St V} (h : Inv exec m.medges st) (n : Nat) :
    let st₁ := (buildTrace exec (m.medges.take n) st).1
    (denote exec m).Correct st₁.content (ninjaBuild exec m st₁).content :=
  sound_of_inv exec hs (build_inv exec hs _ (fun _ he => List.mem_of_mem_take he) h)

end

/-- Two edge lists with the same outputs and inputs, edge by edge. -/
inductive SameShape : List MEdge → List MEdge → Prop
  | nil : SameShape [] []
  | cons {e e' : MEdge} {es es' : List MEdge} : e.outs = e'.outs ∧ e.ins = e'.ins → SameShape es es' →
      SameShape (e :: es) (e' :: es')

theorem SameShape.mem {es es' : List MEdge} (h : SameShape es es') {e' : MEdge} (he' : e' ∈ es') :
    ∃ e ∈ es, e.outs = e'.outs ∧ e.ins = e'.ins := by
  induction h with
  | nil => simp at he'
  | cons hab _ ih =>
    simp only [List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨e, he, h⟩ := ih he'; exact ⟨e, by simp [he], h⟩

theorem SameShape.sched {es es' : List MEdge} (h : SameShape es es') (hs : Sched es) : Sched es' := by
  induction h with
  | nil => trivial
  | cons hab hrest ih =>
    obtain ⟨ho, hi⟩ := hab
    refine ⟨?_, fun e' he' => ?_, ih hs.tail⟩
    · rw [← ho, ← hi]; exact hs.1
    · obtain ⟨e, he, ho', hi'⟩ := hrest.mem he'
      rw [← ho, ← hi, ← ho']; exact hs.2.1 e he

/-- Changing commands in the manifest rebuilds every edge whose command
changed, and the result is correct for the new manifest. `st` is any state
in which every edge of the old manifest is clean and the invariant holds,
such as the result of building the old manifest. -/
theorem command_change_rebuilds {m m' : Manifest} (hs : Sched m.medges) (hshape : SameShape m.medges m'.medges)
    {st : St V} (h : Inv exec m.medges st) (hclean : ∀ e ∈ m.medges, st.dirty e = false) :
    (denote exec m').Correct st.content (ninjaBuild exec m' st).content ∧
    ∀ e ∈ m.medges, ∀ e' ∈ m'.medges, e.outs = e'.outs → e.cmd ≠ e'.cmd → e'.outs ≠ [] →
      e' ∈ (buildTrace exec m'.medges st).2 := by
  have hs' := hshape.sched hs
  -- The old log makes every edge with a changed command dirty.
  have hstale : ∀ e ∈ m.medges, ∀ e' : MEdge, e.outs = e'.outs → e.cmd ≠ e'.cmd → ∀ o ∈ e'.outs, st.Stale e' o := by
    intro e he e' hout hcmd o ho c lt hlog
    obtain ⟨lt', hl⟩ := St.log_of_clean (St.dirty_false (hclean e he) (hout ▸ ho))
    rw [hl] at hlog
    simp only [Option.some.injEq, Prod.mk.injEq] at hlog
    rw [← hlog.1]; exact hcmd
  refine ⟨sound_of_inv exec hs' ⟨h.1, fun e' he' => ?_⟩, ?_⟩
  · obtain ⟨e, he, hout, hin⟩ := hshape.mem he'
    by_cases hcmd : e.cmd = e'.cmd
    · have : e = e' := by cases e; cases e'; simp_all
      subst this; exact h.2 e he
    · intro hcl o ho
      have := St.dirty_false hcl ho
      rw [St.outDirty_of_stale (hstale e he e' hout hcmd o ho)] at this
      cases this
  · intro e he e' he' hout hcmd hne
    obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ hne
    exact trace_mem_of_stale exec _ hs' he' ho (hstale e he e' hout hcmd o ho)

end Mise.Model
