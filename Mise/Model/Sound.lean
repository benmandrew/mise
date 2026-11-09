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

variable {V : Type} [Inhabited V] (sem : Sem V)

omit [Inhabited V] in
theorem fetchAll_deps (R : Store Path V) : ∀ ks : List Path, (fetchAll ks : Task Path V (List V)).deps R = ks
  | [] => rfl
  | k :: ks => by simp [fetchAll, Task.deps, fetchAll_deps R ks]

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
  | some vt => exact hf.1 p vt.1 vt.2 h

/-- Two states agree on some paths: contents, log and deps entries. -/
def Agree (st st' : St V) (ps : List Path) : Prop :=
  ∀ p ∈ ps, st.fs p = st'.fs p ∧ st.log p = st'.log p ∧ st.deps p = st'.deps p

theorem outDirty_false_iff {st : St V} {e : MEdge} {o : Path} :
    st.outDirty e o = false ↔ ∃ v t lt D, st.fs o = some (v, t) ∧ st.log o = some (e.cmd, lt) ∧
      st.effIns e o = some D ∧ (e.restat = false → st.newest D ≤ t) ∧ st.newest D ≤ lt := by
  unfold outDirty
  split
  · rename_i v t c lt D hfs hlog heff
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt, bne_eq_false_iff_eq,
      Bool.and_eq_false_iff, Bool.not_eq_false']
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨v, t, lt, D, hfs, by rw [hlog, h2], heff, fun hr => ?_, h3⟩
      rcases h1 with h1 | h1
      · rw [hr] at h1; cases h1
      · exact h1
    · rintro ⟨v', t', lt', D', h1, h2, h3, h4, h5⟩
      rw [hfs] at h1; rw [hlog] at h2; rw [heff] at h3
      simp only [Option.some.injEq, Prod.mk.injEq] at h1 h2 h3
      obtain ⟨-, rfl⟩ := h1; obtain ⟨rfl, rfl⟩ := h2; subst h3
      refine ⟨⟨?_, rfl⟩, h5⟩
      cases hr : e.restat
      · exact .inr (h4 hr)
      · exact .inl rfl
  · rename_i hne
    simp only [Bool.true_eq_false, false_iff, not_exists, not_and]
    intro v t lt D h1 h2 h3 _ _
    exact hne v t e.cmd lt D h1 h2 h3

theorem clean_iff {st : St V} {e : MEdge} : st.dirty e = false ↔ ∀ o ∈ e.outs, st.outDirty e o = false := by
  unfold dirty; rw [List.any_eq_false]; simp

theorem bool_eq_of_false_iff {a b : Bool} (h : a = false ↔ b = false) : a = b := by
  cases a <;> cases b <;> simp_all

theorem outDirty_congr {st st' : St V} {e : MEdge} {o : Path} (h1 : st.fs o = st'.fs o)
    (h2 : st.log o = st'.log o) (h3 : st.deps o = st'.deps o)
    (hD : ∀ D, st.effIns e o = some D → ∀ p ∈ D, st.fs p = st'.fs p) :
    st.outDirty e o = st'.outDirty e o := by
  have he : st.effIns e o = st'.effIns e o := by simp only [effIns, h3]
  refine bool_eq_of_false_iff ?_
  rw [outDirty_false_iff, outDirty_false_iff]
  constructor
  · rintro ⟨v, t, lt, D, a1, a2, a3, a4, a5⟩
    rw [newest_congr (hD D a3)] at a4 a5
    exact ⟨v, t, lt, D, by rw [← h1]; exact a1, by rw [← h2]; exact a2, by rw [← he]; exact a3, a4, a5⟩
  · rintro ⟨v, t, lt, D, a1, a2, a3, a4, a5⟩
    have a3' : st.effIns e o = some D := by rw [he]; exact a3
    rw [← newest_congr (hD D a3')] at a4 a5
    exact ⟨v, t, lt, D, by rw [h1]; exact a1, by rw [h2]; exact a2, a3', a4, a5⟩

theorem dirty_congr {st st' : St V} {e : MEdge} (hout : Agree st st' e.outs)
    (hD : ∀ o ∈ e.outs, ∀ D, st.effIns e o = some D → ∀ p ∈ D, st.fs p = st'.fs p) :
    st.dirty e = st'.dirty e :=
  any_congr fun o ho => outDirty_congr (hout o ho).1 (hout o ho).2.1 (hout o ho).2.2 (hD o ho)

/-- A static command reads exactly its inputs. -/
theorem task_deps_static {e : MEdge} (h : e.dyn = false) (s : Store Path V) : (e.task sem).deps s = e.ins := by
  simp [MEdge.task, cmdTask, h, fetchAll_deps]

/-- Consistency carries over to a state that agrees on the outputs and on
every path Ninja checks for them. -/
theorem consistent_transfer {st st' : St V} {e : MEdge}
    (hout : ∀ o ∈ e.outs, st.fs o = st'.fs o ∧ st.deps o = st'.deps o)
    (hD : ∀ o ∈ e.outs, ∃ D, st.effIns e o = some D ∧ ∀ p ∈ D, st.fs p = st'.fs p)
    (hc : st.Consistent sem e) : st'.Consistent sem e := by
  intro o ho
  obtain ⟨D, heff, hag⟩ := hD o ho
  obtain ⟨h1, h2⟩ := hc o ho
  have hsub := h2 D heff
  obtain ⟨hr, hd⟩ := Task.run_eq_of_agree (e.task sem) st.content st'.content
    fun k hk => by simp only [content, hag k (hsub k hk)]
  have hco : st.content o = st'.content o := by simp only [content, (hout o ho).1]
  have he : st.effIns e o = st'.effIns e o := by simp only [effIns, (hout o ho).2]
  refine ⟨by rw [← hco, ← hr]; exact h1, fun D' hD' k hk => ?_⟩
  rw [← he] at hD'
  rw [← hd] at hk
  exact h2 D' hD' k hk

/-! ## Dirtiness -/

theorem dirty_false {st : St V} {e : MEdge} (h : st.dirty e = false) {o : Path} (ho : o ∈ e.outs) :
    st.outDirty e o = false := clean_iff.mp h o ho

/-- An input newer than an output's log entry makes the output dirty. -/
theorem outDirty_of_newer {st : St V} {e : MEdge} {i o : Path} {D : List Path} (hD : st.effIns e o = some D)
    (hi : i ∈ D) (h : ∀ c lt, st.log o = some (c, lt) → lt < st.mtime i) : st.outDirty e o = true := by
  cases hc : st.outDirty e o
  · obtain ⟨v, t, lt, D', -, hlog, hD', -, hle⟩ := outDirty_false_iff.mp hc
    rw [hD] at hD'; cases hD'
    have h1 := st.le_newest hi
    have h2 := h _ _ hlog
    omega
  · rfl

/-- A log entry with another command makes the output dirty. -/
def Stale (st : St V) (e : MEdge) (o : Path) : Prop := ∀ c lt, st.log o = some (c, lt) → c ≠ e.cmd

theorem outDirty_of_stale {st : St V} {e : MEdge} {o : Path} (h : st.Stale e o) : st.outDirty e o = true := by
  cases hc : st.outDirty e o
  · obtain ⟨v, t, lt, D, -, hlog, -⟩ := outDirty_false_iff.mp hc
    exact absurd rfl (h e.cmd lt hlog)
  · rfl

theorem log_of_clean {st : St V} {e : MEdge} {o : Path} (h : st.outDirty e o = false) :
    ∃ lt, st.log o = some (e.cmd, lt) := by
  obtain ⟨v, t, lt, D, -, hlog, -⟩ := outDirty_false_iff.mp h
  exact ⟨lt, hlog⟩

/-! ## Writes -/

/-- Writing fresh files outside an edge's outputs keeps the edge's
invariant: either a clean output depends on a written file, which is then
newer and makes it dirty, or the edge sees no change. -/
theorem edgeOK_of_write {st st' : St V} {W : List Path} {e : MEdge} (hf : st.Fresh)
    (hfs : ∀ p, p ∉ W → st'.fs p = st.fs p)
    (hout : ∀ o ∈ e.outs, st'.log o = st.log o ∧ st'.deps o = st.deps o)
    (hnew : ∀ p ∈ W, st.clock < st'.mtime p) (hdis : Disjoint e.outs W) (hok : st.EdgeOK sem e) :
    st'.EdgeOK sem e := by
  intro hclean
  have hav : ∀ o ∈ e.outs, ∀ D, st'.effIns e o = some D → ∀ p ∈ D, p ∉ W := by
    intro o ho D hD p hp hpW
    obtain ⟨v, t, lt, D', -, hlog, hD', -, hle⟩ := outDirty_false_iff.mp (clean_iff.mp hclean o ho)
    rw [hD] at hD'; cases hD'
    have h1 : st'.mtime p ≤ st'.newest D := st'.le_newest hp
    rw [(hout o ho).1] at hlog
    have h4 := hf.2 o _ _ hlog
    have h5 := hnew p hpW
    omega
  have hag : Agree st' st e.outs := fun o ho => ⟨hfs o (hdis o ho), hout o ho⟩
  have hD : ∀ o ∈ e.outs, ∀ D, st'.effIns e o = some D → ∀ p ∈ D, st'.fs p = st.fs p :=
    fun o ho D hD p hp => hfs p (hav o ho D hD p hp)
  have hclean0 : st.dirty e = false := by rw [← dirty_congr hag hD]; exact hclean
  refine consistent_transfer sem (fun o ho => ⟨(hfs o (hdis o ho)).symm, (hout o ho).2.symm⟩)
    (fun o ho => ?_) (hok hclean0)
  obtain ⟨v, t, lt, D, -, -, hD', -, -⟩ := outDirty_false_iff.mp (clean_iff.mp hclean o ho)
  have he : st.effIns e o = st'.effIns e o := by simp only [effIns, (hout o ho).2]
  exact ⟨D, by rw [he]; exact hD', fun p hp => (hfs p (hav o ho D hD' p hp)).symm⟩

theorem run_other {st : St V} {e : MEdge} {p : Path} (hp : p ∉ e.outs) :
    (st.run sem e).fs p = st.fs p ∧ (st.run sem e).log p = st.log p ∧ (st.run sem e).deps p = st.deps p := by
  simp [run, hp]

theorem fresh_run {st : St V} (hf : st.Fresh) (e : MEdge) : (st.run sem e).Fresh := by
  constructor
  · intro p v t h
    show t ≤ st.clock + 1
    simp only [run] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
    · exact Nat.le_succ_of_le (hf.1 p v t h)
  · intro p c t h
    show t ≤ st.clock + 1
    simp only [run] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
    · exact Nat.le_succ_of_le (hf.2 p c t h)

/-- A kept output already holds the contents the run would write. -/
theorem kept_fs {st : St V} {e : MEdge} {o : Path} (h : st.kept sem e o = true) :
    e.restat = true ∧ ∃ t, st.fs o = some (st.outVal sem e o, t) := by
  unfold kept at h
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  split at h2
  · rename_i old t hfs
    exact ⟨t, by rw [hfs, sem.keep_eq _ _ h2]⟩
  · cases h2

/-- The paths Ninja checks for an output right after its edge ran. -/
def ranIns (st : St V) (e : MEdge) : List Path :=
  if e.dyn then e.ins ++ (e.task sem).deps st.content else e.ins

/-- Right after a run, the edge is clean and consistent, provided it reads
none of its own outputs. -/
theorem run_self {st : St V} {e : MEdge} (hf : st.Fresh) (hd : Disjoint e.ins e.outs)
    (hdd : Disjoint ((e.task sem).deps st.content) e.outs) :
    (st.run sem e).dirty e = false ∧ (st.run sem e).Consistent sem e := by
  have hagD : ∀ p ∈ (e.task sem).deps st.content, (st.run sem e).fs p = st.fs p :=
    fun p hp => (run_other sem (hdd p hp)).1
  have hagI : ∀ p ∈ e.ins, (st.run sem e).fs p = st.fs p := fun p hp => (run_other sem (hd p hp)).1
  have hrun := Task.run_eq_of_agree (e.task sem) st.content (st.run sem e).content
    fun k hk => by simp only [content, hagD k hk]
  have heff : ∀ o ∈ e.outs, (st.run sem e).effIns e o = some (st.ranIns sem e) := by
    intro o ho
    cases hdy : e.dyn <;> simp [effIns, run, ranIns, ho, hdy]
  have hDsub : ∀ p ∈ st.ranIns sem e, (st.run sem e).fs p = st.fs p := by
    intro p hp
    unfold ranIns at hp
    cases hdy : e.dyn <;> simp only [hdy, Bool.false_eq_true, ite_false, ite_true] at hp
    · exact hagI p hp
    · rcases List.mem_append.mp hp with h | h
      · exact hagI p h
      · exact hagD p h
  have hle : (st.run sem e).newest (st.ranIns sem e) ≤ st.clock + 1 := by
    rw [newest_congr hDsub]; exact Nat.le_succ_of_le (st.newest_le fun p _ => mtime_le_clock hf p)
  -- Every output holds the new contents, written now or kept.
  have hout : ∀ o ∈ e.outs, ∃ t, (st.run sem e).fs o = some (st.outVal sem e o, t) ∧
      (e.restat = false → t = st.clock + 1) := by
    intro o ho
    cases hk : st.kept sem e o
    · exact ⟨st.clock + 1, by simp [run, ho, hk], fun _ => rfl⟩
    · obtain ⟨hr, t, ht⟩ := kept_fs sem hk
      exact ⟨t, by simp [run, ho, hk, ht], fun h => by rw [hr] at h; cases h⟩
  constructor
  · rw [clean_iff]
    intro o ho
    rw [outDirty_false_iff]
    obtain ⟨t, hfs, ht⟩ := hout o ho
    exact ⟨st.outVal sem e o, t, st.clock + 1, st.ranIns sem e, hfs, by simp [run, ho], heff o ho,
      fun hr => by rw [ht hr]; exact hle, hle⟩
  · intro o ho
    refine ⟨?_, fun D hD k hk => ?_⟩
    · rw [← hrun.1]
      obtain ⟨t, hfs, -⟩ := hout o ho
      simp [content, hfs, outVal]
    · rw [heff o ho] at hD; cases hD
      rw [← hrun.2] at hk
      unfold ranIns
      cases hdy : e.dyn
      · rw [task_deps_static sem hdy] at hk; simpa using hk
      · simp only [ite_true]; exact List.mem_append_right _ hk

theorem edgeOK_run_other {st : St V} {e e' : MEdge} (hf : st.Fresh) (hdis : Disjoint e'.outs e.outs)
    (hok : st.EdgeOK sem e') : (st.run sem e).EdgeOK sem e' := by
  refine edgeOK_of_write sem (W := e.outs.filter fun o => !st.kept sem e o) hf (fun p hp => ?_)
    (fun o ho => ⟨(run_other sem (hdis o ho)).2.1, (run_other sem (hdis o ho)).2.2⟩) (fun p hp => ?_)
    (fun o ho hoW => hdis o ho (List.mem_filter.mp hoW).1) hok
  · by_cases hpo : p ∈ e.outs
    · have : st.kept sem e p = true := by
        cases hk : st.kept sem e p
        · exact absurd (List.mem_filter.mpr ⟨hpo, by simp [hk]⟩) hp
        · rfl
      simp [run, hpo, this]
    · exact (run_other sem hpo).1
  · obtain ⟨hpo, hk⟩ := List.mem_filter.mp hp
    simp only [Bool.not_eq_true'] at hk
    simp [mtime, run, hpo, hk]

theorem fresh_step {st : St V} (hf : st.Fresh) (e : MEdge) : (st.step sem e).Fresh := by
  unfold step; split
  · exact fresh_run sem hf e
  · exact hf

theorem step_other {st : St V} {e : MEdge} {p : Path} (hp : p ∉ e.outs) :
    (st.step sem e).fs p = st.fs p ∧ (st.step sem e).log p = st.log p ∧ (st.step sem e).deps p = st.deps p := by
  unfold step; split
  · exact run_other sem hp
  · exact ⟨rfl, rfl, rfl⟩

theorem fresh_edit {st : St V} (hf : st.Fresh) (p : Path) (v : V) : (st.edit p v).Fresh := by
  constructor
  · intro q w t h
    show t ≤ st.clock + 1
    simp only [edit] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
    · exact Nat.le_succ_of_le (hf.1 q w t h)
  · intro q c t h
    exact Nat.le_succ_of_le (hf.2 q c t h)

end St

/-! ## Schedules -/

theorem Sched.self {es : List MEdge} {e : MEdge} (hs : Sched es) (he : e ∈ es) : Disjoint e.reads e.outs := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact hs.1
    · exact ih hs.2.2 he

theorem Sched.ins {es : List MEdge} {e : MEdge} (hs : Sched es) (he : e ∈ es) : Disjoint e.ins e.outs :=
  fun p hp => hs.self he p (List.mem_append_left _ hp)

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

theorem Sched.append_left : ∀ {l₁ l₂ : List MEdge}, Sched (l₁ ++ l₂) → Sched l₁
  | [], _, _ => trivial
  | _ :: _, _, hs => ⟨hs.1, fun e' he' => hs.2.1 e' (List.mem_append_left _ he'), Sched.append_left hs.2.2⟩

theorem Sched.append_right : ∀ {l₁ l₂ : List MEdge}, Sched (l₁ ++ l₂) → Sched l₂
  | [], _, hs => hs
  | _ :: _, _, hs => Sched.append_right hs.2.2

/-! ## Allowed reads -/

theorem allowed_mono {es l : List MEdge} (hl : ∀ e ∈ l, e ∈ es) {e : MEdge} {k : Path}
    (h : Allowed es e k) : Allowed l e k := by
  rcases h with h | h
  · exact .inl fun e' he' => h e' (hl e' he')
  · exact .inr h

theorem reads_mono {es l : List MEdge} (hl : ∀ e ∈ l, e ∈ es) (hr : Reads sem es) : Reads sem l :=
  fun e he hd => (hr e (hl e he) hd).mono fun _ hk => allowed_mono hl hk

theorem depsOK_mono {es l : List MEdge} (hl : ∀ e ∈ l, e ∈ es) {st : St V} (h : DepsOK es st) : DepsOK l st :=
  fun e he hd o ho D hD k hk => allowed_mono hl (h e (hl e he) hd o ho D hD k hk)

/-- Everything a command reads is allowed: by `Reads` for a depfile
command, by construction for a static one. -/
theorem deps_allowed {es : List MEdge} (hr : Reads sem es) {e : MEdge} (he : e ∈ es) (s : Store Path V) :
    ∀ k ∈ (e.task sem).deps s, Allowed es e k := by
  cases hd : e.dyn
  · rw [St.task_deps_static sem hd]; intro k hk; exact .inr (List.mem_append_left _ hk)
  · have := hr e he hd
    simp only [MEdge.task, cmdTask, hd, ite_true]
    exact this.deps_sat s

theorem allowed_self {es : List MEdge} (hs : Sched es) {e : MEdge} (he : e ∈ es) {k : Path}
    (h : Allowed es e k) : k ∉ e.outs := by
  rcases h with h | h
  · exact h e he
  · exact hs.self he k h

theorem allowed_later {e : MEdge} {l : List MEdge} (hs : Sched (e :: l)) {k : Path} (h : Allowed (e :: l) e k) :
    ∀ e' ∈ l, k ∉ e'.outs := by
  intro e' he'
  rcases h with h | h
  · exact h e' (by simp [he'])
  · exact (hs.2.1 e' he').1 k h

theorem effIns_allowed {es : List MEdge} {st : St V} (hdo : DepsOK es st) {e : MEdge} (he : e ∈ es) {o : Path}
    (ho : o ∈ e.outs) {D : List Path} (hD : st.effIns e o = some D) : ∀ k ∈ D, Allowed es e k := by
  intro k hk
  unfold St.effIns at hD
  cases hd : e.dyn
  · simp only [hd, Bool.false_eq_true, ite_false, Option.some.injEq] at hD
    subst hD; exact .inr (List.mem_append_left _ hk)
  · simp only [hd, ite_true, Option.map_eq_some_iff] at hD
    obtain ⟨D0, h0, rfl⟩ := hD
    rcases List.mem_append.mp hk with h | h
    · exact .inr (List.mem_append_left _ h)
    · exact hdo e he hd o ho D0 h0 k h

theorem depsOK_run {es : List MEdge} (hs : Sched es) (hr : Reads sem es) {e : MEdge} (he : e ∈ es)
    {st : St V} (h : DepsOK es st) : DepsOK es (st.run sem e) := by
  intro e' he' hdy o ho D hD k hk
  by_cases hoe : o ∈ e.outs
  · have hee : e' = e := Classical.byContradiction fun hne => hs.disjoint he' he hne o ho hoe
    rw [hee] at hdy ho ⊢
    have : D = (e.task sem).deps st.content := by simp [St.run, hoe] at hD; exact hD.symm
    subst this
    exact deps_allowed sem hr he _ k hk
  · rw [(St.run_other sem hoe).2.2] at hD
    exact h e' he' hdy o ho D hD k hk

theorem depsOK_step {es : List MEdge} (hs : Sched es) (hr : Reads sem es) {e : MEdge} (he : e ∈ es)
    {st : St V} (h : DepsOK es st) : DepsOK es (st.step sem e) := by
  unfold St.step; split
  · exact depsOK_run sem hs hr he h
  · exact h

/-! ## The invariant -/

theorem inv_step {es : List MEdge} {e : MEdge} {st : St V} (hs : Sched es) (hr : Reads sem es) (he : e ∈ es)
    (h : Inv sem es st) : Inv sem es (st.step sem e) := by
  refine ⟨St.fresh_step sem h.1 e, depsOK_step sem hs hr he h.2.1, fun e' he' => ?_⟩
  unfold St.step
  split
  · by_cases hee : e' = e
    · rw [hee]
      exact fun _ => (St.run_self sem h.1 (hs.ins he)
        fun p hp => allowed_self hs he (deps_allowed sem hr he _ p hp)).2
    · exact St.edgeOK_run_other sem h.1 (hs.disjoint he' he hee) (h.2.2 e' he')
  · exact h.2.2 e' he'

/-- Source edits keep the invariant. -/
theorem inv_edit {es : List MEdge} {st : St V} {p : Path} (v : V) (hp : ∀ e ∈ es, p ∉ e.outs)
    (h : Inv sem es st) : Inv sem es (st.edit p v) := by
  refine ⟨St.fresh_edit h.1 p v, h.2.1, fun e he => ?_⟩
  refine St.edgeOK_of_write sem (W := [p]) h.1 (fun q hq => ?_) (fun o _ => ⟨rfl, rfl⟩) (fun q hq => ?_) ?_
    (h.2.2 e he)
  · simp only [List.mem_singleton] at hq; simp [St.edit, hq]
  · simp only [List.mem_singleton] at hq; subst hq; simp [St.mtime, St.edit]
  · intro o ho hop; simp only [List.mem_singleton] at hop; subst hop; exact hp e he ho

theorem inv_edits {es : List MEdge} (edits : List (Path × V)) (hp : ∀ pv ∈ edits, ∀ e ∈ es, pv.1 ∉ e.outs) :
    ∀ {st : St V}, Inv sem es st → Inv sem es (st.edits edits) := by
  induction edits with
  | nil => exact id
  | cons pv edits ih =>
    intro st h
    exact ih (fun q hq => hp q (by simp [hq])) (inv_edit sem pv.2 (hp pv (by simp)) h)

/-! ## Builds -/

theorem build_fresh : ∀ (l : List MEdge) {st : St V}, st.Fresh → (buildTrace sem l st).1.Fresh
  | [], _, h => h
  | e :: l, _, h => build_fresh l (St.fresh_step sem h e)

theorem build_other : ∀ (l : List MEdge) {st : St V} {p : Path}, (∀ e ∈ l, p ∉ e.outs) →
    (buildTrace sem l st).1.fs p = st.fs p ∧ (buildTrace sem l st).1.log p = st.log p ∧
      (buildTrace sem l st).1.deps p = st.deps p
  | [], _, _, _ => ⟨rfl, rfl, rfl⟩
  | e :: l, st, p, h => by
    have h1 := build_other l (st := st.step sem e) fun e' he' => h e' (by simp [he'])
    have h2 := St.step_other sem (st := st) (h e (by simp))
    exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

theorem build_inv {es : List MEdge} (hs : Sched es) (hr : Reads sem es) :
    ∀ (l : List MEdge) {st : St V}, (∀ e ∈ l, e ∈ es) → Inv sem es st → Inv sem es (buildTrace sem l st).1
  | [], _, _, h => h
  | e :: l, _, hl, h =>
    build_inv hs hr l (fun e' he' => hl e' (by simp [he'])) (inv_step sem hs hr (hl e (by simp)) h)

/-- After a full pass in schedule order, Ninja would skip every edge. -/
theorem build_clean : ∀ (l : List MEdge) {st : St V}, Sched l → Reads sem l → st.Fresh → DepsOK l st →
    ∀ e ∈ l, (buildTrace sem l st).1.dirty e = false
  | [], _, _, _, _, _, e, he => by simp at he
  | a :: l, st, hs, hr, hf, hdo, e, he => by
    have hdo1 : DepsOK (a :: l) (st.step sem a) := depsOK_step sem hs hr (by simp) hdo
    have hsub : ∀ e ∈ l, e ∈ a :: l := fun e he => by simp [he]
    have ih := build_clean l hs.tail (reads_mono sem hsub hr) (St.fresh_step sem hf a) (depsOK_mono hsub hdo1)
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · -- `e` is clean right after its step, and later steps touch nothing it depends on.
      have h1 : (st.step sem e).dirty e = false := by
        unfold St.step; split
        · exact (St.run_self sem hf (hs.ins (by simp))
            fun p hp => allowed_self hs (by simp) (deps_allowed sem hr (by simp) _ p hp)).1
        · rename_i hd; simpa using hd
      have hout : St.Agree (st.step sem e) (buildTrace sem l (st.step sem e)).1 e.outs := fun p hp => by
        obtain ⟨a1, a2, a3⟩ := build_other sem l (st := st.step sem e) fun e' he' hpo => (hs.2.1 e' he').2 p hp hpo
        exact ⟨a1.symm, a2.symm, a3.symm⟩
      have hD : ∀ o ∈ e.outs, ∀ D, (st.step sem e).effIns e o = some D →
          ∀ p ∈ D, (st.step sem e).fs p = (buildTrace sem l (st.step sem e)).1.fs p :=
        fun o ho D hD p hp =>
          (build_other sem l fun e' he' => allowed_later hs (effIns_allowed hdo1 (by simp) ho hD p hp) e' he').1.symm
      show (buildTrace sem l (st.step sem e)).1.dirty e = false
      rw [← St.dirty_congr hout hD]; exact h1
    · exact ih e he

theorem trace_clean : ∀ (l : List MEdge) {st : St V}, (∀ e ∈ l, st.dirty e = false) →
    buildTrace sem l st = (st, [])
  | [], _, _ => rfl
  | e :: l, st, h => by
    have he := h e (by simp)
    have hs : st.step sem e = st := by simp [St.step, he]
    simp only [buildTrace, hs, he, Bool.false_eq_true, ite_false]
    rw [trace_clean l fun e' he' => h e' (by simp [he'])]

/-- An edge whose log entry records another command is run. -/
theorem trace_mem_of_stale : ∀ (l : List MEdge) {st : St V} {e : MEdge} {o : Path}, Sched l → e ∈ l →
    o ∈ e.outs → st.Stale e o → e ∈ (buildTrace sem l st).2
  | [], _, _, _, _, he, _, _ => by simp at he
  | a :: l, st, e, o, hs, he, ho, hst => by
    simp only [buildTrace]
    by_cases hea : e = a
    · subst hea
      have : st.dirty e = true := List.any_eq_true.mpr ⟨o, ho, St.outDirty_of_stale hst⟩
      simp [this]
    · have he' : e ∈ l := by simpa [hea] using he
      have hoa : o ∉ a.outs := fun h => (hs.2.1 e he').2 o h ho
      have hst' : (st.step sem a).Stale e o := by
        intro c lt h; rw [(St.step_other sem hoa).2.1] at h; exact hst c lt h
      have := trace_mem_of_stale l hs.tail he' ho hst'
      split <;> simp [this]

/-- **Scheduling.** When an edge's turn comes, every generated path its
command reads belongs to an earlier edge, and that edge is clean. -/
theorem fetched_up_to_date {pre post : List MEdge} {e : MEdge} (hs : Sched (pre ++ e :: post))
    (hr : Reads sem (pre ++ e :: post)) {st : St V} (hf : st.Fresh) (hdo : DepsOK (pre ++ e :: post) st) :
    ∀ k ∈ (e.task sem).deps (buildTrace sem pre st).1.content,
      (∀ e' ∈ pre ++ e :: post, k ∉ e'.outs) ∨
        ∃ e' ∈ pre, k ∈ e'.outs ∧ (buildTrace sem pre st).1.dirty e' = false := by
  intro k hk
  have hpre : ∀ e' ∈ pre, e' ∈ pre ++ e :: post := fun e' he' => List.mem_append_left _ he'
  rcases deps_allowed sem hr (by simp) _ k hk with h | h
  · exact .inl h
  · by_cases hk' : ∃ e' ∈ pre ++ e :: post, k ∈ e'.outs
    · obtain ⟨e', he', hko⟩ := hk'
      rcases List.mem_append.mp he' with hp | hp
      · exact .inr ⟨e', hp, hko, build_clean sem pre hs.append_left (reads_mono sem hpre hr) hf
          (depsOK_mono hpre hdo) e' hp⟩
      · have hs' : Sched (e :: post) := hs.append_right
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact absurd hko (hs'.1 k h)
        · exact absurd hko ((hs'.2.1 e' hp).1 k h)
    · exact .inl fun e' he' hko => hk' ⟨e', he', hko⟩

/-! ## Correctness -/

omit [Inhabited V] in
theorem fetchAll_run (R : Store Path V) : ∀ ks : List Path, (fetchAll ks : Task Path V (List V)).run R = ks.map R
  | [] => rfl
  | k :: ks => by simp [fetchAll, Task.run, fetchAll_run R ks]

theorem outTask_run (R : Store Path V) (t : Task Path V (List V)) (i : Nat) :
    (outTask t i).run R = (t.run R).getD i default := by
  simp [outTask]

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

theorem source_not_out {es : List MEdge} {k : Path} (h : (specOf sem es).isSource k = true) :
    ∀ e ∈ es, k ∉ e.outs := by
  simp only [specOf, Option.isNone_iff_eq_none] at h
  exact findOut_none_iff h

theorem correct_of_consistent {es : List MEdge} {st : St V} (hc : ∀ e ∈ es, st.Consistent sem e)
    (S : Store Path V) (hS : ∀ k, (specOf sem es).isSource k = true → st.content k = S k) :
    (specOf sem es).Correct S st.content := by
  refine ⟨hS, fun k hk => ?_⟩
  simp only [specOf] at hk ⊢
  cases hf : findOut MEdge.outs k es with
  | none => simp [hf] at hk
  | some p =>
    obtain ⟨i, e⟩ := p
    obtain ⟨-, hke⟩ := findOut_some hf
    simp only [outTask_run]
    exact (hc e (findOut_mem hf) k (by simpa using hke)).1

/-- The deps log covers what every depfile command reads now. -/
def St.DepsCover (st : St V) (es : List MEdge) : Prop :=
  ∀ e ∈ es, ∀ o ∈ e.outs, ∀ D, st.effIns e o = some D → ∀ k ∈ (e.task sem).deps st.content, k ∈ D

theorem depsCover_static {es : List MEdge} (h : ∀ e ∈ es, e.dyn = false) (st : St V) : st.DepsCover sem es := by
  intro e he o ho D hD k hk
  simp only [St.effIns, h e he, Bool.false_eq_true, ite_false, Option.some.injEq] at hD
  subst hD
  rwa [St.task_deps_static sem (h e he)] at hk

theorem consistent_of_correct {es : List MEdge} {st : St V} {S : Store Path V} (hs : Sched es)
    (hc : (specOf sem es).Correct S st.content) (hd : st.DepsCover sem es) :
    ∀ e ∈ es, st.Consistent sem e := by
  intro e he o ho
  obtain ⟨i, hi⟩ := findOut_sched hs he ho
  have := hc.2 o (by simp [specOf, hi])
  simp only [specOf, hi, outTask_run] at this
  exact ⟨this, hd e he o ho⟩

omit [Inhabited V] in
theorem outs_toMEdge (file : Scope) : (MEdge.outs ∘ toMEdge file) = fun c => c.edge.allOuts := rfl

theorem denote_eq (m : Manifest) : denote sem m = specOf sem m.medges := by
  unfold denote specOf Manifest.medges
  simp only [findOut_map, outs_toMEdge]
  congr 1
  · funext k; cases findOut _ k m.elab.edges <;> rfl
  · funext k; cases findOut _ k m.elab.edges <;> rfl

/-! ## Theorems -/

section
variable {m : Manifest}

/-- Under the invariant, a build makes the contents correct. -/
theorem sound_of_inv (hs : Sched m.medges) (hr : Reads sem m.medges) {st : St V} (h : Inv sem m.medges st) :
    (denote sem m).Correct st.content (ninjaBuild sem m st).content := by
  rw [denote_eq]
  have hinv := build_inv sem hs hr m.medges (fun _ h => h) h
  have hclean := build_clean sem m.medges hs hr h.1 h.2.1
  refine correct_of_consistent sem (fun e he => hinv.2.2 e he (hclean e he)) _ fun k hk => ?_
  simp only [St.content, (build_other sem m.medges (source_not_out sem hk)).1]

/-- From empty build and deps logs, a build is correct. -/
theorem ninjaBuild_clean_correct (hs : Sched m.medges) (hr : Reads sem m.medges) {st : St V} (hf : st.Fresh)
    (hlog : ∀ p, st.log p = none) (hdeps : ∀ p, st.deps p = none) :
    (denote sem m).Correct st.content (ninjaBuild sem m st).content := by
  refine sound_of_inv sem hs hr ⟨hf, fun e _ _ o _ D hD => ?_, fun e _ hclean o ho => ?_⟩
  · rw [hdeps] at hD; cases hD
  · obtain ⟨lt, h⟩ := St.log_of_clean (St.dirty_false hclean ho)
    rw [hlog] at h; cases h

/-- **Headline.** Start from correct contents whose deps log covers what
each command reads, edit any sources, and build: the contents are correct
for the new sources. -/
theorem ninjaBuild_sound (hs : Sched m.medges) (hr : Reads sem m.medges) {st : St V} (hf : st.Fresh)
    (hdo : DepsOK m.medges st) (hd : st.DepsCover sem m.medges)
    (hc : (denote sem m).Correct st.content st.content) (edits : List (Path × V))
    (he : ∀ pv ∈ edits, (denote sem m).isSource pv.1 = true) :
    (denote sem m).Correct (st.edits edits).content (ninjaBuild sem m (st.edits edits)).content := by
  rw [denote_eq] at hc he
  have h0 : Inv sem m.medges st :=
    ⟨hf, hdo, fun e he' _ => consistent_of_correct sem hs hc hd e he'⟩
  exact sound_of_inv sem hs hr (inv_edits sem edits (fun pv hpv => source_not_out sem (he pv hpv)) h0)

/-- The Stage 5 statement: with no depfile edges, correct fresh contents
are all a build needs. -/
theorem ninjaBuild_sound_static (hs : Sched m.medges) (hst : ∀ e ∈ m.medges, e.dyn = false) {st : St V}
    (hf : st.Fresh) (hc : (denote sem m).Correct st.content st.content) (edits : List (Path × V))
    (he : ∀ pv ∈ edits, (denote sem m).isSource pv.1 = true) :
    (denote sem m).Correct (st.edits edits).content (ninjaBuild sem m (st.edits edits)).content :=
  ninjaBuild_sound sem hs (fun e he hd => by rw [hst e he] at hd; cases hd) hf
    (fun e he hd => by rw [hst e he] at hd; cases hd) (depsCover_static sem hst st) hc edits he

/-- The contents after an incremental build equal a clean build's. -/
theorem ninjaBuild_eq_cleanBuild (hs : Sched m.medges) (hr : Reads sem m.medges) (ha : (denote sem m).Acyclic)
    {st : St V} (h : Inv sem m.medges st) :
    (ninjaBuild sem m st).content = BuildSpec.cleanBuild ha st.content := by
  funext k
  exact congrFun (BuildSpec.correct_eq_cleanBuild ha (sound_of_inv sem hs hr h)) k

/-- A second build runs no edges and changes nothing. -/
theorem ninjaBuild_idem (hs : Sched m.medges) (hr : Reads sem m.medges) {st : St V} (hf : st.Fresh)
    (hdo : DepsOK m.medges st) :
    buildTrace sem m.medges (ninjaBuild sem m st) = (ninjaBuild sem m st, []) :=
  trace_clean sem m.medges (build_clean sem m.medges hs hr hf hdo)

/-- An interrupted build, one that stops after any prefix of the schedule,
keeps the invariant, so the next build is correct. -/
theorem ninjaBuild_after_interrupt (hs : Sched m.medges) (hr : Reads sem m.medges) {st : St V}
    (h : Inv sem m.medges st) (n : Nat) :
    let st₁ := (buildTrace sem (m.medges.take n) st).1
    (denote sem m).Correct st₁.content (ninjaBuild sem m st₁).content :=
  sound_of_inv sem hs hr (build_inv sem hs hr _ (fun _ he => List.mem_of_mem_take he) h)

end

/-! ## Histories -/

/-- The states reachable from empty logs by source edits and by running or
skipping edges in any order. Interrupted builds, builds of some targets, and
full builds are all sequences of steps. -/
inductive Reach (es : List MEdge) : St V → Prop
  | init {st : St V} : st.Fresh → (∀ p, st.log p = none) → (∀ p, st.deps p = none) → Reach es st
  | edit {st : St V} (p : Path) (v : V) : Reach es st → (∀ e ∈ es, p ∉ e.outs) → Reach es (st.edit p v)
  | step {st : St V} {e : MEdge} : Reach es st → e ∈ es → Reach es (st.step sem e)

theorem inv_of_reach {es : List MEdge} (hs : Sched es) (hr : Reads sem es) {st : St V} (h : Reach sem es st) :
    Inv sem es st := by
  induction h with
  | init hf hlog hdeps =>
    refine ⟨hf, fun e _ _ o _ D hD => ?_, fun e _ hclean o ho => ?_⟩
    · rw [hdeps] at hD; cases hD
    · obtain ⟨lt, h⟩ := St.log_of_clean (St.dirty_false hclean ho)
      rw [hlog] at h; cases h
  | edit p v _ hp ih => exact inv_edit sem v hp ih
  | step _ he ih => exact inv_step sem hs hr he ih

theorem reach_build {es : List MEdge} : ∀ (l : List MEdge) {st : St V}, (∀ e ∈ l, e ∈ es) → Reach sem es st →
    Reach sem es (buildTrace sem l st).1
  | [], _, _, h => h
  | e :: l, _, hl, h => reach_build l (fun e' he' => hl e' (by simp [he'])) (.step h (hl e (by simp)))

/-- **Headline (Stage 6).** After any history of edits and builds from empty
logs, a build gives correct contents, and a second build runs nothing. -/
theorem reach_sound {m : Manifest} (hs : Sched m.medges) (hr : Reads sem m.medges) {st : St V}
    (h : Reach sem m.medges st) :
    (denote sem m).Correct st.content (ninjaBuild sem m st).content ∧
      buildTrace sem m.medges (ninjaBuild sem m st) = (ninjaBuild sem m st, []) := by
  have hinv := inv_of_reach sem hs hr h
  exact ⟨sound_of_inv sem hs hr hinv, ninjaBuild_idem sem hs hr hinv.1 hinv.2.1⟩

/-! ## Command changes -/

/-- Two edge lists with the same outputs and inputs, edge by edge. -/
inductive SameShape : List MEdge → List MEdge → Prop
  | nil : SameShape [] []
  | cons {e e' : MEdge} {es es' : List MEdge} :
      e.outs = e'.outs ∧ e.ins = e'.ins ∧ e.oo = e'.oo ∧ e.dyn = e'.dyn ∧ e.restat = e'.restat →
        SameShape es es' →
      SameShape (e :: es) (e' :: es')

theorem SameShape.mem {es es' : List MEdge} (h : SameShape es es') {e' : MEdge} (he' : e' ∈ es') :
    ∃ e ∈ es, e.outs = e'.outs ∧ e.ins = e'.ins ∧ e.oo = e'.oo ∧ e.dyn = e'.dyn ∧ e.restat = e'.restat := by
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
    obtain ⟨ho, hi, hoo, -, -⟩ := hab
    refine ⟨?_, fun e' he' => ?_, ih hs.tail⟩
    · unfold MEdge.reads; rw [← ho, ← hi, ← hoo]; exact hs.1
    · obtain ⟨e, he, ho', -, -, -, -⟩ := hrest.mem he'
      unfold MEdge.reads; rw [← ho, ← hi, ← hoo, ← ho']; exact hs.2.1 e he

theorem allowed_shape {es es' : List MEdge} (h : SameShape es es') {e e' : MEdge} (hi : e.ins = e'.ins)
    (hoo : e.oo = e'.oo) {k : Path} (ha : Allowed es e k) : Allowed es' e' k := by
  rcases ha with ha | ha
  · exact .inl fun e'' he'' => by obtain ⟨e₀, he₀, ho, -⟩ := h.mem he''; rw [← ho]; exact ha e₀ he₀
  · exact .inr (by unfold MEdge.reads at ha ⊢; rw [← hi, ← hoo]; exact ha)

/-- Changing commands in the manifest rebuilds every edge whose command
changed, and the result is correct for the new manifest. `st` is any state
in which every edge of the old manifest is clean and the invariant holds,
such as the result of building the old manifest. -/
theorem command_change_rebuilds {m m' : Manifest} (hs : Sched m.medges) (hr' : Reads sem m'.medges)
    (hshape : SameShape m.medges m'.medges) {st : St V} (h : Inv sem m.medges st)
    (hclean : ∀ e ∈ m.medges, st.dirty e = false) :
    (denote sem m').Correct st.content (ninjaBuild sem m' st).content ∧
    ∀ e ∈ m.medges, ∀ e' ∈ m'.medges, e.outs = e'.outs → e.cmd ≠ e'.cmd → e'.outs ≠ [] →
      e' ∈ (buildTrace sem m'.medges st).2 := by
  have hs' := hshape.sched hs
  -- The old log makes every edge with a changed command dirty.
  have hstale : ∀ e ∈ m.medges, ∀ e' : MEdge, e.outs = e'.outs → e.cmd ≠ e'.cmd → ∀ o ∈ e'.outs, st.Stale e' o := by
    intro e he e' hout hcmd o ho c lt hlog
    obtain ⟨lt', hl⟩ := St.log_of_clean (St.dirty_false (hclean e he) (hout ▸ ho))
    rw [hl] at hlog
    simp only [Option.some.injEq, Prod.mk.injEq] at hlog
    rw [← hlog.1]; exact hcmd
  have hdo : DepsOK m'.medges st := by
    intro e' he' hdy o ho D hD k hk
    obtain ⟨e, he, hout, hin, hoo, hdyn, hrst⟩ := hshape.mem he'
    exact allowed_shape hshape hin hoo (h.2.1 e he (hdyn ▸ hdy) o (hout ▸ ho) D hD k hk)
  refine ⟨sound_of_inv sem hs' hr' ⟨h.1, hdo, fun e' he' => ?_⟩, ?_⟩
  · obtain ⟨e, he, hout, hin, hoo, hdyn, hrst⟩ := hshape.mem he'
    by_cases hcmd : e.cmd = e'.cmd
    · have : e = e' := by cases e; cases e'; simp_all
      subst this; exact h.2.2 e he
    · intro hcl o ho
      have := St.dirty_false hcl ho
      rw [St.outDirty_of_stale (hstale e he e' hout hcmd o ho)] at this
      cases this
  · intro e he e' he' hout hcmd hne
    obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ hne
    exact trace_mem_of_stale sem _ hs' he' ho (hstale e he e' hout hcmd o ho)

end Mise.Model
