import Mise.Model.Sound

/-!
# Stage 7: minimality and early cutoff

`build_minimal` says why an edge runs. Build after source edits from a state
`st`. An edge that runs was either already dirty in `st`, or one of the
inputs Ninja checks for one of its outputs was rewritten after `st.clock`,
by an edit or by an edge that ran earlier in the same build. `outDirty_cause`
spells out what "already dirty" means: a missing output, log entry or deps
entry, a different logged command, or an input newer than the log entry.
`trace_sublist` says each edge runs at most as often as it appears.

Early cutoff is the case of a `restat` edge that keeps an output. The kept
output keeps its old mtime, so it is never the rewritten input in
`build_minimal`, and `restat_cutoff` shows that a run keeping every output
changes no other edge's dirtiness.
-/

namespace Mise.Model
open Mise Mise.Syntax Mise.Frontend

variable {V : Type} [Inhabited V] (sem : Sem V)

/-! ## At most once -/

/-- The edges a build runs, in the order it runs them, are a sublist of the
schedule. -/
theorem trace_sublist : ∀ (l : List MEdge) (st : St V), (buildTrace sem l st).2.Sublist l
  | [], _ => List.Sublist.slnil
  | e :: l, st => by
    simp only [buildTrace]
    split
    · exact (trace_sublist l _).cons_cons e
    · exact (trace_sublist l _).cons e

/-- A schedule whose edges all have outputs lists each edge once. -/
theorem Sched.nodup : ∀ {es : List MEdge}, Sched es → (∀ e ∈ es, e.outs ≠ []) → es.Nodup
  | [], _, _ => List.nodup_nil
  | e :: es, hs, hne => by
    refine List.nodup_cons.mpr ⟨fun he => ?_, Sched.nodup hs.tail fun e' he' => hne e' (by simp [he'])⟩
    obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ (hne e (by simp))
    exact (hs.2.1 e he).2 o ho ho

/-- **At most once.** Each edge runs at most once per build. -/
theorem trace_nodup {es : List MEdge} (hs : Sched es) (hne : ∀ e ∈ es, e.outs ≠ []) (st : St V) :
    (buildTrace sem es st).2.Nodup :=
  (Sched.nodup hs hne).sublist (trace_sublist sem es st)

/-- An edge the build runs was dirty when its turn came. -/
theorem trace_split : ∀ (l : List MEdge) (st : St V) {e : MEdge}, e ∈ (buildTrace sem l st).2 →
    ∃ pre post, l = pre ++ e :: post ∧ (buildTrace sem pre st).1.dirty e = true
  | [], _, _, h => by simp [buildTrace] at h
  | a :: l, st, e, h => by
    simp only [buildTrace] at h
    by_cases hd : st.dirty a = true
    · rw [ite_eq_left hd] at h
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨[], l, rfl, hd⟩
      · obtain ⟨pre, post, rfl, h2⟩ := trace_split l _ h
        exact ⟨a :: pre, post, rfl, h2⟩
    · rw [ite_eq_right hd] at h
      obtain ⟨pre, post, rfl, h2⟩ := trace_split l _ h
      exact ⟨a :: pre, post, rfl, h2⟩

/-! ## Why an output is dirty -/

namespace St

omit [Inhabited V] in
theorem exists_of_lt_newest (st : St V) {b : Nat} : ∀ {ps : List Path}, b < st.newest ps →
    ∃ p ∈ ps, b < st.mtime p
  | [], h => by simp [newest] at h
  | q :: ps, h => by
    rcases Nat.lt_or_ge b (st.mtime q) with h1 | h1
    · exact ⟨q, by simp, h1⟩
    · have : b < st.newest ps := by simp only [newest] at h; omega
      obtain ⟨p, hp, h2⟩ := exists_of_lt_newest st this
      exact ⟨p, by simp [hp], h2⟩

omit [Inhabited V] in
/-- Ninja's reasons for a dirty output: the output, its log entry or its deps
entry is missing, or the logged command differs, or an input is newer than
the log entry, or, without `restat`, newer than the output. -/
theorem outDirty_cause {st : St V} {e : MEdge} {o : Path} (h : st.outDirty e o = true) :
    st.fs o = none ∨ st.log o = none ∨ st.effIns e o = none ∨
      ∃ v t c lt D, st.fs o = some (v, t) ∧ st.log o = some (c, lt) ∧ st.effIns e o = some D ∧
        (c ≠ e.cmd ∨ ∃ p ∈ D, lt < st.mtime p ∨ (e.restat = false ∧ t < st.mtime p)) := by
  cases h1 : st.fs o with
  | none => exact .inl rfl
  | some vt =>
    cases h2 : st.log o with
    | none => exact .inr (.inl rfl)
    | some cl =>
      cases h3 : st.effIns e o with
      | none => exact .inr (.inr (.inl rfl))
      | some D =>
        obtain ⟨v, t⟩ := vt
        obtain ⟨c, lt⟩ := cl
        refine .inr (.inr (.inr ⟨v, t, c, lt, D, rfl, rfl, rfl, ?_⟩))
        simp only [outDirty, h1, h2, h3, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_true_eq, bne_iff_ne, ne_eq] at h
        rcases h with (⟨hr, h4⟩ | h4) | h4
        · obtain ⟨p, hp, h5⟩ := st.exists_of_lt_newest h4
          exact .inr ⟨p, hp, .inr ⟨hr, h5⟩⟩
        · exact .inl h4
        · obtain ⟨p, hp, h5⟩ := st.exists_of_lt_newest h4
          exact .inr ⟨p, hp, .inl h5⟩

/-! ## Tracking writes -/

/-- Since `st`, every path either holds the same file, or was written after
`st.clock` and satisfies `W`. -/
def Track (st s : St V) (W : Path → Prop) : Prop :=
  st.clock ≤ s.clock ∧ ∀ p, s.fs p = st.fs p ∨ (st.clock < s.mtime p ∧ W p)

omit [Inhabited V] in
theorem Track.refl (st : St V) (W : Path → Prop) : Track st st W := ⟨Nat.le_refl _, fun _ => .inl rfl⟩

omit [Inhabited V] in
theorem Track.mono {st s : St V} {W W' : Path → Prop} (h : Track st s W) (hw : ∀ p, W p → W' p) :
    Track st s W' :=
  ⟨h.1, fun p => (h.2 p).imp_right fun ⟨a, b⟩ => ⟨a, hw p b⟩⟩

omit [Inhabited V] in
theorem Track.edit {st s : St V} {W : Path → Prop} (h : Track st s W) (p : Path) (v : V) :
    Track st (s.edit p v) fun q => W q ∨ q = p := by
  refine ⟨Nat.le_succ_of_le h.1, fun q => ?_⟩
  by_cases hq : q = p
  · subst hq
    refine .inr ⟨?_, .inr rfl⟩
    have := h.1
    simp only [mtime, St.edit, ite_true, Option.map_some, Option.getD_some]
    omega
  · have hfs : (s.edit p v).fs q = s.fs q := by simp [St.edit, hq]
    rcases h.2 q with h1 | ⟨h1, h2⟩
    · exact .inl (hfs.trans h1)
    · exact .inr ⟨by simp only [mtime, hfs]; exact h1, .inl h2⟩

omit [Inhabited V] in
theorem Track.edits {st : St V} : ∀ (E : List (Path × V)) {s : St V} {W : Path → Prop}, Track st s W →
    Track st (s.edits E) fun q => W q ∨ q ∈ E.map (·.1)
  | [], _, _, h => h.mono fun _ hp => .inl hp
  | (p, v) :: E, _, _, h => (Track.edits E (h.edit p v)).mono fun q hq => by
      simp only [List.map_cons, List.mem_cons]
      rcases hq with (hq | hq) | hq
      · exact .inl hq
      · exact .inr (.inl hq)
      · exact .inr (.inr hq)

theorem Track.run {st s : St V} {W : Path → Prop} (h : Track st s W) (e : MEdge) :
    Track st (s.run sem e) fun q => W q ∨ q ∈ e.outs := by
  refine ⟨Nat.le_succ_of_le h.1, fun q => ?_⟩
  by_cases hw : (e.outs.contains q && !s.kept sem e q) = true
  · have hfs : (s.run sem e).fs q = some (s.outVal sem e q, s.clock + 1) := by
      simp only [St.run]; rw [ite_eq_left hw]
    have := h.1
    refine .inr ⟨?_, .inr ?_⟩
    · simp only [mtime, hfs, Option.map_some, Option.getD_some]; omega
    · simp only [Bool.and_eq_true, List.contains_iff_mem] at hw; exact hw.1
  · have hfs : (s.run sem e).fs q = s.fs q := by simp only [St.run]; rw [ite_eq_right hw]
    rcases h.2 q with h1 | ⟨h1, h2⟩
    · exact .inl (hfs.trans h1)
    · exact .inr ⟨by simp only [mtime, hfs]; exact h1, .inl h2⟩

theorem Track.step {st s : St V} {W : Path → Prop} (h : Track st s W) (e : MEdge) :
    Track st (s.step sem e) fun q => W q ∨ (s.dirty e = true ∧ q ∈ e.outs) := by
  unfold St.step
  split
  · rename_i hd
    exact (h.run sem e).mono fun q hq => hq.imp_right fun ho => ⟨hd, ho⟩
  · exact h.mono fun _ hq => .inl hq

end St

theorem St.Track.build {st : St V} : ∀ (l : List MEdge) {s : St V} {W : Path → Prop}, St.Track st s W →
    St.Track st (buildTrace sem l s).1 fun q => W q ∨ ∃ e ∈ (buildTrace sem l s).2, q ∈ e.outs
  | [], _, _, h => h.mono fun _ hq => .inl hq
  | e :: l, s, _, h => by
    refine (St.Track.build l (h.step sem e)).mono fun q hq => ?_
    simp only [buildTrace]
    rcases hq with (hq | ⟨hd, ho⟩) | ⟨e', he', ho⟩
    · exact .inl hq
    · exact .inr ⟨e, by simp [hd], ho⟩
    · refine .inr ⟨e', ?_, ho⟩
      split <;> simp [he']

omit [Inhabited V] in
theorem edits_other {st : St V} : ∀ (E : List (Path × V)) {p : Path}, (∀ pv ∈ E, pv.1 ≠ p) →
    (st.edits E).fs p = st.fs p ∧ (st.edits E).log p = st.log p ∧ (st.edits E).deps p = st.deps p
  | [], _, _ => ⟨rfl, rfl, rfl⟩
  | (q, v) :: E, p, h => by
    have h1 := edits_other (st := st.edit q v) E fun pv hpv => h pv (by simp [hpv])
    have hq : p ≠ q := fun h' => h (q, v) (by simp) h'.symm
    exact ⟨h1.1.trans (by simp [St.edit, hq]), h1.2.1, h1.2.2⟩

/-- No edge before `e` in a schedule shares an output with it. -/
theorem Sched.before {e : MEdge} {post : List MEdge} : ∀ {pre : List MEdge}, Sched (pre ++ e :: post) →
    ∀ e' ∈ pre, Disjoint e'.outs e.outs
  | [], _, _, he' => by simp at he'
  | a :: pre, hs, e', he' => by
    simp only [List.mem_cons] at he'
    rcases he' with rfl | he'
    · exact (hs.2.1 e (by simp)).2
    · exact Sched.before hs.2.2 e' he'

/-! ## Minimality -/

/-- **Minimality, one edge.** Build after source edits `E` from `st`. If
edge `e` is dirty when its turn comes, then it was already dirty in `st`, or
for one of its outputs one of the inputs Ninja checks was written after
`st.clock`, by an edit or by an edge that ran earlier in this build. -/
theorem run_cause {pre post : List MEdge} {e : MEdge} (hs : Sched (pre ++ e :: post)) {st : St V}
    (E : List (Path × V)) (hE : ∀ pv ∈ E, pv.1 ∉ e.outs)
    (hrun : (buildTrace sem pre (st.edits E)).1.dirty e = true) :
    st.dirty e = true ∨ ∃ o ∈ e.outs, ∃ D, st.effIns e o = some D ∧ ∃ p ∈ D,
      st.clock < (buildTrace sem pre (st.edits E)).1.mtime p ∧
        (p ∈ E.map (·.1) ∨ ∃ e' ∈ (buildTrace sem pre (st.edits E)).2, p ∈ e'.outs) := by
  cases hd : st.dirty e
  · right
    have htr := St.Track.build sem pre ((St.Track.refl st fun _ => False).edits E)
    obtain ⟨o, ho, hdo⟩ := List.any_eq_true.mp hrun
    obtain ⟨v, t, lt, D, hfs, hlog, hD, ht, hlt⟩ := St.outDirty_false_iff.mp (St.clean_iff.mp hd o ho)
    have hb := build_other sem pre (st := st.edits E) fun e' he' hoe' => Sched.before hs e' he' o hoe' ho
    have he := edits_other (st := st) E fun pv hpv h => hE pv hpv (h ▸ ho)
    have hfs' : (buildTrace sem pre (st.edits E)).1.fs o = some (v, t) := by rw [hb.1, he.1, hfs]
    have hlog' : (buildTrace sem pre (st.edits E)).1.log o = some (e.cmd, lt) := by rw [hb.2.1, he.2.1, hlog]
    have hD' : (buildTrace sem pre (st.edits E)).1.effIns e o = some D := by
      rw [← hD]; simp only [St.effIns, hb.2.2, he.2.2]
    simp only [St.outDirty, hfs', hlog', hD', bne_self_eq_false, Bool.or_false, Bool.or_eq_true,
      Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hdo
    have hbnd : ∃ b, st.newest D ≤ b ∧ b < (buildTrace sem pre (st.edits E)).1.newest D := by
      rcases hdo with ⟨hr, h1⟩ | h1
      · exact ⟨t, ht hr, h1⟩
      · exact ⟨lt, hlt, h1⟩
    obtain ⟨b, hb1, hb2⟩ := hbnd
    obtain ⟨p, hp, hpb⟩ := St.exists_of_lt_newest _ hb2
    refine ⟨o, ho, D, hD, p, hp, ?_⟩
    rcases htr.2 p with h1 | ⟨h1, h2⟩
    · have : (buildTrace sem pre (st.edits E)).1.mtime p = st.mtime p := by simp only [St.mtime, h1]
      have := st.le_newest hp
      omega
    · refine ⟨h1, ?_⟩
      rcases h2 with (h2 | h2) | h2
      · exact h2.elim
      · exact .inl h2
      · exact .inr h2
  · exact .inl rfl

/-- **Minimality.** Every edge a build runs after source edits had a reason
to run: it was already dirty before the edits (`outDirty_cause` lists why),
or an input Ninja checks for one of its outputs was written after the
previous state, by an edit or by an edge that ran earlier in the build. -/
theorem build_minimal {es : List MEdge} (hs : Sched es) {st : St V} (E : List (Path × V))
    (hE : ∀ pv ∈ E, ∀ e ∈ es, pv.1 ∉ e.outs) {e : MEdge} (he : e ∈ (buildTrace sem es (st.edits E)).2) :
    ∃ pre post, es = pre ++ e :: post ∧
      (st.dirty e = true ∨ ∃ o ∈ e.outs, ∃ D, st.effIns e o = some D ∧ ∃ p ∈ D,
        st.clock < (buildTrace sem pre (st.edits E)).1.mtime p ∧
          (p ∈ E.map (·.1) ∨ ∃ e' ∈ (buildTrace sem pre (st.edits E)).2, p ∈ e'.outs)) := by
  obtain ⟨pre, post, rfl, hd⟩ := trace_split sem _ _ he
  exact ⟨pre, post, rfl, run_cause sem hs E (fun pv hpv => hE pv hpv e (by simp)) hd⟩

/-- From a state where every edge is clean, such as the result of a build,
only edges with an input written since then run. -/
theorem build_minimal_clean {es : List MEdge} (hs : Sched es) {st : St V} (hclean : ∀ e ∈ es, st.dirty e = false)
    (E : List (Path × V)) (hE : ∀ pv ∈ E, ∀ e ∈ es, pv.1 ∉ e.outs) {e : MEdge}
    (he : e ∈ (buildTrace sem es (st.edits E)).2) :
    ∃ pre post, es = pre ++ e :: post ∧ ∃ o ∈ e.outs, ∃ D, st.effIns e o = some D ∧ ∃ p ∈ D,
      st.clock < (buildTrace sem pre (st.edits E)).1.mtime p ∧
        (p ∈ E.map (·.1) ∨ ∃ e' ∈ (buildTrace sem pre (st.edits E)).2, p ∈ e'.outs) := by
  obtain ⟨pre, post, hes, h⟩ := build_minimal sem hs E hE he
  refine ⟨pre, post, hes, h.resolve_left fun hd => ?_⟩
  rw [hclean e (by simp [hes])] at hd; cases hd

/-! ## Early cutoff -/

/-- A kept output's file, mtime included, is untouched by the run. -/
theorem St.run_kept {st : St V} {e : MEdge} {o : Path} (hk : st.kept sem e o = true) :
    (st.run sem e).fs o = st.fs o := by
  simp [St.run, hk]

/-- **Early cutoff.** A `restat` run that keeps every output leaves every
file as it was, so it changes no other edge's dirtiness: dependents are not
rebuilt on its account. -/
theorem restat_cutoff {st : St V} {e e' : MEdge} (hdis : Disjoint e'.outs e.outs)
    (hk : ∀ o ∈ e.outs, st.kept sem e o = true) : (st.run sem e).dirty e' = st.dirty e' := by
  have hfs : ∀ p, (st.run sem e).fs p = st.fs p := by
    intro p
    by_cases hp : p ∈ e.outs
    · exact St.run_kept sem (hk p hp)
    · exact (St.run_other sem hp).1
  refine St.dirty_congr (fun o ho => ?_) fun _ _ _ _ p _ => hfs p
  have := St.run_other sem (st := st) (hdis o ho)
  exact ⟨hfs o, this.2.1, this.2.2⟩

/-- A kept output is never the reason a later edge runs: when its file is
untouched since `st`, its mtime is at most `st.clock`. -/
theorem St.kept_not_newer {st s : St V} (hf : st.Fresh) {p : Path} (h : s.fs p = st.fs p) :
    s.mtime p ≤ st.clock := by
  simp only [St.mtime, h]; exact St.mtime_le_clock hf p

end Mise.Model
