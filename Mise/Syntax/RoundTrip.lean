import Mise.Syntax.Print
import Mise.Syntax.Parse

/-!
# Stage 3: the printer is a right inverse of the parser model

`parse_print`: for every well-formed manifest `m`, `parse (print m) = some m`.
-/

namespace Mise.Syntax

/-! ## Character facts -/

theorem isVarChar_ne {c : Char} (h : isVarChar c = true) :
    c ≠ ' ' ∧ c ≠ '#' ∧ c ≠ '\n' ∧ c ≠ ':' ∧ c ≠ '|' ∧ c ≠ '}' ∧ c ≠ '=' ∧ c ≠ '$' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; revert h; decide)

theorem pathChar_ne {c : Char} (h : pathChar c = true) :
    c ≠ '\n' ∧ c ≠ '|' ∧ litChar c = true := by
  simp only [pathChar, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  refine ⟨?_, h.2, h.1⟩
  rintro rfl; exact absurd h.1 (by decide)

theorem litChar_ne {c : Char} (h : litChar c = true) : c ≠ '\n' := by
  rintro rfl; exact absurd h (by decide)

/-! ## `eatSpaces` -/

@[simp] theorem eatSpaces_nil : eatSpaces [] = [] := rfl

@[simp] theorem eatSpaces_space (l : List Char) : eatSpaces (' ' :: l) = eatSpaces l := by
  simp [eatSpaces]

theorem eatSpaces_of_ne {c : Char} (l : List Char) (h : c ≠ ' ') : eatSpaces (c :: l) = c :: l := by
  simp [eatSpaces, h]

/-! ## `spanWhile` and `readIdent` -/

theorem spanWhile_append (p : Char → Bool) (w X : List Char) (hw : w.all p = true)
    (hX : ∀ c r, X = c :: r → p c = false) : spanWhile p (w ++ X) = (w, X) := by
  induction w with
  | nil =>
    cases X with
    | nil => rfl
    | cons c r => simp [spanWhile, hX c r rfl]
  | cons c w ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    simp [spanWhile, hw.1, ih hw.2]

theorem readIdent_append (w X : List Char) (hne : w ≠ []) (hw : w.all isVarChar = true)
    (hX : ∀ c r, X = c :: r → isVarChar c = false) :
    readIdent (w ++ X) = some (w, eatSpaces X) := by
  unfold readIdent
  rw [spanWhile_append _ _ _ hw hX]
  cases w with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

theorem validIdent_parts {s : String} (h : validIdent s = true) :
    s.toList ≠ [] ∧ s.toList.all isVarChar = true := by
  unfold validIdent at h
  generalize s.toList = l at h ⊢
  cases l <;> simp_all

/-! ## Paths -/

theorem readPath_dollar (d : Char) (r : List Char) :
    readPath ('$' :: d :: r) =
      if d = '$' ∨ d = ' ' ∨ d = ':' then (readPath r).map (fun x => (d :: x.1, x.2)) else none := by
  rw [readPath.eq_def]; simp [or_assoc]

theorem readPath_delim_cons {c : Char} (r : List Char) (h : c = ' ' ∨ c = ':' ∨ c = '|') :
    readPath (c :: r) = some ([], c :: r) := by
  rw [readPath.eq_def]; rcases h with rfl | rfl | rfl <;> simp

theorem readPath_plain {c : Char} (r : List Char) (h1 : c ≠ '$') (h2 : c ≠ ' ') (h3 : c ≠ ':')
    (h4 : c ≠ '|') (h5 : litChar c = true) :
    readPath (c :: r) = (readPath r).map (fun x => (c :: x.1, x.2)) := by
  rw [readPath.eq_def]; simp [h1, h2, h3, h4, h5]

/-- A list that is empty or starts with a character satisfying `P`. -/
def StartsWith (P : Char → Prop) (l : List Char) : Prop := ∀ c r, l = c :: r → P c

theorem readPath_delim (X : List Char) (hX : StartsWith (fun c => c = ' ' ∨ c = ':' ∨ c = '|') X) :
    readPath X = some ([], X) := by
  cases X with
  | nil => rfl
  | cons c r =>
    exact readPath_delim_cons r (hX c r rfl)

theorem readPath_esc (cs X : List Char) (hcs : cs.all pathChar = true)
    (hX : StartsWith (fun c => c = ' ' ∨ c = ':' ∨ c = '|') X) :
    readPath (cs.flatMap escPathChar ++ X) = some (cs, X) := by
  induction cs with
  | nil => exact readPath_delim X hX
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hcs
    have ih := ih hcs.2
    obtain ⟨hnl, hbar, hlit⟩ := pathChar_ne hcs.1
    simp only [List.flatMap_cons, List.append_assoc]
    by_cases h1 : c = '$'
    · subst h1; simp [escPathChar, readPath_dollar, ih]
    by_cases h2 : c = ' '
    · subst h2; simp [escPathChar, readPath_dollar, ih]
    by_cases h3 : c = ':'
    · subst h3; simp [escPathChar, readPath_dollar, ih]
    have : escPathChar c = [c] := by simp [escPathChar, h1, h2, h3]
    rw [this, List.singleton_append, readPath_plain _ h1 h2 h3 hbar hlit, ih]; rfl

theorem escPath_cons (p : Path) (hne : p.toList ≠ []) :
    ∃ c r, escPath p = c :: r ∧ c ≠ ' ' := by
  obtain ⟨c, cs, hp⟩ := List.exists_cons_of_ne_nil hne
  unfold escPath; rw [hp]
  simp only [List.flatMap_cons]
  by_cases h1 : c = '$'
  · simp [escPathChar, h1]
  by_cases h2 : c = ' '
  · simp [escPathChar, h2]
  by_cases h3 : c = ':'
  · simp [escPathChar, h3]
  simp [escPathChar, h1, h2, h3]

theorem validPath_parts {p : Path} (h : validPath p = true) :
    p.toList ≠ [] ∧ p.toList.all pathChar = true := by
  unfold validPath at h
  generalize p.toList = l at h ⊢
  cases l <;> simp_all

theorem readPaths_pathList (ps : List Path) (T : List Char) (hps : ps.all validPath = true)
    (hT : StartsWith (fun c => c = ' ' ∨ c = ':' ∨ c = '|') T)
    (hT' : StartsWith (fun c => c = ':' ∨ c = '|') (eatSpaces T)) :
    readPaths (eatSpaces (pathList ps ++ T)) = some (ps.map String.toList, eatSpaces T) := by
  induction ps with
  | nil =>
    simp only [pathList, List.flatMap_nil, List.nil_append, List.map_nil]
    have := readPath_delim (eatSpaces T) (fun c r h => by rcases hT' c r h with h | h <;> simp [h])
    rw [readPaths]; split <;> simp_all
  | cons p ps ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have ih := ih hps.2
    obtain ⟨hne, hpc⟩ := validPath_parts hps.1
    obtain ⟨c, r, hesc, hc⟩ := escPath_cons p hne
    have hrest : StartsWith (fun c => c = ' ' ∨ c = ':' ∨ c = '|') (pathList ps ++ T) := by
      intro c' r' h
      cases ps with
      | nil => exact hT c' r' (by simpa [pathList] using h)
      | cons q qs => simp [pathList] at h; exact Or.inl h.1.symm
    have hrp : readPath (escPath p ++ (pathList ps ++ T)) = some (p.toList, pathList ps ++ T) :=
      readPath_esc _ _ hpc hrest
    have hpath : pathList (p :: ps) ++ T = ' ' :: (escPath p ++ (pathList ps ++ T)) := by
      simp [pathList]
    rw [hpath, eatSpaces_space, hesc, List.cons_append, eatSpaces_of_ne _ hc, ← List.cons_append,
      ← hesc]
    obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil hne
    rw [readPaths]
    split
    · simp_all
    · simp_all
    · rename_i heq; rw [hrp] at heq; simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨h1, rfl⟩ := heq
      rw [ih, ← h1]; simp

/-! ## Values -/

theorem readValue_dollar_esc {d : Char} (r : List Char) (h : d = '$' ∨ d = ' ' ∨ d = ':') :
    readValue ('$' :: d :: r) = (readValue r).map (consLit d) := by
  rw [readValue.eq_def]; rcases h with rfl | rfl | rfl <;> simp

theorem readValue_brace (n X : List Char) (hne : n ≠ []) (hn : n.all isVarChar = true) :
    readValue ('$' :: '{' :: (n ++ '}' :: X)) =
      (readValue X).map (Seg.var (String.ofList n) :: ·) := by
  rw [readValue.eq_def]
  have hs : spanWhile isVarChar (n ++ '}' :: X) = (n, '}' :: X) :=
    spanWhile_append _ _ _ hn (fun c r h => by cases h; decide)
  simp only [ite_true, Bool.or_eq_true, decide_eq_true_eq]
  simp only [show ¬('{' = '$' ∨ '{' = ' ' ∨ '{' = ':') by decide, ite_false, or_assoc]
  split
  · rename_i heq; rw [hs] at heq; simp only [Prod.mk.injEq, List.cons.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    cases n with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  · rename_i heq; rw [hs] at heq; simp at heq

theorem readValue_plain {c : Char} (r : List Char) (h1 : c ≠ '$') (h2 : litChar c = true) :
    readValue (c :: r) = (readValue r).map (consLit c) := by
  rw [readValue.eq_def]; simp [h1, h2]

theorem validEval_cons {s : Seg} {r : EvalString} (h : validEval (s :: r) = true) :
    s.valid = true ∧ validEval r = true := by
  unfold validEval at h ⊢
  simp only [List.all_cons, Bool.and_eq_true] at h ⊢
  refine ⟨h.1.1, h.1.2, ?_⟩
  have := h.2
  cases r with
  | nil => rfl
  | cons s' r' => cases s <;> cases s' <;> simp_all [noAdjLits]

theorem noAdj_lit {s : String} {r : EvalString} (h : validEval (.lit s :: r) = true) :
    ∀ x r', r = x :: r' → ∃ n, x = .var n := by
  intro x r' hr; subst hr
  unfold validEval at h
  cases x with
  | lit _ => simp [noAdjLits] at h
  | var n => exact ⟨n, rfl⟩

theorem readValue_escLits (cs X : List Char) (hcs : cs.all litChar = true) :
    readValue (cs.flatMap escValChar ++ X) = (readValue X).map (cs.foldr consLit) := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hcs
    have ih := ih hcs.2
    simp only [List.flatMap_cons, List.append_assoc, List.foldr_cons]
    by_cases h1 : c = '$'
    · subst h1
      simp only [escValChar, ite_true, List.cons_append, List.nil_append]
      rw [readValue_dollar_esc _ (Or.inl rfl), ih, Option.map_map]; rfl
    · simp only [escValChar, h1, ite_false, List.singleton_append]
      rw [readValue_plain _ h1 hcs.1, ih, Option.map_map]; rfl

theorem foldr_consLit (cs : List Char) (t : EvalString) (hne : cs ≠ [])
    (ht : ∀ x r', t = x :: r' → ∃ n, x = .var n) :
    cs.foldr consLit t = .lit (String.ofList cs) :: t := by
  induction cs with
  | nil => exact absurd rfl hne
  | cons c cs ih =>
    cases cs with
    | nil =>
      simp only [List.foldr_cons, List.foldr_nil, consLit]
      cases t with
      | nil => rfl
      | cons x r' => obtain ⟨n, rfl⟩ := ht x r' rfl; rfl
    | cons c' cs' =>
      rw [List.foldr_cons, ih (by simp)]
      simp [consLit]

theorem validLit_parts {s : String} (h : validLit s = true) :
    s.toList ≠ [] ∧ s.toList.all litChar = true := by
  unfold validLit at h
  generalize s.toList = l at h ⊢
  cases l <;> simp_all

theorem readValue_segs (e : EvalString) (he : validEval e = true) :
    readValue (e.flatMap renderSeg) = some e := by
  induction e with
  | nil => simp [readValue]
  | cons s r ih =>
    obtain ⟨hs, hr⟩ := validEval_cons he
    have ih := ih hr
    cases s with
    | lit str =>
      obtain ⟨hne, hlit⟩ := validLit_parts (by simpa [Seg.valid] using hs)
      simp only [List.flatMap_cons, renderSeg]
      rw [readValue_escLits _ _ hlit, ih]
      simp only [Option.map_some, Option.some.injEq]
      rw [foldr_consLit _ _ hne (noAdj_lit he)]
      simp
    | var n =>
      obtain ⟨hne, hn⟩ := validIdent_parts (by simpa [Seg.valid] using hs)
      simp only [List.flatMap_cons, renderSeg, List.cons_append, List.append_assoc]
      rw [readValue_brace _ _ hne hn]
      simp [ih]

theorem readValue_escLead (cs X : List Char) :
    readValue (escLead cs ++ X) = readValue (cs.flatMap escValChar ++ X) := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    simp only [escLead]
    split
    · rename_i h; subst h
      simp only [List.cons_append, List.flatMap_cons, escValChar]
      rw [readValue_dollar_esc _ (Or.inr (Or.inl rfl))]
      simp only [show ¬(' ' = '$') by decide, ite_false, List.cons_append]
      rw [readValue_plain (c := ' ') _ (by decide) (by decide)]
      simp
    · rfl

theorem readValue_renderVal (e : EvalString) (he : validEval e = true) :
    readValue (renderVal e) = some e := by
  rw [← readValue_segs e he]
  cases e with
  | nil => rfl
  | cons s r =>
    cases s with
    | lit str =>
      simp only [renderVal, List.flatMap_cons, renderSeg]
      exact readValue_escLead _ _
    | var n => rfl

theorem renderVal_start (e : EvalString) (he : validEval e = true) :
    StartsWith (· ≠ ' ') (renderVal e) := by
  intro c r h
  cases e with
  | nil => simp [renderVal] at h
  | cons s t =>
    cases s with
    | var n => simp [renderVal, renderSeg] at h; rw [← h.1]; decide
    | lit str =>
      obtain ⟨hne, -⟩ := validLit_parts (by simpa [Seg.valid] using (validEval_cons he).1)
      simp only [renderVal] at h
      generalize str.toList = cs at h hne
      cases cs with
      | nil => exact absurd rfl hne
      | cons d ds =>
        simp only [escLead] at h
        split at h
        · simp at h; rw [← h.1]; decide
        · rename_i hd
          simp only [List.flatMap_cons, escValChar, List.append_assoc] at h
          split at h
          · simp at h; rw [← h.1]; decide
          · simp at h; rw [← h.1]; exact hd

theorem eatSpaces_of_start {l : List Char} (h : StartsWith (· ≠ ' ') l) : eatSpaces l = l := by
  cases l with
  | nil => rfl
  | cons c r => exact eatSpaces_of_ne r (h c r rfl)

/-! ## `readPaths` and sections -/

theorem toPaths_map (ps : List Path) : toPaths (ps.map String.toList) = ps := by
  simp [toPaths]

theorem pathList_start (ps : List Path) (T : List Char) (hT : StartsWith (· = ' ') T) :
    StartsWith (· = ' ') (pathList ps ++ T) := by
  intro c r h
  cases ps with
  | nil => exact hT c r (by simpa [pathList] using h)
  | cons q qs => simp [pathList] at h; exact h.1.symm

theorem pathList_cons_start (p : Path) (ps : List Path) (T : List Char) :
    StartsWith (· = ' ') (pathList (p :: ps) ++ T) := by
  intro c r h; simp [pathList] at h; exact h.1.symm

theorem pathList_cons_ne (p : Path) (ps : List Path) (T : List Char) :
    pathList (p :: ps) ++ T ≠ [] := by simp [pathList]

theorem eatSpaces_pathSection_cons (sep : List Char) (p : Path) (ps : List Path) (T : List Char)
    (hsep : StartsWith (· ≠ ' ') sep) (hne : sep ≠ []) :
    eatSpaces (pathSection sep (p :: ps) ++ T) = sep ++ (pathList (p :: ps) ++ T) := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [pathSection, List.isEmpty_cons, Bool.false_eq_true, ite_false, List.cons_append,
    eatSpaces_space, List.append_assoc]
  exact eatSpaces_of_ne _ (hsep c cs rfl)

theorem section1_bar (X : List Char) (hX : StartsWith (· = ' ') X) (hne : X ≠ []) :
    section1 ('|' :: X) = readPaths (eatSpaces X) := by
  obtain ⟨c, r, rfl⟩ := List.exists_cons_of_ne_nil hne
  have := hX c r rfl; subst this
  simp [section1]

theorem section2_bars (X : List Char) (hX : StartsWith (· = ' ') X) (hne : X ≠ []) :
    section2 ('|' :: '|' :: X) = readPaths (eatSpaces X) := by
  obtain ⟨c, r, rfl⟩ := List.exists_cons_of_ne_nil hne
  have := hX c r rfl; subst this
  simp [section2]

theorem section1_pathSection (ps : List Path) (T : List Char) (hps : ps.all validPath = true)
    (hT : StartsWith (fun c => c = ' ' ∨ c = ':' ∨ c = '|') T)
    (hT' : StartsWith (fun c => c = ':' ∨ c = '|') (eatSpaces T))
    (hS : section1 (eatSpaces T) = some ([], eatSpaces T)) :
    section1 (eatSpaces (pathSection ['|'] ps ++ T)) = some (ps.map String.toList, eatSpaces T) := by
  cases ps with
  | nil => simpa [pathSection] using hS
  | cons p ps =>
    rw [eatSpaces_pathSection_cons _ _ _ _ (by intro c r h; cases h; decide) (by simp),
      List.singleton_append, section1_bar _ (pathList_cons_start _ _ _) (pathList_cons_ne _ _ _)]
    exact readPaths_pathList _ _ hps hT hT'

theorem section2_pathSection (ps : List Path) (hps : ps.all validPath = true) :
    section2 (eatSpaces (pathSection ['|', '|'] ps)) = some (ps.map String.toList, []) := by
  cases ps with
  | nil => simp [pathSection, section2]
  | cons p ps =>
    have h := eatSpaces_pathSection_cons ['|', '|'] p ps [] (by intro c r h; cases h; decide) (by simp)
    simp only [List.append_nil] at h
    have h2 := section2_bars _ (pathList_cons_start p ps []) (pathList_cons_ne p ps [])
    simp only [List.append_nil] at h2
    rw [h, List.cons_append, List.cons_append, List.nil_append, h2]
    have := readPaths_pathList (p :: ps) [] hps (by intro c r h; cases h) (by intro c r h; cases h)
    simpa using this

theorem readPaths_nil_tail {l r : List Char} (h : readPath l = some ([], r)) :
    readPaths l = some ([], r) := by
  rw [readPaths]; split <;> simp_all

/-! ## Edge lines -/

theorem readIdent_tail_ok (T : List Char) (hT : StartsWith (fun c => c = ' ' ∨ c = '|' ∨ c = ':') T) :
    ∀ c r, T = c :: r → isVarChar c = false := by
  intro c r h
  rcases hT c r h with rfl | rfl | rfl <;> decide

theorem eatSpaces_section (sep : List Char) (ps : List Path) (X : List Char)
    (hsep : StartsWith (· ≠ ' ') sep) (hne : sep ≠ []) :
    eatSpaces (pathSection sep ps ++ X) = if ps = [] then eatSpaces X else sep ++ (pathList ps ++ X) := by
  cases ps with
  | nil => simp [pathSection]
  | cons p ps => simp only [reduceCtorEq, ite_false]; exact eatSpaces_pathSection_cons _ _ _ _ hsep hne

theorem section_start (P : Char → Prop) (sep : List Char) (ps : List Path) (X : List Char)
    (hX : StartsWith P X) (hP : P ' ') : StartsWith P (pathSection sep ps ++ X) := by
  intro c r h
  cases ps with
  | nil => exact hX c r (by simpa [pathSection] using h)
  | cons _ _ => simp [pathSection] at h; rw [← h.1]; exact hP

theorem bar_ne : StartsWith (· ≠ ' ') ['|'] := by intro c r h; cases h; decide
theorem bars_ne : StartsWith (· ≠ ' ') ['|', '|'] := by intro c r h; cases h; decide

theorem parseEdgeLine_print (e : Edge) (hrule : validIdent e.rule = true)
    (hpaths : e.allPaths.all validPath = true) :
    parseEdgeLine (eatSpaces (pathList e.outs ++ (pathSection ['|'] e.implicitOuts ++
      (':' :: ' ' :: (e.rule.toList ++ (pathList e.ins ++ (pathSection ['|'] e.implicitIns ++
      pathSection ['|', '|'] e.orderOnly))))))) = some { e with bindings := [] } := by
  simp only [Edge.allPaths, Edge.allOuts, Edge.allIns, List.all_append, Bool.and_eq_true] at hpaths
  obtain ⟨⟨hpo, hpio⟩, ⟨hpi, hpii⟩, hpoo⟩ := hpaths
  obtain ⟨hrne, hrv⟩ := validIdent_parts hrule
  -- the last tail
  have hT5s : StartsWith (· = ' ') (pathSection ['|', '|'] e.orderOnly) := by
    have := section_start (· = ' ') ['|', '|'] e.orderOnly [] (by intro c r h; cases h) rfl
    simpa using this
  have hT5e : StartsWith (· = '|') (eatSpaces (pathSection ['|', '|'] e.orderOnly)) := by
    have := eatSpaces_section ['|', '|'] e.orderOnly [] bars_ne (by simp)
    simp only [List.append_nil, eatSpaces_nil] at this
    rw [this]; split
    · intro c r h; cases h
    · intro c r h; simp at h; exact h.1.symm
  have hT5S : section1 (eatSpaces (pathSection ['|', '|'] e.orderOnly)) =
      some ([], eatSpaces (pathSection ['|', '|'] e.orderOnly)) := by
    have := eatSpaces_section ['|', '|'] e.orderOnly [] bars_ne (by simp)
    simp only [List.append_nil, eatSpaces_nil] at this
    rw [this]; split
    · rfl
    · simp [section1]
  -- the tail after the explicit inputs
  have hT4s : StartsWith (· = ' ') (pathSection ['|'] e.implicitIns ++ pathSection ['|', '|'] e.orderOnly) :=
    section_start _ _ _ _ hT5s rfl
  have hT4e : StartsWith (fun c => c = ':' ∨ c = '|')
      (eatSpaces (pathSection ['|'] e.implicitIns ++ pathSection ['|', '|'] e.orderOnly)) := by
    rw [eatSpaces_section _ _ _ bar_ne (by simp)]; split
    · intro c r h; exact Or.inr (hT5e c r h)
    · intro c r h; simp at h; exact Or.inr h.1.symm
  -- the tail after the rule name
  have hT3s : StartsWith (· = ' ') (pathList e.ins ++ (pathSection ['|'] e.implicitIns ++
      pathSection ['|', '|'] e.orderOnly)) := pathList_start _ _ hT4s
  -- the tail after the explicit outputs
  generalize hT2 : ':' :: ' ' :: (e.rule.toList ++ (pathList e.ins ++ (pathSection ['|'] e.implicitIns ++
      pathSection ['|', '|'] e.orderOnly))) = T2
  have hT2e : eatSpaces T2 = T2 := by rw [← hT2]; exact eatSpaces_of_ne _ (by decide)
  have hT2s : StartsWith (· = ':') T2 := by rw [← hT2]; intro c r h; simp at h; exact h.1.symm
  have hT1s : StartsWith (fun c => c = ' ' ∨ c = ':' ∨ c = '|') (pathSection ['|'] e.implicitOuts ++ T2) :=
    section_start _ _ _ _ (fun c r h => Or.inr (Or.inl (hT2s c r h))) (Or.inl rfl)
  have hT1e : StartsWith (fun c => c = ':' ∨ c = '|') (eatSpaces (pathSection ['|'] e.implicitOuts ++ T2)) := by
    rw [eatSpaces_section _ _ _ bar_ne (by simp)]; split
    · rw [hT2e]; intro c r h; exact Or.inl (hT2s c r h)
    · intro c r h; simp at h; exact Or.inr h.1.symm
  have hA := readPaths_pathList e.outs _ hpo hT1s hT1e
  have hB := section1_pathSection e.implicitOuts T2 hpio
    (fun c r h => Or.inr (Or.inl (hT2s c r h))) (by rw [hT2e]; intro c r h; exact Or.inl (hT2s c r h))
    (by rw [hT2e, ← hT2]; simp [section1])
  rw [hT2e] at hB
  have hC := readIdent_append e.rule.toList _ hrne hrv
    (readIdent_tail_ok _ (fun c r h => Or.inl (hT3s c r h)))
  have hD := readPaths_pathList e.ins _ hpi (fun c r h => Or.inl (hT4s c r h)) hT4e
  have hE := section1_pathSection e.implicitIns _ hpii (fun c r h => Or.inl (hT5s c r h))
    (fun c r h => Or.inr (hT5e c r h)) hT5S
  have hF := section2_pathSection e.orderOnly hpoo
  unfold parseEdgeLine
  rw [hA]
  simp only [Option.bind_eq_bind, Option.bind_some, hB]
  rw [← hT2]
  simp only [ite_true, eatSpaces_space]
  rw [eatSpaces_of_start (fun c r h => by
    obtain ⟨d, ds, hd⟩ := List.exists_cons_of_ne_nil hrne
    rw [hd] at h hrv; simp at h; rw [← h.1]; exact (isVarChar_ne (by simp at hrv; exact hrv.1)).1)]
  simp only [hC, Option.bind_some, hD, hE, hF, List.isEmpty_nil, ite_true, toPaths_map]
  simp

/-! ## Headers -/

theorem ident_head {s : String} (h : validIdent s = true) :
    ∃ c r, s.toList = c :: r ∧ c ≠ ' ' ∧ c ≠ '#' := by
  obtain ⟨hne, hv⟩ := validIdent_parts h
  obtain ⟨c, r, hcr⟩ := List.exists_cons_of_ne_nil hne
  rw [hcr] at hv; simp only [List.all_cons, Bool.and_eq_true] at hv
  have := isVarChar_ne hv.1
  exact ⟨c, r, hcr, this.1, this.2.1⟩

theorem parseHeader_binding (k : String) (v : EvalString) (hk : validIdent k = true)
    (hkw : keywords.contains k.toList = false) (hv : validEval v = true) :
    parseHeader (bindingLine false (k, v)) = some (.binding (k, v)) := by
  obtain ⟨hne, hkv⟩ := validIdent_parts hk
  have hr := readIdent_append k.toList (' ' :: '=' :: ' ' :: renderVal v) hne hkv
    (fun c r h => by cases h; decide)
  simp only [bindingLine, Bool.false_eq_true, ite_false, List.nil_append, List.append_assoc,
    List.cons_append] at hr ⊢
  have hne1 : k.toList ≠ ['r', 'u', 'l', 'e'] := by
    intro h; rw [h] at hkw; exact absurd hkw (by decide)
  have hne2 : k.toList ≠ ['b', 'u', 'i', 'l', 'd'] := by
    intro h; rw [h] at hkw; exact absurd hkw (by decide)
  have hne3 : k.toList ≠ ['d', 'e', 'f', 'a', 'u', 'l', 't'] := by
    intro h; rw [h] at hkw; exact absurd hkw (by decide)
  unfold parseHeader
  rw [hr]
  simp only [Option.bind_eq_bind, Option.bind_some, hne1, hne2, hne3, hkw, ite_false,
    eatSpaces_space, Bool.false_eq_true]
  rw [eatSpaces_of_ne _ (by decide)]
  simp only [ite_true]
  rw [eatSpaces_space, eatSpaces_of_start (renderVal_start v hv), readValue_renderVal v hv]
  simp

theorem parseHeader_rule (n : String) (hn : validIdent n = true) :
    parseHeader (['r', 'u', 'l', 'e', ' '] ++ n.toList) = some (.rule n) := by
  obtain ⟨hne, hnv⟩ := validIdent_parts hn
  obtain ⟨c, r, hcr, hc, -⟩ := ident_head hn
  have h1 := readIdent_append ['r', 'u', 'l', 'e'] (' ' :: n.toList) (by simp) (by decide)
    (fun c r h => by cases h; decide)
  have h2 := readIdent_append n.toList [] hne hnv (fun c r h => by cases h)
  simp only [List.append_nil] at h2
  simp only [List.cons_append, List.nil_append] at h1
  unfold parseHeader
  simp only [List.cons_append, List.nil_append]
  rw [h1]
  simp only [Option.bind_eq_bind, Option.bind_some, ite_true, eatSpaces_space]
  rw [hcr, eatSpaces_of_ne _ hc, ← hcr, h2]
  simp

theorem edgeLine_eq (e : Edge) :
    edgeLine e = ['b', 'u', 'i', 'l', 'd'] ++ (pathList e.outs ++ (pathSection ['|'] e.implicitOuts ++
      (':' :: ' ' :: (e.rule.toList ++ (pathList e.ins ++ (pathSection ['|'] e.implicitIns ++
      pathSection ['|', '|'] e.orderOnly)))))) := by
  simp [edgeLine]

theorem parseHeader_edge (e : Edge) (hrule : validIdent e.rule = true) (houts : e.outs ≠ [])
    (hpaths : e.allPaths.all validPath = true) :
    parseHeader (edgeLine e) = some (.edge { e with bindings := [] }) := by
  obtain ⟨o, os, ho⟩ := List.exists_cons_of_ne_nil houts
  rw [edgeLine_eq]
  have h1 := readIdent_append ['b', 'u', 'i', 'l', 'd'] (pathList e.outs ++ (pathSection ['|'] e.implicitOuts ++
      (':' :: ' ' :: (e.rule.toList ++ (pathList e.ins ++ (pathSection ['|'] e.implicitIns ++
      pathSection ['|', '|'] e.orderOnly)))))) (by simp) (by decide)
    (fun c r h => by rw [ho] at h; simp [pathList] at h; rw [← h.1]; decide)
  unfold parseHeader
  rw [h1]
  simp only [Option.bind_eq_bind, Option.bind_some]
  simp only [show ¬(['b', 'u', 'i', 'l', 'd'] = ['r', 'u', 'l', 'e']) by decide, ite_false, ite_true]
  rw [parseEdgeLine_print e hrule hpaths]
  rfl

theorem parseHeader_default (ps : List Path) (hne : ps ≠ []) (hps : ps.all validPath = true) :
    parseHeader (['d', 'e', 'f', 'a', 'u', 'l', 't'] ++ pathList ps) = some (.default ps) := by
  obtain ⟨o, os, ho⟩ := List.exists_cons_of_ne_nil hne
  have h1 := readIdent_append ['d', 'e', 'f', 'a', 'u', 'l', 't'] (pathList ps) (by simp) (by decide)
    (fun c r h => by rw [ho] at h; simp [pathList] at h; rw [← h.1]; decide)
  have h2 := readPaths_pathList ps [] hps (by intro c r h; cases h) (by intro c r h; cases h)
  simp only [List.append_nil, eatSpaces_nil] at h2
  unfold parseHeader
  rw [h1]
  simp only [Option.bind_eq_bind, Option.bind_some]
  simp only [show ¬(['d', 'e', 'f', 'a', 'u', 'l', 't'] = ['r', 'u', 'l', 'e']) by decide,
    show ¬(['d', 'e', 'f', 'a', 'u', 'l', 't'] = ['b', 'u', 'i', 'l', 'd']) by decide, ite_false, ite_true]
  rw [h2]
  simp [toPaths_map]

/-! ## Bindings and blocks -/

def bindingRest (b : Binding) : List Char := b.1.toList ++ [' ', '=', ' '] ++ renderVal b.2

theorem parseLet_rest (b : Binding) (hb : validBinding b = true) : parseLet (bindingRest b) = some b := by
  obtain ⟨k, v⟩ := b
  simp only [validBinding, Bool.and_eq_true] at hb
  obtain ⟨hne, hkv⟩ := validIdent_parts hb.1
  have hr := readIdent_append k.toList (' ' :: '=' :: ' ' :: renderVal v) hne hkv
    (fun c r h => by cases h; decide)
  simp only [bindingRest, List.append_assoc, List.cons_append, List.nil_append] at hr ⊢
  unfold parseLet
  rw [hr]
  simp only [Option.bind_eq_bind, Option.bind_some, eatSpaces_space]
  rw [eatSpaces_of_ne _ (by decide)]
  simp only [ite_true, eatSpaces_space]
  rw [eatSpaces_of_start (renderVal_start v hb.2), readValue_renderVal v hb.2]
  simp

theorem mapM_parseLet (bs : List Binding) (hbs : bs.all validBinding = true) :
    (bs.map bindingRest).mapM parseLet = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hbs
    simp [List.mapM_cons, parseLet_rest b hbs.1, ih hbs.2]

theorem classify_top {c : Char} (r : List Char) (h1 : c ≠ ' ') (h2 : c ≠ '#') :
    classify (c :: r) = .top := by
  simp [classify, eatSpaces_of_ne _ h1, h1, h2]

theorem classify_blank : classify [] = .blank := rfl

theorem classify_binding (b : Binding) (hb : validBinding b = true) :
    classify (bindingLine true b) = .indented (bindingRest b) := by
  simp only [validBinding, Bool.and_eq_true] at hb
  obtain ⟨c, r, hcr, h1, h2⟩ := ident_head hb.1
  simp only [bindingLine, ite_true, bindingRest, List.cons_append, List.nil_append, List.append_assoc]
  unfold classify
  simp only [eatSpaces_space, hcr, List.cons_append, eatSpaces_of_ne _ h1, h2, ite_false,
    List.head?_cons, ite_true]

/-- The line list after a statement starts with a blank or unindented line. -/
def HeadOK (L : List (List Char)) : Prop :=
  ∀ l L', L = l :: L' → classify l = .blank ∨ classify l = .top

theorem takeBlock_headOK (L : List (List Char)) (h : HeadOK L) : takeBlock L = ([], L) := by
  cases L with
  | nil => rfl
  | cons l L' =>
    rw [takeBlock.eq_def]
    rcases h l L' rfl with h | h <;> simp [h]

theorem takeBlock_bindings (bs : List Binding) (hbs : bs.all validBinding = true)
    (L : List (List Char)) (hL : HeadOK L) :
    takeBlock (bs.map (bindingLine true) ++ L) = (bs.map bindingRest, L) := by
  induction bs with
  | nil => simpa using takeBlock_headOK L hL
  | cons b bs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hbs
    simp only [List.map_cons, List.cons_append]
    rw [takeBlock.eq_def]
    simp [classify_binding b hbs.1, ih hbs.2]

theorem parseLines_blank (ls : List (List Char)) (c : Ctx) (acc : List Stmt) :
    parseLines ([] :: ls) c acc = parseLines ls c acc := by
  rw [parseLines.eq_def]; simp [classify_blank]

theorem parseLines_comment (l : List Char) (ls : List (List Char)) (c : Ctx) (acc : List Stmt)
    (h : classify l = .comment) :
    parseLines (l :: ls) c acc = parseLines ls c acc := by
  rw [parseLines.eq_def]; simp [h]

theorem parseLines_top (l : List Char) (ls : List (List Char)) (c : Ctx) (acc : List Stmt)
    (h : Header) (blk rest : List (List Char)) (s : Stmt)
    (hcl : classify l = .top) (hh : parseHeader l = some h) (hb : takeBlock ls = (blk, rest))
    (hf : finishStmt h blk = some s) (hok : s.ok c = true) :
    parseLines (l :: ls) c acc = parseLines rest (c.add s) (acc ++ [s]) := by
  rw [parseLines.eq_def]
  simp only [hcl, hh]
  split
  · rename_i heq; rw [hb] at heq; simp only at heq; rw [hf] at heq; cases heq
  · rename_i s' heq; rw [hb] at heq; simp only at heq; rw [hf] at heq; cases heq
    simp [hok, hb]

/-! ## Statements -/

theorem printStmt_head (s : Stmt) (c : Ctx) (hok : s.ok c = true) :
    ∃ l rest, printStmt s = l :: rest ∧ classify l = .top := by
  cases s with
  | binding k v =>
    simp only [Stmt.ok, Bool.and_eq_true] at hok
    obtain ⟨d, r, hdr, h1, h2⟩ := ident_head hok.1.1
    refine ⟨_, _, rfl, ?_⟩
    simp only [bindingLine, Bool.false_eq_true, ite_false, List.nil_append, hdr, List.cons_append]
    exact classify_top _ h1 h2
  | rule r => exact ⟨_, _, rfl, classify_top _ (by decide) (by decide)⟩
  | edge e => exact ⟨_, _, rfl, by rw [edgeLine_eq]; exact classify_top _ (by decide) (by decide)⟩
  | default ps => exact ⟨_, _, rfl, classify_top _ (by decide) (by decide)⟩

theorem stmt_step (s : Stmt) (c : Ctx) (acc : List Stmt) (hok : s.ok c = true)
    (L : List (List Char)) (hL : HeadOK L) :
    parseLines (printStmt s ++ L) c acc = parseLines L (c.add s) (acc ++ [s]) := by
  obtain ⟨l, rest, hpr, hcl⟩ := printStmt_head s c hok
  cases s with
  | binding k v =>
    have hok' := hok
    simp only [Stmt.ok, Bool.and_eq_true, Bool.not_eq_true'] at hok'
    simp only [printStmt, List.cons.injEq, List.nil_eq] at hpr
    obtain ⟨rfl, rfl⟩ := hpr
    exact parseLines_top _ _ _ _ _ _ _ _ hcl
      (parseHeader_binding k v hok'.1.1 hok'.1.2 hok'.2) (takeBlock_headOK L hL) rfl hok
  | rule r =>
    have hok' := hok
    simp only [Stmt.ok, Bool.and_eq_true] at hok'
    simp only [printStmt] at hpr
    obtain ⟨rfl, rfl⟩ := hpr
    have hbs : r.bindings.all validBinding = true := by
      simp only [List.all_eq_true] at hok' ⊢
      intro b hb; exact (Bool.and_eq_true _ _ ▸ hok'.1.2 b hb).1
    have hshape : printStmt (.rule r) ++ L = (['r', 'u', 'l', 'e', ' '] ++ r.name.toList) ::
        (r.bindings.map (bindingLine true) ++ ([] :: L)) := by simp [printStmt]
    rw [hshape, parseLines_top _ _ _ _ _ _ _ _ hcl (parseHeader_rule r.name hok'.1.1.1)
      (takeBlock_bindings r.bindings hbs ([] :: L) (fun l L' h => by cases h; exact Or.inl rfl))
      (by simp [finishStmt, mapM_parseLet r.bindings hbs]) hok]
    exact parseLines_blank _ _ _
  | edge e =>
    have hok' := hok
    simp only [Stmt.ok, Bool.and_eq_true, Bool.not_eq_true'] at hok'
    simp only [printStmt, List.cons.injEq] at hpr
    obtain ⟨rfl, rfl⟩ := hpr
    have hne : e.outs ≠ [] := by
      have := hok'.1.1.1.1.2; intro h; rw [h] at this; simp at this
    simp only [printStmt, List.cons_append]
    exact parseLines_top _ _ _ _ _ _ _ _ hcl
      (parseHeader_edge e hok'.1.1.1.1.1.1 hne hok'.1.1.1.2)
      (takeBlock_bindings e.bindings hok'.2 L hL)
      (by simp [finishStmt, mapM_parseLet e.bindings hok'.2]) hok
  | default ps =>
    have hok' := hok
    simp only [Stmt.ok, Bool.and_eq_true, Bool.not_eq_true'] at hok'
    simp only [printStmt, List.cons.injEq] at hpr
    obtain ⟨rfl, rfl⟩ := hpr
    have hne : ps ≠ [] := by
      have := hok'.1.1; intro h; rw [h] at this; simp at this
    exact parseLines_top _ _ _ _ _ _ _ _ hcl (parseHeader_default ps hne hok'.1.2)
      (takeBlock_headOK L hL) rfl hok

theorem headOK_stmts (ss : List Stmt) (c : Ctx) (h : stmtsOK c ss = true) :
    HeadOK (ss.flatMap printStmt ++ [[]]) := by
  intro l L' hL
  cases ss with
  | nil => simp at hL; rw [hL.1]; exact Or.inl rfl
  | cons s ss =>
    simp only [stmtsOK, Bool.and_eq_true] at h
    obtain ⟨l0, rest, hpr, hcl⟩ := printStmt_head s c h.1
    simp only [List.flatMap_cons, hpr, List.cons_append, List.cons.injEq] at hL
    rw [← hL.1]; exact Or.inr hcl

theorem parseLines_print (ss : List Stmt) (c : Ctx) (acc : List Stmt) (h : stmtsOK c ss = true) :
    parseLines (ss.flatMap printStmt ++ [[]]) c acc = some (acc ++ ss) := by
  induction ss generalizing c acc with
  | nil => simp [parseLines_blank, parseLines]
  | cons s ss ih =>
    simp only [stmtsOK, Bool.and_eq_true] at h
    rw [List.flatMap_cons, List.append_assoc,
      stmt_step s c acc h.1 _ (headOK_stmts ss (c.add s) h.2), ih _ _ h.2]
    simp

/-! ## Lines -/

theorem splitLines_cons_line (l X : List Char) (hl : '\n' ∉ l) :
    splitLines (l ++ '\n' :: X) = l :: splitLines X := by
  induction l with
  | nil => simp [splitLines]
  | cons c l ih =>
    simp only [List.mem_cons, not_or] at hl
    simp only [List.cons_append, splitLines, Ne.symm hl.1, ite_false]
    rw [ih hl.2]

theorem splitLines_join (ls : List (List Char)) (h : ∀ l ∈ ls, '\n' ∉ l) :
    splitLines (ls.flatMap (· ++ ['\n'])) = ls ++ [[]] := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp only [List.flatMap_cons, List.append_assoc, List.cons_append]
    rw [splitLines_cons_line _ _ h.1, List.nil_append, ih h.2]

theorem nl_escPath (p : Path) (h : p.toList.all pathChar = true) : '\n' ∉ escPath p := by
  simp only [escPath, List.mem_flatMap, not_exists, not_and]
  intro x hx hn
  have := (pathChar_ne (List.all_eq_true.mp h x hx)).1
  unfold escPathChar at hn
  split at hn
  · simp at hn
  · split at hn
    · simp at hn
    · split at hn
      · simp at hn
      · simp at hn; exact this hn.symm

theorem nl_pathList (ps : List Path) (h : ps.all validPath = true) : '\n' ∉ pathList ps := by
  simp only [pathList, List.mem_flatMap, List.mem_cons, not_exists, not_and, not_or]
  intro p hp
  exact ⟨by decide, nl_escPath p (validPath_parts (List.all_eq_true.mp h p hp)).2⟩

theorem nl_pathSection (sep : List Char) (ps : List Path) (hsep : '\n' ∉ sep) (h : ps.all validPath = true) :
    '\n' ∉ pathSection sep ps := by
  unfold pathSection
  split
  · simp
  · simp only [List.mem_cons, List.mem_append, not_or]; exact ⟨⟨by decide, hsep⟩, nl_pathList ps h⟩

theorem nl_ident (s : String) (h : validIdent s = true) : '\n' ∉ s.toList := by
  intro hn
  exact (isVarChar_ne (List.all_eq_true.mp (validIdent_parts h).2 _ hn)).2.2.1 rfl

theorem nl_escVals (cs : List Char) (h : cs.all litChar = true) : '\n' ∉ cs.flatMap escValChar := by
  simp only [List.mem_flatMap, not_exists, not_and]
  intro x hx hn
  unfold escValChar at hn
  split at hn
  · simp at hn
  · simp at hn; exact litChar_ne (List.all_eq_true.mp h x hx) hn.symm

theorem nl_renderSeg (s : Seg) (h : s.valid = true) : '\n' ∉ renderSeg s := by
  cases s with
  | lit str => exact nl_escVals _ (validLit_parts (by simpa [Seg.valid] using h)).2
  | var n =>
    simp only [renderSeg, List.mem_cons, List.mem_append, not_or]
    exact ⟨by decide, by decide, nl_ident n (by simpa [Seg.valid] using h), by simp⟩

theorem nl_renderVal (e : EvalString) (h : validEval e = true) : '\n' ∉ renderVal e := by
  have hall : ∀ s ∈ e, s.valid = true := by
    unfold validEval at h; simp only [Bool.and_eq_true, List.all_eq_true] at h; exact h.1
  have hsegs : ∀ r : EvalString, (∀ s ∈ r, s.valid = true) → '\n' ∉ r.flatMap renderSeg := by
    intro r hr
    simp only [List.mem_flatMap, not_exists, not_and]
    exact fun s hs => nl_renderSeg s (hr s hs)
  cases e with
  | nil => simp [renderVal]
  | cons s r =>
    have hr : ∀ s ∈ r, s.valid = true := fun s hs => hall s (List.mem_cons_of_mem _ hs)
    cases s with
    | var n =>
      simp only [renderVal, List.mem_append, not_or]
      exact ⟨nl_renderSeg _ (hall _ (by simp)), hsegs r hr⟩
    | lit str =>
      simp only [renderVal, List.mem_append, not_or]
      refine ⟨?_, hsegs r hr⟩
      have hl := (validLit_parts (by simpa [Seg.valid] using hall _ (List.mem_cons_self))).2
      generalize str.toList = cs at hl
      cases cs with
      | nil => simp [escLead]
      | cons d ds =>
        simp only [escLead]
        split
        · simp only [List.mem_cons, not_or]
          simp only [List.all_cons, Bool.and_eq_true] at hl
          exact ⟨by decide, by decide, nl_escVals ds hl.2⟩
        · exact nl_escVals _ hl

theorem nl_bindingLine (ind : Bool) (b : Binding) (h : validBinding b = true) : '\n' ∉ bindingLine ind b := by
  simp only [validBinding, Bool.and_eq_true] at h
  simp only [bindingLine, List.mem_append, not_or]
  refine ⟨⟨⟨by split <;> simp, nl_ident _ h.1⟩, by simp⟩, nl_renderVal _ h.2⟩

theorem nl_printStmt (s : Stmt) (c : Ctx) (hok : s.ok c = true) : ∀ l ∈ printStmt s, '\n' ∉ l := by
  have hbs : ∀ bs : List Binding, bs.all validBinding = true →
      ∀ l ∈ bs.map (bindingLine true), '\n' ∉ l := by
    intro bs h l hl
    simp only [List.mem_map] at hl
    obtain ⟨b, hb, rfl⟩ := hl
    exact nl_bindingLine _ _ (List.all_eq_true.mp h b hb)
  cases s with
  | binding k v =>
    simp only [Stmt.ok, Bool.and_eq_true] at hok
    simp only [printStmt, List.mem_singleton, forall_eq]
    exact nl_bindingLine _ _ (by simp [validBinding, hok.1.1, hok.2])
  | rule r =>
    simp only [Stmt.ok, Bool.and_eq_true] at hok
    have hrb : r.bindings.all validBinding = true := by
      simp only [List.all_eq_true] at hok ⊢
      intro b hb; exact (Bool.and_eq_true _ _ ▸ hok.1.2 b hb).1
    intro l hl
    simp only [printStmt, List.mem_cons, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · subst hl
      simp only [List.mem_append, not_or]
      exact ⟨by decide, nl_ident _ hok.1.1.1⟩
    · exact hbs _ hrb l hl
    · rcases hl with rfl | hl
      · simp
      · simp at hl
  | edge e =>
    simp only [Stmt.ok, Bool.and_eq_true] at hok
    have hp := hok.1.1.1.2
    simp only [Edge.allPaths, Edge.allOuts, Edge.allIns, List.all_append, Bool.and_eq_true] at hp
    simp only [printStmt, List.mem_cons]
    rintro l (rfl | hl)
    · simp only [edgeLine, List.mem_append, not_or]
      exact ⟨⟨⟨⟨⟨⟨⟨by decide, nl_pathList _ hp.1.1⟩, nl_pathSection _ _ (by decide) hp.1.2⟩, by decide⟩,
        nl_ident _ hok.1.1.1.1.1.1⟩, nl_pathList _ hp.2.1.1⟩, nl_pathSection _ _ (by decide) hp.2.1.2⟩,
        nl_pathSection _ _ (by decide) hp.2.2⟩
    · exact hbs _ hok.2 l hl
  | default ps =>
    simp only [Stmt.ok, Bool.and_eq_true] at hok
    simp only [printStmt, List.mem_singleton, forall_eq, List.mem_append, not_or]
    exact ⟨by decide, nl_pathList _ hok.1.2⟩

theorem nl_stmts (ss : List Stmt) (c : Ctx) (h : stmtsOK c ss = true) :
    ∀ l ∈ ss.flatMap printStmt, '\n' ∉ l := by
  induction ss generalizing c with
  | nil => simp
  | cons s ss ih =>
    simp only [stmtsOK, Bool.and_eq_true] at h
    simp only [List.flatMap_cons, List.mem_append]
    rintro l (hl | hl)
    · exact nl_printStmt s c h.1 l hl
    · exact ih _ h.2 l hl

/-! ## The round trip -/

/-- **Headline (Stage 3).** Printing a well-formed manifest and parsing the
result with the parser model gives the manifest back. -/
theorem parse_print (m : Manifest) (h : m.WellFormed) : parse (print m) = some m := by
  unfold Manifest.WellFormed at h
  have hnl : ∀ l ∈ printLines m, '\n' ∉ l := by
    simp only [printLines, List.mem_cons, forall_eq_or_imp]
    exact ⟨by decide, nl_stmts _ _ h⟩
  simp only [parse, print, String.toList_ofList, parseChars, printChars]
  rw [splitLines_join _ hnl, printLines, List.cons_append,
    parseLines_comment _ _ _ _ (by decide), parseLines_print _ _ _ h]
  rfl

end Mise.Syntax

namespace Mise.Syntax

/-- Unescape a complete path: the inverse of `escPath`, given by Ninja's
path lexer. -/
def unescapePath (cs : List Char) : Option Path :=
  match readPath cs with
  | some (p, []) => some (String.ofList p)
  | _ => none

/-- Escaping round trip for paths. -/
theorem unescape_escPath (p : Path) (h : validPath p = true) : unescapePath (escPath p) = some p := by
  have := readPath_esc p.toList [] (validPath_parts h).2 (by intro c r h; cases h)
  simp only [List.append_nil] at this
  simp [unescapePath, escPath, this]

/-- Escaping round trip for values. -/
theorem unescape_renderVal (e : EvalString) (h : validEval e = true) : readValue (renderVal e) = some e :=
  readValue_renderVal e h

end Mise.Syntax
