import Mise.Frontend.Graph

/-!
# Stage 4: theorems about `emit`

- `emit_wellFormed`: a valid graph emits a well-formed manifest.
- `denote_emit`: reading the emitted manifest through the Ninja evaluation
  model gives the graph's own meaning.
- `emitAcyclic`: the emitted manifest's meaning is acyclic.
-/

namespace Mise.Frontend
open Mise.Syntax Mise

/-! ## Lists -/

theorem nodupB_cons (x : String) (xs : List String) : nodupB (x :: xs) = (!xs.contains x && nodupB xs) := rfl

section findOut
variable {α : Type} {outs : α → List Path} {k : Path}

theorem findOut_some {l : List α} {i : Nat} {a : α} (h : findOut outs k l = some (i, a)) :
    l[i]? = some a ∧ (outs a).contains k = true := by
  induction l generalizing i with
  | nil => simp [findOut] at h
  | cons b l ih =>
    unfold findOut at h
    split at h
    · cases h; simp_all
    · cases hl : findOut outs k l with
      | none => simp [hl] at h
      | some p =>
        simp only [hl, Option.map_some, Option.some.injEq] at h
        cases h
        simpa using ih hl

theorem findOut_mem {l : List α} {i : Nat} {a : α} (h : findOut outs k l = some (i, a)) : a ∈ l :=
  List.mem_of_getElem? (findOut_some h).1

theorem findOut_none {l : List α} (h : ∀ a ∈ l, (outs a).contains k = false) : findOut outs k l = none := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [findOut, h b (by simp), Bool.false_eq_true, ite_false]
    rw [ih (fun a ha => h a (by simp [ha]))]; rfl

theorem findOut_take {l : List α} {n : Nat} {a : α} (ha : a ∈ l.take n) (hk : (outs a).contains k = true) :
    ∃ i b, i < n ∧ findOut outs k l = some (i, b) := by
  induction l generalizing n with
  | nil => simp at ha
  | cons c l ih =>
    cases n with
    | zero => simp at ha
    | succ n =>
      simp only [List.take_succ_cons, List.mem_cons] at ha
      unfold findOut
      by_cases hc : (outs c).contains k = true
      · exact ⟨0, c, by omega, by simp only [hc, ite_true]⟩
      · rcases ha with rfl | ha
        · exact absurd hk hc
        · obtain ⟨i, b, hi, hf⟩ := ih ha
          exact ⟨i + 1, b, by omega, by simp only [hc, hf, Bool.false_eq_true, ite_false]; rfl⟩

theorem findOut_map {β : Type} (f : β → α) (l : List β) :
    findOut outs k (l.map f) = (findOut (outs ∘ f) k l).map fun p => (p.1, f p.2) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons, findOut, Function.comp]
    split
    · rfl
    · rw [ih]; cases findOut (outs ∘ f) k l <;> rfl

end findOut

/-! ## Edge validity -/

theorem edgesOK_get {names : List String} {srcs : List Path} :
    ∀ {p : List Path} {es : List GEdge} {i : Nat} {e : GEdge},
    edgesOK names srcs p es = true → es[i]? = some e →
    e.ok names srcs (p ++ (es.take i).flatMap GEdge.allOuts) = true
  | _, [], _, _, _, h => by simp at h
  | p, e' :: es, 0, e, h, hi => by
    simp only [edgesOK, Bool.and_eq_true] at h
    simp at hi; subst hi; simpa using h.1
  | p, e' :: es, i + 1, e, h, hi => by
    simp only [edgesOK, Bool.and_eq_true] at h
    simp only [List.getElem?_cons_succ] at hi
    have := edgesOK_get h.2 hi
    simpa [List.append_assoc] using this

theorem edgesOK_mem {names : List String} {srcs : List Path} {p : List Path} {es : List GEdge}
    {e : GEdge} (h : edgesOK names srcs p es = true) (he : e ∈ es) :
    ∃ q, e.ok names srcs q = true := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem he
  exact ⟨_, edgesOK_get h hi⟩

theorem GEdge.ok_parts {names : List String} {srcs prev : List Path} {e : GEdge}
    (h : e.ok names srcs prev = true) :
    names.contains e.rule = true ∧ e.outs ≠ [] ∧ (∀ p ∈ e.allOuts ++ e.allIns, validPath p = true) ∧
    nodupB e.allOuts = true ∧ (∀ o ∈ e.allOuts, prev.contains o = false ∧ srcs.contains o = false) ∧
    (∀ i ∈ e.allIns, srcs.contains i = true ∨ prev.contains i = true) ∧ varsOK e.vars = true := by
  simp only [GEdge.ok, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.or_eq_true,
    List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, h2, h3, h4, fun o ho => ?_, h6, h7⟩
  have := h5 o ho
  simpa using this

/-! ## Well-formedness -/

theorem stmtsOK_append (c : Ctx) (l₁ l₂ : List Stmt) :
    stmtsOK c (l₁ ++ l₂) = (stmtsOK c l₁ && stmtsOK (l₁.foldl Ctx.add c) l₂) := by
  induction l₁ generalizing c with
  | nil => simp [stmtsOK]
  | cons s l ih => simp [stmtsOK, ih, Bool.and_assoc]

theorem emitRule_ok (c : Ctx) (r : GRule) (hr : r.ok = true) (hf : c.rules.contains r.name = false) :
    (Stmt.rule (emitRule r)).ok c = true := by
  simp only [GRule.ok, Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨h1, _⟩, h3⟩, h4⟩, _⟩, h6⟩ := hr
  have hc : validIdent "command" = true := by decide
  have hd : validIdent "description" = true := by decide
  have hdb : depfileBindings.all (fun b => validBinding b && ruleKeys.contains b.1) = true := by decide
  have hrb : restatBindings.all (fun b => validBinding b && ruleKeys.contains b.1) = true := by decide
  simp only [depfileBindings, restatBindings] at hdb hrb
  by_cases he : r.description.isEmpty <;> by_cases hdf : r.depfile <;> by_cases hrs : r.restat <;>
    simp_all [Stmt.ok, emitRule, validBinding, ruleKeys, depfileBindings, restatBindings]

theorem rules_fold (c : Ctx) (rs : List GRule) :
    (rs.map (Stmt.rule ∘ emitRule)).foldl Ctx.add c = { c with rules := c.rules ++ rs.map (·.name) } := by
  induction rs generalizing c with
  | nil => simp
  | cons r rs ih => simp [Ctx.add, ih, emitRule]

theorem rules_ok (rs : List GRule) (c : Ctx) (hnd : nodupB (rs.map (·.name)) = true)
    (hok : rs.all GRule.ok = true) (hf : ∀ r ∈ rs, c.rules.contains r.name = false) :
    stmtsOK c (rs.map (Stmt.rule ∘ emitRule)) = true := by
  induction rs generalizing c with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, nodupB_cons, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    simp only [List.all_cons, Bool.and_eq_true] at hok
    simp only [List.map_cons, stmtsOK, Function.comp, Bool.and_eq_true]
    refine ⟨emitRule_ok c r hok.1 (hf r (by simp)), ih _ hnd.2 hok.2 ?_⟩
    intro r' hr'
    have h1 := hf r' (by simp [hr'])
    have h2 : r'.name ≠ r.name := by
      intro heq
      have : r.name ∈ rs.map (·.name) := heq ▸ List.mem_map_of_mem hr'
      simp_all
    simp_all [Ctx.add, emitRule]

theorem emitEdge_ok (c : Ctx) (names : List String) (srcs : List Path) (e : GEdge)
    (hR : ∀ n ∈ names, c.rules.contains n = true) (hn : ∀ n ∈ names, validIdent n = true)
    (he : e.ok names srcs c.outs = true) : (Stmt.edge (emitEdge e)).ok c = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := GEdge.ok_parts he
  have hr : e.rule ∈ names := by simpa using h1
  simp only [varsOK, Bool.and_eq_true, List.all_eq_true] at h7
  simp only [Stmt.ok, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨hn _ hr, hR _ hr⟩, ?_⟩, h3⟩, h4⟩, fun o ho => (h5 o ho).1⟩, ?_⟩, ?_⟩
  · simpa [emitEdge] using h2
  · intro b hb
    simp only [emitEdge, List.mem_map] at hb
    obtain ⟨⟨k, v⟩, hkv, rfl⟩ := hb
    have := h7.2 _ hkv
    simp only [Bool.not_eq_true'] at this
    have hpt : parseTimeKeys.contains k = false := by
      have h := this.1.2
      simp only [reserved, List.contains_append, Bool.or_eq_false_iff] at h
      exact h.2
    simp only [validBinding, this.1.1, hpt, Bool.true_and, Bool.not_false, Bool.and_true, litVal]
    split
    · simp [validEval, noAdjLits]
    · rename_i hv
      simpa [validEval, Seg.valid, validLit, hv, noAdjLits] using this.2
  · -- Inputs are sources or earlier outputs, which no output is.
    intro i hi
    have hi' : i ∈ e.allIns := by simpa [emitEdge, Edge.allIns, GEdge.allIns] using hi
    cases hm : (emitEdge e).allOuts.contains i
    · rfl
    · have ho : i ∈ e.allOuts := by simpa [emitEdge, Edge.allOuts, GEdge.allOuts] using hm
      have := h5 i ho; have := h6 i hi'; simp_all

theorem edges_fold (c : Ctx) (es : List GEdge) :
    (es.map (Stmt.edge ∘ emitEdge)).foldl Ctx.add c =
      { c with outs := c.outs ++ es.flatMap GEdge.allOuts,
               known := c.known ++ es.flatMap fun e => e.allOuts ++ e.allIns } := by
  induction es generalizing c with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.foldl_cons, Function.comp, ih, List.flatMap_cons]
    simp [Ctx.add, emitEdge, Edge.allPaths, Edge.allOuts, Edge.allIns, GEdge.allOuts, GEdge.allIns,
      List.append_assoc]

theorem edges_ok (names : List String) (srcs : List Path) (es : List GEdge) (c : Ctx)
    (hR : ∀ n ∈ names, c.rules.contains n = true) (hn : ∀ n ∈ names, validIdent n = true)
    (h : edgesOK names srcs c.outs es = true) : stmtsOK c (es.map (Stmt.edge ∘ emitEdge)) = true := by
  induction es generalizing c with
  | nil => rfl
  | cons e es ih =>
    simp only [edgesOK, Bool.and_eq_true] at h
    simp only [List.map_cons, stmtsOK, Function.comp, Bool.and_eq_true]
    refine ⟨emitEdge_ok c names srcs e hR hn h.1, ih _ (by simpa [Ctx.add] using hR) ?_⟩
    simpa [Ctx.add, emitEdge, Edge.allOuts, GEdge.allOuts] using h.2

theorem aliasesOK_parts {srcs outs : List Path} {as : List GAlias} (h : aliasesOK srcs outs as = true) :
    nodupB (as.map (·.name)) = true ∧ ∀ a ∈ as, validPath a.name = true ∧ a.name ∉ srcs ∧ a.name ∉ outs ∧
      a.targets ≠ [] ∧ ∀ t ∈ a.targets, validPath t = true ∧ (t ∈ srcs ∨ t ∈ outs) := by
  simp only [aliasesOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', Bool.or_eq_true,
    List.isEmpty_eq_false_iff, List.contains_iff_mem] at h
  refine ⟨h.1, fun a ha => ?_⟩
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h.2 a ha
  refine ⟨h1, ?_, ?_, h4, h5⟩
  · simpa using h2
  · simpa using h3

theorem aliases_fold (c : Ctx) (as : List GAlias) :
    (as.map (Stmt.edge ∘ emitAlias)).foldl Ctx.add c =
      { c with outs := c.outs ++ as.map (·.name), known := c.known ++ as.flatMap fun a => a.name :: a.targets } := by
  induction as generalizing c with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.foldl_cons, Function.comp, ih, List.flatMap_cons]
    simp [Ctx.add, emitAlias, Edge.allPaths, Edge.allOuts, Edge.allIns, List.append_assoc]

theorem aliases_ok' (as : List GAlias) (c : Ctx) (hp : c.rules.contains "phony" = true)
    (hnd : nodupB (as.map (·.name)) = true)
    (hok : ∀ a ∈ as, validPath a.name = true ∧ (∀ t ∈ a.targets, validPath t = true) ∧ a.name ∉ a.targets)
    (hc : ∀ a ∈ as, a.name ∉ c.outs) : stmtsOK c (as.map (Stmt.edge ∘ emitAlias)) = true := by
  induction as generalizing c with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, nodupB_cons, Bool.and_eq_true, Bool.not_eq_true'] at hnd
    obtain ⟨h1, h5, hself⟩ := hok a (by simp)
    simp only [List.map_cons, stmtsOK, Function.comp, Bool.and_eq_true]
    refine ⟨?_, ih _ (by simpa [Ctx.add] using hp) hnd.2 (fun a' ha' => hok a' (by simp [ha'])) ?_⟩
    · have hv : validIdent "phony" = true := by decide
      have hn : c.outs.contains a.name = false := by
        cases hm : c.outs.contains a.name
        · rfl
        · exact absurd (List.contains_iff_mem.mp hm) (hc a (by simp))
      simp only [Stmt.ok, emitAlias, hv, hp, Bool.true_and, Bool.and_eq_true, List.all_eq_true,
        Edge.allPaths, Edge.allOuts, Edge.allIns, List.append_nil, List.mem_cons, List.mem_append,
        List.isEmpty_cons, Bool.not_false, List.mem_nil_iff, or_false, forall_eq, hn, Bool.not_false]
      and_intros
      · rintro p (rfl | hp')
        · exact h1
        · exact h5 p hp'
      all_goals first | decide | (simp; intro t ht h; subst h; exact hself ht) | simp | simp [nodupB]
    · intro a' ha'
      simp only [Ctx.add, emitAlias, Edge.allOuts, List.append_nil, List.mem_append, List.mem_singleton]
      rintro (ho | ho)
      · exact hc a' (by simp [ha']) ho
      · have : a.name ∈ as.map (·.name) := ho ▸ List.mem_map_of_mem ha'
        simp_all

theorem aliases_ok (srcs outs : List Path) (as : List GAlias) (c : Ctx)
    (hp : c.rules.contains "phony" = true) (hc : ∀ o, o ∈ c.outs → o ∈ outs)
    (h : aliasesOK srcs outs as = true) : stmtsOK c (as.map (Stmt.edge ∘ emitAlias)) = true := by
  obtain ⟨hnd, hok⟩ := aliasesOK_parts h
  refine aliases_ok' as c hp hnd (fun a ha => ⟨(hok a ha).1, fun t ht => ((hok a ha).2.2.2.2 t ht).1, ?_⟩)
    fun a ha ho => (hok a ha).2.2.1 (hc _ ho)
  -- Targets are sources or edge outputs, which an alias name is not.
  intro ht
  rcases ((hok a ha).2.2.2.2 _ ht).2 with h | h
  · exact (hok a ha).2.1 h
  · exact (hok a ha).2.2.1 h

theorem Graph.check_parts {g : Graph} (hg : g.Valid) :
    nodupB g.ruleNames = true ∧ (∀ r ∈ g.rules, r.ok = true) ∧
    edgesOK g.ruleNames g.sources [] g.edges = true ∧
    aliasesOK g.sources (g.edges.flatMap GEdge.allOuts) g.aliases = true ∧
    (∀ d ∈ g.defaults, (∃ e ∈ g.edges, d ∈ e.allOuts) ∨ ∃ a ∈ g.aliases, a.name = d) := by
  simp only [Graph.Valid, Graph.check, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    List.contains_iff_mem, Bool.or_eq_true, beq_iff_eq] at hg
  exact ⟨hg.1.1.1.1.1, hg.1.1.1.1.2, hg.1.1.1.2, hg.1.1.2, hg.1.2⟩

theorem GRule.ok_name {r : GRule} (h : r.ok = true) : validIdent r.name = true ∧ r.name ≠ "phony" := by
  simp only [GRule.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2⟩

theorem versionStmt_ok (c : Ctx) : versionStmt.ok c = true := by
  show (validIdent versionVar && !keywords.contains versionVar.toList && validEval [.lit ninjaMinVersion]) = true
  decide

theorem versionStmt_add (c : Ctx) : c.add versionStmt = c := rfl

/-- A valid graph emits a well-formed manifest. -/
theorem emit_wellFormed (g : Graph) (hg : g.Valid) : (emit g).WellFormed := by
  obtain ⟨hnd, hok, hedges, hal, hdef⟩ := Graph.check_parts hg
  have hnames : ∀ n ∈ g.ruleNames, ∃ r ∈ g.rules, r.name = n := by simp [Graph.ruleNames]
  unfold Manifest.WellFormed emit
  rw [stmtsOK, versionStmt_ok, Bool.true_and, versionStmt_add]
  simp only [stmtsOK_append, Bool.and_eq_true, List.foldl_append, rules_fold, edges_fold, aliases_fold]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · refine rules_ok g.rules {} hnd (by simpa using hok) fun r hr => ?_
    simpa [eq_comm] using (GRule.ok_name (hok r hr)).2
  · refine edges_ok g.ruleNames g.sources g.edges _ (fun n hn => by simp [Graph.ruleNames] at hn ⊢; simp_all [Graph.ruleNames]) ?_ (by simpa using hedges)
    intro n hn
    obtain ⟨r, hr, rfl⟩ := hnames n hn
    exact (GRule.ok_name (hok r hr)).1
  · exact aliases_ok g.sources _ g.aliases _ (by simp) (fun o ho => by simpa using ho) hal
  · split
    · rfl
    · rename_i hne
      obtain ⟨-, hak⟩ := aliasesOK_parts hal
      simp only [stmtsOK, Stmt.ok, Bool.and_true, Bool.and_eq_true, List.all_eq_true, hne,
        Bool.not_false, Bool.true_and, List.contains_iff_mem]
      constructor
      · intro d hd
        rcases hdef d hd with ⟨e, he, hde⟩ | ⟨a, ha, rfl⟩
        · obtain ⟨q, hq⟩ := edgesOK_mem hedges he
          exact (GEdge.ok_parts hq).2.2.1 d (by simp [hde])
        · exact (hak a ha).1
      · intro d hd
        simp only [List.nil_append, List.mem_flatMap, List.mem_append, List.mem_cons]
        rcases hdef d hd with ⟨e, he, hde⟩ | ⟨a, ha, rfl⟩
        · exact .inl ⟨e, he, .inl hde⟩
        · exact .inr ⟨a, ha, .inl rfl⟩

/-! ## Elaborating the emitted manifest -/

theorem elab_ruleStmts (st : Elab) (rs : List GRule) :
    (rs.map (Stmt.rule ∘ emitRule)).foldl Elab.step st = { st with rules := st.rules ++ rs.map emitRule } := by
  induction rs generalizing st with
  | nil => simp
  | cons r rs ih => simp [Elab.step, ih]

theorem elab_edgeStmts (st : Elab) (es : List GEdge) :
    (es.map (Stmt.edge ∘ emitEdge)).foldl Elab.step st =
      { st with edges := st.edges ++ es.map (edgeInfo st.rules st.file ∘ emitEdge) } := by
  induction es generalizing st with
  | nil => simp
  | cons e es ih => simp [Elab.step, ih]

/-- The rules Ninja knows after reading the emitted manifest. -/
def emitRules (g : Graph) : List Rule := ⟨"phony", []⟩ :: g.rules.map emitRule

/-- The file scope after the emitted version binding. -/
def emitFile : Scope := [(versionVar, ninjaMinVersion)]

theorem emitFile_get {v : String} (hv : v ≠ versionVar) : emitFile.get v = none := by
  have : (versionVar == v) = false := by simpa using Ne.symm hv
  simp [emitFile, Scope.get, this]

theorem elab_aliasStmts (st : Elab) (as : List GAlias) :
    (as.map (Stmt.edge ∘ emitAlias)).foldl Elab.step st =
      { st with edges := st.edges ++ as.map (edgeInfo st.rules st.file ∘ emitAlias) } := by
  induction as generalizing st with
  | nil => simp
  | cons a as ih => simp [Elab.step, ih]

theorem elab_emit (g : Graph) :
    (emit g).elab.file = emitFile ∧
      (emit g).elab.edges = g.edges.map (edgeInfo (emitRules g) emitFile ∘ emitEdge) ++
        g.aliases.map (edgeInfo (emitRules g) emitFile ∘ emitAlias) := by
  unfold Manifest.elab emit
  simp only [List.foldl_cons, List.foldl_append, elab_ruleStmts, elab_edgeStmts, elab_aliasStmts]
  split <;> simp [Elab.step, emitRules, versionStmt, emitFile, evalWith]

/-- The rule of every edge of a valid graph is a declared rule, so not
`phony`. -/
theorem rule_ne_phony {g : Graph} (hg : g.Valid) {e : GEdge} (he : e ∈ g.edges) : e.rule ≠ "phony" := by
  obtain ⟨_, hok, hedges, _⟩ := Graph.check_parts hg
  obtain ⟨q, hq⟩ := edgesOK_mem hedges he
  obtain ⟨h1, -⟩ := GEdge.ok_parts hq
  simp only [Graph.ruleNames, List.contains_iff_mem, List.mem_map] at h1
  obtain ⟨r, hr, hrn⟩ := h1
  exact hrn ▸ (GRule.ok_name (hok r hr)).2

/-- Ninja runs a command for exactly the emitted edges of the graph's own
edges: the aliases are `phony`. -/
theorem cmdEdges_emit (g : Graph) (hg : g.Valid) :
    (emit g).elab.cmdEdges = g.edges.map (edgeInfo (emitRules g) emitFile ∘ emitEdge) := by
  rw [Elab.cmdEdges, (elab_emit g).2, List.filter_append]
  have h2 : (g.aliases.map (edgeInfo (emitRules g) emitFile ∘ emitAlias)).filter
      (·.edge.rule != "phony") = [] := by
    simp [List.filter_eq_nil_iff, edgeInfo, emitAlias]
  rw [h2, List.append_nil, List.filter_eq_self]
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  simpa [edgeInfo, emitEdge] using rule_ne_phony hg he

/-! ## Commands -/

theorem evalWith_congr (f g : String → String) (t : EvalString) (h : ∀ n, Seg.var n ∈ t → f n = g n) :
    evalWith f t = evalWith g t := by
  induction t with
  | nil => rfl
  | cons s t ih =>
    have ih := ih fun n hn => h n (by simp [hn])
    cases s with
    | lit s => simp [evalWith, ih]
    | var n => simp [evalWith, ih, h n (by simp)]

theorem foldl_cons_rev {β : Type} (f : β → String × String) (l : List β) (acc : Scope) :
    l.foldl (fun acc b => f b :: acc) acc = (l.map f).reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons b l ih => simp [ih]

theorem get_reverse (l : Scope) (v : String) (h : nodupB (l.map (·.1)) = true) :
    Scope.get l.reverse v = Scope.get l v := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, nodupB_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [Scope.get, List.reverse_cons, List.find?_append, List.find?_cons, List.find?_nil] at ih ⊢
    by_cases ha : a.1 = v
    · subst ha
      have : List.find? (fun x => x.1 == a.1) l.reverse = none := by
        rw [List.find?_eq_none]
        intro x hx hxa
        have : a.1 ∈ l.map (·.1) := List.mem_map.mpr ⟨x, List.mem_reverse.mp hx, by simpa using hxa⟩
        simp_all
      simp [this]
    · have hb : (a.1 == v) = false := by simpa using ha
      simp only [hb, Option.or_none]
      exact ih h.2

theorem evalWith_litVal (f : String → String) (s : String) : evalWith f (litVal s) = s := by
  unfold litVal; split
  · rename_i h; simp only [evalWith]; simpa using h
  · simp [evalWith]

/-- The scope Ninja gives an emitted edge holds exactly the edge's variables,
apart from the version binding. -/
theorem own_get (rules : List Rule) (e : GEdge) (v : String) (h : nodupB (e.vars.map (·.1)) = true)
    (hv : v ≠ versionVar) :
    (((edgeInfo rules emitFile (emitEdge e)).own).getD emitFile).get v = (e.vars.find? (·.1 == v)).map (·.2) := by
  simp only [edgeInfo, emitEdge]
  by_cases hb : e.vars = []
  · simp [hb, emitFile_get hv]
  · simp only [List.isEmpty_iff, List.map_eq_nil_iff, hb, ite_false, Option.getD_some, foldl_cons_rev,
      List.append_nil, List.map_map]
    have : (List.map ((fun b => (b.1, evalWith (fileLook emitFile) b.2)) ∘ fun b => (b.1, litVal b.2)) e.vars) = e.vars := by
      conv => rhs; rw [← List.map_id e.vars]
      apply List.map_congr_left; intro b _; simp [evalWith_litVal]
    rw [this, get_reverse _ _ h]; rfl

theorem emitRule_get_command (r : GRule) : (emitRule r).get "command" = some r.command := by
  unfold emitRule Rule.get; split <;> split <;> split <;> simp [depfileBindings, restatBindings]

theorem emitRule_get_deps (r : GRule) :
    (emitRule r).get "deps" = if r.depfile then some [.lit "gcc"] else none := by
  unfold emitRule Rule.get; split <;> split <;> split <;> simp_all [depfileBindings, restatBindings]

theorem emitRule_get_restat (r : GRule) :
    (emitRule r).get "restat" = if r.restat then some [.lit "1"] else none := by
  unfold emitRule Rule.get; split <;> split <;> split <;> simp_all [depfileBindings, restatBindings]

theorem emitRule_get_none (r : GRule) (v : String) (hv : v ≠ "command") (hd : v ≠ "description")
    (hf : v ≠ "depfile") (hp : v ≠ "deps") (hr : v ≠ "restat") : (emitRule r).get v = none := by
  have h1 : "command" ≠ v := Ne.symm hv
  have h2 : "description" ≠ v := Ne.symm hd
  have h3 : "depfile" ≠ v := Ne.symm hf
  have h4 : "deps" ≠ v := Ne.symm hp
  have h5 : "restat" ≠ v := Ne.symm hr
  unfold emitRule Rule.get
  split <;> split <;> split <;> simp [h1, h2, h3, h4, h5, depfileBindings, restatBindings]

theorem not_reserved {v : String} (h : reserved.contains v = false) :
    v ≠ "in" ∧ v ≠ "out" ∧ v ≠ "in_newline" ∧ v ≠ "command" ∧ v ≠ "description" ∧ v ≠ "depfile" ∧
      v ≠ "deps" ∧ v ≠ "restat" ∧ v ≠ versionVar := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; revert h; decide)

theorem lookup_emit (rules : List Rule) (r : GRule) (e : GEdge) (n : Nat) (v : String)
    (hrule : (edgeInfo rules emitFile (emitEdge e)).rule = emitRule r) (hvars : nodupB (e.vars.map (·.1)) = true)
    (hv : v = "in" ∨ v = "out" ∨ reserved.contains v = false) :
    (edgeInfo rules emitFile (emitEdge e)).lookup emitFile n v = e.look v := by
  rcases hv with rfl | rfl | hv
  · rw [EdgeInfo.lookup_in]; rfl
  · rw [EdgeInfo.lookup_out]; rfl
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := not_reserved hv
    have hown := own_get rules e v hvars h9
    have hget := emitRule_get_none r v h4 h5 h6 h7 h8
    rw [EdgeInfo.lookup_other _ _ _ _ h1 h3 h2, hown, hrule, hget]
    simp only [GEdge.look, h1, h2, ite_false]
    cases e.vars.find? (·.1 == v) <;> cases n <;> simp [emitFile_get h9]

theorem tmplVarsOK_mem {t : EvalString} (h : tmplVarsOK t = true) {n : String} (hn : Seg.var n ∈ t) :
    n = "in" ∨ n = "out" ∨ reserved.contains n = false := by
  simp only [tmplVarsOK, List.all_eq_true] at h
  have := h _ hn
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
  rcases this with (h | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)

theorem GRule.ok_command {r : GRule} (h : r.ok = true) : tmplVarsOK r.command = true := by
  simp only [GRule.ok, Bool.and_eq_true] at h
  exact h.1.2

/-- An edge's variable names are distinct and none is reserved. -/
theorem vars_get_reserved {e : GEdge} (h7 : varsOK e.vars = true) {v : String} (hv : reserved.contains v = true) :
    e.vars.find? (·.1 == v) = none := by
  simp only [varsOK, Bool.and_eq_true, List.all_eq_true] at h7
  cases hf : e.vars.find? (·.1 == v) with
  | none => rfl
  | some b =>
    have hb := List.find?_some hf
    have := (h7.2 b (List.mem_of_find?_eq_some hf)).1.2
    simp only [beq_iff_eq] at hb
    rw [hb, hv] at this
    cases this

/-- The rule Ninja finds for an emitted edge. -/
theorem rule_emit (g : Graph) (hg : g.Valid) (e : GEdge) (he : e ∈ g.edges) :
    ∃ r, g.ruleOf e = some r ∧ r.ok = true ∧ (edgeInfo (emitRules g) emitFile (emitEdge e)).rule = emitRule r := by
  obtain ⟨_, hok, hedges, _⟩ := Graph.check_parts hg
  obtain ⟨q, hq⟩ := edgesOK_mem hedges he
  obtain ⟨h1, -, -, -, -, -, -⟩ := GEdge.ok_parts hq
  obtain ⟨r, hfind⟩ : ∃ r, g.rules.find? (·.name == e.rule) = some r := by
    simp only [Graph.ruleNames, List.contains_iff_mem, List.mem_map] at h1
    obtain ⟨r, hr, hrn⟩ := h1
    exact Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨r, hr, by simp [hrn]⟩)
  have hr : r ∈ g.rules := List.mem_of_find?_eq_some hfind
  have hrn : r.name = e.rule := by simpa using List.find?_some hfind
  have hrok := hok r hr
  refine ⟨r, hfind, hrok, ?_⟩
  have hp : ("phony" == e.rule) = false := by
    have : e.rule ≠ "phony" := hrn ▸ (GRule.ok_name hrok).2
    simpa using Ne.symm this
  simp only [edgeInfo, emitRules, emitEdge, List.find?_cons, hp, List.find?_map]
  have : ((fun x : Rule => x.name == e.rule) ∘ emitRule) = (fun x : GRule => x.name == e.rule) := by
    funext x; simp [emitRule]
  simp [this, hfind]

theorem varsOK_of_mem {g : Graph} (hg : g.Valid) {e : GEdge} (he : e ∈ g.edges) : varsOK e.vars = true := by
  obtain ⟨_, _, hedges, _⟩ := Graph.check_parts hg
  obtain ⟨q, hq⟩ := edgesOK_mem hedges he
  exact (GEdge.ok_parts hq).2.2.2.2.2.2

/-- Ninja evaluates every emitted edge's command to the command the DSL means. -/
theorem command_emit (g : Graph) (hg : g.Valid) (e : GEdge) (he : e ∈ g.edges) :
    (edgeInfo (emitRules g) emitFile (emitEdge e)).command emitFile = g.cmd e := by
  have h7 := varsOK_of_mem hg he
  have hvars : nodupB (e.vars.map (·.1)) = true := by
    simp only [varsOK, Bool.and_eq_true] at h7; exact h7.1
  obtain ⟨r, hfind, hrok, hrule⟩ := rule_emit g hg e he
  have hcmd : g.cmd e = evalWith e.look r.command := by simp [Graph.cmd, hfind]
  rw [hcmd]
  simp only [EdgeInfo.command, EdgeInfo.binding]
  rw [EdgeInfo.lookup_other _ _ _ _ (by decide) (by decide) (by decide)]
  have hc : ((edgeInfo (emitRules g) emitFile (emitEdge e)).own.getD emitFile).get "command" = none := by
    rw [own_get _ e _ hvars (by decide), vars_get_reserved h7 (by decide)]; rfl
  simp only [hc, hrule, emitRule_get_command]
  exact evalWith_congr _ _ _ fun n hn =>
    lookup_emit _ r e _ n hrule hvars (tmplVarsOK_mem (GRule.ok_command hrok) hn)

/-- Ninja reads the deps log for exactly the edges whose rule has a depfile. -/
theorem isDyn_emit (g : Graph) (hg : g.Valid) (e : GEdge) (he : e ∈ g.edges) :
    (edgeInfo (emitRules g) emitFile (emitEdge e)).isDyn emitFile = g.isDyn e := by
  have h7 := varsOK_of_mem hg he
  have hvars : nodupB (e.vars.map (·.1)) = true := by
    simp only [varsOK, Bool.and_eq_true] at h7; exact h7.1
  obtain ⟨r, hfind, -, hrule⟩ := rule_emit g hg e he
  simp only [EdgeInfo.isDyn, EdgeInfo.binding, Graph.isDyn, hfind]
  rw [EdgeInfo.lookup_other _ _ _ _ (by decide) (by decide) (by decide)]
  have hc : ((edgeInfo (emitRules g) emitFile (emitEdge e)).own.getD emitFile).get "deps" = none := by
    rw [own_get _ e _ hvars (by decide), vars_get_reserved h7 (by decide)]; rfl
  simp only [hc, hrule, emitRule_get_deps]
  cases r.depfile
  · simp only [Bool.false_eq_true, ite_false]
    split <;> simp [emitFile, Scope.get, versionVar]
  · simp only [ite_true]
    rw [show evalWith _ [Seg.lit "gcc"] = "gcc" from rfl]
    decide

/-- Ninja re-reads output mtimes for exactly the edges whose rule has `restat`. -/
theorem isRestat_emit (g : Graph) (hg : g.Valid) (e : GEdge) (he : e ∈ g.edges) :
    (edgeInfo (emitRules g) emitFile (emitEdge e)).isRestat emitFile = g.isRestat e := by
  have h7 := varsOK_of_mem hg he
  have hvars : nodupB (e.vars.map (·.1)) = true := by
    simp only [varsOK, Bool.and_eq_true] at h7; exact h7.1
  obtain ⟨r, hfind, -, hrule⟩ := rule_emit g hg e he
  simp only [EdgeInfo.isRestat, EdgeInfo.binding, Graph.isRestat, hfind]
  rw [EdgeInfo.lookup_other _ _ _ _ (by decide) (by decide) (by decide)]
  have hc : ((edgeInfo (emitRules g) emitFile (emitEdge e)).own.getD emitFile).get "restat" = none := by
    rw [own_get _ e _ hvars (by decide), vars_get_reserved h7 (by decide)]; rfl
  simp only [hc, hrule, emitRule_get_restat]
  cases r.restat
  · simp only [Bool.false_eq_true, ite_false]
    split <;> simp [emitFile, Scope.get, versionVar]
  · simp only [ite_true]
    rw [show evalWith _ [Seg.lit "1"] = "1" from rfl]
    decide

/-! ## Meaning -/

theorem outs_emit (R : List Rule) :
    ((fun c : EdgeInfo => c.edge.allOuts) ∘ edgeInfo R emitFile ∘ emitEdge) = GEdge.allOuts := by
  funext e; rfl

variable {V : Type} [Inhabited V]

/-- **Headline.** Reading the emitted manifest through the Ninja model gives
the graph's own meaning. -/
theorem denote_emit (sem : Sem V) (g : Graph) (hg : g.Valid) :
    denote sem (emit g) = g.spec sem := by
  have hfile := (elab_emit g).1
  have hedges := cmdEdges_emit g hg
  unfold denote Graph.spec
  simp only [hfile, hedges, findOut_map, outs_emit]
  congr 1
  · funext k; show _ = (findOut GEdge.allOuts k g.edges).isNone; cases findOut GEdge.allOuts k g.edges <;> rfl
  · funext k
    cases hf : findOut GEdge.allOuts k g.edges with
    | none => rfl
    | some p =>
      obtain ⟨i, e⟩ := p
      simp only [Option.map_some, Function.comp]
      rw [command_emit g hg e (findOut_mem hf), isDyn_emit g hg e (findOut_mem hf)]
      rfl

/-! ## Acyclicity -/

omit [Inhabited V] in
theorem fetchAll_fetchesOnly {K : Type} {P : K → Prop} :
    ∀ (ks : List K), (∀ k ∈ ks, P k) → (fetchAll ks : Task K V (List V)).FetchesOnly P
  | [], _ => .pure _
  | k :: ks, h => .fetch k _ (h k (by simp)) fun _ =>
      (fetchAll_fetchesOnly ks fun j hj => h j (by simp [hj])).bind fun _ => .pure _

omit [Inhabited V] in
/-- A command's task fetches only inputs, or for a depfile command only what
its bound allows. -/
theorem cmdTask_fetchesOnly {P : Path → Prop} (sem : Sem V) (dyn : Bool) (cmd : String) (ins : List Path)
    (hs : dyn = false → ∀ k ∈ ins, P k) (hd : dyn = true → (sem.dyn cmd).FetchesOnly P) :
    (cmdTask sem dyn cmd ins).FetchesOnly P := by
  unfold cmdTask
  cases dyn
  · exact (fetchAll_fetchesOnly ins (hs rfl)).bind fun _ => .pure _
  · exact hd rfl

theorem outTask_fetchesOnly {P : Path → Prop} {t : Task Path V (List V)} (h : t.FetchesOnly P) (i : Nat) :
    (outTask t i).FetchesOnly P :=
  h.bind fun _ => .pure _

/-- An output's rank is one more than its edge's position; sources rank 0. -/
def Graph.rank (g : Graph) (k : Path) : Nat :=
  match findOut GEdge.allOuts k g.edges with
  | some (i, _) => i + 1
  | none => 0

theorem Graph.rank_source (g : Graph) {j : Path} (hs : g.isSource j = true) : g.rank j = 0 := by
  simp only [Graph.isSource, Option.isNone_iff_eq_none] at hs
  simp [Graph.rank, hs]

theorem Graph.rank_lt (g : Graph) (hg : g.Valid) {k : Path} {i : Nat} {e : GEdge}
    (hf : findOut GEdge.allOuts k g.edges = some (i, e)) {j : Path} (hj : j ∈ e.allIns) :
    g.rank j < i + 1 := by
  obtain ⟨-, -, hedges, -⟩ := Graph.check_parts hg
  have hq := edgesOK_get hedges (findOut_some hf).1
  obtain ⟨-, -, -, -, -, h6, -⟩ := GEdge.ok_parts hq
  unfold Graph.rank
  rcases h6 j hj with hs | hp
  · have hn : findOut GEdge.allOuts j g.edges = none := by
      refine findOut_none fun a ha => ?_
      obtain ⟨q, hq⟩ := edgesOK_mem hedges ha
      obtain ⟨-, -, -, -, h5, -, -⟩ := GEdge.ok_parts hq
      cases hc : a.allOuts.contains j
      · rfl
      · have := (h5 j (by simpa using hc)).2; rw [hs] at this; cases this
    rw [hn]; exact Nat.succ_pos i
  · simp only [List.nil_append, List.contains_iff_mem, List.mem_flatMap] at hp
    obtain ⟨a, ha, hja⟩ := hp
    obtain ⟨i', b, hi', hf'⟩ := findOut_take ha (by simpa using hja)
    rw [hf']; show i' + 1 < i + 1; omega

/-- The DSL's meaning is acyclic, with edge positions as ranks, provided
every depfile command reads only sources and its edge's declared inputs. -/
def Graph.acyclic (sem : Sem V) (g : Graph) (hg : g.Valid) (hd : g.DynOK sem) :
    (g.spec sem).Acyclic where
  rank := g.rank
  fetches k hk := by
    simp only [Graph.spec] at hk ⊢
    cases hf : findOut GEdge.allOuts k g.edges with
    | none => simp [Graph.isSource, hf] at hk
    | some p =>
      obtain ⟨i, e⟩ := p
      have hrk : g.rank k = i + 1 := by simp [Graph.rank, hf]
      refine outTask_fetchesOnly (cmdTask_fetchesOnly sem _ _ _ (fun _ j hj => ?_) (fun hdyn => ?_)) _
      · exact hrk ▸ g.rank_lt hg hf (by simp only [GEdge.inputs, GEdge.allIns, List.mem_append] at hj ⊢; exact .inl hj)
      · refine (hd e (findOut_mem hf) hdyn).mono fun j hj => ?_
        rcases hj with hs | hj
        · rw [hrk, g.rank_source hs]; exact Nat.succ_pos i
        · exact hrk ▸ g.rank_lt hg hf hj

/-- The emitted manifest's meaning is acyclic. -/
def emitAcyclic (sem : Sem V) (g : Graph) (hg : g.Valid) (hd : g.DynOK sem) :
    (denote sem (emit g)).Acyclic :=
  (denote_emit sem g hg) ▸ g.acyclic sem hg hd

theorem emit_acyclic (sem : Sem V) (g : Graph) (hg : g.Valid) (hd : g.DynOK sem) :
    Nonempty (denote sem (emit g)).Acyclic :=
  ⟨emitAcyclic sem g hg hd⟩

end Mise.Frontend
