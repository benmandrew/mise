import Mise.Model.Sound

/-!
# Stages 5 and 6: the model on emitted manifests

A valid graph emits a manifest whose edges are in schedule order
(`sched_emit`). When every depfile command reads only sources and its
declared inputs (`Graph.DynOK`), the emitted manifest meets the
static-ancestor condition (`reads_emit`). `dsl_sound` composes these with
`denote_emit`: after any history of edits and builds, building the emitted
manifest gives the clean build of the DSL's own meaning.
-/

namespace Mise.Model
open Mise Mise.Syntax Mise.Frontend

/-- The model edge for a DSL edge. -/
def gEdge (g : Graph) (e : GEdge) : MEdge :=
  ⟨e.allOuts, e.inputs, e.orderOnly, g.cmd e, g.isDyn e, g.isRestat e⟩

theorem medges_emit (g : Graph) (hg : g.Valid) : (emit g).medges = g.edges.map (gEdge g) := by
  unfold Manifest.medges
  rw [(elab_emit g).1, (elab_emit g).2, List.map_map]
  refine List.map_congr_left fun e he => ?_
  simp only [Function.comp, toMEdge, gEdge, command_emit g hg e he, isDyn_emit g hg e he,
    isRestat_emit g hg e he]
  rfl

theorem edgesOK_outs {names : List String} {srcs p : List Path} {es : List GEdge}
    (h : edgesOK names srcs p es = true) {e : GEdge} (he : e ∈ es) : ∀ o ∈ e.allOuts, o ∉ p ∧ o ∉ srcs := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem he
  obtain ⟨-, -, -, -, h5, -, -⟩ := GEdge.ok_parts (edgesOK_get h hi)
  intro o ho
  obtain ⟨h1, h2⟩ := h5 o ho
  have h1 : o ∉ p ++ List.flatMap GEdge.allOuts (List.take i es) := by simpa using h1
  exact ⟨fun hp => h1 (List.mem_append_left _ hp), by simpa using h2⟩

theorem sched_of_edgesOK {names : List String} {srcs : List Path} (f : GEdge → String) (d r : GEdge → Bool) :
    ∀ (p : List Path) (es : List GEdge), edgesOK names srcs p es = true →
      Sched (es.map fun e => ⟨e.allOuts, e.inputs, e.orderOnly, f e, d e, r e⟩)
  | _, [], _ => trivial
  | p, e :: es, h => by
    have h' := h
    simp only [edgesOK, Bool.and_eq_true] at h'
    obtain ⟨-, -, -, -, h5, h6, -⟩ := GEdge.ok_parts h'.1
    have hin : ∀ i ∈ e.inputs ++ e.orderOnly, i ∈ srcs ∨ i ∈ p := fun i hi => by
      have := h6 i (by simpa only [GEdge.inputs, GEdge.allIns, List.append_assoc] using hi)
      simpa using this
    have hrest : ∀ {e'}, e' ∈ es → ∀ o ∈ e'.allOuts, o ∉ p ++ e.allOuts ∧ o ∉ srcs :=
      fun he' => edgesOK_outs h'.2 he'
    refine ⟨?_, ?_, sched_of_edgesOK f d r _ es h'.2⟩
    · intro i hi hio
      obtain ⟨hp, hs⟩ := h5 i hio
      rcases hin i hi with h | h
      · simp_all
      · simp_all
    · simp only [List.mem_map]
      rintro _ ⟨e', he', rfl⟩
      refine ⟨fun i hi hio => ?_, fun o ho ho' => ?_⟩
      · obtain ⟨hp, hs⟩ := hrest he' i hio
        rcases hin i hi with h | h
        · exact hs h
        · exact hp (List.mem_append_left _ h)
      · exact (hrest he' o ho').1 (List.mem_append_right _ ho)

/-- Emitted manifests are in schedule order. -/
theorem sched_emit (g : Graph) (hg : g.Valid) : Sched (emit g).medges := by
  rw [medges_emit g hg]
  exact sched_of_edgesOK g.cmd g.isDyn g.isRestat [] g.edges (Graph.check_parts hg).2.2.1

variable {V : Type} [Inhabited V] (sem : Sem V)

omit [Inhabited V] in
/-- The static-ancestor condition holds for the emitted manifest when it
holds for the graph. -/
theorem reads_emit (g : Graph) (hg : g.Valid) (hd : g.DynOK sem) : Reads sem (emit g).medges := by
  rw [medges_emit g hg]
  intro me hme hdy
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hme
  refine (hd e he hdy).mono fun k hk => ?_
  rcases hk with hk | hk
  · refine .inl fun e' he' hko => ?_
    obtain ⟨e'', he'', rfl⟩ := List.mem_map.mp he'
    simp only [Graph.isSource, Option.isNone_iff_eq_none] at hk
    exact findOut_none_iff hk e'' he'' hko
  · exact .inr (by simpa only [MEdge.reads, gEdge, GEdge.allIns, GEdge.inputs, List.append_assoc] using hk)

/-- **End to end.** After any history of source edits and builds from empty
logs, running the model of Ninja on the emitted manifest gives a clean
build of the DSL's meaning, and a second build runs nothing. -/
theorem dsl_sound (g : Graph) (hg : g.Valid) (hd : g.DynOK sem) {st : St V}
    (h : Reach sem (emit g).medges st) :
    (ninjaBuild sem (emit g) st).content = BuildSpec.cleanBuild (g.acyclic sem hg hd) st.content ∧
      buildTrace sem (emit g).medges (ninjaBuild sem (emit g) st) = (ninjaBuild sem (emit g) st, []) := by
  obtain ⟨hc, hi⟩ := reach_sound sem (sched_emit g hg) (reads_emit sem g hg hd) h
  rw [denote_emit sem g hg] at hc
  refine ⟨?_, hi⟩
  funext k
  exact congrFun (BuildSpec.correct_eq_cleanBuild (g.acyclic sem hg hd) hc) k

omit [Inhabited V] in
/-- With no depfile rules, the condition on depfile commands holds. -/
theorem dynOK_static (g : Graph) (h : ∀ e ∈ g.edges, g.isDyn e = false) : g.DynOK sem :=
  fun e he hd => by rw [h e he] at hd; cases hd

end Mise.Model
