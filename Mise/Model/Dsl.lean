import Mise.Model.Sound

/-!
# Stage 5: the model on emitted manifests

A valid graph emits a manifest whose edges are in schedule order
(`sched_emit`), so the Stage 5 theorems apply to it. `dsl_sound` composes
them with `denote_emit`: after any source edits, building the emitted
manifest gives the clean build of the DSL's own meaning.
-/

namespace Mise.Model
open Mise Mise.Syntax Mise.Frontend

/-- The model edge for a DSL edge. -/
def gEdge (g : Graph) (e : GEdge) : MEdge := ⟨e.allOuts, e.inputs, g.cmd e⟩

theorem medges_emit (g : Graph) (hg : g.Valid) : (emit g).medges = g.edges.map (gEdge g) := by
  unfold Manifest.medges
  rw [(elab_emit g).1, (elab_emit g).2, List.map_map]
  refine List.map_congr_left fun e he => ?_
  simp only [Function.comp, toMEdge, gEdge, command_emit g hg e he]
  rfl

theorem edgesOK_outs {names : List String} {srcs p : List Path} {es : List GEdge}
    (h : edgesOK names srcs p es = true) {e : GEdge} (he : e ∈ es) : ∀ o ∈ e.allOuts, o ∉ p ∧ o ∉ srcs := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem he
  obtain ⟨-, -, -, -, h5, -, -⟩ := GEdge.ok_parts (edgesOK_get h hi)
  intro o ho
  obtain ⟨h1, h2⟩ := h5 o ho
  have h1 : o ∉ p ++ List.flatMap GEdge.allOuts (List.take i es) := by simpa using h1
  exact ⟨fun hp => h1 (List.mem_append_left _ hp), by simpa using h2⟩

theorem sched_of_edgesOK {names : List String} {srcs : List Path} (f : GEdge → String) :
    ∀ (p : List Path) (es : List GEdge), edgesOK names srcs p es = true →
      Sched (es.map fun e => ⟨e.allOuts, e.inputs, f e⟩)
  | _, [], _ => trivial
  | p, e :: es, h => by
    have h' := h
    simp only [edgesOK, Bool.and_eq_true] at h'
    obtain ⟨-, -, -, -, h5, h6, -⟩ := GEdge.ok_parts h'.1
    have hin : ∀ i ∈ e.inputs, i ∈ srcs ∨ i ∈ p := fun i hi => by
      have := h6 i (by simp only [GEdge.inputs, GEdge.allIns, List.mem_append] at hi ⊢; exact .inl hi)
      simpa using this
    have hrest : ∀ {e'}, e' ∈ es → ∀ o ∈ e'.allOuts, o ∉ p ++ e.allOuts ∧ o ∉ srcs :=
      fun he' => edgesOK_outs h'.2 he'
    refine ⟨?_, ?_, sched_of_edgesOK f _ es h'.2⟩
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
  exact sched_of_edgesOK (g.cmd) [] g.edges (Graph.check_parts hg).2.2.1

variable {V : Type} [Inhabited V] (exec : String → List V → List V)

/-- **End to end.** Start from contents correct for the DSL's meaning, edit
any sources, and run the model of Ninja on the emitted manifest: the
contents equal a clean build of the DSL's meaning for the new sources. -/
theorem dsl_sound (g : Graph) (hg : g.Valid) {st : St V} (hf : st.Fresh)
    (hc : (g.spec exec).Correct st.content st.content) (edits : List (Path × V))
    (he : ∀ pv ∈ edits, (g.spec exec).isSource pv.1 = true) :
    (ninjaBuild exec (emit g) (st.edits edits)).content =
      BuildSpec.cleanBuild (g.acyclic exec hg) (st.edits edits).content := by
  rw [← denote_emit exec g hg] at hc he
  have h := ninjaBuild_sound exec (sched_emit g hg) hf hc edits he
  rw [denote_emit exec g hg] at h
  funext k
  exact congrFun (BuildSpec.correct_eq_cleanBuild (g.acyclic exec hg) h) k

/-- From an empty build log, building the emitted manifest gives the clean
build of the DSL's meaning. -/
theorem dsl_clean (g : Graph) (hg : g.Valid) {st : St V} (hf : st.Fresh) (hlog : ∀ p, st.log p = none) :
    (ninjaBuild exec (emit g) st).content = BuildSpec.cleanBuild (g.acyclic exec hg) st.content := by
  have h := ninjaBuild_clean_correct exec (sched_emit g hg) hf hlog
  rw [denote_emit exec g hg] at h
  funext k
  exact congrFun (BuildSpec.correct_eq_cleanBuild (g.acyclic exec hg) h) k

end Mise.Model
