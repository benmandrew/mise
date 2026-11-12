import Mise.Task.Basic

/-!
# Stage 2: build specifications and correctness

A `BuildSpec` says which keys are sources and gives a task for every key.
`Correct b S R` is the "à la carte" correctness predicate. `cleanBuild` is a
reference build from scratch, and `correct_unique` shows that there is at most
one correct store for any set of sources.
-/

namespace Mise

/-- A build specification: which keys are sources, and for every key a task
that computes its value from the values of other keys. Correctness
(`Correct`) ignores the task of a source.
Gloss: build specifications with keys {K} and values {V} -/
structure BuildSpec (K V : Type) where
  isSource : K → Bool
  task : K → Task K V V

namespace Task

variable {K V α : Type}

/-- Run a task against a partial store that only needs keys satisfying `P`. -/
def runP {P : K → Prop} : (t : Task K V α) → t.FetchesOnly P → ((k : K) → P k → V) → α
  | .pure a, _, _ => a
  | .fetch k c, h, g => (c (g k h.head)).runP (h.tail _) g

theorem runP_eq {P : K → Prop} (t : Task K V α) (h : t.FetchesOnly P)
    (g : (k : K) → P k → V) (s : Store K V) (hg : ∀ k hk, g k hk = s k) :
    t.runP h g = t.run s := by
  induction t with
  | pure a => rfl
  | fetch k c ih => simp only [runP, run, hg]; exact ih _ _

end Task

namespace BuildSpec

variable {K V : Type} (b : BuildSpec K V)

/-- `R` is a correct result of building `b` from sources `S`.
Gloss: {R} is a correct result of building {b} from the sources {S} -/
def Correct (S R : Store K V) : Prop :=
  (∀ k, b.isSource k = true → R k = S k) ∧
  (∀ k, b.isSource k = false → R k = (b.task k).run R)

/-- A rank witnessing acyclicity: every target's task fetches, on every branch,
only keys of strictly smaller rank. This is data, so that `cleanBuild` stays
computable. -/
structure Acyclic where
  rank : K → Nat
  fetches : ∀ k, b.isSource k = false → (b.task k).FetchesOnly (fun j => rank j < rank k)

variable {b}

/-- Build every key from scratch, by well-founded recursion on rank. -/
def cleanBuild (h : b.Acyclic) (S : Store K V) (k : K) : V :=
  if hs : b.isSource k = true then S k
  else (b.task k).runP (h.fetches k (by simpa using hs)) (fun j _ => cleanBuild h S j)
termination_by h.rank k
decreasing_by assumption

theorem cleanBuild_source (h : b.Acyclic) (S : Store K V) {k : K} (hs : b.isSource k = true) :
    cleanBuild h S k = S k := by
  rw [cleanBuild]; simp [hs]

theorem cleanBuild_target (h : b.Acyclic) (S : Store K V) {k : K} (hs : b.isSource k = false) :
    cleanBuild h S k = (b.task k).run (cleanBuild h S) := by
  rw [cleanBuild]
  simp only [hs, Bool.false_eq_true, ↓reduceDIte]
  exact Task.runP_eq _ _ _ _ (fun _ _ => rfl)

theorem cleanBuild_correct (h : b.Acyclic) (S : Store K V) : b.Correct S (cleanBuild h S) :=
  ⟨fun _ hs => cleanBuild_source h S hs, fun _ hs => cleanBuild_target h S hs⟩

/-- **Headline (Stage 2).** An acyclic spec has at most one correct store. -/
theorem correct_unique (h : b.Acyclic) {S R₁ R₂ : Store K V}
    (h₁ : b.Correct S R₁) (h₂ : b.Correct S R₂) : R₁ = R₂ := by
  have key : ∀ n k, h.rank k < n → R₁ k = R₂ k := by
    intro n
    induction n with
    | zero => intro k hk; omega
    | succ n ih =>
      intro k hk
      cases hs : b.isSource k
      · rw [h₁.2 k hs, h₂.2 k hs]
        apply (Task.run_eq_of_agree _ _ _ _).1
        intro j hj
        exact ih j (by have := (h.fetches k hs).deps_sat R₁ j hj; omega)
      · rw [h₁.1 k hs, h₂.1 k hs]
  funext k
  exact key _ k (Nat.lt_succ_self _)

/-- Any correct store equals the clean build. -/
theorem correct_eq_cleanBuild (h : b.Acyclic) {S R : Store K V} (hR : b.Correct S R) :
    R = cleanBuild h S :=
  correct_unique h hR (cleanBuild_correct h S)

end BuildSpec

end Mise
