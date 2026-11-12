/-!
# Stage 1: tasks as a free monad over `fetch`

A `Task K V α` is a tree. Each `fetch` node asks for the value of one key and
continues with a function of that value. This is the initial encoding of the
"à la carte" task, which gives us structural induction.
-/

namespace Mise

/-- A build task with keys `K`, values `V` and result `α`, as a tree: `pure a`
returns `a`, and `fetch k c` asks for the value of key `k` and continues
with `c` applied to that value. -/
inductive Task (K V : Type) (α : Type) where
  | pure  : α → Task K V α
  | fetch : K → (V → Task K V α) → Task K V α

/-- A store maps every key to its current value. -/
abbrev Store (K V : Type) := K → V

namespace Task

variable {K V α β γ : Type}

/-- Run the first task, then the task that `f` builds from its result. The
first task's fetches come first. -/
def bind : Task K V α → (α → Task K V β) → Task K V β
  | .pure a, f => f a
  | .fetch k c, f => .fetch k (fun v => (c v).bind f)

instance : Monad (Task K V) where
  pure := Task.pure
  bind := Task.bind

@[simp] theorem pure_eq (a : α) : (Pure.pure a : Task K V α) = Task.pure a := rfl

@[simp] theorem bind_eq (t : Task K V α) (f : α → Task K V β) :
    t >>= f = t.bind f := rfl

@[simp] theorem pure_bind (a : α) (f : α → Task K V β) :
    (Task.pure a).bind f = f a := rfl

@[simp] theorem fetch_bind (k : K) (c : V → Task K V α) (f : α → Task K V β) :
    (Task.fetch k c).bind f = .fetch k (fun v => (c v).bind f) := rfl

@[simp] theorem bind_pure (t : Task K V α) : t.bind Task.pure = t := by
  induction t with
  | pure a => rfl
  | fetch k c ih => simp [ih]

theorem bind_assoc (t : Task K V α) (f : α → Task K V β) (g : β → Task K V γ) :
    (t.bind f).bind g = t.bind (fun a => (f a).bind g) := by
  induction t with
  | pure a => rfl
  | fetch k c ih => simp [ih]

instance : LawfulMonad (Task K V) := LawfulMonad.mk'
  (id_map := fun t => by
    show t.bind (fun a => Task.pure (id a)) = t
    exact bind_pure t)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun t f g => bind_assoc t f g)

end Task

/-- Ask for the value of key `k`. -/
def fetch {K V : Type} (k : K) : Task K V V := .fetch k .pure

namespace Task

variable {K V α β : Type}

/-- Interpret a task in any monad, given a way to fetch a key. -/
def interp {M : Type → Type} [Monad M] (h : K → M V) : Task K V α → M α
  | .pure a => Pure.pure a
  | .fetch k c => h k >>= fun v => (c v).interp h

/-- The result of a task when each fetch reads from the store `s`. -/
def run (s : Store K V) : Task K V α → α
  | .pure a => a
  | .fetch k c => (c (s k)).run s

/-- The keys a task fetches when run against `s`, in order. -/
def deps (s : Store K V) : Task K V α → List K
  | .pure _ => []
  | .fetch k c => k :: (c (s k)).deps s

@[simp] theorem run_pure (s : Store K V) (a : α) : (Task.pure a).run s = a := rfl
@[simp] theorem run_fetch (s : Store K V) (k : K) (c : V → Task K V α) :
    (Task.fetch k c).run s = (c (s k)).run s := rfl
@[simp] theorem deps_pure (s : Store K V) (a : α) : (Task.pure a : Task K V α).deps s = [] := rfl
@[simp] theorem deps_fetch (s : Store K V) (k : K) (c : V → Task K V α) :
    (Task.fetch k c).deps s = k :: (c (s k)).deps s := rfl

@[simp] theorem run_bind (s : Store K V) (t : Task K V α) (f : α → Task K V β) :
    (t.bind f).run s = (f (t.run s)).run s := by
  induction t with
  | pure a => rfl
  | fetch k c ih => simp [ih]

@[simp] theorem deps_bind (s : Store K V) (t : Task K V α) (f : α → Task K V β) :
    (t.bind f).deps s = t.deps s ++ (f (t.run s)).deps s := by
  induction t with
  | pure a => rfl
  | fetch k c ih => simp [ih]

/-! ## `interp` is a monad morphism -/

@[simp] theorem interp_pure {M : Type → Type} [Monad M] (h : K → M V) (a : α) :
    (Task.pure a).interp h = (Pure.pure a : M α) := rfl

theorem interp_bind {M : Type → Type} [Monad M] [LawfulMonad M] (h : K → M V)
    (t : Task K V α) (f : α → Task K V β) :
    (t >>= f).interp h = t.interp h >>= (interp h ∘ f) := by
  show (t.bind f).interp h = _
  induction t with
  | pure a => simp [interp, bind]
  | fetch k c ih => simp [interp, ih]

/-! ## The direct definitions agree with `interp` -/

theorem run_eq_interp (s : Store K V) (t : Task K V α) :
    t.run s = Id.run (t.interp (M := Id) (fun k => Pure.pure (s k))) := by
  induction t with
  | pure a => rfl
  | fetch k c ih => simp [run, interp, ih]

/-- The logging interpretation: each fetch appends its key to the state. -/
def logFetch (s : Store K V) (k : K) : StateM (List K) V :=
  fun l => (s k, l ++ [k])

theorem interp_logFetch (s : Store K V) (t : Task K V α) (l : List K) :
    (t.interp (logFetch s)).run l = (t.run s, l ++ t.deps s) := by
  induction t generalizing l with
  | pure a => simp [interp]; rfl
  | fetch k c ih =>
    simp only [interp, run, deps]
    show ((c (s k)).interp (logFetch s)).run (l ++ [k]) = _
    rw [ih]
    simp

theorem deps_eq_interp (s : Store K V) (t : Task K V α) :
    t.deps s = ((t.interp (logFetch s)).run []).2 := by
  simp [interp_logFetch]

/-! ## The trace lemma -/

/-- **Headline (Stage 1).** If two stores agree on every key a task fetched
against the first, the task takes the same path against both. -/
theorem run_eq_of_agree (t : Task K V α) (s s' : Store K V)
    (h : ∀ k ∈ t.deps s, s k = s' k) :
    t.run s = t.run s' ∧ t.deps s = t.deps s' := by
  induction t with
  | pure a => exact ⟨rfl, rfl⟩
  | fetch k c ih =>
    have hk : s k = s' k := h k (by simp)
    have := ih (s k) (fun j hj => h j (by simp [hj]))
    simp only [run, deps, ← hk]
    exact ⟨this.1, by rw [this.2]⟩

@[simp] theorem run_congr_store (t : Task K V α) (s s' : Store K V) (h : ∀ k, s k = s' k) :
    t.run s = t.run s' :=
  (run_eq_of_agree t s s' (fun k _ => h k)).1

@[simp] theorem deps_congr_store (t : Task K V α) (s s' : Store K V) (h : ∀ k, s k = s' k) :
    t.deps s = t.deps s' :=
  (run_eq_of_agree t s s' (fun k _ => h k)).2

/-! ## Static fetch bound -/

/-- On every branch of the tree, every `fetch` node's key satisfies `P`. -/
inductive FetchesOnly (P : K → Prop) : Task K V α → Prop
  | pure (a : α) : FetchesOnly P (.pure a)
  | fetch (k : K) (c : V → Task K V α) :
      P k → (∀ v, FetchesOnly P (c v)) → FetchesOnly P (.fetch k c)

namespace FetchesOnly

variable {P Q : K → Prop}

theorem head {k : K} {c : V → Task K V α} (h : FetchesOnly P (.fetch k c)) : P k := by
  cases h; assumption

theorem tail {k : K} {c : V → Task K V α} (h : FetchesOnly P (.fetch k c)) (v : V) :
    FetchesOnly P (c v) := by
  cases h with
  | fetch _ _ _ h => exact h v

theorem mono {t : Task K V α} (h : FetchesOnly P t) (hPQ : ∀ k, P k → Q k) :
    FetchesOnly Q t := by
  induction h with
  | pure a => exact .pure a
  | fetch k c hk _ ih => exact .fetch k c (hPQ k hk) ih

theorem bind {t : Task K V α} {f : α → Task K V β}
    (ht : FetchesOnly P t) (hf : ∀ a, FetchesOnly P (f a)) :
    FetchesOnly P (t.bind f) := by
  induction ht with
  | pure a => exact hf a
  | fetch k c hk _ ih => exact .fetch k _ hk ih

end FetchesOnly

theorem FetchesOnly.deps_sat {P : K → Prop} {t : Task K V α} (h : FetchesOnly P t)
    (s : Store K V) : ∀ k ∈ t.deps s, P k := by
  induction h with
  | pure a => simp
  | fetch k c hk _ ih =>
    intro j hj
    simp only [deps, List.mem_cons] at hj
    rcases hj with rfl | hj
    · exact hk
    · exact ih _ j hj

end Task

theorem fetch_fetchesOnly {K V : Type} {P : K → Prop} {k : K} (hk : P k) :
    (fetch k : Task K V V).FetchesOnly P :=
  .fetch k _ hk (fun v => .pure v)

end Mise
