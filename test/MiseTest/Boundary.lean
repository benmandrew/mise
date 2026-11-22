import MiseTest.Reachable

/-! Tests at the boundary of the theorems in `Mise/Theorems.lean`. A
definition in a hypothesis that is too strong makes a theorem vacuous, so
those get positive tests: realistic cases satisfy them. A definition in a
conclusion that is too weak makes a theorem trivial, so those get negative
tests, or a positive test against a value computed by hand. -/

namespace MiseTest.Boundary
open Mise Mise.Syntax Mise.Model Mise.Frontend Mise.Theorems MiseTest.Reachable

/-! ## The one-edge graph `g` from `MiseTest.Reachable` -/

/-- The one edge of `g`, as the model sees it. -/
def cc : MEdge := { outs := ["main.o"], ins := ["main.c"], cmd := "cc -c main.c -o main.o" }

example : edges g = [cc] := by decide

/-! ### `ran` (conclusion of `rebuild_noop`, hypothesis of `rebuild_minimal`) -/

/-- A first build runs the edge. If `ran` were always empty, `rebuild_noop`
would say nothing. -/
example : ran sem g start = [cc] := by decide

/-- The hypotheses of `rebuild_minimal` hold: `main.c` is a source, and the
rebuild after editing it runs `cc`. -/
example : g.isSource "main.c" ∧ cc ∈ ran sem g ((build sem g start).edits [("main.c", "v2")]) := by
  decide

/-! ### `Checks` (conclusion of `rebuild_minimal`) -/

/-- Ninja does not check an edge's own output as one of its inputs. -/
example : ¬ Checks (build sem g start) cc "main.o" := by
  simp [Checks, cc, St.effIns]

/-! ### `Correct` (conclusion of `build_correct`, hypothesis of `correct_unique`) -/

/-- The correct result for `start`, worked out by hand. -/
def expected : Path → String := fun p =>
  if p = "main.c" then "v1" else if p = "main.o" then "compiled v1" else ""

theorem g_isSource (k : Path) : g.isSource k = !decide (k = "main.o") := by
  by_cases h : k = "main.o" <;> simp [Graph.isSource, findOut, g, GEdge.allOuts, h]

/-- With `correct_unique`, `expected` is the only result `Correct` accepts. -/
example : (g.spec sem).Correct start.content expected := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · change g.isSource k = true at hk
    by_cases h : k = "main.c" <;> simp_all [g_isSource, expected, start, St.content]
  · change g.isSource k = false at hk
    simp [g_isSource] at hk; subst hk; decide

/-- `main.c` emptied, and `main.o` compiled from the empty file. -/
def emptied : Path → String := fun p =>
  if p = "main.o" then "compiled " else ""

/-- `Correct` rejects a result whose source was emptied. -/
example : ¬ (g.spec sem).Correct start.content emptied := fun h =>
  absurd (h.1 "main.c" (by decide)) (by decide)

/-! ### `Spec` (conclusion of `build_correct` and `any_order`) -/

/-- A build that ignores its input and leaves `emptied`. -/
def emptyingBuild (_ : St String) : St String := { start with fs := fun p => some (emptied p, 0) }

/-- `Spec` rejects `emptyingBuild`. The test above checks `Correct` alone;
this one checks how the two theorems use it. A `Spec` that compared the
result with itself, `Correct (f st).content (f st).content`, would accept
`emptyingBuild`, because its targets match the emptied source. -/
example : ¬ Spec sem g emptyingBuild := fun h =>
  absurd ((h (by reach_init start_fresh)).1 "main.c" (by decide))
    (by decide)

/-! ### `wrapped_run` and `runWrapped` -/

/-- Build under `cmp`, then edit `main.c`, so the edge is dirty again. -/
def edited : St String := (build sem.withCmp g start).edit "main.c" "v2"

theorem edited_reachable : Reachable sem.withCmp g edited :=
  .edit "main.c" "v2" (.step (show Reachable sem.withCmp g start by reach_init start_fresh) (.head _))
    (by decide)

/-- The command writes what `sem` says. -/
def w : Path → Option String := fun o => some (edited.outVal sem cc o)

/-- Every hypothesis of `wrapped_run` holds on a real state: the edge is in
the manifest and dirty, no `.mise-old` file is an output, and none exists. -/
example : Reachable sem.withCmp g (edited.runWrapped sem cc w true) :=
  (wrapped_run sem g (by decide) edited_reachable (by decide) (by decide) w true
    (fun _ _ _ h => (Option.some.inj h).symm) (by decide) (by decide)).2

/-- A successful wrapped run writes the output and leaves the edge clean. If
`runWrapped` changed nothing, `wrapped_run` would still hold. -/
example : (edited.runWrapped sem cc w true).content "main.o" = "compiled v2" ∧
    (edited.runWrapped sem cc w true).dirty cc = false := by decide

/-! ## A depfile graph -/

/-- A generator writes `config.h`. Two depfile compiles may read it: it is an
order-only input of each. -/
def two : Graph :=
  { sources := ["a.c", "b.c", "util.h", "config.in"]
    rules := [{ name := "gen", command := [.lit "gen ", .var "in", .lit " ", .var "out"] },
              { name := "cc", command := [.lit "cc -c ", .var "in", .lit " -o ", .var "out"], depfile := true }]
    edges := [{ rule := "gen", outs := ["config.h"], ins := ["config.in"] },
              { rule := "cc", outs := ["a.o"], ins := ["a.c"], orderOnly := ["config.h"] },
              { rule := "cc", outs := ["b.o"], ins := ["b.c"], orderOnly := ["config.h"] }] }

def gen : MEdge := { outs := ["config.h"], ins := ["config.in"], cmd := "gen config.in config.h" }
def aO : MEdge := { outs := ["a.o"], ins := ["a.c"], oo := ["config.h"], cmd := "cc -c a.c -o a.o", dyn := true }
def bO : MEdge := { outs := ["b.o"], ins := ["b.c"], oo := ["config.h"], cmd := "cc -c b.c -o b.o", dyn := true }

example : two.Valid ∧ edges two = [gen, aO, bO] := by decide

/-- The source in `cc -c SRC -o OUT`. It works on characters because the
kernel cannot evaluate `String.splitOn`, and `decide` needs it to. -/
def srcOf (cmd : String) : Path := .ofList ((cmd.toList.drop "cc -c ".length).takeWhile (· != ' '))

/-- A compile reads its `.c` file, then `util.h` and `config.h`, neither of
which its edge lists as an explicit input. -/
def depSem : Sem String :=
  { exec := fun _ ins => [String.join ins]
    dyn := fun cmd => (fetchAll [srcOf cmd, "util.h", "config.h"]).bind fun vs => .pure [String.join vs] }

/-! ### `DynOK` (hypothesis of four theorems) -/

/-- A depfile compile may read an undeclared source and an order-only input.
The proof builds `FetchesOnly` from its constructors, so it also tests
`FetchesOnly`; the library lemma `fetchAll_fetchesOnly` would not. -/
example : two.DynOK depSem := by
  intro e he hd
  simp [two] at he
  rcases he with rfl | rfl | rfl
  · simp [Graph.isDyn, Graph.ruleOf, two] at hd
  all_goals
    simp only [depSem, fetchAll]
    exact .fetch _ _ (by decide) fun _ => .fetch _ _ (by decide) fun _ => .fetch _ _ (by decide) fun _ => .pure _

/-! ### `ran` and `Checks` on more than one edge -/

/-- The sources of `two` hold their own names, written at time 0. -/
def start2 : St String :=
  { fs := fun p => if p ∈ two.sources then some (p, 0) else none, log := fun _ => none, clock := 0 }

theorem start2_fresh : start2.Fresh :=
  ⟨fun p v t h => by simp [start2] at h ⊢; omega, fun _ _ _ h => nomatch h⟩

/-- `Reach.step` may visit any edge of the manifest, not only the first. -/
example : Reachable depSem two (((start2.step depSem gen).step depSem aO).step depSem bO) :=
  .step (.step (.step (by reach_init start2_fresh) (by decide)) (by decide)) (by decide)

/-- A first build runs all three edges, in manifest order. -/
example : ran depSem two start2 = [gen, aO, bO] := by decide

/-- Depfile compiles that read only their `.c` file. -/
def srcSem : Sem String :=
  { exec := fun _ ins => [String.join ins]
    dyn := fun cmd => (fetchAll [srcOf cmd]).bind fun vs => .pure [String.join vs] }

/-- `config.h` is an order-only input of `aO`. A compile that does not read
it records no dependency on it, so Ninja does not check it. -/
example : ¬ Checks (build srcSem two start2) aO "config.h" := by
  have h : (build srcSem two start2).effIns aO "a.o" = some ["a.c", "a.c"] := by decide
  simp only [aO] at h
  simp [Checks, aO, h]

/-! ### `ValidOrder` (hypothesis of `any_order`) -/

/-- The two compiles may run in either order. -/
example : ValidOrder two [gen, bO, aO] := by
  constructor
  · decide
  · simp [Sched, Disjoint, gen, aO, bO, MEdge.reads]

end MiseTest.Boundary
