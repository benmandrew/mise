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
  rintro ⟨o, ho, D, hD, hp⟩
  simp [cc, St.effIns] at ho hD; subst hD; simp at hp

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

/-! ### `wrapped_run` and `runWrapped` -/

/-- Build under `cmp`, then edit `main.c`, so the edge is dirty again. -/
def edited : St String := (build sem.withCmp g start).edit "main.c" "v2"

theorem edited_reachable : Reachable sem.withCmp g edited :=
  .edit "main.c" "v2" (.step (.init start_fresh (fun _ => rfl) (fun _ => rfl)) (.head _)) (by decide)

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

/-- A depfile compile may read an undeclared source and an order-only input. -/
example : two.DynOK depSem := by
  intro e he hd
  simp [two] at he
  rcases he with rfl | rfl | rfl
  · simp [Graph.isDyn, Graph.ruleOf, two] at hd
  all_goals exact (fetchAll_fetchesOnly _ (by decide)).bind fun _ => .pure _

/-! ### `ValidOrder` (hypothesis of `any_order`) -/

/-- The two compiles may run in either order. -/
example : ValidOrder two [gen, bO, aO] := by
  constructor
  · decide
  · simp [Sched, Disjoint, gen, aO, bO, MEdge.reads]

end MiseTest.Boundary
