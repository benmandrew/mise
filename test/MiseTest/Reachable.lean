import Mise.Theorems

/-! Two concrete checks of `Reachable` on a one-edge graph: a state that a
history reaches, and a state no history reaches. -/

namespace MiseTest.Reachable
open Mise Mise.Model Mise.Frontend Mise.Theorems

/-- One compile: `main.c` → `main.o`. -/
def g : Graph :=
  { sources := ["main.c"]
    rules := [{ name := "cc", command := [.lit "cc -c ", .var "in", .lit " -o ", .var "out"] }]
    edges := [{ rule := "cc", outs := ["main.o"], ins := ["main.c"] }] }

/-- A compile turns each input's contents `s` into `compiled s`. -/
def sem : Sem String := { exec := fun _ ins => ins.map ("compiled " ++ ·), dyn := fun _ => .pure [] }

/-- `main.c` holds `v1`, written at time 0. Nothing is built and the logs are empty. -/
def start : St String :=
  { fs := fun p => if p = "main.c" then some ("v1", 0) else none, log := fun _ => none, clock := 0 }

theorem start_fresh : start.Fresh :=
  ⟨fun p v t h => by simp [start] at h; omega, fun _ _ _ h => nomatch h⟩

/-- Start, build, edit `main.c`, build again. A build of `g` is one visit to its one edge. -/
example : Reachable sem g (build sem g ((build sem g start).edit "main.c" "v2")) := by
  have s0 : Reachable sem g start := .init start_fresh (fun _ => rfl) (fun _ => rfl)
  have s1 := Reach.step s0 (.head _)                  -- build
  have s2 := Reach.edit "main.c" "v2" s1 (by decide)  -- edit: no edge writes main.c
  exact Reach.step s2 (.head _)                       -- build again

/-- `main.o` holds garbage. It is newer than `main.c`, and its log entry has
the edge's command at a time no older than `main.c`, so Ninja would skip it. -/
def bad : St String :=
  { fs := fun p => if p = "main.c" then some ("v1", 1)
                   else if p = "main.o" then some ("garbage", 2) else none
    log := fun p => if p = "main.o" then some ("cc -c main.c -o main.o", 2) else none
    clock := 2 }

example : (edges g).map bad.dirty = [false] := by decide

/-- `g` has no depfile rules. -/
theorem g_dynOK : g.DynOK sem := by simp [Graph.DynOK, g, Graph.isDyn, Graph.ruleOf]

/-- If `bad` were reachable, a build that runs nothing would leave correct contents. -/
example : ¬ Reachable sem g bad := fun h => by
  have := (build_correct sem g (by decide) g_dynOK h).2 "main.o" rfl
  exact absurd this (by decide)

end MiseTest.Reachable
