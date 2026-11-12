import Mise.Model.Basic

/-!
# Stage 7: the `cmp` wrapper for `restat` commands

The DSL wraps a `restat` command in a shell script, `Mise.Frontend.cmpWrap`,
that moves each old output aside, runs the command, and moves the old file
back when `cmp` finds it equal to the new one. `wrapRun` models the
script's effect on the files. `wrapRun_content` says it never changes what
the outputs hold, only which mtimes are kept, and `wrapRun_kept_iff` says an
output keeps its old file exactly when the command wrote the old contents
again, which is `Sem.keep_eq` for the command it wraps. `wrapRun_fail` says a
failed command, or one that left an output missing, changes no file.

`run_withCmp` connects the script to the Ninja model: under `Sem.withCmp`, a
`restat` run writes the files as `wrapRun` does. So for a build whose
`restat` rules are all wrapped, `Sem.withCmp` is the semantics to choose,
and every theorem about `Sem` applies to it with no assumption about how
the wrapped commands decide to keep a file. What remains assumed is that the
script, `cmp` and `mv` behave as `wrapRun` says.
-/

namespace Mise.Model
open Mise Mise.Syntax Mise.Frontend

variable {V : Type} [DecidableEq V]

/-- The files after the wrapper runs a command with outputs `outs` at time
`t`. `r` is what the command wrote to each output, or `none` when it failed
or left an output missing; then the wrapper restores every output. -/
def wrapRun (fs : Path → Option (V × Nat)) (outs : List Path) (r : Option (Path → V)) (t : Nat) :
    Path → Option (V × Nat) := fun p =>
  match r with
  | none => fs p
  | some new =>
    if outs.contains p then
      match fs p with
      | some (old, t0) => if old = new p then some (old, t0) else some (new p, t)
      | none => some (new p, t)
    else fs p

theorem wrapRun_fail (fs : Path → Option (V × Nat)) (outs : List Path) (t : Nat) :
    wrapRun fs outs none t = fs := rfl

/-- The wrapper is invisible in contents: each output holds what the
command wrote, and every other file is unchanged. -/
theorem wrapRun_content (fs : Path → Option (V × Nat)) (outs : List Path) (new : Path → V) (t : Nat)
    (p : Path) : (wrapRun fs outs (some new) t p).map (·.1) =
      if p ∈ outs then some (new p) else (fs p).map (·.1) := by
  simp only [wrapRun, List.contains_iff_mem]
  split
  · split
    · split <;> simp_all
    · simp
  · rfl

/-- An output keeps its old file and mtime exactly when the command wrote
the old contents again. -/
theorem wrapRun_kept_iff (fs : Path → Option (V × Nat)) (outs : List Path) (new : Path → V) (t : Nat)
    (p : Path) (hp : p ∈ outs) (old : V) (t0 : Nat) (hold : fs p = some (old, t0)) (ht : t0 ≠ t) :
    wrapRun fs outs (some new) t p = some (old, t0) ↔ old = new p := by
  simp only [wrapRun, List.contains_iff_mem, hp, ite_true, hold]
  by_cases h : old = new p
  · simp [h]
  · simp only [h, ite_false, Option.some.injEq, Prod.mk.injEq, iff_false]
    exact fun ⟨_, h2⟩ => ht h2.symm

/-- Under `Sem.withCmp`, the model runs a `restat` edge as the wrapper
does: what the command writes is `outVal`, at the run's time. -/
theorem run_withCmp [Inhabited V] (sem : Sem V) (st : St V) (e : MEdge) (hr : e.restat = true) :
    (st.run sem.withCmp e).fs = wrapRun st.fs e.outs (some (st.outVal sem e)) (st.clock + 1) := by
  funext p
  have hv : ∀ o, st.outVal sem.withCmp e o = st.outVal sem e o := fun _ => rfl
  simp only [St.run, wrapRun, St.kept, hr, hv, Bool.true_and, List.contains_iff_mem]
  by_cases hp : p ∈ e.outs
  · simp only [hp, ite_true]
    cases hf : st.fs p with
    | none => simp [hp]
    | some ov =>
      obtain ⟨old, t0⟩ := ov
      by_cases h : old = st.outVal sem e p <;> simp [Sem.withCmp, h, hp]
  · simp [hp]

end Mise.Model
