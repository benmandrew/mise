import Mise.Model.Dsl

/-!
# The command wrapper

The DSL wraps every command in a shell script, `Mise.Frontend.wrapCommand`,
unless the rule opts out. The script moves each old output aside, runs the
command, and checks that it exited 0 and wrote every output. On success it
deletes the old files, except that for a `restat` rule it moves an old file
back when `cmp` finds it equal to the new one. On failure it deletes what
the command wrote and moves every old file back.

`script` models the script as file operations, one per shell command, and
`script_eq` computes its effect: `wrapRun`. `script_fail` says a failure
changes no file and `script_ok` that a success writes or keeps every output.
`wrapRun_content` says the wrapper never changes what the outputs hold, only
which mtimes are kept, and `wrapRun_kept_iff` says a `restat` output keeps
its old file exactly when the command wrote the old contents again, which is
`Sem.keep_eq` for the command it wraps.

`run_withCmp` connects the wrapper to the Ninja model: under `Sem.withCmp`,
a run writes the files as `wrapRun` does. `St.runWrapped` is Ninja running
an edge through the wrapper, which records the edge only on success.
`runWrapped_fail` says a failed run leaves the state as it was, and
`runWrapped_ok` that a successful one is the model's run, so
`reach_runWrapped` keeps every state reachable. For a build whose rules are
all wrapped, `Sem.withCmp` is the semantics to choose, and every theorem
about `Sem` applies to it with no assumption about how the commands decide
to keep a file or whether they write every output. What remains assumed is
that the script, `cmp`, `mv` and `rm` behave as `script` says.
-/

namespace Mise.Model
open Mise Mise.Syntax Mise.Frontend

variable {V : Type} [DecidableEq V]

/-- The files after the wrapper runs a command with outputs `outs` at time
`t`. `r` is what the command wrote to each output, or `none` when it failed
or left an output missing; then the wrapper restores every output. With
`cmp` (a `restat` rule) an output whose contents are unchanged keeps its old
file. -/
def wrapRun (fs : Path → Option (V × Nat)) (outs : List Path) (cmp : Bool) (r : Option (Path → V))
    (t : Nat) : Path → Option (V × Nat) := fun p =>
  match r with
  | none => fs p
  | some new =>
    if outs.contains p then
      match fs p with
      | some (old, t0) => if cmp = true ∧ old = new p then some (old, t0) else some (new p, t)
      | none => some (new p, t)
    else fs p

theorem wrapRun_fail (fs : Path → Option (V × Nat)) (outs : List Path) (cmp : Bool) (t : Nat) :
    wrapRun fs outs cmp none t = fs := rfl

/-- The wrapper is invisible in contents: each output holds what the
command wrote, and every other file is unchanged. -/
theorem wrapRun_content (fs : Path → Option (V × Nat)) (outs : List Path) (cmp : Bool) (new : Path → V)
    (t : Nat) (p : Path) : (wrapRun fs outs cmp (some new) t p).map (·.1) =
      if p ∈ outs then some (new p) else (fs p).map (·.1) := by
  simp only [wrapRun, List.contains_iff_mem]
  split
  · split
    · split <;> simp_all
    · simp
  · rfl

/-- For a `restat` rule, an output keeps its old file and mtime exactly when
the command wrote the old contents again. -/
theorem wrapRun_kept_iff (fs : Path → Option (V × Nat)) (outs : List Path) (new : Path → V) (t : Nat)
    (p : Path) (hp : p ∈ outs) (old : V) (t0 : Nat) (hold : fs p = some (old, t0)) (ht : t0 ≠ t) :
    wrapRun fs outs true (some new) t p = some (old, t0) ↔ old = new p := by
  simp only [wrapRun, List.contains_iff_mem, hp, ite_true, hold, true_and]
  by_cases h : old = new p
  · simp [h]
  · simp only [h, ite_false, Option.some.injEq, Prod.mk.injEq, iff_false]
    exact fun ⟨_, h2⟩ => ht h2.symm

/-- Without `cmp`, a success writes every output afresh. -/
theorem wrapRun_nocmp (fs : Path → Option (V × Nat)) (outs : List Path) (new : Path → V) (t : Nat)
    (p : Path) (hp : p ∈ outs) : wrapRun fs outs false (some new) t p = some (new p, t) := by
  simp only [wrapRun, List.contains_iff_mem, hp, ite_true]
  split <;> simp

theorem wrapRun_congr (fs : Path → Option (V × Nat)) (outs : List Path) (cmp : Bool) {new new' : Path → V}
    (h : ∀ p ∈ outs, new p = new' p) (t : Nat) :
    wrapRun fs outs cmp (some new) t = wrapRun fs outs cmp (some new') t := by
  funext p
  simp only [wrapRun, List.contains_iff_mem]
  by_cases hp : p ∈ outs
  · simp [hp, h p hp]
  · simp [hp]

/-- Under `Sem.withCmp`, the model runs an edge as the wrapper does: what
the command writes is `outVal`, at the run's time, and a `restat` edge
compares. -/
theorem run_withCmp [Inhabited V] (sem : Sem V) (st : St V) (e : MEdge) :
    (st.run sem.withCmp e).fs = wrapRun st.fs e.outs e.restat (some (st.outVal sem e)) (st.clock + 1) := by
  funext p
  have hv : ∀ o, st.outVal sem.withCmp e o = st.outVal sem e o := fun _ => rfl
  simp only [St.run, wrapRun, St.kept, hv, List.contains_iff_mem]
  by_cases hp : p ∈ e.outs
  · cases hr : e.restat with
    | false => cases st.fs p <;> simp [hp]
    | true =>
      cases st.fs p with
      | none => simp [hp]
      | some ov =>
        obtain ⟨old, t0⟩ := ov
        by_cases h : old = st.outVal sem e p <;> simp [Sem.withCmp, h, hp]
  · simp [hp]

/-! ## The script as file operations -/

/-- The files: contents and mtime of each path, or `none` when absent. -/
abbrev Files (V : Type) := Path → Option (V × Nat)

/-- Where the wrapper moves an old output while its command runs.
Gloss: the `.mise-old` file of {p} -/
def aside (p : Path) : Path := p ++ ".mise-old"

theorem aside_inj {p q : Path} (h : aside p = aside q) : p = q := (String.append_left_inj _).mp h

/-- `mv -f a b`: `b` gets `a`'s file, mtime included, and `a` is gone. -/
def mvF (a b : Path) (fs : Files V) : Files V := fun p => if p = b then fs a else if p = a then none else fs p

/-- `rm -f a`. -/
def rmF (a : Path) (fs : Files V) : Files V := fun p => if p = a then none else fs p

/-- The first loop, for output `f`:
`if [ -e f ]; then mv -f f f.mise-old; elif [ -e f.mise-old ]; then rm -f f.mise-old; fi`. -/
def stash (fs : Files V) (f : Path) : Files V :=
  if (fs f).isSome then mvF f (aside f) fs else if (fs (aside f)).isSome then rmF (aside f) fs else fs

/-- The command: it writes `v` at time `t` to each output `f` with
`w f = some v`, and changes no other file. -/
def command (outs : List Path) (w : Path → Option V) (t : Nat) (fs : Files V) : Files V := fun p =>
  if p ∈ outs then
    match w p with
    | some v => some (v, t)
    | none => fs p
  else fs p

/-- The last loop, for output `f`, where `s` is whether the status is 0:
`if [ $s != 0 ]; then rm -f f; if [ -e f.mise-old ]; then mv -f f.mise-old f; fi;
elif [ -e f.mise-old ]; then ...; fi`. The elided part is `rm -f f.mise-old`,
or with `cmp` (a `restat` rule)
`if cmp -s f f.mise-old; then mv -f f.mise-old f; else rm -f f.mise-old; fi`. -/
def settle (cmp s : Bool) (fs : Files V) (f : Path) : Files V :=
  if !s then
    let fs' := rmF f fs
    if (fs' (aside f)).isSome then mvF (aside f) f fs' else fs'
  else if (fs (aside f)).isSome then
    if cmp && decide ((fs f).map (·.1) = (fs (aside f)).map (·.1)) then mvF (aside f) f fs
    else rmF (aside f) fs
  else fs

/-- The script `wrapCommand` emits, for a command with outputs `outs` that
leaves `w` and exits 0 when `ok`, run at time `t`: the files afterwards, and
whether the script exits 0. The status is 0 when the command exited 0 and
every output exists. -/
def script (cmp : Bool) (outs : List Path) (w : Path → Option V) (ok : Bool) (t : Nat) (fs : Files V) :
    Files V × Bool :=
  let fs₁ := outs.foldl stash fs
  let fs₂ := command outs w t fs₁
  let s := ok && outs.all fun f => (fs₂ f).isSome
  (outs.foldl (settle cmp s) fs₂, s)

/-! ### Each loop acts on one output and its `.mise-old` file at a time -/

section Loops
variable {step : Files V → Path → Files V}

omit [DecidableEq V] in
theorem foldl_other (h1 : ∀ fs f p, p ≠ f → p ≠ aside f → step fs f p = fs p) :
    ∀ (outs : List Path) (fs : Files V) (p : Path), (∀ f ∈ outs, p ≠ f ∧ p ≠ aside f) →
      outs.foldl step fs p = fs p
  | [], _, _, _ => rfl
  | f :: outs, fs, p, hp => by
    rw [List.foldl_cons, foldl_other h1 outs _ p fun g hg => hp g (by simp [hg])]
    exact h1 fs f p (hp f (by simp)).1 (hp f (by simp)).2

omit [DecidableEq V] in
theorem foldl_at (h1 : ∀ fs f p, p ≠ f → p ≠ aside f → step fs f p = fs p)
    (h2 : ∀ fs fs' f, fs f = fs' f → fs (aside f) = fs' (aside f) →
      ∀ p, (p = f ∨ p = aside f) → step fs f p = step fs' f p) :
    ∀ (outs : List Path) (fs : Files V), outs.Nodup → (∀ f ∈ outs, aside f ∉ outs) →
      ∀ f ∈ outs, ∀ p, (p = f ∨ p = aside f) → outs.foldl step fs p = step fs f p
  | [], _, _, _, f, hf, _, _ => by simp at hf
  | g :: outs, fs, hn, ha, f, hf, p, hp => by
    obtain ⟨hg, hn⟩ := List.nodup_cons.mp hn
    have ha' : ∀ f ∈ outs, aside f ∉ outs := fun f hf h => ha f (by simp [hf]) (by simp [h])
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hf with rfl | hf
    · refine foldl_other h1 outs _ p fun f' hf' => ?_
      have hne : f ≠ f' := fun h => hg (h ▸ hf')
      rcases hp with rfl | rfl
      · exact ⟨hne, fun h => ha f' (by simp [hf']) (by simp [← h])⟩
      · exact ⟨fun h => ha f (by simp) (by simp [h, hf']), fun h => hne (aside_inj h)⟩
    · rw [foldl_at h1 h2 outs _ hn ha' f hf p hp]
      have hne : f ≠ g := fun h => hg (h ▸ hf)
      refine h2 _ _ f ?_ ?_ p hp
      · exact h1 fs g f hne fun h => ha g (by simp) (by rw [← h]; exact List.mem_cons_of_mem _ hf)
      · exact h1 fs g (aside f) (fun h => ha f (by simp [hf]) (by simp [h]))
          fun h => hne (aside_inj h)

end Loops

theorem aside_ne (f : Path) : f ≠ aside f := by
  intro h
  have := congrArg String.length h
  simp [aside, String.length_append] at this

omit [DecidableEq V] in
theorem stash_other (fs : Files V) (f p : Path) (h1 : p ≠ f) (h2 : p ≠ aside f) : stash fs f p = fs p := by
  unfold stash
  by_cases ha : (fs f).isSome
  · simp [ha, mvF, h1, h2]
  · by_cases hb : (fs (aside f)).isSome <;> simp [ha, hb, rmF, h2]

omit [DecidableEq V] in
theorem stash_at (fs : Files V) (f : Path) : stash fs f f = none ∧ stash fs f (aside f) = fs f := by
  have hne := aside_ne f
  cases hf : fs f <;> cases hg : fs (aside f) <;> simp [stash, mvF, rmF, hf, hg, hne]

omit [DecidableEq V] in
theorem stash_local (fs fs' : Files V) (f : Path) (h1 : fs f = fs' f) (h2 : fs (aside f) = fs' (aside f))
    (p : Path) (hp : p = f ∨ p = aside f) : stash fs f p = stash fs' f p := by
  rcases hp with rfl | rfl
  · rw [(stash_at fs p).1, (stash_at fs' p).1]
  · rw [(stash_at fs f).2, (stash_at fs' f).2, h1]

theorem ite_app {α β : Type} (c : Prop) [Decidable c] (f g : α → β) (a : α) :
    (if c then f else g) a = if c then f a else g a := by
  split <;> rfl

theorem settle_other (cmp s : Bool) (fs : Files V) (f p : Path) (h1 : p ≠ f) (h2 : p ≠ aside f) :
    settle cmp s fs f p = fs p := by
  have hne := aside_ne f
  cases s <;> simp [settle, ite_app, mvF, rmF, h1, h2, Ne.symm hne]

theorem settle_at (cmp s : Bool) (fs : Files V) (f : Path) :
    settle cmp s fs f (aside f) = none ∧
      settle cmp s fs f f = if !s then fs (aside f) else
        if (fs (aside f)).isSome ∧ cmp = true ∧ (fs f).map (·.1) = (fs (aside f)).map (·.1) then fs (aside f)
        else fs f := by
  have hne := aside_ne f
  cases s <;> cases cmp <;> cases hf : fs f <;> cases hg : fs (aside f) <;>
    simp [settle, ite_app, mvF, rmF, hf, hg, hne, Ne.symm hne]

theorem settle_local (cmp s : Bool) (fs fs' : Files V) (f : Path) (h1 : fs f = fs' f)
    (h2 : fs (aside f) = fs' (aside f)) (p : Path) (hp : p = f ∨ p = aside f) :
    settle cmp s fs f p = settle cmp s fs' f p := by
  rcases hp with rfl | rfl
  · rw [(settle_at cmp s fs p).2, (settle_at cmp s fs' p).2, h1, h2]
  · rw [(settle_at cmp s fs f).1, (settle_at cmp s fs' f).1]

/-! ### What the script does -/

section Script
variable (cmp : Bool) (outs : List Path) (w : Path → Option V) (ok : Bool) (t : Nat) (fs : Files V)

/-- The script exits 0 exactly when the command did and wrote every output. -/
theorem script_status (hn : outs.Nodup) (ha : ∀ f ∈ outs, aside f ∉ outs) :
    (script cmp outs w ok t fs).2 = (ok && outs.all fun f => (w f).isSome) := by
  have h : ∀ f ∈ outs, ((command outs w t (outs.foldl stash fs)) f).isSome = (w f).isSome := by
    intro f hf
    have h1 := foldl_at stash_other stash_local outs fs hn ha f hf f (.inl rfl)
    simp only [command, hf, ite_true]
    cases w f <;> simp [h1, (stash_at fs f).1]
  simp only [script]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun h' f hf => h f hf ▸ h' f hf, fun h' f hf => (h f hf).symm ▸ h' f hf⟩

variable [Inhabited V]

/-- The script's effect on the files, given that no `.mise-old` file of an
output exists beforehand: `wrapRun` with what the command wrote, or with
`none` when the script fails. -/
theorem script_eq (hn : outs.Nodup) (ha : ∀ f ∈ outs, aside f ∉ outs) (hold : ∀ f ∈ outs, fs (aside f) = none) :
    (script cmp outs w ok t fs).1 =
      wrapRun fs outs cmp (if (script cmp outs w ok t fs).2 then some fun p => (w p).getD default else none) t := by
  have hs := script_status cmp outs w ok t fs hn ha
  funext p
  -- The files after the first loop and the command.
  let fs₁ := outs.foldl stash fs
  let fs₂ := command outs w t fs₁
  have h1 : ∀ f ∈ outs, fs₁ f = none ∧ fs₁ (aside f) = fs f := fun f hf =>
    ⟨(foldl_at stash_other stash_local outs fs hn ha f hf f (.inl rfl)).trans (stash_at fs f).1,
     (foldl_at stash_other stash_local outs fs hn ha f hf _ (.inr rfl)).trans (stash_at fs f).2⟩
  have h2 : ∀ f ∈ outs, fs₂ f = (w f).map (·, t) ∧ fs₂ (aside f) = fs f := fun f hf => by
    refine ⟨?_, ?_⟩
    · simp only [fs₂, command, hf, ite_true]
      cases w f <;> simp [(h1 f hf).1]
    · simp only [fs₂, command, ha f hf, ite_false]
      exact (h1 f hf).2
  have hfin : (script cmp outs w ok t fs).1 = outs.foldl (settle cmp (script cmp outs w ok t fs).2) fs₂ := rfl
  rw [hfin]
  generalize hS : (script cmp outs w ok t fs).2 = S at hs
  by_cases hp : ∃ f ∈ outs, p = f ∨ p = aside f
  · obtain ⟨f, hf, hpf⟩ := hp
    rw [foldl_at (settle_other cmp S) (settle_local cmp S) outs fs₂ hn ha f hf p hpf]
    rcases hpf with rfl | rfl
    · rw [(settle_at cmp S fs₂ p).2, (h2 p hf).1, (h2 p hf).2]
      cases S with
      | false => rfl
      | true =>
        have hw : (w p).isSome := by
          have := hs.symm; simp only [Bool.and_eq_true, List.all_eq_true] at this; exact this.2 p hf
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hw
        simp only [wrapRun, List.contains_iff_mem, hf, ite_true, hv, Option.getD_some, ite_true]
        cases hfp : fs p with
        | none => simp
        | some ov =>
          obtain ⟨old, t0⟩ := ov
          by_cases hc : cmp = true
          · by_cases he : old = v
            · simp [hc, he]
            · simp [hc, he, Ne.symm he]
          · simp [hc]
    · rw [(settle_at cmp S fs₂ f).1]
      have : aside f ∉ outs := ha f hf
      cases S <;> simp [wrapRun, this, hold f hf]
  · have hp' : ∀ f ∈ outs, p ≠ f ∧ p ≠ aside f := fun f hf =>
      ⟨fun h => hp ⟨f, hf, .inl h⟩, fun h => hp ⟨f, hf, .inr h⟩⟩
    rw [foldl_other (settle_other cmp S) outs fs₂ p hp']
    have hpo : p ∉ outs := fun h => (hp' p h).1 rfl
    have : fs₂ p = fs p := by
      simp only [fs₂, command, hpo, ite_false]
      exact foldl_other stash_other outs fs p hp'
    cases S <;> simp [wrapRun, hpo, this]

/-- A failed script, because the command failed or left an output missing,
changes no file. -/
theorem script_fail (hn : outs.Nodup) (ha : ∀ f ∈ outs, aside f ∉ outs) (hold : ∀ f ∈ outs, fs (aside f) = none)
    (h : (script cmp outs w ok t fs).2 = false) : (script cmp outs w ok t fs).1 = fs := by
  rw [script_eq cmp outs w ok t fs hn ha hold, h]
  rfl

/-- A successful script writes every output at time `t`, or for a `restat`
rule keeps its old file when the contents are unchanged. Every other file is
unchanged. -/
theorem script_ok (hn : outs.Nodup) (ha : ∀ f ∈ outs, aside f ∉ outs) (hold : ∀ f ∈ outs, fs (aside f) = none)
    (h : (script cmp outs w ok t fs).2 = true) :
    ok = true ∧ (∀ o ∈ outs, ∃ v, w o = some v ∧ ((script cmp outs w ok t fs).1 o = some (v, t) ∨
      cmp = true ∧ (script cmp outs w ok t fs).1 o = fs o ∧ (fs o).map (·.1) = some v)) ∧
      ∀ p ∉ outs, (script cmp outs w ok t fs).1 p = fs p := by
  have hs := (script_status cmp outs w ok t fs hn ha).symm.trans h
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  have he := script_eq cmp outs w ok t fs hn ha hold
  simp only [h, ↓reduceIte] at he
  refine ⟨hs.1, fun o ho => ?_, fun p hp => ?_⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hs.2 o ho)
    refine ⟨v, hv, ?_⟩
    rw [he]
    simp only [wrapRun, List.contains_iff_mem, ho, ite_true, hv, Option.getD_some]
    cases hfo : fs o with
    | none => simp
    | some ov =>
      obtain ⟨old, t0⟩ := ov
      by_cases hc : cmp = true ∧ old = v
      · exact .inr ⟨hc.1, by simp [hc.1, hc.2], by simp [hc.2]⟩
      · exact .inl (by simp only [hc, ite_false])
  · rw [he]; simp [wrapRun, hp]

end Script

/-! ## Ninja running an edge through the wrapper -/

section Run
variable [Inhabited V]

/-- Ninja runs edge `e` through the wrapper at the next time step, where the
command leaves `w` at the outputs and exits 0 when `ok`. The files are what
the script leaves. Ninja writes the log and deps entries only when the
script exits 0.
Gloss: the state after {e} runs wrapped in {st}, writing {w} and exiting 0 when {ok} -/
def St.runWrapped (sem : Sem V) (st : St V) (e : MEdge) (w : Path → Option V) (ok : Bool) : St V :=
  let r := script e.restat e.outs w ok (st.clock + 1) st.fs
  if r.2 then { st.run sem e with fs := r.1 } else { st with fs := r.1 }

variable (sem : Sem V) (st : St V) (e : MEdge) (w : Path → Option V) (ok : Bool)

/-- A wrapped run whose command fails or leaves an output missing leaves
the state as it was. -/
theorem runWrapped_fail (hn : e.outs.Nodup) (ha : ∀ o ∈ e.outs, aside o ∉ e.outs)
    (hold : ∀ o ∈ e.outs, st.fs (aside o) = none) (hf : ok = false ∨ ∃ o ∈ e.outs, w o = none) :
    st.runWrapped sem e w ok = st := by
  have hs : (script e.restat e.outs w ok (st.clock + 1) st.fs).2 = false := by
    rw [script_status _ _ _ _ _ _ hn ha]
    rcases hf with h | ⟨o, ho, h⟩
    · simp [h]
    · simp only [Bool.and_eq_false_iff, List.all_eq_false]
      exact .inr ⟨o, ho, by simp [h]⟩
  have hfs := script_fail e.restat e.outs w ok (st.clock + 1) st.fs hn ha hold hs
  simp only [St.runWrapped, hs, hfs]
  rfl

/-- A wrapped run whose command exits 0 and writes what `sem` says is the
model's run under `Sem.withCmp`. -/
theorem runWrapped_ok (hn : e.outs.Nodup) (ha : ∀ o ∈ e.outs, aside o ∉ e.outs)
    (hold : ∀ o ∈ e.outs, st.fs (aside o) = none) (hok : ok = true)
    (hw : ∀ o ∈ e.outs, w o = some (st.outVal sem e o)) :
    st.runWrapped sem e w ok = st.run sem.withCmp e := by
  have hs : (script e.restat e.outs w ok (st.clock + 1) st.fs).2 = true := by
    rw [script_status _ _ _ _ _ _ hn ha, hok]
    simp only [Bool.true_and, List.all_eq_true]
    exact fun o ho => by simp [hw o ho]
  have hfs : (script e.restat e.outs w ok (st.clock + 1) st.fs).1 = (st.run sem.withCmp e).fs := by
    rw [script_eq _ _ _ _ _ _ hn ha hold, hs, run_withCmp]
    exact wrapRun_congr _ _ _ (fun o ho => by simp [hw o ho]) _
  simp only [St.runWrapped, hs, hfs, ↓reduceIte]
  rfl

/-- Either way, a wrapped run of a dirty edge keeps the state reachable: a
failure leaves it as it was, and a success is a step of the model. -/
theorem reach_runWrapped {es : List MEdge} (h : Reach sem.withCmp es st) (he : e ∈ es)
    (hd : st.dirty e = true) (hn : e.outs.Nodup) (ha : ∀ o ∈ e.outs, aside o ∉ e.outs)
    (hold : ∀ o ∈ e.outs, st.fs (aside o) = none)
    (hw : ∀ o ∈ e.outs, ∀ v, w o = some v → v = st.outVal sem e o) :
    Reach sem.withCmp es (st.runWrapped sem e w ok) := by
  by_cases hf : ok = false ∨ ∃ o ∈ e.outs, w o = none
  · rw [runWrapped_fail sem st e w ok hn ha hold hf]
    exact h
  · simp only [not_or, Bool.not_eq_false, not_exists, not_and] at hf
    have hw' : ∀ o ∈ e.outs, w o = some (st.outVal sem e o) := fun o ho => by
      cases hwo : w o with
      | none => exact absurd hwo (hf.2 o ho)
      | some v => rw [hw o ho v hwo]
    rw [runWrapped_ok sem st e w ok hn ha hold hf.1 hw']
    have := Reach.step h he
    simp only [St.step, hd, ↓reduceIte] at this
    exact this

end Run

theorem nodup_of_nodupB : ∀ {l : List String}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupB_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact List.nodup_cons.mpr ⟨by simpa using h.1, nodup_of_nodupB h.2⟩

/-- An emitted edge's outputs are distinct. -/
theorem outs_nodup_emit {g : Graph} (hg : g.Valid) {e : MEdge} (he : e ∈ (emit g).medges) : e.outs.Nodup := by
  rw [medges_emit g hg, List.mem_map] at he
  obtain ⟨e', he', rfl⟩ := he
  obtain ⟨i, hi⟩ := List.getElem?_of_mem he'
  obtain ⟨-, -, -, h4, -⟩ := GEdge.ok_parts (edgesOK_get (Graph.check_parts hg).2.2.1 hi)
  exact nodup_of_nodupB h4

end Mise.Model
