import MiseTest.Reachable
import Mise.Syntax.Print

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

/-- A failed wrapped run leaves the state as it was: the old output is
back, no `.mise-old` file is left, and Ninja writes no log entry and the
clock does not move. This is the first half of `wrapped_run`. -/
example : (edited.runWrapped sem cc w false).fs "main.o" = edited.fs "main.o" ∧
    (edited.runWrapped sem cc w false).fs (aside "main.o") = none ∧
    (edited.runWrapped sem cc w false).log "main.o" = edited.log "main.o" ∧
    (edited.runWrapped sem cc w false).clock = edited.clock := by decide

/-- `g` after a full build under `cmp`: `main.o` holds `compiled v1`. -/
def built : St String := build sem.withCmp g start

/-- A command without `restat` that writes the same contents again still
gives its output the next tick as mtime: the wrapper keeps the new file,
and compares with `cmp` only for a `restat` rule. -/
example : (built.runWrapped sem cc (fun _ => some "compiled v1") true).fs "main.o" =
    some ("compiled v1", built.clock + 1) := by decide

/-- Only a `restat` edge leaves an unchanged output untouched (`kept`). -/
example : built.kept sem.withCmp cc "main.o" = false ∧
    built.kept sem.withCmp { cc with restat := true } "main.o" = true := by decide

/-! ## A command with two outputs -/

/-- The first output holds `1 ` and the second `2 ` before each input's
contents. -/
def twoOut : Sem String :=
  { exec := fun _ ins => ins.map ("1 " ++ ·) ++ ins.map ("2 " ++ ·), dyn := fun _ => .pure [] }

/-- One edge that writes `a` and `b` from `x`. -/
def pair : MEdge := { outs := ["a", "b"], ins := ["x"], cmd := "gen x" }

/-- `x` holds `v`, written at time 0, and nothing else exists. -/
def pairStart : St String :=
  { fs := fun p => if p = "x" then some ("v", 0) else none, log := fun _ => none, clock := 0 }

/-- Each output gets its own value from the command (`cmdTask`, `outVal`). -/
example : pairStart.outVal twoOut pair "a" = "1 v" ∧ pairStart.outVal twoOut pair "b" = "2 v" := by decide

/-- A wrapped run writes every output, not only the first. -/
example : (pairStart.runWrapped twoOut pair (fun o => some (pairStart.outVal twoOut pair o)) true).fs "b" =
    some ("2 v", 1) := by decide

/-! ## Top-level variables in a rule -/

-- A rule reads top-level variables: `cflags` in its command and `d` in
-- `deps`. The model evaluates both in the final file scope, as Ninja does,
-- including bindings older than the newest one.
#guard Manifest.medges ⟨[.binding "d" [.lit "gcc"], .binding "cflags" [.lit "-O2"], .binding "x" [.lit "1"],
    .rule { name := "cc", bindings := [("command", [.lit "cc ", .var "cflags"]), ("deps", [.var "d"])] },
    .edge { outs := ["a.o"], rule := "cc" }]⟩ ==
  [{ outs := ["a.o"], ins := [], oo := [], cmd := "cc -O2", dyn := true, restat := false }]

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

/-- The sources of `two` hold their own names, written at time 0. -/
def start2 : St String :=
  { fs := fun p => if p ∈ two.sources then some (p, 0) else none, log := fun _ => none, clock := 0 }

theorem start2_fresh : start2.Fresh :=
  ⟨fun p v t h => by simp [start2] at h ⊢; omega, fun _ _ _ h => nomatch h⟩

/-! ### `Graph.spec` on a depfile edge (conclusion of `build_correct`) -/

/-- The specification of `a.o` is the depfile command: it reads `a.c`,
`util.h` and the generated `config.h`. If `Graph.spec` treated it as a
static command, it would read `a.c` alone, and `build_correct` would accept
a build that ignored the headers. -/
example : ((two.spec depSem).task "a.o").run (build depSem two start2).content = "a.cutil.hconfig.in" := by
  decide

/-! ### `ran` and `Checks` on more than one edge -/

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

/-! ## The printer (trust item 1)

Trust item 1 says that Ninja reads `print m` as `m` when `m.WellFormed`, so
a printer that writes the wrong text breaks it without breaking a theorem. -/

/-- A manifest that uses each case of the printer: escapes in paths and
values, a leading space, an empty value, a value that starts with a
variable, empty and non-empty `|` and `||` sections. -/
def pm : Manifest := ⟨[
  .binding "x" [.lit " a$b", .var "v", .lit "c"],
  .binding "v" [.var "x", .lit "$"],
  .rule ⟨"cc", [("command", [.lit "cc ", .var "in"]), ("depfile", [.var "out", .lit ".d"])]⟩,
  .edge { outs := ["a b.o"], implicitOuts := ["x:y"], rule := "cc", ins := ["s$.c"],
          implicitIns := ["h"], orderOnly := ["gen"],
          bindings := [("flags", [.lit " -O2"]), ("empty", [])] },
  .edge { outs := ["gen"], rule := "phony" },
  .default ["a b.o"]
]⟩

/-- Trust item 1 applies to `pm`. -/
example : pm.WellFormed := by decide

set_option maxRecDepth 8000 in
/-- The text of `pm`, written by hand. -/
example : print pm = "# Generated by mise. Do not edit.
x = $ a$$b${v}c
v = ${x}$$
rule cc
  command = cc ${in}
  depfile = ${out}.d

build a$ b.o | x$:y: cc s$$.c | h || gen
  flags = $ -O2
  empty = \n\
build gen: phony
default a$ b.o
" := by decide

/-! ## Tests that kill generated mutants

`test/trust-mutants.py` generates mutants of the trusted definitions, and
its triage turns each survivor into a test on an input where the mutant and
the definition differ. These are a smallest set of those tests that kills
every such survivor, each checked by hand against the behaviour it pins.
Many inputs use the empty string, which the generator draws first. -/

/-! ### Well-formed manifests (`Manifest.WellFormed`, trust item 1) -/

#guard !(Stmt.ok { rules := ["a"] }
  (Stmt.rule { name := "a", bindings := [("command", [Seg.var "a"])] }))

#guard !(Stmt.ok { } (Stmt.rule { name := "a", bindings := [("command", [])] }))

#guard !(Stmt.ok { } (Stmt.binding "rule" []))

#guard !(Stmt.ok { } (Stmt.binding "a" [Seg.lit "a", Seg.lit ""]))

#guard !(Stmt.ok { rules := ["a"] } (Stmt.edge { outs := ["a"], implicitOuts := ["a"], rule := "a" }))

#guard !(Stmt.ok { } (Stmt.rule { name := "", bindings := [("command", [Seg.lit "a"])] }))

#guard !(Stmt.ok { } (Stmt.rule { name := "a", bindings := [("command", [Seg.lit ""])] }))

#guard !(Stmt.ok { }
  (Stmt.rule { name := "a", bindings := [("a", []), ("command", [Seg.var "a"])] }))

#guard !(Stmt.ok { } (Stmt.binding "" []))

#guard !(Stmt.ok { rules := [""] } (Stmt.edge { outs := ["a"], rule := "" }))

#guard !(Stmt.ok { } (Stmt.edge { outs := ["a"], rule := "a" }))

#guard !(Stmt.ok { rules := ["a"] } (Stmt.edge { outs := [], rule := "a" }))

#guard !(Stmt.ok { rules := ["a"] } (Stmt.edge { outs := [""], rule := "a" }))

#guard !(Stmt.ok { outs := ["phony"] } (Stmt.edge { outs := ["phony"], rule := "phony" }))

#guard !(Stmt.ok { } (Stmt.edge { outs := ["a"], rule := "phony", bindings := [("", [])] }))

#guard !(Stmt.ok { rules := ["a"] }
  (Stmt.edge { outs := ["a"], rule := "a", bindings := [("pool", [])] }))

#guard !(Stmt.ok { } (Stmt.edge { outs := ["phony"], rule := "phony", ins := ["phony"] }))

#guard !(Stmt.ok { } (Stmt.default []))

#guard !(Stmt.ok { known := [""] } (Stmt.default [""]))

#guard !(Stmt.ok { } (Stmt.binding "dyndep" []))

#guard !(canonical [])

#guard !(canonical ['.', '.'])

#guard canonical ['/', '.', 'a']

#guard canonical ['.', 'a']

#guard !(canonical ['/', '.'])

#guard !(litChar '\x0d')

#guard !(noAdjLits [Seg.var "", Seg.lit "", Seg.lit ""])

#guard !(nodupB ["", "a", "a"])

#guard !(pathChar '\x00')

#guard !(validBinding ("a", [Seg.var "a", Seg.var ""]))

#guard !(validEval [Seg.lit "a", Seg.lit "a"])

#guard !(validIdent ",")

#guard !(validLit "\n")

#guard !(validPath "a/")

/-! ### The printer -/

#guard edgeLine { outs := [], implicitOuts := ["", ""], rule := "" } == ['b', 'u', 'i', 'l', 'd', ' ', '|', ' ', ' ', ':', ' ']

/-! ### Variable evaluation and `Manifest.medges` -/

-- An acyclic chain of rule bindings evaluates to the end. Fuel of the
-- binding count, one less than `EdgeInfo.binding` gives, is enough for any
-- acyclic rule, so no test pins the extra unit: the two differ only on a
-- cyclic rule, which Ninja rejects. Its mutant is a known survivor.
#guard EdgeInfo.binding []
  { edge := { outs := [], rule := "" },
    rule := { name := "cc", bindings := [("command", [Seg.var "depfile"]), ("depfile", [Seg.lit "a"])] },
    own := none }
  "command" == "a"

#guard Ctx.outs (Ctx.add { } (Stmt.edge { outs := [""], rule := "" })) == [""]

#guard Ctx.outs (Ctx.add { outs := [""] } (Stmt.edge { outs := [], rule := "" })) == [""]

#guard Edge.allPaths { outs := [], rule := "", implicitIns := [""], orderOnly := [""] } == ["", ""]

#guard EdgeInfo.command [("", ""), ("command", "a")]
  { edge := { outs := [], rule := "" }, rule := { name := "", bindings := [] }, own := some [] } == "a"

#guard EdgeInfo.isDyn [("", ""), ("deps", "a")]
  { edge := { outs := [], rule := "" }, rule := { name := "", bindings := [] }, own := none }

#guard EdgeInfo.lookup []
  { edge := { outs := [], rule := "" }, rule := { name := "", bindings := [] }, own := some [] } 0 "in_newline" == ""

#guard EdgeInfo.lookup []
  { edge := { outs := [], rule := "", ins := ["", ""] }, rule := { name := "", bindings := [] }, own := some [] } 0
  "in_newline" == "\n"

#guard EdgeInfo.lookup []
  { edge := { outs := ["", ""], rule := "" }, rule := { name := "", bindings := [] }, own := none } 0 "out" == " "

#guard EdgeInfo.lookup [("a", ""), (",", "a")]
  { edge := { outs := [], rule := "" }, rule := { name := "", bindings := [("", [Seg.var ","])] },
    own := none }
  1 "" == "a"

#guard Elab.file
  (Elab.step { file := [("", ""), ("a", "a")] } (Stmt.binding "" [Seg.var "a"])) == [("", "a"), ("", ""), ("a", "a")]

#guard Elab.file
  (Elab.step { } (Stmt.binding "" [Seg.var "", Seg.lit "a"])) == [("", "a")]

#guard (Elab.step { file := [("", ""), ("a", "a")] }
  (.edge { outs := [], rule := "", bindings := [("", [.var "a"])] })).edges[0]!.own == some [("", "a")]

#guard Manifest.medges
  {
    stmts :=
      [Stmt.binding "restat" [Seg.lit "a"], Stmt.edge { outs := [], rule := "" },
        Stmt.binding "" []] } == [{ outs := [], ins := [], oo := [], cmd := "", dyn := false, restat := true }]

#guard EdgeInfo.own (edgeInfo [] [] { outs := [], rule := "" }) == none

#guard EdgeInfo.own (edgeInfo [] [] { outs := [], rule := "", bindings := [("", []), ("", [])] }) == some [("", ""), ("", "")]

#guard EdgeInfo.own
  (edgeInfo [] []
    { outs := [], rule := "", bindings := [("", [Seg.lit "", Seg.lit "a"])] }) == some [("", "a")]

#guard shellSafe '_'

#guard shellSafe '+'

/-! ### DSL graphs -/

#guard GEdge.allIns { rule := "", outs := [], implicitIns := [""] } == [""]

#guard GEdge.allIns { rule := "", outs := [], ins := [""] } == [""]

#guard GEdge.allOuts { rule := "", outs := [""], implicitOuts := [""] } == ["", ""]

#guard GEdge.look { rule := "", outs := ["", ""] } "out" == " "

#guard !(Graph.isDyn { } { rule := "", outs := [] })

#guard findOut (fun (a : Nat) => if a = 2 then [""] else []) "" [0, 0, 2] == some (2, 2)

/-! ### The model's state and edges -/

#guard MEdge.reads { outs := [], ins := [""], oo := [""], cmd := "" } == ["", ""]

#guard St.fs
  (St.edits
    { fs := fun (_ : Path) => none, log := fun (_ : Path) => none, clock := 0 }
    [("", 0), ("", 0)])
  "" == some (0, 2)

#guard !(St.outDirty (V := Nat)
  { fs := fun (_ : Path) => some (0, 0), log := fun (_ : Path) => some ("", 0), clock := 0 }
  { outs := [], ins := [], cmd := "" } "")

#guard St.outDirty (V := Nat)
  { fs := fun (_ : Path) => some (0, 0), log := fun (_ : Path) => some ("", 0), clock := 0 }
  { outs := [], ins := [], cmd := "a" } ""

#guard St.outDirty (V := Nat)
  { fs := fun (a : Path) => if a = "" then some (0, 1) else some (0, 0),
    log := fun (_ : Path) => some ("", 1), clock := 0 }
  { outs := [], ins := ["a", ""], cmd := "" } "a"

#guard command [] (fun (_ : Path) => some 0) 0 (fun (_ : Path) => none) "" == none

/-! ### The command wrapper (`script`, `wrapped_run`) -/

#guard aside "a" == "a.mise-old"

#guard mvF "" "" (fun (_ : Path) => some (0, 0)) "a" == some (0, 0)

#guard !(Prod.snd (α := Files Nat)
  (script true [""] (fun (_ : Path) => none) true 0 fun (_ : Path) => some (0, 0)))

#guard Prod.fst
  (script false [""] (fun (_ : Path) => some 2) true 1 fun (_ : Path) => some (2, 0))
  "" == some (2, 1)

#guard Prod.fst
  (script true ["", "a"] (fun (_ : Path) => some 0) true 0 fun (_ : Path) => none) "" == some (0, 0)

#guard !(Prod.snd (α := Files Nat)
  (script false [] (fun (_ : Path) => none) false 0 fun (_ : Path) => none))

#guard settle true true (fun (a : Path) => if a = ".mise-old" then some (0, 0) else none) "" ".mise-old" == none

#guard settle true false (fun (_ : Path) => some (0, 0)) "" "" == some (0, 0)

#guard settle true true (fun (a : Path) => if a = "" then some (2, 1) else some (2, 0)) "" "" == some (2, 0)

#guard settle false false (fun (a : Path) => if a = "" then some (0, 0) else none) "" "" == none

#guard settle true true (fun (a : Path) => if a = "" then none else some (0, 0)) "" "" == none

#guard stash (fun (a : Path) => if a = "" then none else some (0, 0)) "" ".mise-old" == none

end MiseTest.Boundary
