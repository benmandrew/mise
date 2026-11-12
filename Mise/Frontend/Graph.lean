import Mise.Spec.Basic
import Mise.Frontend.Eval

/-!
# Stage 4: build graphs, their meaning, and their Ninja form

A `Graph` is what the DSL builds: declared sources, rules, and edges in the
order they were added. `Graph.check` is the condition the builder enforces.
`Graph.spec` is the meaning of a graph read straight from the DSL, `emit`
writes it as a Ninja manifest, and `denote` reads a manifest back as a build
specification through the Ninja evaluation model.

Command semantics are abstract and collected in `Sem`. A static command
`cmd` writes `exec cmd vs` when its inputs hold `vs`, one value per output. A
command whose rule has a depfile (Stage 6) is a task `dyn cmd`: it fetches
what it reads and returns its outputs.
-/

namespace Mise.Frontend
open Mise.Syntax

/-- The oldest Ninja release `mise` supports. `emit` writes it first in every
manifest as the top-level binding `ninja_required_version`, which makes older
releases refuse the manifest. -/
def ninjaMinVersion : String := "1.12.1"

/-- The top-level binding Ninja checks its own version against. -/
def versionVar : String := "ninja_required_version"

/-- Names a template or an edge may not use as a variable of its own. Edge
bindings with these names would change what Ninja runs, and a template
reference to `versionVar` would read the emitted top-level binding. -/
def reserved : List String := ["in", "out", "in_newline", versionVar] ++ ruleKeys

/-- A rule. The command and description are Ninja values; `${in}` and
`${out}` stand for the edge's explicit inputs and outputs, and any other
variable is bound by the edge. An empty description is not emitted. -/
structure GRule where
  name : String
  command : EvalString
  description : EvalString := []
  /-- Emit `depfile = ${out}.d` and `deps = gcc`: the command writes a
  Makefile-style depfile listing what it read. -/
  depfile : Bool := false
  /-- Emit `restat = 1`: the command may leave an output untouched when its
  contents would not change, and Ninja then skips dependents on its account. -/
  restat : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- An edge in the DSL: the name of its rule, explicit and implicit outputs,
explicit, implicit and order-only inputs, and the edge's own variables
with their literal values. -/
structure GEdge where
  rule : String
  outs : List Path
  implicitOuts : List Path := []
  ins : List Path := []
  implicitIns : List Path := []
  orderOnly : List Path := []
  vars : List (String × String) := []
  deriving DecidableEq, Repr, Inhabited

namespace GEdge

/-- Explicit then implicit outputs. -/
def allOuts (e : GEdge) : List Path := e.outs ++ e.implicitOuts
/-- The inputs the command reads: explicit and implicit. -/
def inputs (e : GEdge) : List Path := e.ins ++ e.implicitIns
/-- Explicit, implicit and order-only inputs. -/
def allIns (e : GEdge) : List Path := e.ins ++ e.implicitIns ++ e.orderOnly

/-- The value of a variable in this edge's command, as the DSL defines it. -/
def look (e : GEdge) (v : String) : String :=
  if v = "in" then shellList " " e.ins
  else if v = "out" then shellList " " e.outs
  else ((e.vars.find? (·.1 == v)).map (·.2)).getD ""

end GEdge

/-- A build as the DSL describes it: declared sources, rules, edges in the
order they were added, and default targets.
Gloss: build graphs -/
structure Graph where
  sources : List Path := []
  rules : List GRule := []
  edges : List GEdge := []
  defaults : List Path := []
  deriving Repr, Inhabited

/-! ## Validity -/

/-- Every variable the template refers to is `in`, `out`, or a name outside
`reserved`. -/
def tmplVarsOK (t : EvalString) : Bool :=
  t.all fun
    | .var n => n == "in" || n == "out" || !reserved.contains n
    | .lit _ => true

/-- A rule `mise` can emit: the name is an identifier other than `phony`, the
command is a valid nonempty value whose only reserved variables are `in`
and `out`, and the description is a valid value. -/
def GRule.ok (r : GRule) : Bool :=
  validIdent r.name && r.name != "phony" && validEval r.command && !r.command.isEmpty &&
    tmplVarsOK r.command && validEval r.description

/-- Edge variables `mise` can emit: no name occurs twice, every name is an
identifier outside `reserved`, and no value contains a newline, carriage
return or NUL. -/
def varsOK (vs : List (String × String)) : Bool :=
  nodupB (vs.map (·.1)) && vs.all fun b => validIdent b.1 && !reserved.contains b.1 && b.2.toList.all litChar

/-- An edge is acceptable after the edges whose outputs are `prev`. -/
def GEdge.ok (names : List String) (srcs prev : List Path) (e : GEdge) : Bool :=
  names.contains e.rule && !e.outs.isEmpty && (e.allOuts ++ e.allIns).all validPath &&
    nodupB e.allOuts && e.allOuts.all (fun o => !prev.contains o && !srcs.contains o) &&
    e.allIns.all (fun i => srcs.contains i || prev.contains i) && varsOK e.vars

/-- Each edge is acceptable (`GEdge.ok`) after the ones before it. The list
of paths holds the outputs of the edges already checked. -/
def edgesOK (names : List String) (srcs : List Path) : List Path → List GEdge → Bool
  | _, [] => true
  | prev, e :: es => e.ok names srcs prev && edgesOK names srcs (prev ++ e.allOuts) es

/-- The names of the graph's rules, in order. -/
def Graph.ruleNames (g : Graph) : List String := g.rules.map (·.name)

/-- An edge whose rule has a depfile has one explicit output. The depfile
is `${out}.d`, which names one file only for one output; with more, Ninja
finds no depfile, treats it as empty and records no deps. -/
def depfileOutsOK (rules : List GRule) (e : GEdge) : Bool :=
  match rules.find? (·.name == e.rule) with
  | some r => !r.depfile || e.outs.length == 1
  | none => true

/-- The validity check: rule names are distinct, every rule is acceptable
(`GRule.ok`), every edge is acceptable after the ones before it
(`edgesOK`), every default target is an output of some edge, and every
edge whose rule has a depfile has one explicit output
(`depfileOutsOK`). -/
def Graph.check (g : Graph) : Bool :=
  nodupB g.ruleNames && g.rules.all GRule.ok && edgesOK g.ruleNames g.sources [] g.edges &&
    (g.defaults.all fun d => g.edges.any (·.allOuts.contains d)) && g.edges.all (depfileOutsOK g.rules)

/-- Every input is a declared source or an output of an earlier edge, every
output has one producer, every name and path can be written in Ninja, and
every depfile edge has one explicit output.
Gloss: {g} is valid -/
def Graph.Valid (g : Graph) : Prop := g.check = true

instance (g : Graph) : Decidable g.Valid := inferInstanceAs (Decidable (_ = _))

/-! ## Meaning -/

/-- The first element whose outputs contain `k`, with its index. -/
def findOut {α : Type} (outs : α → List Path) (k : Path) : List α → Option (Nat × α)
  | [] => none
  | a :: as => if (outs a).contains k then some (0, a) else (findOut outs k as).map fun p => (p.1 + 1, p.2)

/-- Fetch keys in order. -/
def fetchAll {K V : Type} : List K → Task K V (List V)
  | [] => .pure []
  | k :: ks => .fetch k fun v => (fetchAll ks).bind fun vs => .pure (v :: vs)

/-- What commands mean.
Gloss: command meanings over {V} -/
structure Sem (V : Type) where
  /-- A static command's outputs from its inputs' contents. -/
  exec : String → List V → List V
  /-- A depfile command: what it reads, and its outputs. -/
  dyn : String → Task Path V (List V)
  /-- Stage 7: when a `restat` command would write `new` over `old`, it may
  leave the file untouched when `keep old new` holds. -/
  keep : V → V → Bool := fun _ _ => false
  /-- The assumption behind early cutoff: a command leaves a file untouched
  only when its new contents would be identical. -/
  keep_eq : ∀ a b, keep a b = true → a = b := by intro a b h; simp at h

/-- The semantics of a build whose `restat` commands go through the DSL's
command wrapper (`wrapCommand`), which compares with `cmp`: an output is
left untouched exactly when its contents are equal, so `keep_eq` holds by
construction. -/
def Sem.withCmp {V : Type} [DecidableEq V] (sem : Sem V) : Sem V :=
  { sem with keep := fun a b => decide (a = b), keep_eq := fun _ _ h => of_decide_eq_true h }

/-- A command as a task returning all its outputs. A static command fetches
its explicit and implicit inputs in order. -/
def cmdTask {V : Type} (sem : Sem V) (dyn : Bool) (cmd : String) (ins : List Path) : Task Path V (List V) :=
  if dyn then sem.dyn cmd else (fetchAll ins).bind fun vs => .pure (sem.exec cmd vs)

/-- Output `i` of a command. -/
def outTask {V : Type} [Inhabited V] (t : Task Path V (List V)) (i : Nat) : Task Path V V :=
  t.bind fun vs => .pure (vs.getD i default)

/-- The first rule whose name is the edge's rule name. -/
def Graph.ruleOf (g : Graph) (e : GEdge) : Option GRule := g.rules.find? (·.name == e.rule)

/-- The command the DSL means for an edge. -/
def Graph.cmd (g : Graph) (e : GEdge) : String :=
  match g.ruleOf e with
  | some r => evalWith e.look r.command
  | none => ""

/-- Whether an edge's rule has a depfile. -/
def Graph.isDyn (g : Graph) (e : GEdge) : Bool :=
  match g.ruleOf e with
  | some r => r.depfile
  | none => false

/-- Whether an edge's rule has `restat`. -/
def Graph.isRestat (g : Graph) (e : GEdge) : Bool :=
  match g.ruleOf e with
  | some r => r.restat
  | none => false

/-- Paths no edge produces. -/
def Graph.isSource (g : Graph) (k : Path) : Bool := (findOut GEdge.allOuts k g.edges).isNone

variable {V : Type} [Inhabited V]

/-- The meaning of a graph, straight from the DSL.
Gloss: the build specification {g} describes -/
def Graph.spec (sem : Sem V) (g : Graph) : BuildSpec Path V where
  isSource := g.isSource
  task k := match findOut GEdge.allOuts k g.edges with
    | some (_, e) => outTask (cmdTask sem (g.isDyn e) (g.cmd e) e.inputs) (e.allOuts.idxOf k)
    | none => .pure default

/-- The static-ancestor condition (Stage 6): every depfile command reads
only sources and the edge's own inputs, order-only inputs included.
Gloss: every depfile command of {g} reads only sources and its edge's inputs -/
def Graph.DynOK (sem : Sem V) (g : Graph) : Prop :=
  ∀ e ∈ g.edges, g.isDyn e = true → (sem.dyn (g.cmd e)).FetchesOnly fun k => g.isSource k = true ∨ k ∈ e.allIns

/-! ## Ninja form -/

/-- What a rule with a depfile adds: `depfile = ${out}.d` and `deps = gcc`. -/
def depfileBindings : List Binding := [("depfile", [.var "out", .lit ".d"]), ("deps", [.lit "gcc"])]

/-- What a rule with `restat` adds: `restat = 1`. -/
def restatBindings : List Binding := [("restat", [.lit "1"])]

/-- A DSL rule as a Ninja rule: `command`, then `description` when it is
nonempty, then the depfile and `restat` bindings when the rule asks for
them. -/
def emitRule (r : GRule) : Rule :=
  ⟨r.name, [("command", r.command)] ++ (if r.description.isEmpty then [] else [("description", r.description)]) ++
    (if r.depfile then depfileBindings else []) ++ (if r.restat then restatBindings else [])⟩

/-- A string as a value of literal text. The empty string is the empty value. -/
def litVal (s : String) : EvalString := if s.toList.isEmpty then [] else [.lit s]

/-- A DSL edge as a Ninja edge with the same paths and rule. Each edge
variable becomes a binding to its literal value. -/
def emitEdge (e : GEdge) : Edge :=
  { outs := e.outs, implicitOuts := e.implicitOuts, rule := e.rule, ins := e.ins,
    implicitIns := e.implicitIns, orderOnly := e.orderOnly,
    bindings := e.vars.map fun b => (b.1, litVal b.2) }

/-- The first statement of every emitted manifest. -/
def versionStmt : Stmt := .binding versionVar [.lit ninjaMinVersion]

/-- The manifest `mise` writes for a graph: the version statement
(`versionStmt`), the rules, then the edges in order, then a `default`
statement if the graph has default targets.
Gloss: the manifest `mise` emits for {g} -/
def emit (g : Graph) : Manifest :=
  ⟨versionStmt :: (g.rules.map (Stmt.rule ∘ emitRule) ++ g.edges.map (Stmt.edge ∘ emitEdge) ++
    (if g.defaults.isEmpty then [] else [.default g.defaults]))⟩

/-- The meaning of a manifest under the Ninja evaluation model: each output
is computed by its edge's evaluated command, which is static or reads a
depfile according to the edge's `deps` binding. Paths no edge produces are
sources.
Gloss: the meaning of {m} under the Ninja evaluation model -/
def denote (sem : Sem V) (m : Manifest) : BuildSpec Path V where
  isSource k := (findOut (·.edge.allOuts) k m.elab.edges).isNone
  task k := match findOut (·.edge.allOuts) k m.elab.edges with
    | some (_, c) => outTask (cmdTask sem (c.isDyn m.elab.file) (c.command m.elab.file)
        (c.edge.ins ++ c.edge.implicitIns)) (c.edge.allOuts.idxOf k)
    | none => .pure default

end Mise.Frontend
