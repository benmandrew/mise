import Mise.Frontend.Emit
import Mise.Syntax.Print
import Mise.Syntax.Parse

/-!
# Stage 4: the build DSL

A build description is a `Build` action. `source` declares a source file,
`rule` declares a rule, and `edge` adds an edge and returns handles to its
outputs. A `Handle` can only be made by `source` or `edge`, so every input
names a declared source or an output of an earlier edge.

`Build.graph` runs the description and then decides `Graph.Valid`, so a
`ValidGraph` always emits a well-formed, acyclic manifest whose meaning is
`Graph.spec` (`emit_wellFormed`, `emitAcyclic`, `denote_emit`). The checks
inside `source` and `edge` only give earlier, clearer error messages.

Commands and descriptions are written in Ninja syntax: `$in`, `$out`,
`${name}` for an edge variable, and `$$` for a dollar sign.
-/

namespace Mise.Frontend
open Mise.Syntax

/-- A file the build knows about. Only the builder can make one. -/
structure Handle where
  private mk ::
  path : Path
  deriving Repr, BEq, Inhabited

/-- A declared rule. Only the builder can make one. -/
structure RuleRef where
  private mk ::
  name : String
  deriving Repr, Inhabited

abbrev Build := StateT Graph (Except String)

abbrev ValidGraph := { g : Graph // g.Valid }

private def known (g : Graph) (p : Path) : Bool :=
  g.sources.contains p || g.edges.any (·.allOuts.contains p)

private def require (b : Bool) (msg : String) : Build Unit :=
  if b then pure () else throw msg

/-- Declare a source file. -/
def source (p : Path) : Build Handle := do
  let g ← get
  require (validPath p) s!"source {repr p}: not a valid canonical path"
  require (!known g p) s!"source {repr p}: already declared"
  set { g with sources := g.sources ++ [p] }
  pure ⟨p⟩

def sources (ps : List Path) : Build (List Handle) := ps.mapM source

/-- Parse a Ninja value. -/
def parseValue (what s : String) : Build EvalString :=
  match readValue s.toList with
  | some e => pure e
  | none => throw s!"{what}: cannot parse {repr s} as a Ninja value"

/-- Declare a rule. -/
def rule (name command : String) (description : String := "") : Build RuleRef := do
  let cmd ← parseValue s!"rule {name}: command" command
  let desc ← parseValue s!"rule {name}: description" description
  let r : GRule := { name, command := cmd, description := desc }
  let g ← get
  require r.ok s!"rule {name}: invalid name, empty command, or a reserved variable in the command"
  require (!g.ruleNames.contains name) s!"rule {name}: already declared"
  set { g with rules := g.rules ++ [r] }
  pure ⟨name⟩

/-- Add an edge. Returns handles to the explicit outputs, then the implicit
outputs. -/
def edge (r : RuleRef) (outs : List Path) (ins : List Handle := []) (implicitIns : List Handle := [])
    (orderOnly : List Handle := []) (implicitOuts : List Path := [])
    (vars : List (String × String) := []) : Build (List Handle) := do
  let e : GEdge := { rule := r.name, outs, implicitOuts, ins := ins.map (·.path),
                     implicitIns := implicitIns.map (·.path), orderOnly := orderOnly.map (·.path), vars }
  let g ← get
  for o in e.allOuts do
    require (validPath o) s!"edge {repr outs}: output {repr o} is not a valid canonical path"
    require (!known g o) s!"edge {repr outs}: output {repr o} is already declared"
  require (e.ok g.ruleNames g.sources (g.edges.flatMap GEdge.allOuts))
    s!"edge {repr outs}: no outputs, a repeated output, or an invalid variable"
  set { g with edges := g.edges ++ [e] }
  pure (e.allOuts.map (⟨·⟩))

/-- Add an edge with one output. -/
def edge1 (r : RuleRef) (out : Path) (ins : List Handle := []) (implicitIns : List Handle := [])
    (orderOnly : List Handle := []) (vars : List (String × String) := []) : Build Handle := do
  let hs ← edge r [out] ins implicitIns orderOnly [] vars
  pure (hs.headD default)

/-- Set the targets `ninja` builds when given none. -/
def defaults (hs : List Handle) : Build Unit :=
  modify fun g => { g with defaults := g.defaults ++ hs.map (·.path) }

/-- Run a build description and check the result. -/
def Build.graph (b : Build Unit) : Except String ValidGraph := do
  let ((), g) ← b.run {}
  if h : g.Valid then pure ⟨g, h⟩ else throw "the build graph is not valid"

/-- The `build.ninja` text for a valid graph. -/
def ValidGraph.ninja (g : ValidGraph) : String := print (emit g.1)

end Mise.Frontend
