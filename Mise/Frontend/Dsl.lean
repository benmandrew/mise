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

A `restat` rule's command is wrapped by `cmpWrap` unless the rule asks
otherwise, so that it leaves an output untouched exactly when `cmp` finds
its contents unchanged. `Mise.Model.run_withCmp` relates the wrapper to the
model.
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
  /-- The command is wrapped by `cmpWrap`. -/
  cmp : Bool := false
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

/-- The edge variable that holds a `cmpWrap` edge's implicit outputs,
shell-quoted. `edge` sets it, and a build may not set it itself. -/
def cmpOutsVar : String := "mise_iouts"

/-- Wrap a `restat` command, written in Ninja syntax, so that it leaves an
output untouched exactly when its contents would not change. The wrapper
runs in `/bin/sh` and, for each output (`$out`, then `${mise_iouts}`):

1. moves an existing output `f` to `f.mise-old`;
2. runs the command in a subshell;
3. if the command succeeded and wrote every output, moves `f.mise-old`
   back over `f` when `cmp` finds them equal, which restores the old file
   and its mtime, and deletes `f.mise-old` otherwise;
4. if the command failed or left an output missing, deletes what it wrote
   and moves every `f.mise-old` back, then exits with a nonzero status.

So a success leaves each output holding what the command wrote, untouched
when that equals the old contents, and a failure leaves the outputs as they
were. A missing output counts as a failure, so a wrapped command always
produces every output, as the model assumes. The command must not contain
a shell comment, which would hide the closing parenthesis. `Mise.Model.wrapRun`
is the model of this script. -/
def cmpWrap (command : String) : String :=
  "set -- $out ${" ++ cmpOutsVar ++ "}; " ++
  "for f; do rm -f \"$$f.mise-old\"; if [ -e \"$$f\" ]; then mv -f \"$$f\" \"$$f.mise-old\"; fi; done; " ++
  "if ( " ++ command ++ " ); then s=0; for f; do if [ ! -e \"$$f\" ]; then " ++
  "echo \"mise: $$f was not written\" >&2; s=1; fi; done; else s=$$?; fi; " ++
  "for f; do if [ $$s != 0 ]; then rm -f \"$$f\"; " ++
  "if [ -e \"$$f.mise-old\" ]; then mv -f \"$$f.mise-old\" \"$$f\"; fi; " ++
  "elif [ -e \"$$f.mise-old\" ] && cmp -s \"$$f\" \"$$f.mise-old\"; then mv -f \"$$f.mise-old\" \"$$f\"; " ++
  "else rm -f \"$$f.mise-old\"; fi; done; exit $$s"

/-- Declare a rule. A `restat` rule's command is wrapped by `cmpWrap`
unless `restatCmp := false`, for a command that already leaves unchanged
outputs untouched and is trusted to do so correctly (`Sem.keep_eq`). -/
def rule (name command : String) (description : String := "") (depfile : Bool := false)
    (restat : Bool := false) (restatCmp : Bool := true) : Build RuleRef := do
  let wrap := restat && restatCmp
  let cmd ← parseValue s!"rule {name}: command" (if wrap then cmpWrap command else command)
  let desc ← parseValue s!"rule {name}: description" description
  let r : GRule := { name, command := cmd, description := desc, depfile, restat }
  let g ← get
  require r.ok s!"rule {name}: invalid name, empty command, or a reserved variable in the command"
  require (!g.ruleNames.contains name) s!"rule {name}: already declared"
  set { g with rules := g.rules ++ [r] }
  pure ⟨name, wrap⟩

/-- Add an edge. Returns handles to the explicit outputs, then the implicit
outputs. -/
def edge (r : RuleRef) (outs : List Path) (ins : List Handle := []) (implicitIns : List Handle := [])
    (orderOnly : List Handle := []) (implicitOuts : List Path := [])
    (vars : List (String × String) := []) : Build (List Handle) := do
  require (!r.cmp || vars.all (·.1 != cmpOutsVar))
    s!"edge {repr outs}: the variable {cmpOutsVar} is set by the restat wrapper"
  let vars := if r.cmp && !implicitOuts.isEmpty then vars ++ [(cmpOutsVar, shellList " " implicitOuts)] else vars
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

/-- Add an edge with one output whose rule has a depfile. The command may
read any source, plus the generated files in `mayReadGenerated`, which
become order-only inputs: Ninja builds them first, and the depfile records
which of them the command read. -/
def dynEdge1 (r : RuleRef) (out : Path) (ins : List Handle := []) (mayReadGenerated : List Handle := [])
    (vars : List (String × String) := []) : Build Handle :=
  edge1 r out ins [] mayReadGenerated vars

/-- Parameters a build description reads, such as compiler flags, given on
the command line as `--set key=value`. -/
abbrev Params := List (String × String)

def Params.get (ps : Params) (k : String) (d : String) : String := (ps.lookup k).getD d

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
