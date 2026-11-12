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

Every command is wrapped by `wrapCommand` unless the rule asks otherwise,
so that it writes every output when it succeeds and changes no file when it
fails, and a `restat` command leaves an output untouched exactly when `cmp`
finds its contents unchanged. `Mise.Model.script` models the wrapper, and
`Mise.Model.runWrapped_ok` and `runWrapped_fail` relate it to the model's
runs.
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
  /-- The command is wrapped by `wrapCommand`. -/
  wrapped : Bool := false
  deriving Repr, Inhabited

abbrev Build := StateT Graph (Except String)

abbrev ValidGraph := { g : Graph // g.Valid }

private def known (g : Graph) (p : Path) : Bool :=
  g.sources.contains p || g.edges.any (·.allOuts.contains p)

/-- The suffix of the path an old output is moved to while its command
runs. No source or output may end with it. -/
def asideSuffix : String := ".mise-old"

private def require (b : Bool) (msg : String) : Build Unit :=
  if b then pure () else throw msg

/-- Declare a source file. -/
def source (p : Path) : Build Handle := do
  let g ← get
  require (validPath p) s!"source {repr p}: not a valid canonical path"
  require (!known g p) s!"source {repr p}: already declared"
  require (!p.endsWith asideSuffix) s!"source {repr p}: the suffix {asideSuffix} is kept for the command wrapper"
  set { g with sources := g.sources ++ [p] }
  pure ⟨p⟩

def sources (ps : List Path) : Build (List Handle) := ps.mapM source

/-- Parse a Ninja value. -/
def parseValue (what s : String) : Build EvalString :=
  match readValue s.toList with
  | some e => pure e
  | none => throw s!"{what}: cannot parse {repr s} as a Ninja value"

/-- The edge variable that holds a wrapped edge's implicit outputs,
shell-quoted. `edge` sets it, and a build may not set it itself. -/
def wrapOutsVar : String := "mise_iouts"

/-- Wrap a command, written in Ninja syntax, so that a success writes every
output and a failure changes no file. The wrapper runs in `/bin/sh` and,
for each output `f` (`$out`, then `${mise_iouts}`):

1. moves an existing `f` to `f.mise-old`, or deletes a stale `f.mise-old`;
2. runs the command in a subshell;
3. if the command exited 0 and wrote every output, deletes `f.mise-old`,
   or for a `restat` rule first compares it with `cmp`, and when the two are
   equal moves it back over `f`, which restores the old file and its mtime;
4. if the command failed or left an output missing, deletes what it wrote
   and moves every `f.mise-old` back, then exits with a nonzero status.

So a success leaves each output holding what the command wrote, and a
`restat` output untouched when that equals the old contents; a failure
leaves the outputs as they were, and Ninja records nothing for the edge.
The command must not contain a shell comment, which would hide the closing
parenthesis. `Mise.Model.script` models this script. -/
def wrapCommand (restat : Bool) (command : String) : String :=
  "set -- $out ${" ++ wrapOutsVar ++ "}; " ++
  "for f; do if [ -e \"$$f\" ]; then mv -f \"$$f\" \"$$f.mise-old\"; " ++
  "elif [ -e \"$$f.mise-old\" ]; then rm -f \"$$f.mise-old\"; fi; done; " ++
  "if ( " ++ command ++ " ); then s=0; for f; do if [ ! -e \"$$f\" ]; then " ++
  "echo \"mise: $$f was not written\" >&2; s=1; fi; done; else s=$$?; fi; " ++
  "for f; do if [ $$s != 0 ]; then rm -f \"$$f\"; " ++
  "if [ -e \"$$f.mise-old\" ]; then mv -f \"$$f.mise-old\" \"$$f\"; fi; " ++
  "elif [ -e \"$$f.mise-old\" ]; then " ++
  (if restat then "if cmp -s \"$$f\" \"$$f.mise-old\"; then mv -f \"$$f.mise-old\" \"$$f\"; " ++
     "else rm -f \"$$f.mise-old\"; fi; "
   else "rm -f \"$$f.mise-old\"; ") ++
  "fi; done; exit $$s"

/-- Declare a rule. Its command is wrapped by `wrapCommand` unless
`wrap := false`, for a command that is trusted to write every output when
it exits 0, to change no file when it fails, and, for a `restat` rule, to
leave an output untouched only when its contents would not change
(`Sem.keep_eq`). -/
def rule (name command : String) (description : String := "") (depfile : Bool := false)
    (restat : Bool := false) (wrap : Bool := true) : Build RuleRef := do
  let cmd ← parseValue s!"rule {name}: command" (if wrap then wrapCommand restat command else command)
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
  require (!r.wrapped || vars.all (·.1 != wrapOutsVar))
    s!"edge {repr outs}: the variable {wrapOutsVar} is set by the command wrapper"
  let vars := if r.wrapped && !implicitOuts.isEmpty then vars ++ [(wrapOutsVar, shellList " " implicitOuts)] else vars
  let e : GEdge := { rule := r.name, outs, implicitOuts, ins := ins.map (·.path),
                     implicitIns := implicitIns.map (·.path), orderOnly := orderOnly.map (·.path), vars }
  let g ← get
  for o in e.allOuts do
    require (validPath o) s!"edge {repr outs}: output {repr o} is not a valid canonical path"
    require (!known g o) s!"edge {repr outs}: output {repr o} is already declared"
    require (!o.endsWith asideSuffix) s!"edge {repr outs}: output {repr o}: the suffix {asideSuffix} is kept for the command wrapper"
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
