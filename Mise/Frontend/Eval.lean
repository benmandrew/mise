import Mise.Syntax.Ast

/-!
# Stage 4: Ninja variable evaluation

A model of how Ninja turns a parsed manifest into evaluated commands. It
follows `manifest_parser.cc`, `eval_env.cc` and `graph.cc` (`EdgeEnv`):

- a top-level binding is evaluated when it is read, in the file scope as it
  stands at that point;
- an edge binding is also evaluated when it is read, in the file scope;
- an edge with no bindings uses the file scope itself as its scope, so a
  top-level binding shadows a rule binding of the same name for that edge;
- a variable lookup on an edge tries `in`, `in_newline` and `out`, then the
  edge's scope, then the rule's binding (evaluated in the edge's context),
  then the file scope;
- `$in` and `$out` are the explicit paths, each shell-quoted, joined by spaces.

Ninja reports a cycle among rule variables as an error; the model cuts the
recursion with fuel instead.
-/

namespace Mise.Syntax

/-- A scope: evaluated bindings, newest first. -/
abbrev Scope := List (String × String)

def Scope.get (s : Scope) (k : String) : Option String := (s.find? (·.1 == k)).map (·.2)

/-- Evaluate a value, looking variables up with `look`. -/
def evalWith (look : String → String) : EvalString → String
  | [] => ""
  | .lit s :: r => s ++ evalWith look r
  | .var n :: r => look n ++ evalWith look r

/-- Characters Ninja's `IsKnownShellSafeCharacter` accepts. -/
def shellSafe (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '+' || c == '-' || c == '.' || c == '/'

/-- Ninja's `GetShellEscapedString` for POSIX shells. -/
def shellEscape (s : String) : String :=
  if s.toList.all shellSafe then s
  else String.ofList ('\'' :: (s.toList.flatMap fun c => if c = '\'' then "'\\''".toList else [c]) ++ ['\''])

/-- Ninja's `MakePathList` with shell escaping. -/
def shellList (sep : String) (ps : List Path) : String := sep.intercalate (ps.map shellEscape)

/-- The last binding of `k` in a rule. -/
def Rule.get (r : Rule) (k : String) : Option EvalString := (r.bindings.reverse.find? (·.1 == k)).map (·.2)

/-- What Ninja stores for an edge after parsing it. -/
structure EdgeInfo where
  edge : Edge
  rule : Rule
  /-- The edge's own scope, or `none` when the edge has no bindings and uses
  the file scope. -/
  own : Option Scope
  deriving Repr, Inhabited

/-- Look up a variable on an edge. `file` is the final file scope. -/
def EdgeInfo.lookup (file : Scope) (c : EdgeInfo) : Nat → String → String
  | fuel, v =>
    if v = "in" then shellList " " c.edge.ins
    else if v = "in_newline" then shellList "\n" c.edge.ins
    else if v = "out" then shellList " " c.edge.outs
    else match (c.own.getD file).get v with
      | some s => s
      | none => match c.rule.get v, fuel with
        | some ev, fuel + 1 => evalWith (c.lookup file fuel) ev
        | some _, 0 => ""
        | none, _ => if c.own.isSome then (file.get v).getD "" else ""

/-- The evaluated command, as Ninja hashes it in the build log. -/
def EdgeInfo.command (file : Scope) (c : EdgeInfo) : String :=
  c.lookup file (c.rule.bindings.length + 1) "command"

/-- The state of Ninja's parser after reading a prefix of the manifest. -/
structure Elab where
  file : Scope := []
  rules : List Rule := [⟨"phony", []⟩]
  edges : List EdgeInfo := []
  deriving Repr, Inhabited

def fileLook (s : Scope) (v : String) : String := (s.get v).getD ""

/-- What Ninja stores for an edge read with the given rules and file scope. -/
def edgeInfo (rules : List Rule) (file : Scope) (e : Edge) : EdgeInfo where
  edge := e
  rule := (rules.find? (·.name == e.rule)).getD ⟨e.rule, []⟩
  own := if e.bindings.isEmpty then none
    else some (e.bindings.foldl (fun acc b => (b.1, evalWith (fileLook file) b.2) :: acc) [])

def Elab.step (st : Elab) : Stmt → Elab
  | .binding k v => { st with file := (k, evalWith (fileLook st.file) v) :: st.file }
  | .rule r => { st with rules := st.rules ++ [r] }
  | .edge e => { st with edges := st.edges ++ [edgeInfo st.rules st.file e] }
  | .default _ => st

def Manifest.elab (m : Manifest) : Elab := m.stmts.foldl Elab.step {}

/-- Every edge with its evaluated command, in manifest order. -/
def Manifest.commands (m : Manifest) : List (Edge × String) :=
  let st := m.elab
  st.edges.map fun c => (c.edge, c.command st.file)

end Mise.Syntax

namespace Mise.Syntax.EdgeInfo

theorem lookup_in (file : Scope) (c : EdgeInfo) (n : Nat) : c.lookup file n "in" = shellList " " c.edge.ins := by
  rw [EdgeInfo.lookup.eq_def]; simp

theorem lookup_out (file : Scope) (c : EdgeInfo) (n : Nat) : c.lookup file n "out" = shellList " " c.edge.outs := by
  rw [EdgeInfo.lookup.eq_def]; simp

theorem lookup_other (file : Scope) (c : EdgeInfo) (n : Nat) (v : String)
    (h1 : v ≠ "in") (h2 : v ≠ "in_newline") (h3 : v ≠ "out") :
    c.lookup file n v = match (c.own.getD file).get v with
      | some s => s
      | none => match c.rule.get v, n with
        | some ev, n + 1 => evalWith (c.lookup file n) ev
        | some _, 0 => ""
        | none, _ => if c.own.isSome then (file.get v).getD "" else "" := by
  rw [EdgeInfo.lookup.eq_def]; simp [h1, h2, h3]

end Mise.Syntax.EdgeInfo
