/-!
# Stage 3: Ninja syntax

The supported subset of Ninja's manifest format, and the checks that make a
manifest well formed. The parser model (`Mise.Syntax.Parse`) runs the same
`Stmt.ok` check on every statement it reads, so well-formedness and
"accepted by the parser model" use one definition.
-/

namespace Mise.Syntax

/-- A path is a string. `validPath` says which strings the printer and the
parser model accept.
Gloss: paths -/
abbrev Path := String

/-- A piece of an evaluated string: literal text or a variable reference. -/
inductive Seg where
  | lit (s : String)
  | var (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- Ninja's `EvalString`: a value whose variable references are expanded later. -/
abbrev EvalString := List Seg

/-- A variable binding `key = value`; the value is not yet evaluated. -/
abbrev Binding := String × EvalString

/-- A `rule` statement: its name and its indented bindings, in order. -/
structure Rule where
  name : String
  bindings : List Binding
  deriving DecidableEq, Repr, Inhabited

/-- A `build` statement: explicit outputs, implicit outputs (after `|`), the
rule, explicit inputs, implicit inputs (after `|`), order-only inputs
(after `||`), and the edge's indented bindings. -/
structure Edge where
  outs : List Path
  implicitOuts : List Path := []
  rule : String
  ins : List Path := []
  implicitIns : List Path := []
  orderOnly : List Path := []
  bindings : List Binding := []
  deriving DecidableEq, Repr, Inhabited

/-- A top-level statement: a variable binding, a rule, a build edge, or a
`default` statement naming targets. -/
inductive Stmt where
  | binding (key : String) (value : EvalString)
  | rule (r : Rule)
  | edge (e : Edge)
  | default (targets : List Path)
  deriving DecidableEq, Repr, Inhabited

/-- A manifest: its statements in file order.
Gloss: manifests -/
structure Manifest where
  stmts : List Stmt
  deriving DecidableEq, Repr, Inhabited

namespace Edge

/-- Explicit then implicit outputs. -/
def allOuts (e : Edge) : List Path := e.outs ++ e.implicitOuts
/-- Explicit, implicit and order-only inputs, in that order. -/
def allIns (e : Edge) : List Path := e.ins ++ e.implicitIns ++ e.orderOnly
/-- Every path the edge names: its outputs, then its inputs. -/
def allPaths (e : Edge) : List Path := e.allOuts ++ e.allIns

end Edge

/-! ## Character classes -/

/-- Characters of Ninja's `varname`: identifiers, rule names, `${...}` names. -/
def isVarChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '-' || c == '.'

/-- Characters of Ninja's `simple_varname`, used by `$name` references. -/
def isSimpleVarChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '-'

/-- Characters allowed in literal text. Ninja ends a line at `\n`, rejects a
lone `\r`, and treats `\0` as end of input. -/
def litChar (c : Char) : Bool := c != '\n' && c != '\r' && c != '\x00'

/-- Characters allowed in a path. Ninja has no escape for `|`. -/
def pathChar (c : Char) : Bool := litChar c && c != '|'

/-- Top-level keywords, which cannot be top-level variable names. -/
def keywords : List (List Char) :=
  [['b','u','i','l','d'], ['r','u','l','e'], ['d','e','f','a','u','l','t'],
   ['p','o','o','l'], ['i','n','c','l','u','d','e'], ['s','u','b','n','i','n','j','a']]

/-- Rule variables in the supported subset. -/
def ruleKeys : List String :=
  ["command", "description", "depfile", "deps", "restat", "generator", "dyndep"]

/-! ## Validity -/

/-- A nonempty string of `varname` characters (`isVarChar`). -/
def validIdent (s : String) : Bool := !s.toList.isEmpty && s.toList.all isVarChar

/-- Nonempty literal text with no newline, carriage return or NUL. -/
def validLit (s : String) : Bool := !s.toList.isEmpty && s.toList.all litChar

/-- A literal segment is valid when its text is (`validLit`); a variable
reference when its name is an identifier (`validIdent`). -/
def Seg.valid : Seg → Bool
  | .lit s => validLit s
  | .var n => validIdent n

/-- Two literal segments are never adjacent; the parser model merges them. -/
def noAdjLits : EvalString → Bool
  | [] => true
  | [_] => true
  | .lit _ :: .lit _ :: _ => false
  | _ :: s :: r => noAdjLits (s :: r)

/-- Every segment is valid and no two literal segments are adjacent
(`noAdjLits`). -/
def validEval (e : EvalString) : Bool := e.all Seg.valid && noAdjLits e

/-- Split a character list at every `/`. -/
def splitSlash : List Char → List (List Char)
  | [] => [[]]
  | c :: r =>
    if c = '/' then [] :: splitSlash r
    else match splitSlash r with
      | l :: ls => (c :: l) :: ls
      | [] => [[c]]

/-- A path Ninja's `CanonicalizePath` leaves unchanged, conservatively: no
empty, `.` or `..` component, except a leading `/`. -/
def canonical (p : List Char) : Bool :=
  match splitSlash p with
  | [] => false
  | first :: rest =>
    let bad (c : List Char) := c == ['.'] || c == ['.', '.']
    (rest.all fun c => !c.isEmpty && !bad c) && !bad first && (!first.isEmpty || !rest.isEmpty)

/-- A path `mise` accepts: nonempty, made of path characters (`pathChar`), and
canonical (`canonical`). -/
def validPath (p : Path) : Bool :=
  !p.toList.isEmpty && p.toList.all pathChar && canonical p.toList

/-- The key is an identifier and the value is valid. -/
def validBinding (b : Binding) : Bool := validIdent b.1 && validEval b.2

/-- No string occurs twice in the list. -/
def nodupB : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

/-! ## Context-sensitive checks -/

/-- What the parser model knows after reading a prefix of the manifest. -/
structure Ctx where
  rules : List String := ["phony"]
  outs : List Path := []
  known : List Path := []
  deriving Repr, Inhabited

/-- Record a statement in the context. A rule adds its name to the rules; an
edge adds its outputs to `outs` and all its paths to `known`. Other
statements change nothing. -/
def Ctx.add (c : Ctx) : Stmt → Ctx
  | .rule r => { c with rules := c.rules ++ [r.name] }
  | .edge e => { c with outs := c.outs ++ e.allOuts, known := c.known ++ e.allPaths }
  | _ => c

/-- One statement is acceptable after the statements summarised by `c`. -/
def Stmt.ok (c : Ctx) : Stmt → Bool
  | .binding k v => validIdent k && !keywords.contains k.toList && validEval v
  | .rule r =>
    validIdent r.name && !c.rules.contains r.name &&
    r.bindings.all (fun b => validBinding b && ruleKeys.contains b.1) &&
    -- Ninja keeps the last `command` binding and rejects it if it is empty.
    ((r.bindings.filter (·.1 == "command")).getLast?.any fun b => !b.2.isEmpty)
  | .edge e =>
    validIdent e.rule && c.rules.contains e.rule && !e.outs.isEmpty &&
    e.allPaths.all validPath && nodupB e.allOuts &&
    e.allOuts.all (fun o => !c.outs.contains o) &&
    e.bindings.all validBinding
  | .default ps => !ps.isEmpty && ps.all validPath && ps.all c.known.contains

def stmtsOK : Ctx → List Stmt → Bool
  | _, [] => true
  | c, s :: ss => s.ok c && stmtsOK (c.add s) ss

/-- A manifest is well formed when every statement passes `Stmt.ok` in the
context of the statements before it. -/
def Manifest.WellFormed (m : Manifest) : Prop := stmtsOK {} m.stmts = true

instance (m : Manifest) : Decidable m.WellFormed := inferInstanceAs (Decidable (_ = _))

end Mise.Syntax
