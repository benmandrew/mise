import Lean
open Lean Meta

/-!
# Mechanical English for theorem statements

`Gloss.statement` turns the type of a theorem into English. It walks the
elaborated `Expr`, not the source text, and every word it produces comes from
one of two places:

* fixed phrases in this file for the logical connectives (`∀`, `∃`, `∧`, `∨`,
  `¬`, `→`, `↔`, `=`, `≠`, `∈`, `∉`, `<`, `≤`) and for a few names from Lean's
  core library (`coreTemplates`);
* templates written beside each `Mise` definition, as a line of its
  docstring that starts with `Gloss:`. `Gloss.fst:` and `Gloss.snd:` give the
  two components of a definition whose value is a pair, and `Gloss.fun:`
  reads the definition with its last explicit argument missing, as a
  function (`st.content` rather than `st.content p`). A type carries a
  plural template, used where the statement ranges over the type, and a
  singular noun on a `Gloss.one:` line (`coreSingulars` for core types).

A template is text with slots. `{x}` is the argument whose binder is named
`x`; `{#k}` is the `k`-th explicit argument, counting from 1. Text between
backticks is set in code font. A template may leave out arguments: the
templates for the model leave out `sem`, the meaning of commands, which is
the same throughout a statement. When the argument for `sem` is anything other
than a variable, the phrase ends with `(taking sem to be …)`. Any other
explicit argument a template leaves out is reported in `omits`. Arguments that are not a single name are put in
parentheses, except in the phrase for a type. A partial application without
a `Gloss.fun:` line is read as `fun x => f … x`.

A constant without a template is printed in Lean notation, in code font, and
recorded in `missing`, so the output lists it as a warning. Definitions are
never unfolded, so the English follows the statement as written.

The list of variables a statement ranges over is far from where they are
used, so the first mention of each one in the hypotheses and conclusions
names its type's singular noun ("the model edge `e`"), and later mentions are
the bare name. A variable bound inside the statement by `∀ x ∈ l` or
`∃ x ∈ l`, which names no type, gets the noun at its binder ("for every path
`o` in …"). A type without a singular noun is recorded in `noSingular`.
-/

namespace Gloss

/-- Inline text: plain words, code, or a parenthesised group. -/
inductive Inl where
  | txt (s : String)
  | code (s : String)
  | grp (body : Array Inl)
  /-- The first mention of a variable, with its type's noun. It reads as one
  noun phrase, so it is never parenthesised. -/
  | intro (body : Array Inl)
  deriving Inhabited, BEq

abbrev Phrase := Array Inl

/-- The glosses found in a docstring, and the docstring without them. -/
structure Glosses where
  main : Option String := none
  fst : Option String := none
  snd : Option String := none
  fn : Option String := none
  one : Option String := none
  rest : String := ""
  deriving Inhabited

/-- Split the `Gloss:` lines from a docstring. -/
def Glosses.parse (doc : String) : Glosses := Id.run do
  let mut g : Glosses := {}
  let mut keep : Array String := #[]
  for line in doc.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.startsWith "Gloss.fst:" then g := { g with fst := some (t.drop 10).trimAscii.toString }
    else if t.startsWith "Gloss.snd:" then g := { g with snd := some (t.drop 10).trimAscii.toString }
    else if t.startsWith "Gloss.fun:" then g := { g with fn := some (t.drop 10).trimAscii.toString }
    else if t.startsWith "Gloss.one:" then g := { g with one := some (t.drop 10).trimAscii.toString }
    else if t.startsWith "Gloss:" then g := { g with main := some (t.drop 6).trimAscii.toString }
    else keep := keep.push line
  return { g with rest := ("\n".intercalate keep.toList).trimAscii.toString }

/-- What kind of phrase an expression becomes. -/
inductive Mode where
  /-- A clause: the expression is a proposition. -/
  | prop
  /-- A noun phrase naming a value. -/
  | noun
  /-- A plural noun phrase naming the values of a type. -/
  | typ
  deriving BEq, Inhabited

/-- Templates for names from Lean's core library, which carry no `Gloss:`
line of their own. -/
def coreTemplates : List (Name × Mode × String) := [
  (``Prod.fst, .noun, "the first component of {#1}"),
  (``Prod.snd, .noun, "the second component of {#1}"),
  (``List.nil, .noun, "the empty list"),
  (``List.cons, .noun, "{#1} followed by {#2}"),
  (``HAppend.hAppend, .noun, "{#1} followed by {#2}"),
  (``Option.some, .noun, "`some` {#1}"),
  (``Option.none, .noun, "`none`"),
  (``Bool.true, .noun, "`true`"),
  (``Bool.false, .noun, "`false`"),
  (``List.Perm, .prop, "{#1} is a reordering of {#2}"),
  (``List.Nodup, .prop, "no element occurs twice in {#1}"),
  (``Inhabited, .prop, "{#1} has a default element"),
  (``DecidableEq, .prop, "equality on {#1} is decidable"),
  (``True, .prop, "true"),
  (``False, .prop, "false"),
  (``List, .typ, "lists of {#1}"),
  (``Prod, .typ, "pairs of {#1} and {#2}"),
  (``Option, .typ, "optional {#1}"),
  (``Nat, .typ, "natural numbers"),
  (``Bool, .typ, "Booleans"),
  (``String, .typ, "strings")]

/-- Singular nouns for the core types in `coreTemplates`. -/
def coreSingulars : List (Name × String) := [
  (``List, "list"),
  (``Prod, "pair"),
  (``Option, "optional value"),
  (``Nat, "natural number"),
  (``Bool, "Boolean"),
  (``String, "string")]

/-- One piece of a parsed template. -/
inductive Piece where
  | txt (s : String)
  | code (s : String)
  | slot (key : String)

/-- Split a template into text, code and slots. -/
def pieces (t : String) : Array Piece := Id.run do
  let mut out : Array Piece := #[]
  let mut buf := ""
  let mut cs := t.toList
  while h : cs ≠ [] do
    let c := cs.head h
    cs := cs.tail
    if c == '{' || c == '`' then
      let close := if c == '{' then '}' else '`'
      let body := cs.takeWhile (· != close)
      cs := (cs.dropWhile (· != close)).drop 1
      if !buf.isEmpty then out := out.push (.txt buf); buf := ""
      out := out.push (if c == '{' then .slot (String.ofList body) else .code (String.ofList body))
    else buf := buf.push c
  if !buf.isEmpty then out := out.push (.txt buf)
  return out

structure State where
  /-- Constants printed in Lean notation because they have no template. -/
  missing : NameSet := {}
  /-- `Mise` constants whose template was used. -/
  used : NameSet := {}
  /-- Explicit arguments, other than `sem`, that a template leaves out. -/
  omits : NameSet := {}
  /-- Types with a plural template but no singular noun. -/
  noSingular : NameSet := {}
  /-- Variables of the statement not yet mentioned, each with the phrase that
  introduces it. -/
  intros : Std.HashMap FVarId Phrase := {}
  /-- Set while writing the list of variables, which is not a mention. -/
  quiet : Bool := false

abbrev M := StateT State MetaM

def txt (s : String) : Phrase := #[.txt s]
def code (s : String) : Phrase := #[.code s]

/-- Join phrases with `sep`, and the last two with `last`. -/
def joinWith (sep last : String) : List Phrase → Phrase
  | [] => #[]
  | [a] => a
  | [a, b] => a ++ txt last ++ b
  | a :: rest => a ++ txt sep ++ joinWith sep last rest

def andList (ps : List Phrase) : Phrase := joinWith ", " (if ps.length > 2 then ", and " else " and ") ps

/-- A phrase that is a single name or word needs no parentheses. -/
def isAtom (p : Phrase) : Bool :=
  match p.toList with
  | [.code _] => true
  | [.grp _] => true
  | [.intro _] => true
  | [.txt s] => !s.contains ' '
  | _ => false

def group (p : Phrase) : Phrase := if isAtom p then p else #[.grp p]

/-- Which template of a constant: the main one, a component of a pair, or
the function form. -/
inductive Which where
  | main | fst | snd | fn | one
  deriving BEq

/-- The template of a constant: from its docstring, or the core table. -/
def templateOf (n : Name) (which : Which := .main) : M (Option (Mode × String)) := do
  if let some (_, m, t) := coreTemplates.find? (·.1 == n) then
    return if which == .main then some (m, t) else none
  let some doc ← findDocString? (← getEnv) n | return none
  let g := Glosses.parse doc
  let t := match which with
    | .main => g.main
    | .fst => g.fst
    | .snd => g.snd
    | .fn => g.fn
    | .one => g.one
  let some t := t | return none
  let ty := (← getConstInfo n).type
  let m ← forallTelescope ty fun _ r => do
    if r.isProp then return Mode.prop
    if (← whnf r).isSort then return .typ
    return .noun
  return some (if which == .main then m else .noun, t)

/-- The display name of a local. -/
def localName (e : Expr) : MetaM String := do
  return toString (← e.fvarId!.getDecl).userName

def ppCode (e : Expr) : MetaM Phrase := do
  return code (toString (← ppExpr e)).trimAscii.toString

/-- A mention of a local: the phrase that introduces it the first time, and
its name after that. -/
def mention (x : Expr) : M Phrase := do
  let s ← get
  if !s.quiet then
    if let some p := s.intros[x.fvarId!]? then
      set { s with intros := s.intros.erase x.fvarId! }
      return #[.intro p]
  return code (← localName x)

/-- The singular noun for the values of type `t`, as the text before and
after a name: `model edge` for `MEdge`, and `element`, `of V` for a type
variable `V`. -/
def singular (t : Expr) : M (Option (Phrase × Phrase)) := do
  match t.consumeMData with
  | .sort .zero => return some (txt "proposition", #[])
  | .sort _ => return some (txt "type", #[])
  | .fvar _ => return some (txt "element", txt " of " ++ code (← localName t))
  | .forallE _ _ b _ => if b.hasLooseBVars then return none else return some (txt "function", #[])
  | t =>
    let .const n _ := t.getAppFn | return none
    let one? ← if let some (_, s) := coreSingulars.find? (·.1 == n) then pure (some s) else
      match ← findDocString? (← getEnv) n with
      | some doc => pure (Glosses.parse doc).one
      | none => pure none
    let some one := one? | do
      modify fun s => { s with noSingular := s.noSingular.insert n }
      return none
    let ph := (pieces one).map fun
      | .txt s => Inl.txt s
      | .code s => .code s
      | .slot k => .txt s!"\{{k}}"
    return some (ph, #[])

/-- The variable `x` of type `t` named with its type's noun, without an
article: `model edge e`. -/
def named (x t : Expr) : M Phrase := do
  let name := code (← localName x)
  match ← singular t with
  | some (pre, post) => return pre ++ txt " " ++ name ++ post
  | none => return name

/-- `a` or `an`, by the first letter of `p`. -/
def article (p : Phrase) : String :=
  match p.toList with
  | Inl.txt s :: _ => if "aeiouAEIOU".contains (s.front) then "an " else "a "
  | _ => "a "

/-- Bind a local whose name is readable. -/
def withNamed {α} (n : Name) (t : Expr) (k : Expr → M α) : M α := do
  let n := if n.hasMacroScopes then n.eraseMacroScopes else n
  let n := (← getLCtx).getUnusedName n
  withLocalDeclD n t k

/-- `x ∈ coll`, giving `coll`. -/
def memOf (x h : Expr) : Option Expr :=
  match h.consumeMData.getAppFn.constName?, h.consumeMData.getAppArgs with
  | some ``Membership.mem, #[_, _, _, coll, y] => if y == x then some coll else none
  | _, _ => none

/-- `x ∈ coll ∧ rest`, giving `coll` and `rest`. -/
def boundedAnd (x b : Expr) : Option (Expr × Expr) :=
  match b.consumeMData.getAppFn.constName?, b.consumeMData.getAppArgs with
  | some ``And, #[h, rest] => (memOf x h).map (·, rest)
  | _, _ => none

/-- `∃ x : t, body`, with `body` still under the binder. -/
def asExists (e : Expr) : Option (Name × Expr × Expr) :=
  match e.consumeMData.getAppFn.constName?, e.consumeMData.getAppArgs with
  | some ``Exists, #[_, .lam n t b _] => some (n, t, b)
  | _, _ => none

/-- The conjuncts of a right-nested `∧`. -/
partial def conjuncts (e : Expr) : List Expr :=
  match e.consumeMData.getAppFn.constName?, e.consumeMData.getAppArgs with
  | some ``And, #[a, b] => a :: conjuncts b
  | _, _ => [e]

mutual

/-- Fill a template with the arguments of an application. Returns `none` when
a slot names an argument that is not supplied. -/
partial def fill (n : Name) (mode : Mode) (t : String) (args : Array Expr) : M (Option Phrase) := do
  let info ← getConstInfo n
  let binders ← forallTelescope info.type fun xs _ => xs.mapM fun x => do
    let d ← x.fvarId!.getDecl
    return (d.userName.eraseMacroScopes.toString, d.binderInfo.isExplicit)
  -- Arguments past the constant's own binders (a field of function type,
  -- applied) count as further explicit arguments.
  let explicit := (List.range binders.size).filter (fun i => binders[i]!.2) ++
    (List.range args.size).filter (· ≥ binders.size)
  let slot (key : String) : M Nat := do
    let idx? := if key.startsWith "#" then
        (key.drop 1).toString.toNat?.bind fun k => explicit[k - 1]?
      else
        let hits := (List.range binders.size).filter fun i => binders[i]!.1 == key
        if hits.length == 1 then hits.head? else none
    let some i := idx? | throwError "template of {n}: unknown slot \{{key}}"
    return i
  -- Check every slot first, so that a template that does not apply mentions
  -- no variable.
  for p in pieces t do
    if let .slot key := p then
      if args[← slot key]?.isNone then return none
  let mut out : Phrase := #[]
  let mut seen : List Nat := []
  for p in pieces t do
    match p with
    | .txt s => out := out.push (.txt s)
    | .code s => out := out.push (.code s)
    | .slot key =>
      let i ← slot key
      seen := i :: seen
      let a := args[i]!
      let ph ← argPhrase mode a
      -- Plural type phrases nest without ambiguity, so they are not grouped.
      out := out ++ (if mode == .typ then ph else group ph)
  for i in explicit do
    if i < args.size && !seen.contains i then
      let name := (binders[i]?.map (·.1)).getD s!"#{i + 1}"
      if name != "sem" then
        modify fun s => { s with omits := s.omits.insert (n ++ .mkSimple name) }
      -- `sem` may be left out only when it is the statement's own variable;
      -- any other argument there is spelt out.
      else if !args[i]!.isFVar then
        out := out ++ txt " (taking " ++ code name ++ txt " to be " ++ group (← argPhrase mode args[i]!) ++
          txt ")"
  return some out

/-- A slot's argument: a clause if it is a proposition, a type in type
templates, and a noun phrase otherwise. -/
partial def argPhrase (mode : Mode) (a : Expr) : M Phrase := do
  if ← isProp a then return ← prop a
  if (← isType a) && (mode == .typ || !a.isFVar) then return ← typ a
  noun a

/-- Apply a named template or a variable, or fall back to Lean notation. -/
partial def applied (mode : Mode) (e : Expr) : M Phrase := do
  let f := e.getAppFn
  let args := e.getAppArgs
  if let .const n _ := f then
    -- The components of a pair-valued definition.
    if (n == ``Prod.fst || n == ``Prod.snd) && args.size == 3 then
      let inner := args[2]!
      if let .const m _ := inner.getAppFn then
        if let some (_, t) ← templateOf m (if n == ``Prod.fst then .fst else .snd) then
          if let some p ← fill m .noun t inner.getAppArgs then
            if (`Mise).isPrefixOf m then modify fun s => { s with used := s.used.insert m }
            return p
    if let some (_, t) ← templateOf n then
      if let some p ← fill n mode t args then
        if (`Mise).isPrefixOf n then modify fun s => { s with used := s.used.insert n }
        return p
      -- A partial application: the function form, or `fun x => f … x`.
      if let some (_, t) ← templateOf n .fn then
        if let some p ← fill n .noun t args then
          modify fun s => { s with used := s.used.insert n }
          return p
      let e' ← etaExpand e
      if e'.isLambda then return ← noun e'
    modify fun s => { s with missing := s.missing.insert n }
  -- A variable applied to arguments: `the value of f at x`.
  if f.isFVar && !args.isEmpty && mode != .typ then
    let as ← args.toList.mapM fun a => return group (← noun a)
    let fn ← mention f
    if mode == .prop then return fn ++ txt " holds at " ++ andList as
    return txt "the value of " ++ fn ++ txt " at " ++ andList as
  ppCode e

/-- A run of `∃`. A bounded binder (`∃ x ∈ l, P`, which elaborates to
`∃ x, x ∈ l ∧ P`) gets its own phrase; unbounded binders of one type in a
row share one. -/
partial def exists_ (e : Expr) : M Phrase := do
  let some (n, t, body) := asExists e | prop e
  withNamed n t fun x => do
    let b := body.instantiate1 x
    if let some (coll, rest) := boundedAnd x b then
      let nm ← named x t
      return txt "there is " ++ txt (article nm) ++ nm ++ txt " in " ++ group (← noun coll) ++
        txt " such that " ++ (← prop rest)
    existsRun t #[x] b

partial def existsRun (t : Expr) (xs : Array Expr) (b : Expr) : M Phrase := do
  if let some (n', t', body') := asExists b then
    if t' == t then
      let r? ← withNamed n' t' fun y => do
        let b' := body'.instantiate1 y
        if (boundedAnd y b').isSome then return none
        return some (← existsRun t (xs.push y) b')
      if let some r := r? then return r
  let names ← xs.toList.mapM fun x => return code (← localName x)
  let verb := if xs.size == 1 then "there is " else "there are "
  return txt verb ++ andList names ++ txt " among " ++ (← typ t) ++ txt " such that " ++ (← prop b)

/-- A clause for a proposition. -/
partial def prop (e : Expr) : M Phrase := do
  let e := e.consumeMData
  if let .forallE n t b _ := e then
    if ← isProp t then
      if !b.hasLooseBVars then
        return txt "if " ++ (← prop t) ++ txt ", then " ++ (← prop b)
      return ← withNamed n t fun x => do
        return txt "if " ++ (← prop t) ++ txt ", then " ++ (← prop (b.instantiate1 x))
    return ← withNamed n t fun x => do
      let body := b.instantiate1 x
      -- `∀ x ∈ l, P` elaborates to `∀ x, x ∈ l → P`.
      if let .forallE _ h r _ := body then
        if !r.hasLooseBVars then
          if let some coll := memOf x h then
            return txt "for every " ++ (← named x t) ++ txt " in " ++ group (← noun coll) ++
              txt ", " ++ (← prop r)
      return txt "for every " ++ code (← localName x) ++ txt " among " ++ (← typ t) ++ txt ", " ++
        (← prop body)
  if (asExists e).isSome then return ← exists_ e
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``And, _ =>
    let cs ← (conjuncts e).mapM prop
    return txt (if cs.length > 2 then "all of: " else "both ") ++ andList cs
  | some ``Or, #[a, b] => return txt "either " ++ (← prop a) ++ txt ", or " ++ (← prop b)
  | some ``Iff, #[a, b] => return (← prop a) ++ txt " if and only if " ++ (← prop b)
  | some ``Not, #[a] =>
    match a.getAppFn.constName?, a.getAppArgs with
    | some ``Eq, #[_, x, y] => return group (← noun x) ++ txt " does not equal " ++ group (← noun y)
    | some ``Membership.mem, #[_, _, _, coll, x] =>
      return group (← noun x) ++ txt " is not in " ++ group (← noun coll)
    | _, _ => return txt "it is not the case that " ++ (← prop a)
  | some ``Ne, #[_, x, y] => return group (← noun x) ++ txt " does not equal " ++ group (← noun y)
  | some ``Eq, #[_, x, y] =>
    if y.isConstOf ``Bool.true then return group (← noun x) ++ txt " is " ++ code "true"
    return group (← noun x) ++ txt " equals " ++ group (← noun y)
  | some ``Membership.mem, #[_, _, _, coll, x] =>
    return group (← noun x) ++ txt " is in " ++ group (← noun coll)
  | some ``LT.lt, #[_, _, x, y] => return group (← noun x) ++ txt " is less than " ++ group (← noun y)
  | some ``LE.le, #[_, _, x, y] => return group (← noun x) ++ txt " is at most " ++ group (← noun y)
  | some ``GT.gt, #[_, _, x, y] => return group (← noun x) ++ txt " is greater than " ++ group (← noun y)
  | some ``GE.ge, #[_, _, x, y] => return group (← noun x) ++ txt " is at least " ++ group (← noun y)
  | _, _ =>
    if e.isFVar then return ← mention e
    applied .prop e

/-- A noun phrase for a value. -/
partial def noun (e : Expr) : M Phrase := do
  let e := e.consumeMData
  match e with
  | .fvar _ => mention e
  | .lit (.natVal k) => return code (toString k)
  | .lit (.strVal s) => return code s.quote
  | .lam n t b _ =>
    withNamed n t fun x => do
      return txt "the function taking " ++ code (← localName x) ++ txt " to " ++
        group (← noun (b.instantiate1 x))
  | _ =>
    -- `List.map f l`: the list of `f x` for each `x` in `l`.
    if e.isAppOfArity ``List.map 4 then
      let f := e.appFn!.appArg!
      let l := e.appArg!
      let elemTy := e.getAppArgs[0]!
      let (n, b) := match f with
        | .lam n _ b _ => (n, b)
        | _ => (`x, mkApp f (.bvar 0))
      return ← withNamed n elemTy fun x => do
        return txt "the list of " ++ group (← noun (b.instantiate1 x)) ++ txt " for each " ++
          (← named x elemTy) ++ txt " in " ++ group (← noun l)
    if ← isProp e then return ← prop e
    applied .noun e

/-- A plural noun phrase for the values of a type. -/
partial def typ (e : Expr) : M Phrase := do
  let e := e.consumeMData
  match e with
  | .sort .zero => return txt "propositions"
  | .sort _ => return txt "types"
  | .fvar _ => return txt "elements of " ++ code (← localName e)
  | .forallE _ t b _ =>
    if !b.hasLooseBVars then
      return txt "functions from " ++ (← typ t) ++ txt " to " ++ (← typ b)
    ppCode e
  | _ => applied .typ e

end

/-- A theorem statement in English: the variables it ranges over, its
hypotheses with their names, and its conclusions. -/
structure Statement where
  /-- Each entry: the variables, and the type they range over. -/
  vars : Array (Array String × Phrase)
  /-- Each entry: the hypothesis name, if it has a readable one, and the clause. -/
  hyps : Array (Option String × Phrase)
  /-- One clause, or several when the conclusion is a conjunction. -/
  conclude : Array Phrase

/-- Translate the type of a theorem. -/
partial def statementAux (e : Expr) (vars : Array (Array String × Phrase))
    (hyps : Array (Option String × Phrase)) : M Statement := do
  match e.consumeMData with
  | .forallE n t b bi =>
    withNamed n t fun x => do
      let name ← localName x
      let readable := !n.hasMacroScopes && !n.isAnonymous && !bi.isInstImplicit
      if (← isProp t) || bi.isInstImplicit then
        let h := if readable then some name else none
        statementAux (b.instantiate1 x) vars (hyps.push (h, ← prop t))
      else
        modify fun s => { s with quiet := true }
        let ty ← typ t
        modify fun s => { s with quiet := false }
        if let some (pre, post) ← singular t then
          let intro := txt "the " ++ pre ++ txt " " ++ code name ++ post
          modify fun s => { s with intros := s.intros.insert x.fvarId! intro }
        -- Variables of the same type in a row share an entry.
        let vars := match vars.back? with
          | some (vs, ty') => if ty' == ty then vars.pop.push (vs.push name, ty) else vars.push (#[name], ty)
          | none => vars.push (#[name], ty)
        statementAux (b.instantiate1 x) vars hyps
  | body =>
    let cs ← (conjuncts body).mapM prop
    return { vars, hyps, conclude := cs.toArray }

def statement (ty : Expr) : M Statement := statementAux ty #[] #[]

end Gloss
