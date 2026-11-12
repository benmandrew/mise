import Mise.Syntax.Ast

/-!
# Stage 3: parser model

A model of Ninja's lexer and manifest parser, restricted to the subset in
`Mise.Syntax.Ast`. It is a specification artefact: it exists so that the
printer can be proved correct against it, and it is tested against real Ninja.

The input is split into lines first. Ninja's `$`-newline line continuation is
outside the model, and so is a `\r\n` line ending: both make `parse` fail.
-/

namespace Mise.Syntax

/-- Drop leading spaces. -/
def eatSpaces : List Char → List Char
  | [] => []
  | c :: r => if c = ' ' then eatSpaces r else c :: r

/-- Split a list before the first character that fails `p`. -/
def spanWhile (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: r => if p c then ((spanWhile p r).1.cons c, (spanWhile p r).2) else ([], c :: r)

/-- Ninja's `ReadIdent`: a nonempty `varname`, then any spaces. -/
def readIdent (l : List Char) : Option (List Char × List Char) :=
  match spanWhile isVarChar l with
  | ([], _) => none
  | (w, r) => some (w, eatSpaces r)

/-- One path, in Ninja's path mode. It stops before an unescaped space, `:`
or `|`, or at the end of the line. A variable reference in a path is outside
the model. -/
def readPath : List Char → Option (List Char × List Char)
  | [] => some ([], [])
  | c :: r =>
    if c = '$' then
      match r with
      | [] => none
      | d :: r' =>
        if d = '$' || d = ' ' || d = ':' then (readPath r').map (fun x => (d :: x.1, x.2))
        else none
    else if c = ' ' || c = ':' || c = '|' then some ([], c :: r)
    else if litChar c then (readPath r).map (fun x => (c :: x.1, x.2))
    else none

theorem spanWhile_length (p : Char → Bool) (l : List Char) :
    (spanWhile p l).2.length ≤ l.length := by
  induction l with
  | nil => simp [spanWhile]
  | cons c r ih => unfold spanWhile; split <;> simp <;> omega

theorem eatSpaces_length (l : List Char) : (eatSpaces l).length ≤ l.length := by
  induction l with
  | nil => simp [eatSpaces]
  | cons c r ih => unfold eatSpaces; split <;> simp <;> omega

theorem readPath_length : ∀ {l p r : List Char}, readPath l = some (p, r) →
    p.length + r.length ≤ l.length
  | [], p, r, h => by simp [readPath] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | c :: rest, p, r, h => by
    unfold readPath at h
    split at h
    · split at h
      · contradiction
      · rename_i d r'
        split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨⟨p', r''⟩, h', he⟩ := h
          simp at he; obtain ⟨rfl, rfl⟩ := he
          have := readPath_length h'; simp; omega
        · contradiction
    · split at h
      · simp at h; obtain ⟨rfl, rfl⟩ := h; simp
      · split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨⟨p', r''⟩, h', he⟩ := h
          simp at he; obtain ⟨rfl, rfl⟩ := he
          have := readPath_length h'; simp; omega
        · contradiction

/-- Paths separated by spaces, up to the first empty path. -/
def readPaths (l : List Char) : Option (List (List Char) × List Char) :=
  match _h : readPath l with
  | none => none
  | some ([], r) => some ([], r)
  | some (c :: p, r) => (readPaths (eatSpaces r)).map (fun x => ((c :: p) :: x.1, x.2))
termination_by l.length
decreasing_by
  have h1 := readPath_length _h
  have h2 := eatSpaces_length r
  simp at h1 ⊢; omega

/-- Merge one literal character into the front of an evaluated string. -/
def consLit (c : Char) (t : EvalString) : EvalString :=
  match t with
  | .lit s :: t' => .lit (String.ofList (c :: s.toList)) :: t'
  | _ => .lit (String.ofList [c]) :: t

/-- A value, in Ninja's value mode, running to the end of the line. -/
def readValue (l : List Char) : Option EvalString :=
  match l with
  | [] => some []
  | c :: r =>
    if c = '$' then
      match r with
      | [] => none
      | d :: r' =>
        if d = '$' || d = ' ' || d = ':' then (readValue r').map (consLit d)
        else if d = '{' then
          match _h : spanWhile isVarChar r' with
          | (n, e :: r'') =>
            if e = '}' && !n.isEmpty then
              (readValue r'').map (Seg.var (String.ofList n) :: ·)
            else none
          | (_, []) => none
        else if isSimpleVarChar d then
          match _h : spanWhile isSimpleVarChar r' with
          | (n, r'') => (readValue r'').map (Seg.var (String.ofList (d :: n)) :: ·)
        else none
    else if litChar c then (readValue r).map (consLit c)
    else none
termination_by l.length
decreasing_by
  all_goals simp
  all_goals first
    | omega
    | (have := spanWhile_length isVarChar r'; rw [_h] at this; simp at this; omega)
    | (have := spanWhile_length isSimpleVarChar r'; rw [_h] at this; simp at this; omega)

/-- Ninja's `ParseLet` on the text after any indentation: `key = value`. -/
def parseLet (l : List Char) : Option Binding := do
  let (k, r) ← readIdent l
  match r with
  | c :: v => if c = '=' then (readValue (eatSpaces v)).map (String.ofList k, ·) else none
  | [] => none

/-- An optional `|` section: a single `|`, not `||` or `|@`. -/
def section1 (l : List Char) : Option (List (List Char) × List Char) :=
  match l with
  | c :: r =>
    if c = '|' && r.head? != some '|' && r.head? != some '@' then readPaths (eatSpaces r)
    else some ([], l)
  | [] => some ([], [])

/-- An optional `||` section. -/
def section2 (l : List Char) : Option (List (List Char) × List Char) :=
  match l with
  | c :: d :: r =>
    if c = '|' && d = '|' && r.head? != some '@' then readPaths (eatSpaces r) else some ([], l)
  | _ => some ([], l)

/-- Character lists as paths. -/
def toPaths (ps : List (List Char)) : List Path := ps.map String.ofList

/-- A `build` line after the keyword and its spaces. Bindings come later. -/
def parseEdgeLine (l : List Char) : Option Edge := do
  let (outs, l) ← readPaths l
  let (iouts, l) ← section1 l
  match l with
  | c :: l =>
    if c = ':' then do
      let (rule, l) ← readIdent (eatSpaces l)
      let (ins, l) ← readPaths l
      let (iins, l) ← section1 l
      let (oo, l) ← section2 l
      if l.isEmpty then
        pure { outs := toPaths outs, implicitOuts := toPaths iouts, rule := String.ofList rule,
               ins := toPaths ins, implicitIns := toPaths iins, orderOnly := toPaths oo }
      else none
    else none
  | [] => none

/-- The first line of a statement. -/
inductive Header where
  | binding (b : Binding)
  | rule (name : String)
  | edge (e : Edge)
  | default (ps : List Path)

/-- Parse the first line of a statement: `rule name`, `build …`,
`default paths`, or `key = value`. Fails on any other keyword, on text after
a rule name or default targets, and on a line in no such form. -/
def parseHeader (l : List Char) : Option Header := do
  let (w, r) ← readIdent l
  if w = ['r', 'u', 'l', 'e'] then
    let (n, r) ← readIdent r
    if r.isEmpty then pure (.rule (String.ofList n)) else none
  else if w = ['b', 'u', 'i', 'l', 'd'] then
    (parseEdgeLine r).map .edge
  else if w = ['d', 'e', 'f', 'a', 'u', 'l', 't'] then
    let (ps, r) ← readPaths r
    if r.isEmpty then pure (.default (toPaths ps)) else none
  else if keywords.contains w then none
  else match r with
    | c :: v => if c = '=' then (readValue (eatSpaces v)).map (fun e => .binding (String.ofList w, e))
                else none
    | [] => none

/-- How a line starts: blank (spaces only), a comment (`#` after any spaces),
indented (a space, then other text), or at the top level. -/
inductive LineKind where
  | blank
  | comment
  | indented (rest : List Char)
  | top
  deriving DecidableEq

/-- The `LineKind` of a line. An indented line keeps its text after the
leading spaces. -/
def classify (l : List Char) : LineKind :=
  match eatSpaces l with
  | [] => .blank
  | c :: r =>
    if c = '#' then .comment
    else if l.head? = some ' ' then .indented (c :: r)
    else .top

/-- The indented lines after a header, skipping comment lines. A blank line or
an unindented line ends the block. -/
def takeBlock : List (List Char) → List (List Char) × List (List Char)
  | [] => ([], [])
  | l :: ls =>
    match classify l with
    | .comment => takeBlock ls
    | .indented r => ((takeBlock ls).1.cons r, (takeBlock ls).2)
    | _ => ([], l :: ls)

theorem takeBlock_length (ls : List (List Char)) : (takeBlock ls).2.length ≤ ls.length := by
  induction ls with
  | nil => simp [takeBlock]
  | cons l ls ih => unfold takeBlock; split <;> simp <;> omega

/-- Combine a header with its block of indented lines. -/
def finishStmt : Header → List (List Char) → Option Stmt
  | .binding b, [] => some (.binding b.1 b.2)
  | .default ps, [] => some (.default ps)
  | .rule n, blk => (blk.mapM parseLet).map (fun bs => .rule ⟨n, bs⟩)
  | .edge e, blk => (blk.mapM parseLet).map (fun bs => .edge { e with bindings := bs })
  | _, _ :: _ => none

/-- Parse lines into statements, after the statements `acc` already read with
context `c`. Blank and comment lines are skipped, and an indented line
outside a statement fails. Each statement must pass `Stmt.ok` in the
context of the statements before it. -/
def parseLines (ls : List (List Char)) (c : Ctx) (acc : List Stmt) : Option (List Stmt) :=
  match ls with
  | [] => some acc
  | l :: ls =>
    match classify l with
    | .blank => parseLines ls c acc
    | .comment => parseLines ls c acc
    | .indented _ => none
    | .top =>
      match parseHeader l with
      | none => none
      | some h =>
        match _hb : takeBlock ls with
        | (blk, rest) =>
          match finishStmt h blk with
          | none => none
          | some s => if s.ok c then parseLines rest (c.add s) (acc ++ [s]) else none
termination_by ls.length
decreasing_by
  all_goals first
    | (simp; done)
    | (have := takeBlock_length ls; rw [_hb] at this; simp at this ⊢; omega)

/-- Split a character list at every newline. The result has one more element
than there are newlines. -/
def splitLines : List Char → List (List Char)
  | [] => [[]]
  | c :: r =>
    if c = '\n' then [] :: splitLines r
    else match splitLines r with
      | l :: ls => (c :: l) :: ls
      | [] => [[c]]

/-- Parse a whole manifest, starting from the context that knows only the
`phony` rule; `none` if any line fails. -/
def parseChars (cs : List Char) : Option Manifest :=
  (parseLines (splitLines cs) {} []).map Manifest.mk

/-- The parser model: the manifest the text describes, or `none` when the
model rejects the text.
Gloss: the result of parsing {s} -/
def parse (s : String) : Option Manifest := parseChars s.toList

end Mise.Syntax
