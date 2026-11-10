import Mise.Frontend.Dsl

/-!
# TOML build descriptions

`parse` reads the subset of TOML that build descriptions use, and `decode`
turns the result into a build by calling the DSL's `source`, `rule` and
`edge`, so a TOML description passes the same checks as one written in
Lean, and `Build.graph` still decides `Graph.Valid`. The theorems are about
the resulting graph, so this file is outside the proofs: a mistake here can
give the wrong build, never an unsound one.

```toml
sources = ["main.c", "greet.h"]
defaults = ["build/hello"]

[params]                 # defaults, overridden by `mise build --set cflags=...`
cflags = "-O2 -Wall"

[[rule]]
name = "cc"
command = "cc $cflags -c $in -o $out"
description = "CC $out"  # optional; also `depfile = true`, `restat = true`

[[build]]
rule = "cc"
outs = ["build/main.o"]
ins = ["main.c"]
implicit-ins = ["greet.h"]   # also `implicit-outs`, `order-only`
params = ["cflags"]          # edge variables bound to parameters
vars = { opt = "-g" }        # edge variables with literal values
```

Inputs and defaults name declared sources or outputs of earlier `[[build]]`
entries. Unknown keys are errors.

The parser is written here so that the `mise` binary does not link Lean's
compiler: importing `Lake.Toml` made it 103 MB and added 23 ms to every
start. It supports comments, bare and quoted keys, basic strings with
escapes, literal strings, booleans, decimal integers, arrays (across lines,
with a trailing comma), inline tables, `[table]` and `[[array]]` headers.
It rejects with a position: dotted keys, dotted headers, multi-line strings,
floats, dates, and other integer forms. `test/MiseTest/Toml.lean` compares
it with Lake's parser.
-/

namespace Mise.Frontend.Toml
open Mise.Frontend Mise.Syntax

inductive Value where
  | str (s : String)
  | bool (b : Bool)
  | int (n : Int)
  | arr (xs : List Value)
  | table (t : List (String × Value))
  deriving Repr, BEq

instance : Inhabited Value := ⟨.bool false⟩

/-- A table, with its keys in file order. -/
abbrev Table := List (String × Value)

def find? (t : Table) (k : String) : Option Value := t.lookup k

/-! ## Parser -/

structure Pos where
  cs : List Char
  line : Nat := 1
  col : Nat := 1

abbrev P := StateT Pos (Except String)

def fail (msg : String) : P α := do
  let s ← get
  throw s!"{s.line}:{s.col}: {msg}"

def peek : P (Option Char) := do return (← get).cs.head?

def peek2 : P (Option Char) := do return ((← get).cs.drop 1).head?

def next : P Char := do
  let s ← get
  match s.cs with
  | c :: r =>
    set (if c == '\n' then { cs := r, line := s.line + 1, col := 1 : Pos } else { s with cs := r, col := s.col + 1 })
    return c
  | [] => fail "unexpected end of file"

def expect (c : Char) : P Unit := do
  if (← peek) == some c then discard next else fail s!"expected '{c}'"

/-- Skip spaces and tabs. -/
partial def ws : P Unit := do
  if (← peek) == some ' ' || (← peek) == some '\t' then discard next; ws

/-- Skip a comment, up to the end of the line. -/
partial def comment : P Unit := do
  match ← peek with
  | some '\n' | none => pure ()
  | some _ => discard next; comment

/-- Skip whitespace, newlines and comments. -/
partial def wsnl : P Unit := do
  match ← peek with
  | some ' ' | some '\t' | some '\n' => discard next; wsnl
  | some '\r' => if (← peek2) == some '\n' then discard next; wsnl
  | some '#' => comment; wsnl
  | _ => pure ()

/-- The rest of a line after a key-value pair or a header. -/
def lineEnd : P Unit := do
  ws
  if (← peek) == some '#' then comment
  match ← peek with
  | none => pure ()
  | some '\n' => discard next
  | some '\r' => discard next; expect '\n'
  | some _ => fail "expected the end of the line"

def isCtrl (c : Char) : Bool := (c.toNat < 0x20 && c != '\t') || c.toNat == 0x7f

def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def unicodeEscape (n : Nat) : P Char := do
  let mut v := 0
  for _ in [0:n] do
    match hexDigit? (← next) with
    | some d => v := 16 * v + d
    | none => fail "expected a hexadecimal digit"
  if h : v.isValidChar then return Char.ofNatAux v h else fail "escape is not a Unicode scalar value"

partial def basicBody (acc : String) : P String := do
  if (← peek).isNone then fail "unterminated string"
  match ← next with
  | '"' => pure acc
  | '\\' =>
    let c ← match ← next with
      | 'b' => pure '\x08' | 't' => pure '\t' | 'n' => pure '\n' | 'f' => pure '\x0c'
      | 'r' => pure '\r' | '"' => pure '"' | '\\' => pure '\\'
      | 'u' => unicodeEscape 4 | 'U' => unicodeEscape 8
      | _ => fail "unknown escape"
    basicBody (acc.push c)
  | c => if isCtrl c then fail "control character or newline in a string" else basicBody (acc.push c)

partial def literalBody (acc : String) : P String := do
  if (← peek).isNone then fail "unterminated string"
  match ← next with
  | '\'' => pure acc
  | c => if isCtrl c then fail "control character or newline in a string" else literalBody (acc.push c)

/-- A string, opened by `q`. -/
def string (q : Char) : P String := do
  expect q
  if (← peek) == some q && (← peek2) == some q then fail "multi-line strings are not supported"
  if q == '"' then basicBody "" else literalBody ""

def isBare (c : Char) : Bool := c.isAlphanum || c == '_' || c == '-'

partial def takeWhile (p : Char → Bool) (acc : String) : P String := do
  match ← peek with
  | some c => if p c then discard next; takeWhile p (acc.push c) else pure acc
  | none => pure acc

/-- A key; dotted keys are rejected. -/
def key : P String := do
  let k ← match ← peek with
    | some '"' => string '"'
    | some '\'' => string '\''
    | _ => do
      let k ← takeWhile isBare ""
      if k.isEmpty then fail "expected a key" else pure k
  ws
  if (← peek) == some '.' then fail "dotted keys are not supported"
  pure k

/-- A decimal integer, with optional sign and `_` between digits. -/
def integer (tok : String) : Option Int :=
  let (neg, body) := match tok.toList with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  let groups := (String.ofList body).splitOn "_"
  if groups.any (fun g => g.isEmpty || !g.all Char.isDigit) then none
  else if body.length > 1 && body.head? == some '0' then none
  else
    let n := (String.join groups).toNat!
    some (if neg then -(n : Int) else n)

def addKey (what : String) (t : Table) (k : String) (v : Value) : P Table := do
  if (t.lookup k).isSome then fail s!"duplicate key {repr k}{what}" else pure (t ++ [(k, v)])

mutual
partial def value : P Value := do
  match ← peek with
  | some '"' => .str <$> string '"'
  | some '\'' => .str <$> string '\''
  | some '[' => discard next; .arr <$> arrayItems #[]
  | some '{' => discard next; ws; .table <$> inlineItems []
  | some _ =>
    let tok ← takeWhile (fun c => c.isAlphanum || c == '_' || c == '-' || c == '+' || c == '.' || c == ':') ""
    match tok with
    | "true" => pure (.bool true)
    | "false" => pure (.bool false)
    | "" => fail "expected a value"
    | _ => match integer tok with
      | some n => pure (.int n)
      | none => fail s!"unsupported value {tok}: expected a string, boolean, decimal integer, array or table"
  | none => fail "expected a value"

partial def arrayItems (acc : Array Value) : P (List Value) := do
  wsnl
  if (← peek) == some ']' then discard next; return acc.toList
  let v ← value
  wsnl
  match ← peek with
  | some ',' => discard next; arrayItems (acc.push v)
  | some ']' => discard next; return (acc.push v).toList
  | _ => fail "expected ',' or ']'"

partial def inlineItems (acc : Table) : P Table := do
  if acc.isEmpty && (← peek) == some '}' then discard next; return acc
  let k ← key
  expect '='
  ws
  let acc ← addKey " in an inline table" acc k (← value)
  ws
  match ← peek with
  | some ',' => discard next; ws; inlineItems acc
  | some '}' => discard next; return acc
  | _ => fail "expected ',' or '}'"
end

/-! A document is the top-level table followed by sections. The section being
read is held apart and added to the root when the next header starts. -/

structure Doc where
  root : Table := []
  /-- Names created by `[[name]]` headers. -/
  arrays : List String := []
  /-- The open section: whether it is `[[...]]`, its name, and its header's position. -/
  cur : Option (Bool × String × String) := none
  /-- The keys read since the last header. -/
  kvs : Table := []

def flush (d : Doc) : Except String Doc := do
  match d.cur with
  | none => pure { d with root := d.root ++ d.kvs, kvs := [] }
  | some (isArr, name, pos) =>
    let kvs := d.kvs
    let d := { d with cur := none, kvs := [] }
    if isArr && d.arrays.contains name then
      pure { d with root := d.root.map fun (k, v) => match v with
        | .arr xs => if k == name then (k, .arr (xs ++ [.table kvs])) else (k, v)
        | _ => (k, v) }
    else if (d.root.lookup name).isSome then throw s!"{pos}: {repr name} is already defined"
    else if isArr then pure { d with root := d.root ++ [(name, .arr [.table kvs])], arrays := name :: d.arrays }
    else pure { d with root := d.root ++ [(name, .table kvs)] }

def liftE (x : Except String α) : P α := match x with
  | .ok a => pure a
  | .error e => throw e

partial def doc (d : Doc) : P Doc := do
  wsnl
  match ← peek with
  | none => liftE (flush d)
  | some '[' =>
    let s ← get
    let pos := s!"{s.line}:{s.col}"
    discard next
    let isArr := (← peek) == some '['
    if isArr then discard next
    ws
    let name ← key
    expect ']'
    if isArr then expect ']'
    lineEnd
    -- The section before this header is complete.
    let d ← liftE (flush d)
    doc { d with cur := some (isArr, name, pos) }
  | some _ =>
    let k ← key
    expect '='
    ws
    let v ← value
    lineEnd
    doc { d with kvs := ← addKey "" d.kvs k v }

/-- Parse TOML text. Errors carry a `line:column` position. -/
def parse (text : String) : Except String Table :=
  match (doc {}).run { cs := text.toList } with
  | .ok (d, _) => .ok d.root
  | .error e => .error e

def checkKeys (what : String) (t : Table) (allowed : List String) : Build Unit := do
  for (k, _) in t do
    unless allowed.contains k do throw s!"{what}: unknown key {repr k}"

def asStr (what : String) : Value → Build String
  | .str s => pure s
  | _ => throw s!"{what}: expected a string"

def asStrs (what : String) : Value → Build (List String)
  | .arr xs => xs.mapM (asStr what)
  | _ => throw s!"{what}: expected an array of strings"

def asTable (what : String) : Value → Build Table
  | .table t => pure t
  | _ => throw s!"{what}: expected a table"

def asTables (what : String) : Value → Build (List Table)
  | .arr xs => xs.mapM (asTable what)
  | _ => throw s!"{what}: expected an array of tables"

def reqStr (what : String) (t : Table) (k : String) : Build String :=
  match find? t k with
  | some v => asStr s!"{what}: {k}" v
  | none => throw s!"{what}: missing {k}"

def optStr (what : String) (t : Table) (k : String) (d : String) : Build String :=
  match find? t k with
  | some v => asStr s!"{what}: {k}" v
  | none => pure d

def optBool (what : String) (t : Table) (k : String) : Build Bool :=
  match find? t k with
  | some (.bool b) => pure b
  | some _ => throw s!"{what}: {k}: expected true or false"
  | none => pure false

def optStrs (what : String) (t : Table) (k : String) : Build (List String) :=
  match find? t k with
  | some v => asStrs s!"{what}: {k}" v
  | none => pure []

def optTables (t : Table) (k : String) : Build (List Table) :=
  match find? t k with
  | some v => asTables k v
  | none => pure []

/-- The parameters: the defaults in `[params]`, with `--set` values applied. -/
def params (t : Table) (ps : Params) : Build Params := do
  let defs ← match find? t "params" with
    | some v => do
      let pt ← asTable "params" v
      pt.mapM fun (k, v) => do pure (k, ← asStr s!"params: {k}" v)
    | none => pure []
  for (k, _) in ps do
    unless (defs.lookup k).isSome do throw s!"--set {k}: no such parameter in [params]"
  pure (defs.map fun (k, d) => (k, ps.get k d))

/-- Read a build description. -/
def decode (t : Table) (ps : Params) : Build Unit := do
  checkKeys "mise.toml" t ["sources", "defaults", "params", "rule", "build"]
  let prm ← params t ps
  let mut known : List (Path × Handle) := []
  for p in ← optStrs "mise.toml" t "sources" do
    known := known ++ [(p, ← source p)]
  let mut rules : List (String × RuleRef) := []
  for r in ← optTables t "rule" do
    let name ← reqStr "rule" r "name"
    let what := s!"rule {name}"
    checkKeys what r ["name", "command", "description", "depfile", "restat"]
    let rr ← rule name (← reqStr what r "command") (← optStr what r "description" "")
      (← optBool what r "depfile") (← optBool what r "restat")
    rules := rules ++ [(name, rr)]
  for b in ← optTables t "build" do
    let outs ← optStrs "build" b "outs"
    let what := s!"build {repr outs}"
    checkKeys what b ["rule", "outs", "implicit-outs", "ins", "implicit-ins", "order-only", "vars", "params"]
    let rn ← reqStr what b "rule"
    let some r := rules.lookup rn | throw s!"{what}: no rule named {repr rn}"
    let handles (k : String) : Build (List Handle) := do
      (← optStrs what b k).mapM fun p => match known.lookup p with
        | some h => pure h
        | none => throw s!"{what}: {k}: {repr p} is not a source or an output of an earlier build"
    let vars ← match find? b "vars" with
      | some v => do
        let vt ← asTable s!"{what}: vars" v
        vt.mapM fun (k, v) => do pure (k, ← asStr s!"{what}: vars: {k}" v)
      | none => pure []
    let pvars ← (← optStrs what b "params").mapM fun k => match prm.lookup k with
      | some v => pure (k, v)
      | none => throw s!"{what}: params: no parameter {repr k} in [params]"
    let implicitOuts ← optStrs what b "implicit-outs"
    let hs ← edge r outs (← handles "ins") (← handles "implicit-ins") (← handles "order-only") implicitOuts
      (vars ++ pvars)
    known := known ++ (outs ++ implicitOuts).zip hs
  let ds ← (← optStrs "mise.toml" t "defaults").mapM fun p => match known.lookup p with
    | some h => pure h
    | none => throw s!"defaults: {repr p} is not a source or a build output"
  defaults ds

/-- Read and check a TOML build description. -/
def load (text : String) (ps : Params := []) : Except String ValidGraph := do
  (decode (← parse text) ps).graph

end Mise.Frontend.Toml
