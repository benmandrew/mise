import Mise.Frontend.Dsl
import Mise.Frontend.Glob
import Std.Data.HashMap

/-!
# TOML build descriptions

`parse` reads the subset of TOML that build descriptions use, and `decode`
turns the result into a build by calling the DSL's `source`, `rule` and
`edge`, so a TOML description passes the same checks as one written in
Lean, and `Build.graph` still decides `Graph.Valid`. The theorems are about
the resulting graph, so this file is outside the proofs: a mistake here can
give the wrong build, never an unsound one.

```toml
sources = ["greet.h"]
source-globs = ["src/*.c"]   # files matching a glob are sources too
defaults = ["build/hello"]   # outputs or aliases

[params]                 # defaults, overridden by `mise build --set cflags=...`
cflags = "-O2 -Wall"

[[rule]]
name = "cc"
command = "cc $cflags -c $in -o $out"
description = "CC $out"  # optional; also `depfile = true`, `restat = true`,
                         # and `wrap = false` to skip the command wrapper

[[build]]
rule = "cc"
outs = ["build/main.o"]
ins = ["main.c"]
implicit-ins = ["greet.h"]   # also `implicit-outs`, `order-only`
params = ["cflags"]          # edge variables bound to parameters
vars = { opt = "-g" }        # edge variables with literal values

[[build]]                    # one build per source or output matching foreach
rule = "cc"
foreach = "src/%.c"          # `%` matches a nonempty stem
outs = ["build/%.o"]         # `%` in a path is replaced by the stem
ins = ["src/%.c"]

[aliases]                    # `phony` edges: `ninja all` builds the targets
all = ["build/hello", "build/main.o"]
```

Inputs name sources or outputs of any `[[build]]`, in any order: `decode`
sorts the builds so that each comes after the builds it reads, and rejects
a cycle. An alias names sources, outputs or other aliases, flattened into a
list of paths. In a build without `foreach`, and in an alias, a path with
`%` stands for every source and output that matches it. Unknown keys are errors.

`decode` is pure. The caller expands each `source-globs` pattern with
`Glob.expand` and passes the results in.

The parser is written here so that the `mise` binary does not link Lean's
compiler: importing `Lake.Toml` made it 103 MB and added 23 ms to every
start. It supports comments, bare and quoted keys, basic strings with
escapes, literal strings, booleans, decimal integers, arrays (across lines,
with a trailing comma), inline tables, `[table]` and `[[array]]` headers.
It rejects with a position: dotted keys, dotted headers, multi-line strings,
floats, dates, and other integer forms. `test/MiseTest/Toml.lean` compares
it with Lake's parser, and `test/toml-diff.sh` with Python's `tomllib`.
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

/-- A control character other than tab: not allowed in strings or comments. -/
def isCtrl (c : Char) : Bool := (c.toNat < 0x20 && c != '\t') || c.toNat == 0x7f

/-- Skip a comment, up to the end of the line. A carriage return may only
start a CRLF line ending. -/
partial def comment : P Unit := do
  match ← peek with
  | some '\n' | none => pure ()
  | some '\r' => if (← peek2) == some '\n' then pure () else fail "control character in a comment"
  | some c => if isCtrl c then fail "control character in a comment" else discard next; comment

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

/-- A string or an array of strings. -/
def strOrStrs (what : String) : Value → Build (List String)
  | .str s => pure [s]
  | v => asStrs what v

/-- The `source-globs` patterns of a description, for the caller to expand. -/
def globPatterns (t : Table) : Except String (List String) :=
  match find? t "source-globs" with
  | some v => ((asStrs "source-globs" v).run' {})
  | none => pure []

/-- A `[[build]]` with its paths as strings, before handles are made. -/
structure Decl where
  what : String
  rule : String
  outs : List Path
  implicitOuts : List Path
  ins : List Path
  implicitIns : List Path
  orderOnly : List Path
  vars : List (String × String)
  deriving Inhabited

/-- The input lists of a build, with their keys. -/
def Decl.inLists (d : Decl) : List (String × List Path) :=
  [("ins", d.ins), ("implicit-ins", d.implicitIns), ("order-only", d.orderOnly)]

/-- The stem a `foreach` pattern with one `%` gives a path, if it matches. -/
def stemOf (pre suf p : String) : Option String :=
  if p.startsWith pre && p.endsWith suf && p.length > pre.length + suf.length then
    some ((p.drop pre.length).dropEnd suf.length).toString
  else none

/-- Replace every `%` in a path by the stem. -/
def subst (stem p : String) : String := stem.intercalate (p.splitOn "%")

/-- Order the builds so that each comes after the builds that produce its
inputs, keeping file order where it already does. -/
partial def sortDecls (ds : Array Decl) (srcs : Std.HashMap Path Unit) : Except String (List Decl) := do
  let mut prod : Std.HashMap Path Nat := {}
  for h : i in [:ds.size] do
    for o in ds[i].outs ++ ds[i].implicitOuts do
      unless prod.contains o do prod := prod.insert o i
  let mut deps : Array (List Nat) := #[]
  for d in ds do
    let mut js : List Nat := []
    for (k, ps) in d.inLists do
      for p in ps do
        if srcs.contains p then continue
        match prod.get? p with
        | some j => js := js ++ [j]
        | none => throw s!"{d.what}: {k}: {repr p} is not a source or a build output"
    deps := deps.push js
  -- 0 unvisited, 1 on the stack, 2 done
  let rec visit (stack : List Nat) (i : Nat) (st : Array Nat × Array Nat) :
      Except String (Array Nat × Array Nat) := do
    let (mark, out) := st
    match mark[i]! with
    | 2 => pure st
    | 1 =>
      let cyc := (i :: (stack.takeWhile (· != i)).reverse ++ [i]).map fun j => ds[j]!.what
      throw s!"cycle: {" -> ".intercalate cyc}"
    | _ =>
      let mut st := (mark.set! i 1, out)
      for j in deps[i]! do st ← visit (i :: stack) j st
      pure (st.1.set! i 2, st.2.push i)
  let mut st := (Array.replicate ds.size 0, #[])
  for i in [:ds.size] do st ← visit [] i st
  pure (st.2.toList.map fun i => ds[i]!)

/-- Flatten the aliases: each name maps to the paths it builds, with other
aliases replaced by their paths, without repeats. -/
partial def flattenAliases (as : List (String × List String)) : Except String (List (String × List String)) :=
  as.mapM fun (n, _) => do pure (n, ← go [n] n)
where
  go (stack : List String) (n : String) : Except String (List String) := do
    let ts := (as.lookup n).getD []
    let mut out : List String := []
    for t in ts do
      if (as.lookup t).isSome then
        if stack.contains t then
          throw s!"aliases: cycle: {" -> ".intercalate ((t :: stack).reverse)}"
        for p in ← go (t :: stack) t do
          unless out.contains p do out := out ++ [p]
      else unless out.contains t do out := out ++ [t]
    pure out

/-- Read a build description. `globs` gives the files each `source-globs`
pattern matches. -/
def decode (t : Table) (ps : Params) (globs : List (String × List Path) := []) : Build Unit := do
  checkKeys "mise.toml" t ["sources", "source-globs", "defaults", "params", "rule", "build", "aliases"]
  let prm ← params t ps
  let mut known : Std.HashMap Path Handle := {}
  let mut srcs : Std.HashMap Path Unit := {}
  for p in ← optStrs "mise.toml" t "sources" do
    known := known.insert p (← source p)
    srcs := srcs.insert p ()
  for pat in ← optStrs "mise.toml" t "source-globs" do
    if let .error e := Glob.components pat then throw s!"source-globs: {e}"
    let some fs := globs.lookup pat | throw s!"source-globs: {repr pat} was not expanded"
    let fs := fs.filter (!·.endsWith asideSuffix)
    if fs.isEmpty then throw s!"source-globs: {repr pat} matches no file"
    for p in fs do
      unless srcs.contains p do
        known := known.insert p (← source p)
        srcs := srcs.insert p ()
  let mut rules : List (String × RuleRef) := []
  for r in ← optTables t "rule" do
    let name ← reqStr "rule" r "name"
    let what := s!"rule {name}"
    checkKeys what r ["name", "command", "description", "depfile", "restat", "wrap"]
    let wrap ← match find? r "wrap" with
      | some _ => optBool what r "wrap"
      | none => pure true
    let rr ← rule name (← reqStr what r "command") (← optStr what r "description" "")
      (← optBool what r "depfile") (← optBool what r "restat") wrap
    rules := rules ++ [(name, rr)]
  -- Read every build; a `foreach` build is a template for later.
  let mut raw : Array (Decl ⊕ (String × List String × Decl)) := #[]
  for b in ← optTables t "build" do
    let outs ← optStrs "build" b "outs"
    let what := s!"build {repr outs}"
    checkKeys what b ["rule", "outs", "implicit-outs", "ins", "implicit-ins", "order-only", "vars", "params", "foreach"]
    let rn ← reqStr what b "rule"
    unless (rules.lookup rn).isSome do throw s!"{what}: no rule named {repr rn}"
    let vars ← match find? b "vars" with
      | some v => do
        let vt ← asTable s!"{what}: vars" v
        vt.mapM fun (k, v) => do pure (k, ← asStr s!"{what}: vars: {k}" v)
      | none => pure []
    let pvars ← (← optStrs what b "params").mapM fun k => match prm.lookup k with
      | some v => pure (k, v)
      | none => throw s!"{what}: params: no parameter {repr k} in [params]"
    let d : Decl := { what, rule := rn, outs, implicitOuts := ← optStrs what b "implicit-outs",
                      ins := ← optStrs what b "ins", implicitIns := ← optStrs what b "implicit-ins",
                      orderOnly := ← optStrs what b "order-only", vars := vars ++ pvars }
    match find? b "foreach" with
    | none => raw := raw.push (.inl d)
    | some v =>
      let pats ← strOrStrs s!"{what}: foreach" v
      if pats.isEmpty then throw s!"{what}: foreach: no patterns"
      for p in pats do
        unless (p.splitOn "%").length == 2 do throw s!"{what}: foreach: {repr p} must contain one %"
      unless (d.outs ++ d.implicitOuts).any (·.contains '%') do
        throw s!"{what}: foreach: no output contains %"
      raw := raw.push (.inr (what, pats, d))
  -- Expand each `foreach` build over the sources, the outputs of plain
  -- builds, and the outputs of earlier `foreach` builds.
  let mut avail : Array Path := srcs.keys.toArray.qsort (· < ·)
  for r in raw do
    if let .inl d := r then avail := avail ++ (d.outs ++ d.implicitOuts).toArray
  let mut decls : Array (Bool × Decl) := #[]
  for r in raw do
    match r with
    | .inl d => decls := decls.push (true, d)
    | .inr (what, pats, d) =>
      let mut stems : List String := []
      for pat in pats do
        let pre := (pat.splitOn "%").headD ""
        let suf := (pat.splitOn "%").getLastD ""
        for p in avail do
          if let some s := stemOf pre suf p then
            unless stems.contains s do stems := stems ++ [s]
      if stems.isEmpty then throw s!"{what}: foreach: no source or output matches {repr pats}"
      for s in stems do
        let f := (·.map (subst s))
        let i := { d with what := s!"build {repr (f d.outs)}", outs := f d.outs, implicitOuts := f d.implicitOuts,
                          ins := f d.ins, implicitIns := f d.implicitIns, orderOnly := f d.orderOnly }
        decls := decls.push (false, i)
        avail := avail ++ (i.outs ++ i.implicitOuts).toArray
  -- In a build without `foreach`, and in an alias, a path with `%` stands
  -- for every source or output that matches it, in path order, the build's
  -- own outputs excepted.
  let all := (avail.qsort (· < ·)).toList
  let expandPct (what : String) (own ps : List Path) : Build (List Path) := do
    let mut out : List Path := []
    for p in ps do
      if !p.contains '%' then out := out ++ [p]; continue
      let parts := p.splitOn "%"
      unless parts.length == 2 do throw s!"{what}: {repr p} must contain one %"
      let ms := all.filter fun q => (stemOf (parts.headD "") (parts.getLastD "") q).isSome && !own.contains q
      if ms.isEmpty then throw s!"{what}: no source or output matches {repr p}"
      for q in ms do unless out.contains q do out := out ++ [q]
    pure out
  let mut plainDecls : Array Decl := #[]
  for (plain, d) in decls do
    if plain then
      let ex (k : String) (ps : List Path) : Build (List Path) :=
        expandPct s!"{d.what}: {k}" (d.outs ++ d.implicitOuts) ps
      plainDecls := plainDecls.push { d with ins := ← ex "ins" d.ins, implicitIns := ← ex "implicit-ins" d.implicitIns,
                                             orderOnly := ← ex "order-only" d.orderOnly }
    else plainDecls := plainDecls.push d
  let sorted ← match sortDecls plainDecls srcs with
    | .ok l => pure l
    | .error e => throw e
  for d in sorted do
    let some r := rules.lookup d.rule | throw s!"{d.what}: no rule named {repr d.rule}"
    let handles (k : String) (ps : List Path) : Build (List Handle) :=
      ps.mapM fun p => match known.get? p with
        | some h => pure h
        | none => throw s!"{d.what}: {k}: {repr p} is not a source or a build output"
    let hs ← edge r d.outs (← handles "ins" d.ins) (← handles "implicit-ins" d.implicitIns)
      (← handles "order-only" d.orderOnly) d.implicitOuts d.vars
    for (p, h) in (d.outs ++ d.implicitOuts).zip hs do known := known.insert p h
  -- Aliases.
  let araw ← match find? t "aliases" with
    | some v => do
      let atbl ← asTable "aliases" v
      atbl.mapM fun (k, v) => do pure (k, ← expandPct s!"aliases: {k}" [] (← asStrs s!"aliases: {k}" v))
    | none => pure []
  let flat ← match flattenAliases araw with
    | .ok l => pure l
    | .error e => throw e
  let mut aliasRefs : List (String × AliasRef) := []
  for (n, ts) in flat do
    let hs ← ts.mapM fun p => match known.get? p with
      | some h => pure h
      | none => throw s!"aliases: {n}: {repr p} is not a source, a build output or an alias"
    aliasRefs := aliasRefs ++ [(n, ← alias n hs)]
  for p in ← optStrs "mise.toml" t "defaults" do
    match aliasRefs.lookup p, known.get? p with
    | some a, _ => defaults [] [a]
    | none, some h =>
      if srcs.contains p then throw s!"defaults: {repr p} is a source"
      defaults [h]
    | none, none => throw s!"defaults: {repr p} is not a build output or an alias"

/-- Read and check a TOML build description, with the files each
`source-globs` pattern matches. -/
def loadWith (text : String) (ps : Params) (globs : List (String × List Path)) : Except String ValidGraph := do
  (decode (← parse text) ps globs).graph

/-- Read and check a TOML build description that has no `source-globs`. -/
def load (text : String) (ps : Params := []) : Except String ValidGraph := loadWith text ps []

end Mise.Frontend.Toml
