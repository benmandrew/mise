import Lake.Toml
import Mise.Frontend.Dsl

/-!
# TOML build descriptions

`decode` reads a build description from TOML by calling the DSL's `source`,
`rule` and `edge`, so a TOML description passes the same checks as one
written in Lean, and `Build.graph` still decides `Graph.Valid`. The theorems
are about the resulting graph, so this file is outside the proofs: a mistake
here can give the wrong build, never an unsound one.

```toml
sources = ["main.c", "greet.h"]
defaults = ["build/hello"]

[params]                 # defaults, overridden by `gen --set cflags=...`
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
-/

namespace Mise.Frontend.Toml
open Mise.Frontend Mise.Syntax

abbrev Table := Lake.Toml.Table
abbrev Value := Lake.Toml.Value

def keyName (n : Lean.Name) : String := n.toString (escape := false)

def find? (t : Table) (k : String) : Option Value := t.find? (Lean.Name.mkSimple k)

def checkKeys (what : String) (t : Table) (allowed : List String) : Build Unit := do
  for (k, _) in t.items do
    unless allowed.contains (keyName k) do throw s!"{what}: unknown key {repr (keyName k)}"

def asStr (what : String) : Value → Build String
  | .string _ s => pure s
  | _ => throw s!"{what}: expected a string"

def asStrs (what : String) : Value → Build (List String)
  | .array _ xs => xs.toList.mapM (asStr what)
  | _ => throw s!"{what}: expected an array of strings"

def asTable (what : String) : Value → Build Table
  | .table _ t => pure t
  | _ => throw s!"{what}: expected a table"

def asTables (what : String) : Value → Build (List Table)
  | .array _ xs => xs.toList.mapM (asTable what)
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
  | some (.boolean _ b) => pure b
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
      pt.items.toList.mapM fun (k, v) => do pure (keyName k, ← asStr s!"params: {keyName k}" v)
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
        vt.items.toList.mapM fun (k, v) => do pure (keyName k, ← asStr s!"{what}: vars: {keyName k}" v)
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

/-- Parse TOML text. -/
def parse (text : String) (fileName : String := "mise.toml") : IO (Except String Table) := do
  match ← (Lake.Toml.loadToml (Lean.Parser.mkInputContext text fileName)).toBaseIO with
  | .ok t => pure (.ok t)
  | .error log => pure (.error ("\n".intercalate (← log.toList.mapM (·.toString))))

/-- Read and check a TOML build description. -/
def load (text : String) (ps : Params := []) (fileName : String := "mise.toml") : IO (Except String ValidGraph) := do
  match ← parse text fileName with
  | .error e => pure (.error e)
  | .ok t => pure (decode t ps).graph

end Mise.Frontend.Toml
