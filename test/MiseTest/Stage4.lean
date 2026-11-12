import Mise.Frontend.Dsl
import MiseTest.Fixtures

/-! Stage 4: the DSL on hello-c and on graphs the builder must reject. -/

namespace MiseTest.Stage4
open Mise.Frontend Mise.Syntax

def hello : Graph := match (Fixtures.helloC []).graph with
  | .ok g => g.1
  | .error _ => {}

#guard decide hello.Valid
#guard decide (emit hello).WellFormed
#guard parse (print (emit hello)) == some (emit hello)
/-- What Ninja makes of a wrapped command with one output and no implicit
outputs. -/
def wrapped (out cmd : String) : String :=
  (((wrapCommand false cmd).replace "$out" out).replace "${mise_iouts}" "").replace "$$" "$"

-- Every command goes through the wrapper.
#guard hello.edges.map hello.cmd ==
  [wrapped "build/main.o" "cc -O2 -Wall -c main.c -o build/main.o",
   wrapped "build/greet.o" "cc -O2 -Wall -c greet.c -o build/greet.o",
   wrapped "build/hello" "cc build/main.o build/greet.o -o build/hello"]
#guard (hello.edges.map hello.cmd).all (·.startsWith "set -- build/")
-- `wrap := false` emits the command as written.
#guard match (do let r ← rule "r" "touch $out" (wrap := false); let _ ← edge1 r "a").graph with
  | .ok g => g.1.edges.map g.1.cmd == ["touch a"]
  | .error _ => false
-- The Ninja model evaluates the emitted commands the same way.
#guard (emit hello).commands.map (·.2) == hello.edges.map hello.cmd

-- Shell quoting of awkward paths.
#guard shellEscape "a b" == "'a b'"
#guard shellEscape "it's" == "'it'\\''s'"
#guard shellEscape "src/x-1.c" == "src/x-1.c"

def rejects (b : Build Unit) : Bool := match b.graph with
  | .ok _ => false
  | .error _ => true

-- An undeclared input cannot be named: handles come only from the builder.
#guard rejects do
  let r ← rule "r" "touch $out"
  let a ← edge1 r "a"
  let _ ← edge1 r "a" [a]
#guard rejects do
  let r ← rule "r" "touch $out"
  let _ ← edge r [] []
#guard rejects do
  let _ ← source "x"
  let _ ← source "x"
#guard rejects do
  let _ ← rule "phony" "x"
#guard rejects do
  let r ← rule "r" "touch $out"
  let _ ← edge1 r "a" (vars := [("command", "rm -rf /")])
#guard rejects do
  let _ ← rule "r" "echo $command"
-- The emitted version binding is in the file scope, so neither a template
-- nor an edge may name it.
#guard rejects do
  let _ ← rule "r" "echo $ninja_required_version > $out"
#guard rejects do
  let r ← rule "r" "touch $out"
  let _ ← edge1 r "a" (vars := [("ninja_required_version", "1.2")])
#guard (emit hello).stmts.head? == some (.binding "ninja_required_version" [.lit "1.12.1"])
#guard rejects do
  let _ ← source "./x"
#guard rejects do
  let _ ← source "a|b"
-- The wrapper's `.mise-old` files cannot be declared.
#guard rejects do
  let _ ← source "x.mise-old"
#guard rejects do
  let r ← rule "r" "touch $out"
  let _ ← edge1 r "a.mise-old"

/-! Aliases: `phony` edges after the edges, which the Ninja model leaves out. -/

def withAlias : Graph := match (do
    let a ← source "a.c"
    let r ← rule "cc" "cc -c $in -o $out"
    let o ← edge1 r "a.o" [a]
    let al ← alias "objs" [o, a]
    defaults [] [al]).graph with
  | .ok g => g.1
  | .error _ => {}

#guard decide withAlias.Valid
#guard decide (emit withAlias).WellFormed
#guard parse (print (emit withAlias)) == some (emit withAlias)
#guard (emit withAlias).elab.edges.length == 2
#guard (emit withAlias).elab.cmdEdges.length == 1
#guard (emit withAlias).commands.map (·.2) == withAlias.edges.map withAlias.cmd
#guard rejects do
  let a ← source "a.c"
  let _ ← alias "a.c" [a]
#guard rejects do
  let _ ← alias "x" []
#guard rejects do
  let a ← source "a.c"
  let _ ← alias "x" [a]
  let _ ← source "x"
-- `Graph.check` rejects what the builder would, for graphs made directly.
#guard !decide ({ withAlias with aliases := [⟨"a.o", ["a.c"]⟩] } : Graph).Valid
#guard !decide ({ withAlias with aliases := [⟨"x", []⟩] } : Graph).Valid
#guard !decide ({ withAlias with aliases := [⟨"x", ["b.c"]⟩] } : Graph).Valid
#guard !decide ({ withAlias with aliases := [⟨"x", ["a.c"]⟩, ⟨"x", ["a.o"]⟩] } : Graph).Valid
#guard !decide ({ withAlias with defaults := ["y"] } : Graph).Valid

end MiseTest.Stage4
