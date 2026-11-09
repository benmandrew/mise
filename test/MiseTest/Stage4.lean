import Mise.Frontend.Dsl
import HelloC

/-! Stage 4: the DSL on hello-c and on graphs the builder must reject. -/

namespace MiseTest.Stage4
open Mise.Frontend Mise.Syntax

def hello : Graph := match (HelloC.build []).graph with
  | .ok g => g.1
  | .error _ => {}

#guard decide hello.Valid
#guard decide (emit hello).WellFormed
#guard parse (print (emit hello)) == some (emit hello)
#guard hello.edges.map hello.cmd ==
  ["cc -O2 -Wall -c main.c -o build/main.o", "cc -O2 -Wall -c greet.c -o build/greet.o",
   "cc build/main.o build/greet.o -o build/hello"]
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
#guard rejects do
  let _ ← source "./x"
#guard rejects do
  let _ ← source "a|b"

end MiseTest.Stage4
