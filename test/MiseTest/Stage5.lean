import Mise.Model.Dsl
import MiseTest.Fixtures

/-! Stage 5: hello-c in the Ninja model, with a symbolic `exec` that records
which command ran on which inputs. -/

namespace MiseTest.Stage5
open Mise Mise.Model Mise.Frontend Mise.Syntax

/-- A symbolic command run: the command applied to the contents of its inputs. -/
def exec (cmd : String) (vs : List String) : List String := [cmd ++ "(" ++ ",".intercalate vs ++ ")"]

/-- The model semantics that uses `exec` and has no dynamic dependencies. -/
def sem : Sem String := { exec, dyn := fun _ => .pure [] }

/-- The valid `hello-c` graph, or the empty graph if it is rejected. -/
def vg : ValidGraph := match (Fixtures.helloC []).graph with
  | .ok g => g
  | .error _ => ⟨{}, by decide⟩

/-- The Ninja manifest of `vg`. -/
def m : Manifest := emit vg.1

/-- The source files of `hello-c`. -/
def srcs : List Path := ["main.c", "greet.c", "greet.h"]

/-- The starting state: every source present, no logs, clock at zero. -/
def st0 : St String :=
  { fs := fun p => if p ∈ srcs then some (p ++ "@1", 0) else none, log := fun _ => none, clock := 0 }

/-- The outputs of the edges that a build from `st` runs, in order. -/
def outsRun (st : St String) : List (List Path) := (buildTrace sem m.medges st).2.map (·.outs)

/-- Contents of every output agree with a clean build. -/
def agreesClean (st : St String) : Bool :=
  let r := ninjaBuild sem m st
  ["build/main.o", "build/greet.o", "build/hello"].all fun k =>
    r.content k == BuildSpec.cleanBuild (vg.1.acyclic sem vg.2 fun _ _ _ => .pure _) st.content k

/-- The state after a first full build. -/
def b1 := ninjaBuild sem m st0

#guard outsRun st0 == [["build/main.o"], ["build/greet.o"], ["build/hello"]]
#guard agreesClean st0
-- A second build does nothing.
#guard outsRun b1 == []
-- Editing a `.c` file rebuilds its object and the link.
#guard outsRun (b1.edit "greet.c" "greet.c@2") == [["build/greet.o"], ["build/hello"]]
#guard agreesClean (b1.edit "greet.c" "greet.c@2")
-- Editing the shared header rebuilds everything.
#guard outsRun (b1.edit "greet.h" "greet.h@2") == [["build/main.o"], ["build/greet.o"], ["build/hello"]]
#guard agreesClean (b1.edit "greet.h" "greet.h@2")
-- Deleting an object rebuilds it and the link, and nothing else.
#guard outsRun { b1 with fs := fun p => if p = "build/main.o" then none else b1.fs p } ==
  [["build/main.o"], ["build/hello"]]
-- An interrupted build followed by a full build agrees with a clean build.
#guard agreesClean (buildTrace sem (m.medges.take 1) (b1.edit "greet.h" "greet.h@3")).1

end MiseTest.Stage5
