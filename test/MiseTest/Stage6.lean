import Mise.Model.Dsl
import MiseTest.Fixtures

/-! Stage 6: gen-header in the Ninja model. A source's contents are words;
a word `+h` means the file includes `h`. A compile reads its `.c` file, then
each header it includes, with `config.h` found in `build/`. -/

namespace MiseTest.Stage6
open Mise Mise.Model Mise.Frontend Mise.Syntax

/-- A symbolic command run: the command applied to the contents of its inputs. -/
def exec (cmd : String) (vs : List String) : List String := [cmd ++ "(" ++ ",".intercalate vs ++ ")"]

/-- The file after `-c` in a compile command. -/
def srcOf (cmd : String) : Path :=
  match (cmd.splitOn " ").dropWhile (· != "-c") with
  | _ :: f :: _ => f
  | _ => ""

/-- The headers a file's contents include, with `config.h` found in `build/`. -/
def includes (c : String) : List Path :=
  ((c.splitOn " ").filter (·.startsWith "+")).map fun w =>
    let h := w.drop 1 |>.toString
    if h == "config.h" then "build/config.h" else h

/-- The dynamic task of a compile command: read its source, then each header it includes. -/
def compile (cmd : String) : Task Path String (List String) :=
  .fetch (srcOf cmd) fun c => (fetchAll (includes c)).bind fun vs => .pure (exec cmd (c :: vs))

/-- The model semantics with `exec` and the compile tasks. -/
def sem : Sem String := { exec, dyn := compile }

/-- The valid `gen-header` graph, or the empty graph if it is rejected. -/
def vg : ValidGraph := match (Fixtures.genHeader []).graph with
  | .ok g => g
  | .error _ => ⟨{}, by decide⟩

/-- The Ninja manifest of `vg`. -/
def m : Manifest := emit vg.1

/-- The files that a build makes. -/
def products : List Path := ["build/config.h", "build/main.o", "build/util.o", "build/app"]

/-- The source files with their contents. -/
def srcs : List (Path × String) :=
  [("main.c", "main@1 +config.h +util.h"), ("util.c", "util@1 +config.h +util.h"), ("util.h", "util.h@1"),
   ("extra.h", "extra.h@1"), ("config.in", "config@1"), ("gen-config.py", "gen@1")]

/-- The starting state: sources present at time zero, no logs. -/
def st0 : St String :=
  { fs := fun p => (srcs.lookup p).map (·, 0), log := fun _ => none, clock := 0 }

/-- The first output of each edge that a build from `st` runs, in order. -/
def ran (st : St String) : List Path := (buildTrace sem m.medges st).2.map fun e => e.outs.headD ""

/-- The same sources with empty logs. -/
def fresh (st : St String) : St String :=
  { fs := fun p => if (srcs.lookup p).isSome then some (st.content p, 0) else none, log := fun _ => none, clock := 0 }

/-- An incremental build agrees with a build from empty logs. -/
def agreesClean (st : St String) : Bool :=
  let a := ninjaBuild sem m st
  let b := ninjaBuild sem m (fresh st)
  products.all fun k => a.content k == b.content k

/-- The state after a first full build. -/
def b1 := ninjaBuild sem m st0
/-- The state after the first build and an edit of `main.c` that adds an include. -/
def b2 := ninjaBuild sem m (b1.edit "main.c" "main@2 +config.h +util.h +extra.h")

#guard m.medges.map (·.dyn) == [false, true, true, false]
#guard m.medges.map (·.oo) == [[], ["build/config.h"], ["build/config.h"], []]
#guard ran st0 == products
-- The deps log holds what each compile read.
#guard b1.deps "build/main.o" == some ["main.c", "build/config.h", "util.h"]
#guard ran b1 == []
-- `extra.h` is not included yet, so editing it rebuilds nothing.
#guard ran (b1.edit "extra.h" "extra.h@2") == []
-- Adding the include rebuilds `main.o`, and from then on `extra.h` counts.
#guard ran (b1.edit "main.c" "main@2 +config.h +util.h +extra.h") == ["build/main.o", "build/app"]
#guard ran (b2.edit "extra.h" "extra.h@2") == ["build/main.o", "build/app"]
#guard agreesClean (b2.edit "extra.h" "extra.h@2")
-- Removing it again: `extra.h` stops counting after the rebuild.
#guard ran ((ninjaBuild sem m (b2.edit "main.c" "main@3 +config.h +util.h")).edit "extra.h" "extra.h@3") == []
-- The generated header's input reaches both compiles.
#guard ran (b1.edit "config.in" "config@2") == products
#guard agreesClean (b1.edit "config.in" "config@2")
-- Editing a header both files include rebuilds both objects.
#guard ran (b1.edit "util.h" "util.h@2") == ["build/main.o", "build/util.o", "build/app"]
#guard agreesClean (b1.edit "util.h" "util.h@2")

-- A depfile edge has one explicit output, since `${out}.d` must name one
-- file; implicit outputs are allowed.
/-- A one-edge graph with a depfile rule, given its outputs and implicit outputs. -/
def dynG (outs implicitOuts : List Path) : Graph :=
  { sources := ["a.c"], rules := [{ name := "cc", command := [.lit "cc"], depfile := true }],
    edges := [{ rule := "cc", outs, implicitOuts, ins := ["a.c"] }] }

#guard (dynG ["a.o"] ["a.h"]).check
#guard !(dynG ["a.o", "b.o"] []).check

end MiseTest.Stage6
