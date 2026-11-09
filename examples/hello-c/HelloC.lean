import Mise.Frontend.Dsl

/-!
# hello-c

Two C files and a header, with the header listed by hand as an implicit
input of each compile.
-/

namespace HelloC
open Mise.Frontend

def build (ps : Params) : Build Unit := do
  let mainC ← source "main.c"
  let greetC ← source "greet.c"
  let greetH ← source "greet.h"
  let cc ← rule "cc" "cc $cflags -c $in -o $out" (description := "CC $out")
  let link ← rule "link" "cc $in -o $out" (description := "LINK $out")
  let cflags := [("cflags", ps.get "cflags" "-O2 -Wall")]
  let mainO ← edge1 cc "build/main.o" [mainC] (implicitIns := [greetH]) (vars := cflags)
  let greetO ← edge1 cc "build/greet.o" [greetC] (implicitIns := [greetH]) (vars := cflags)
  let hello ← edge1 link "build/hello" [mainO, greetO]
  defaults [hello]

end HelloC
