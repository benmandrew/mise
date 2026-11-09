# Usage

`lake exe gen [--commands] [--set KEY=VALUE]... DIR` writes `DIR/build.ninja` from the build registered for `DIR` in `Main.lean`. `--set` passes a parameter, such as `--set cflags=-O0`. `--commands` prints each edge's command and writes nothing. The registered examples are `hello-c` and `gen-header`; the second needs `python3`.

A build is a `Build` action. From `examples/hello-c/HelloC.lean`:

```lean
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
```

`rule` also takes `depfile := true`, for compiles whose includes the compiler reports, and `restat := true`, for commands that leave an unchanged output untouched. `examples/gen-header/GenHeader.lean` uses both, with `dynEdge1` for compiles that read a generated header.
