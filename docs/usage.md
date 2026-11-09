# Usage

`gen [--commands] [--set KEY=VALUE]... DIR` reads `DIR/mise.toml` and writes `DIR/build.ninja`. `--set` overrides a parameter declared in `[params]`, such as `--set cflags=-O0`. `--commands` prints each edge's command and writes nothing. In the Nix shell `gen` is on `PATH` after `lake build`; elsewhere run `lake exe gen`.

From `examples/hello-c/mise.toml`:

```toml
sources = ["main.c", "greet.c", "greet.h"]
defaults = ["build/hello"]

[params]
cflags = "-O2 -Wall"

[[rule]]
name = "cc"
command = "cc $cflags -c $in -o $out"
description = "CC $out"

[[build]]
rule = "cc"
outs = ["build/main.o"]
ins = ["main.c"]
implicit-ins = ["greet.h"]
params = ["cflags"]
```

A `[[rule]]` has `name`, `command`, and optionally `description`, `depfile = true` (the compiler reports what it read) and `restat = true` (the command leaves an unchanged output untouched). A `[[build]]` has `rule` and `outs`, and optionally `implicit-outs`, `ins`, `implicit-ins`, `order-only`, `vars` (edge variables with literal values) and `params` (edge variables bound to parameters). Inputs and defaults must name declared sources or outputs of earlier builds, and unknown keys are errors. For a depfile rule, `order-only` lists the generated files the command may read, as in `examples/gen-header/mise.toml`.

The same builds can be written in Lean with the library in `Mise/Frontend/Dsl.lean`, which is what `gen` calls after reading the TOML; `test/MiseTest/Fixtures.lean` has two examples.
