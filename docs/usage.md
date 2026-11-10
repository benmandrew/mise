# Usage

`mise build [--set KEY=VALUE]... [DIR] [-- NINJA_ARGS...]` reads `DIR/mise.toml`, writes `DIR/build.ninja`, and runs `ninja` in `DIR` with any arguments after `--`. Run it for every build and rebuild: it rewrites `build.ninja` only when the contents change. `--set` overrides a parameter declared in `[params]`, such as `--set cflags=-O0`. It applies only to that run, so a later `mise build` without it goes back to the default.

`mise gen` writes `build.ninja` without running Ninja. `mise gen --commands` prints each edge's command and writes nothing. `DIR` defaults to the current directory. In the Nix shell `mise` is on `PATH` after `lake build`; elsewhere run `lake exe mise`.

Running `ninja` directly also works, but it does not notice an edit to `mise.toml`.

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

A `[[rule]]` has `name`, `command`, and optionally `description`, `depfile = true` (the compiler reports what it read) and `restat = true` (the command leaves an unchanged output untouched). A `[[build]]` has `rule` and `outs`, and optionally `implicit-outs`, `ins`, `implicit-ins`, `order-only`, `vars` (edge variables with literal values) and `params` (edge variables bound to parameters). Inputs and defaults must name declared sources or outputs of earlier builds, and unknown keys are errors. The file is read as a subset of TOML: comments, bare and quoted keys, strings, booleans, decimal integers, arrays, inline tables, and `[table]` and `[[array]]` headers. Dotted keys, multi-line strings, floats and dates are rejected with a line and column. For a depfile rule, `order-only` lists the generated files the command may read, as in `examples/gen-header/mise.toml`.

The same builds can be written in Lean with the library in `Mise/Frontend/Dsl.lean`, which is what `mise` calls after reading the TOML; `test/MiseTest/Fixtures.lean` has two examples.
