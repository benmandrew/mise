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

A `[[rule]]` has `name`, `command`, and optionally `description`, `depfile = true` (the compiler reports what it read), `restat = true` (an output whose contents do not change keeps its old file, and its dependents do not rebuild) and `wrap = false` (below). A `[[build]]` has `rule` and `outs`, and optionally `implicit-outs`, `ins`, `implicit-ins`, `order-only`, `vars` (edge variables with literal values) and `params` (edge variables bound to parameters). Inputs and defaults must name declared sources or outputs of earlier builds, and unknown keys are errors. The file is read as a subset of TOML: comments, bare and quoted keys, strings, booleans, decimal integers, arrays, inline tables, and `[table]` and `[[array]]` headers. Dotted keys, multi-line strings, floats and dates are rejected with a line and column. For a depfile rule, `order-only` lists the generated files the command may read, as in `examples/gen-header/mise.toml`.

`mise` wraps every command in a short `sh` script, so that a command that succeeds has written every output and a command that fails changes no file. Before the command runs, the script moves each existing output `f`, implicit outputs included, to `f.mise-old`. If the command exits 0 and writes every output, the script deletes the old files. For a `restat = true` rule it first compares each output with its old file using `cmp`, and an equal old file is moved back with its old mtime. If the command fails, or exits 0 but leaves an output missing, the script prints `mise: OUTPUT was not written` for each missing output, deletes what the command wrote, moves every old file back and fails. Ninja then records nothing for the edge, so the next build runs it again. The command can therefore always write its outputs, as `examples/gen-header/gen-config.py` does, and must write all of them. The command must not contain a shell comment, it runs with the positional parameters set to its outputs, no source or output may end in `.mise-old`, and the edge variable `mise_iouts`, which passes the implicit outputs to the script, is set by `mise`.

`wrap = false` in a `[[rule]]` emits the command as written. The proofs then assume what the script would otherwise ensure (item 4 of [trust.md](trust.md)): the command writes every output when it exits 0, leaves the outputs as they were when it fails, and for a `restat` rule leaves an output untouched only when its contents would not change. A command that exits 0 without writing an output makes Ninja run it again on every build.

The same builds can be written in Lean with the library in `Mise/Frontend/Dsl.lean`, which is what `mise` calls after reading the TOML; `test/MiseTest/Fixtures.lean` has two examples.
