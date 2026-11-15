# Usage

`mise build [--set KEY=VALUE]... [DIR] [-- NINJA_ARGS...]` reads `DIR/mise.toml`, writes `DIR/build.ninja`, and runs `ninja` in `DIR` with any arguments after `--`. Run it for every build: it rewrites `build.ninja` only when the contents change. `--set` overrides a parameter from `[params]` for that run only, such as `--set cflags=-O0`.

`mise gen` writes `build.ninja` without running Ninja, and `mise gen --commands` prints each edge's command and writes nothing. `DIR` defaults to the current directory. In the Nix shell `mise` is on `PATH` after `lake build`; elsewhere run `lake exe mise`. Running `ninja` directly also works, but it does not notice an edit to `mise.toml`.

`mise` needs Ninja 1.12.1 or later, and an older Ninja refuses the manifest (trust item 1 in [theorems.md](theorems.md#assumptions) gives the reason). The name `ninja_required_version` is reserved.

## `mise.toml`

`examples/hello-c/mise.toml` compiles every C file in its directory and links the objects:

```toml
source-globs = ["*.c", "*.h"]
defaults = ["build/hello"]

[params]
cflags = "-O2 -Wall"

[[rule]]
name = "cc"
command = "cc $cflags -c $in -o $out"
description = "CC $out"

[[rule]]
name = "link"
command = "cc $in -o $out"
description = "LINK $out"

[[build]]
rule = "link"
outs = ["build/hello"]
ins = ["build/%.o"]

[[build]]
rule = "cc"
foreach = "%.c"
outs = ["build/%.o"]
ins = ["%.c"]
implicit-ins = ["greet.h"]
params = ["cflags"]

[aliases]
objs = ["build/%.o"]
```

A `[[rule]]` has `name` and `command`. Its optional keys are `description`, `depfile = true` (the compiler reports what it read), `restat = true` (an output whose contents do not change keeps its old file, so its dependents do not rebuild) and `wrap = false` (below).

A `[[build]]` has `rule` and `outs`. Its optional keys are `implicit-outs`, `ins`, `implicit-ins`, `order-only`, `vars` (edge variables with literal values), `params` (edge variables bound to parameters) and `foreach` (below). For a depfile rule, `order-only` lists the generated files the command may read, as in `examples/gen-header/mise.toml`. Inputs name sources or outputs of any build. Builds may come in any order: `mise` sorts them so that each follows the builds it reads, and rejects a cycle. Defaults name build outputs or aliases. Unknown keys are errors.

The file is read as a subset of TOML: comments, bare and quoted keys, strings, booleans, decimal integers, arrays, inline tables, and `[table]` and `[[array]]` headers. Dotted keys, multi-line strings, floats and dates are rejected with a line and column.

## Shorthands

Each of these expands into ordinary sources, builds and `phony` edges before the validity check, so the proofs cover the expanded description.

- `source-globs` lists glob patterns whose matches are sources too. A `*` or `?` matches within one path component, and a whole component `**` matches any number of directories. A wildcard does not match a leading `.`. A pattern that matches no file is an error. `mise` expands the patterns on every run, so a new source file is in the next build.
- `foreach` turns a `[[build]]` into one build per match. It is a pattern with one `%`, or a list of them, matched against the sources and the outputs of other builds. The `%` matches a nonempty stem, which may contain `/`, and every `%` in the copy's paths is replaced by the stem.
- In a build without `foreach`, an input with `%` stands for every source and output that matches it, in path order, except the build's own outputs.
- `[aliases]` names sets of targets, so `mise build -- NAME` builds an alias's targets. A target is a source, a build output or another alias, and a target with `%` stands for every match. No build may read an alias.

## The command wrapper

`mise` wraps every command in a short `sh` script. When the command fails, or exits 0 and leaves an output missing, the script prints `mise: OUTPUT was not written`, puts the old outputs back and fails, so the next build runs the edge again. For a `restat` rule the script keeps an output's old file when `cmp` finds the contents unchanged. A command may therefore write its outputs unconditionally, and must write all of them. It must not contain a shell comment, and no source or output may end in `.mise-old`.

`wrap = false` in a `[[rule]]` emits the command as written. The proofs then assume what the script would ensure ([trust item 4](theorems.md#assumptions)). A command that exits 0 without writing an output makes Ninja run it again on every build.

The same builds can be written in Lean with the library in `Mise/Frontend/Dsl.lean`, which `mise` calls after reading the TOML; `test/MiseTest/Fixtures.lean` has two examples.
