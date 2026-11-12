# Usage

`mise build [--set KEY=VALUE]... [DIR] [-- NINJA_ARGS...]` reads `DIR/mise.toml`, writes `DIR/build.ninja`, and runs `ninja` in `DIR` with any arguments after `--`. Run it for every build and rebuild: it rewrites `build.ninja` only when the contents change. `--set` overrides a parameter declared in `[params]`, such as `--set cflags=-O0`. It applies only to that run, so a later `mise build` without it goes back to the default.

`mise gen` writes `build.ninja` without running Ninja. `mise gen --commands` prints each edge's command and writes nothing. `DIR` defaults to the current directory. In the Nix shell `mise` is on `PATH` after `lake build`; elsewhere run `lake exe mise`.

Running `ninja` directly also works, but it does not notice an edit to `mise.toml`.

`mise` needs Ninja 1.12.1 or later. Every `build.ninja` starts with `ninja_required_version = 1.12.1`, so an older Ninja refuses it with "incompatible with build file ninja_required_version". After `.ninja_deps` is deleted, Ninja 1.10.2 and 1.11.1 can rerun a `restat` depfile edge once in a build that should have no work ([testing.md](testing.md)). Because the binding is in the file scope, a rule command and an edge variable may not use the name `ninja_required_version`.

A description with one compile, each build written out:

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

A `[[rule]]` has `name`, `command`, and optionally `description`, `depfile = true` (the compiler reports what it read), `restat = true` (an output whose contents do not change keeps its old file, and its dependents do not rebuild) and `wrap = false` (below). A `[[build]]` has `rule` and `outs`, and optionally `implicit-outs`, `ins`, `implicit-ins`, `order-only`, `vars` (edge variables with literal values), `params` (edge variables bound to parameters) and `foreach` (below). Inputs name sources or outputs of any build, and the builds may come in any order: `mise` sorts them so that each follows the builds it reads, and rejects a cycle. Defaults name build outputs or aliases. Unknown keys are errors. The file is read as a subset of TOML: comments, bare and quoted keys, strings, booleans, decimal integers, arrays, inline tables, and `[table]` and `[[array]]` headers. Dotted keys, multi-line strings, floats and dates are rejected with a line and column. For a depfile rule, `order-only` lists the generated files the command may read, as in `examples/gen-header/mise.toml`.

Four features shorten a description. Each expands into ordinary sources, builds and `phony` edges before the validity check, so the proofs cover the result as they cover a description written out in full.

- `source-globs` lists glob patterns whose matches are sources too. A `*` or `?` matches within one path component, and a whole component `**` matches any number of directories. A wildcard does not match a leading `.`, so hidden files need a pattern component that starts with `.`. Files ending in `.mise-old` are skipped. A pattern that matches no file is an error. `mise` expands the patterns each time it runs, so a new source file is in the next build.
- `foreach` turns a `[[build]]` into one build per match. It is a pattern with one `%`, or a list of them, matched against the sources, the outputs of builds without `foreach`, and the outputs of earlier `foreach` builds. The `%` matches a nonempty stem, which may contain `/`. In each copy, every `%` in the paths is replaced by the stem.
- In a build without `foreach`, an input with `%` stands for every source and output that matches it, in path order. The build's own outputs are left out.
- `[aliases]` names sets of targets. Each alias becomes a Ninja `phony` edge, so `mise build -- NAME` builds its targets. A target is a source, a build output or another alias, whose targets are put in its place, and a target with `%` stands for every match, as in an input. No build may read an alias.

`examples/hello-c/mise.toml` compiles every C file in its directory and links the objects, with the link written first:

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

`mise` wraps every command in a short `sh` script, so that a command that succeeds has written every output and a command that fails changes no file. Before the command runs, the script moves each existing output `f`, implicit outputs included, to `f.mise-old`. If the command exits 0 and writes every output, the script deletes the old files. For a `restat = true` rule it first compares each output with its old file using `cmp`, and an equal old file is moved back with its old mtime. If the command fails, or exits 0 but leaves an output missing, the script prints `mise: OUTPUT was not written` for each missing output, deletes what the command wrote, moves every old file back and fails. Ninja then records nothing for the edge, so the next build runs it again. The command can therefore always write its outputs, as `examples/gen-header/gen-config.py` does, and must write all of them. The command must not contain a shell comment, it runs with the positional parameters set to its outputs, no source or output may end in `.mise-old`, and the edge variable `mise_iouts`, which passes the implicit outputs to the script, is set by `mise`.

`wrap = false` in a `[[rule]]` emits the command as written. The proofs then assume what the script would otherwise ensure (item 4 of [trust.md](trust.md)): the command writes every output when it exits 0, leaves the outputs as they were when it fails, and for a `restat` rule leaves an output untouched only when its contents would not change. A command that exits 0 without writing an output makes Ninja run it again on every build.

The same builds can be written in Lean with the library in `Mise/Frontend/Dsl.lean`, which is what `mise` calls after reading the TOML; `test/MiseTest/Fixtures.lean` has two examples.
