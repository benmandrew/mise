# Stage 4 notes: the build DSL, emission and denotation

## Definitions

- `Eval.lean` models Ninja's variable evaluation (`manifest_parser.cc`, `eval_env.cc`, `EdgeEnv` in `graph.cc`). `Manifest.elab` reads a manifest into `EdgeInfo` records; `EdgeInfo.command` is the evaluated command.
- `Graph.lean` defines `GRule`, `GEdge`, `Graph`, `Graph.Valid`, `Graph.spec sem` (the DSL's meaning), `emit`, and `denote sem` (a manifest's meaning through `Manifest.elab`).
- `Emit.lean` holds the proofs; `Dsl.lean` is the builder (`source`, `rule`, `edge`, `edge1`, `defaults`, and `Build.graph`, which returns a `ValidGraph`).
- `Toml.lean` parses a subset of TOML and calls the same builder functions, so it adds no checks and no proofs. Its conveniences expand before the builder runs: `source-globs` become `source` calls, a `foreach` build becomes one `edge` per match, a `%` input of another build becomes the list of matching paths, the builds are sorted so that every input comes from an earlier edge, and `[aliases]` are flattened into `alias` calls. `Glob.lean` matches glob patterns and lists the files they match; `decode` itself is pure, and `Main.lean` passes it the expanded patterns. The parser is hand-written so that the binary does not link Lean's compiler: with `Lake.Toml` it was 103 MB and each start took 23 ms longer. `test/MiseTest/Toml.lean` compares it with Lake's parser on accepted inputs and checks its error cases, `test/toml-diff.sh` compares it with Python's `tomllib` on random documents, and the shell tests run the examples' `mise.toml` files through `mise`. There is no print-then-parse theorem for the value tree. The parser's recursive functions are `partial def`s, which proofs cannot unfold, so a theorem would first need a total rewrite of the parser with termination measures.

Commands are abstract, collected in `Sem V`: `sem.exec cmd vs` gives one content per output, from the explicit and implicit inputs in order. Stages 6 and 7 add `sem.dyn` and `sem.keep`; `Sem.withCmp` sets `keep` to equality, the semantics of the command wrapper below. A missing entry reads as `default`, so `V` needs `Inhabited`.

## Ninja's evaluation rules

Confirmed against Ninja 1.13.2.

- Top-level and edge bindings are evaluated when read, in the current file scope, without `$in`, `$out` or the edge's other bindings.
- An edge with no bindings uses the file scope, so a top-level `command` replaces the rule's command on those edges.
- An edge variable resolves through `in`, `in_newline`, `out`, the edge scope, the rule binding, then the file scope.
- `$in` and `$out` list explicit paths only, quoted by `GetShellEscapedString`.

Ninja rejects cyclic rule variables; the model uses fuel of the binding count plus one, which suffices for acyclic rules.

## Validity

`Graph.Valid g` is decidable:

- rule names are distinct identifiers other than `phony`, commands nonempty, templates using only `in`, `out` and names outside `reserved`;
- each edge names a declared rule and has an explicit output;
- paths are writable in Ninja and canonical;
- outputs are distinct, not sources, and new;
- inputs are sources or earlier outputs;
- edge variables have distinct names outside `reserved` and newline-free values;
- aliases have distinct names that are valid paths, neither sources nor edge outputs, and a nonempty list of targets, each a valid path that is a source or an edge output (`aliasesOK`);
- default targets are edge outputs or aliases;
- an edge whose rule has a depfile has one explicit output, since the emitted `depfile = ${out}.d` names one file only then (`depfileOutsOK`).

`reserved` holds `in`, `out`, `in_newline`, `ninja_required_version` (`versionVar`) and the rule keys. `Handle` and `RuleRef` have private constructors, so a description names only what it declared.

## The version binding

`emit` puts `versionStmt`, the top-level binding `ninja_required_version = 1.12.1`, before the rules. The version is `ninjaMinVersion`, the oldest supported release; Ninja 1.11.1 and older refuse the manifest with "incompatible with build file ninja_required_version". The binding is the whole file scope, `emitFile`. A template or edge reference to it would read `1.12.1` where `GEdge.look` gives the empty string, so the name is in `reserved`; with it reserved, every lookup the proofs make misses the file scope, as it did when the scope was empty (`emitFile_get`). The models read it as an ordinary binding and leave out Ninja's version check, which runs when Ninja reads the line and changes no edge.

## Aliases

`alias` declares a name for a set of targets, and `emit` writes it as `build NAME: phony TARGETS` after the edges. `denote` and the model's `Manifest.medges` read only `Elab.cmdEdges`, the edges whose rule is not `phony`, so an alias changes neither the meaning of the manifest nor the edges the model runs. That is exact for the aliases `Graph.check` allows. Ninja runs no command for a `phony` edge and logs nothing for it, and its output's dirtiness matters only to edges that read it, of which there are none, since an edge reads only sources and earlier outputs. An alias with no targets would differ: Ninja treats its missing output as always dirty. `aliasesOK` rejects it. Building an alias builds a subset of the edges, which `Reach` already covers as a partial build.

## Theorems

- `emit_wellFormed`: `(emit g).WellFormed` for valid `g`, so `parse_print` applies.
- `denote_emit` (headline): `denote sem (emit g) = g.spec sem` for valid `g` and any `sem`, via `command_emit` and `cmdEdges_emit`.
- `cmdEdges_emit`: the emitted edges that run a command are the graph's own edges, since every alias is a `phony` edge and no rule of a valid graph is called `phony`.
- `isDyn_emit`, `isRestat_emit`: the evaluated `deps` and `restat` bindings match the rule's flags, emitted by `emitRule` as `depfile = ${out}.d`, `deps = gcc` and `restat = 1`.
- `emitAcyclic`: an `Acyclic` structure for `denote sem (emit g)` given `Graph.DynOK`, with edge positions as ranks; `emit_acyclic` states existence.

## The command wrapper

`rule` wraps every command in `wrapCommand` unless `wrap := false` (TOML `wrap = false`). The wrapper is a `sh` script around the command, in the rule's command template. It moves each existing output `f` to `f.mise-old`, deleting a stale `f.mise-old` when `f` is absent, and runs the command in a subshell. If the command exits 0 and every output exists, it deletes each `f.mise-old`; for a `restat` rule it first moves `f.mise-old` back over `f` when `cmp -s` finds them equal. On failure, or when an output is missing, it deletes what the command wrote, moves every old file back and exits nonzero. The outputs are `$out` and `${mise_iouts}`, which `edge` sets to the shell-quoted implicit outputs of a wrapped edge; a build may not set `mise_iouts` itself on a wrapped rule. `source` and `edge` reject paths ending in `.mise-old`.

- *Why every command*: the model's `St.run` writes every output, and the model has no failing commands. A real command that exits 0 without writing an output makes Ninja rerun its edge on every build, so `rebuild_noop` fails against real Ninja. The wrapper turns that into a failure. A failure restores the old files and Ninja records nothing, so the state after it equals the state before it, which `Reach` already covers (`Mise.Model.reach_runWrapped`). Changing `Sem` to allow missing outputs was the alternative, and was not taken.
- *Moving the old file aside* replaces the plan's alternative of writing new outputs to temporary paths. `$out` is one space-separated string, and a command names its implicit outputs itself, so the wrapper cannot redirect the writes. Ninja sees the same: a kept output keeps its file and mtime, and a changed one has a new mtime.
- *On by default*: with the wrapper, `Sem.keep_eq` holds for every `restat` rule the DSL emits, and every command writes all its outputs. The cost is a shell, a subshell, and a rename and a delete per existing output per run, plus a `cmp` for `restat` rules. The command cannot read its previous output, which assumption 2 of `docs/trust.md` already rules out.
- *Failure* leaves the old outputs and mtimes; the log entry is not written, so the edge stays dirty and the next build retries it. An interrupt between the rename and the restore leaves an output missing, which Ninja rebuilds. A depfile written by a failed command stays; Ninja reads it only after a success.
- The command must not contain a shell comment, since it would hide the closing parenthesis of the subshell. It runs with the positional parameters set to the outputs and with the shell variables `f` and `s` set.
- *Opting out*: `wrap = false` emits the command as written. The proofs then assume the command writes every output on exit 0, changes no file on failure, and for a `restat` rule keeps an output only when its contents would not change.

`Mise.Model.script` models the script as file operations (`Mise/Model/Cmp.lean`), `script_eq` computes its effect as `wrapRun`, and `Sem.withCmp` is the semantics it gives (`keep` is equality, so `keep_eq` holds by construction).

## Deviations from the plan

- `emitAcyclic` is a definition because Stage 2 made `Acyclic` data.
- The DSL emits `phony` edges only for aliases, after every other edge, and no top-level bindings other than the version binding.
- `GRule` carries a description that no meaning uses.
- `Graph.spec` uses `GEdge.look`, with Ninja's shell quoting because the build log compares command strings.

## Tests

`test/stage3-diff.sh`, `test/stage4-hello.sh`, `test/restat-cmp.sh`, `test/wrap-outputs.sh` and `test/MiseTest/Stage4.lean`; see `docs/testing.md`.
