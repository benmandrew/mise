# Stage 4 notes: the build DSL, emission and denotation

## Definitions

- `Eval.lean` models Ninja's variable evaluation (`manifest_parser.cc`, `eval_env.cc`, `EdgeEnv` in `graph.cc`). `Manifest.elab` reads a manifest into `EdgeInfo` records; `EdgeInfo.command` is the evaluated command.
- `Graph.lean` defines `GRule`, `GEdge`, `Graph`, `Graph.Valid`, `Graph.spec sem` (the DSL's meaning), `emit`, and `denote sem` (a manifest's meaning through `Manifest.elab`).
- `Emit.lean` holds the proofs; `Dsl.lean` is the builder (`source`, `rule`, `edge`, `edge1`, `defaults`, and `Build.graph`, which returns a `ValidGraph`).
- `Toml.lean` parses a subset of TOML and calls the same builder functions, so it adds no checks and no proofs. The parser is hand-written so that the binary does not link Lean's compiler: with `Lake.Toml` it was 103 MB and each start took 23 ms longer. `test/MiseTest/Toml.lean` compares it with Lake's parser on accepted inputs and checks its error cases, `test/toml-diff.sh` compares it with Python's `tomllib` on random documents, and the shell tests run the examples' `mise.toml` files through `mise`. There is no print-then-parse theorem for the value tree. The parser's recursive functions are `partial def`s, which proofs cannot unfold, so a theorem would first need a total rewrite of the parser with termination measures.

Commands are abstract, collected in `Sem V`: `sem.exec cmd vs` gives one content per output, from the explicit and implicit inputs in order. Stages 6 and 7 add `sem.dyn` and `sem.keep`; `Sem.withCmp` sets `keep` to equality, the semantics of the `cmp` wrapper below. A missing entry reads as `default`, so `V` needs `Inhabited`.

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
- default targets are edge outputs;
- an edge whose rule has a depfile has one explicit output, since the emitted `depfile = ${out}.d` names one file only then (`depfileOutsOK`).

`reserved` holds `in`, `out`, `in_newline` and the rule keys. `Handle` and `RuleRef` have private constructors, so a description names only what it declared.

## Theorems

- `emit_wellFormed`: `(emit g).WellFormed` for valid `g`, so `parse_print` applies.
- `denote_emit` (headline): `denote sem (emit g) = g.spec sem` for valid `g` and any `sem`, via `command_emit`.
- `isDyn_emit`, `isRestat_emit`: the evaluated `deps` and `restat` bindings match the rule's flags, emitted by `emitRule` as `depfile = ${out}.d`, `deps = gcc` and `restat = 1`.
- `emitAcyclic`: an `Acyclic` structure for `denote sem (emit g)` given `Graph.DynOK`, with edge positions as ranks; `emit_acyclic` states existence.

## The `cmp` wrapper for `restat`

`rule` wraps a `restat` command in `cmpWrap` unless `restatCmp := false` (TOML `restat-cmp = false`). The wrapper is a `sh` script around the command, in the rule's command template. It moves each existing output `f` to `f.mise-old`, runs the command in a subshell, and on success moves `f.mise-old` back over `f` when `cmp -s` finds them equal, deleting it otherwise. On failure, or when an output is missing, it deletes what the command wrote, moves every old file back and exits nonzero. The outputs are `$out` and `${mise_iouts}`, which `edge` sets to the shell-quoted implicit outputs of a wrapped edge; a build may not set `mise_iouts` itself.

- *Moving the old file aside* replaces the plan's alternative of writing new outputs to temporary paths. `$out` is one space-separated string, and a command names its implicit outputs itself, so the wrapper cannot redirect the writes. Ninja sees the same: a kept output keeps its file and mtime, and a changed one has a new mtime.
- *On by default*: with the wrapper, `Sem.keep_eq` holds for every `restat` rule the DSL emits, and a missing output becomes a failure, which removes the model's "always produces every output" deviation. The cost is a rename and a `cmp` per output per run. The command cannot read its previous output, which assumption 2 of `docs/trust.md` already rules out.
- *Failure* leaves the old outputs and mtimes; the log entry is not written, so the edge stays dirty. An interrupt between the rename and the restore leaves an output missing, which Ninja rebuilds.
- The command must not contain a shell comment, since it would hide the closing parenthesis of the subshell.

`Mise.Model.wrapRun` models the script (`Mise/Model/Cmp.lean`) and `Sem.withCmp` is the semantics it gives (`keep` is equality, so `keep_eq` holds by construction).

## Deviations from the plan

- `emitAcyclic` is a definition because Stage 2 made `Acyclic` data.
- The DSL emits no `phony` edges or top-level bindings; `denote` gives a phony edge the empty command, unlike Ninja.
- `GRule` carries a description that no meaning uses.
- `Graph.spec` uses `GEdge.look`, with Ninja's shell quoting because the build log compares command strings.

## Tests

`test/stage3-diff.sh`, `test/stage4-hello.sh`, `test/restat-cmp.sh` and `test/MiseTest/Stage4.lean`; see `docs/testing.md`.
