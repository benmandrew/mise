# Stage 4 notes: the build DSL, emission and denotation

## Definitions

- `Eval.lean` models Ninja's variable evaluation (`manifest_parser.cc`, `eval_env.cc`, `EdgeEnv` in `graph.cc`). `Manifest.elab` reads a manifest into `EdgeInfo` records; `EdgeInfo.command` is the evaluated command.
- `Graph.lean` defines `GRule`, `GEdge`, `Graph`, `Graph.Valid`, `Graph.spec sem` (the DSL's meaning), `emit`, and `denote sem` (a manifest's meaning through `Manifest.elab`).
- `Emit.lean` holds the proofs; `Dsl.lean` is the builder (`source`, `rule`, `edge`, `edge1`, `defaults`, and `Build.graph`, which returns a `ValidGraph`).
- `Toml.lean` parses a subset of TOML and calls the same builder functions, so it adds no checks and no proofs. The parser is hand-written so that the binary does not link Lean's compiler: with `Lake.Toml` it was 103 MB and each start took 23 ms longer. `test/MiseTest/Toml.lean` compares it with Lake's parser on accepted inputs and checks its error cases; the shell tests run the examples' `mise.toml` files through `mise`.

Commands are abstract, collected in `Sem V`: `sem.exec cmd vs` gives one content per output, from the explicit and implicit inputs in order. Stages 6 and 7 add `sem.dyn` and `sem.keep`. A missing entry reads as `default`, so `V` needs `Inhabited`.

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
- default targets are edge outputs.

`reserved` holds `in`, `out`, `in_newline` and the rule keys. `Handle` and `RuleRef` have private constructors, so a description names only what it declared.

## Theorems

- `emit_wellFormed`: `(emit g).WellFormed` for valid `g`, so `parse_print` applies.
- `denote_emit` (headline): `denote sem (emit g) = g.spec sem` for valid `g` and any `sem`, via `command_emit`.
- `isDyn_emit`, `isRestat_emit`: the evaluated `deps` and `restat` bindings match the rule's flags, emitted by `emitRule` as `depfile = ${out}.d`, `deps = gcc` and `restat = 1`.
- `emitAcyclic`: an `Acyclic` structure for `denote sem (emit g)` given `Graph.DynOK`, with edge positions as ranks; `emit_acyclic` states existence.

## Deviations from the plan

- `emitAcyclic` is a definition because Stage 2 made `Acyclic` data.
- The DSL emits no `phony` edges or top-level bindings; `denote` gives a phony edge the empty command, unlike Ninja.
- `GRule` carries a description that no meaning uses.
- `Graph.spec` uses `GEdge.look`, with Ninja's shell quoting because the build log compares command strings.

## Tests

`test/stage3-diff.sh`, `test/stage4-hello.sh` and `test/MiseTest/Stage4.lean`; see `docs/testing.md`.
