# Stage 4 notes: the build DSL, emission and denotation

## Definitions

- `Eval.lean` models how Ninja evaluates variables. It follows `manifest_parser.cc`, `eval_env.cc` and the *edge environment* (`EdgeEnv` in `graph.cc`). `Manifest.elab` reads a manifest into `EdgeInfo` records: the edge, its rule, and its own scope. `EdgeInfo.command` gives the evaluated command, which is also the string Ninja hashes in its build log.
- `Graph.lean` defines `GRule`, `GEdge` and `Graph`, the validity check `Graph.Valid`, and three meanings. `Graph.spec exec` reads the meaning straight from the DSL, `emit` writes a manifest, and `denote exec` reads a manifest back through `Manifest.elab`.
- `Emit.lean` holds the proofs.
- `Dsl.lean` is the user-facing builder: `source`, `rule`, `edge`, `edge1`, `defaults`, and `Build.graph`, which returns a `ValidGraph`.

Commands are abstract. `exec cmd vs` is the list of contents the command `cmd` writes when its inputs hold `vs`, one entry per output. An output's task fetches the edge's explicit and implicit inputs in order, then takes its own entry of `exec`. A missing entry reads as `default`, which is why `V` needs `Inhabited`.

## Ninja's evaluation rules

These rules come from the Ninja source and were confirmed against Ninja 1.13.2 by probes and by the differential test.

- A top-level binding is evaluated when it is read, in the file scope as it stands then.
- An edge binding is also evaluated when it is read, in the file scope. It does not see the edge's other bindings, `$in` or `$out`.
- An edge with no bindings uses the file scope as its own scope. A top-level `command = X` therefore replaces the rule's command on exactly those edges.
- A variable on an edge resolves through `in`, `in_newline` and `out` first, then the edge's scope, then the rule's binding (evaluated on the edge), then the file scope.
- `$in` and `$out` list the explicit paths only. Each path is shell-quoted by `GetShellEscapedString`, so `a b` becomes `'a b'` and `it's` becomes `'it'\''s'`.

Ninja reports a cycle among rule variables as an error. The model cuts the recursion with fuel equal to the number of rule bindings plus one, which never runs out on an acyclic rule.

## Validity

`Graph.Valid g` is a decidable check with these parts:

- rule names are valid identifiers, distinct, and not `phony`; commands are nonempty; templates use only `in`, `out` and names outside `reserved`;
- each edge names a declared rule and has at least one explicit output;
- every path can be written in Ninja and is canonical;
- outputs are distinct, never declared as sources, and never produced by an earlier edge;
- every input is a declared source or an output of an earlier edge;
- edge variables have distinct, valid names outside `reserved`, and their values contain no newline;
- every default target is an edge output.

`reserved` holds `in`, `out`, `in_newline` and the rule keys. An edge binding named `command` would replace the rule's command, and an edge binding named `in` would be ignored, so the DSL forbids both.

`Build.graph` decides `Graph.Valid` at the end, and the `ValidGraph` subtype carries the proof. The checks inside `source` and `edge` repeat parts of it to give earlier error messages. `Handle` and `RuleRef` have private constructors, so a description can only name files and rules it declared.

## Theorems

- `emit_wellFormed`: `(emit g).WellFormed` for every valid `g`. With Stage 3's `parse_print`, the printed manifest parses back to `emit g`.
- `denote_emit` (headline): `denote exec (emit g) = g.spec exec` for every valid `g` and every `exec`. The core step is `command_emit`: Ninja's evaluation of each emitted edge's command equals the DSL's command `g.cmd e`.
- `emitAcyclic`: an `Acyclic` structure for `denote exec (emit g)`. An output's rank is its edge's position plus one, and a source's rank is 0. `emit_acyclic` states that one exists.

## Deviations from the plan

- `emitAcyclic` is a definition. Stage 2 made `Acyclic` data so that `cleanBuild` can run, and `emit_acyclic` is the `Nonempty` form.
- The DSL does not emit `phony` edges or top-level bindings. `denote` gives a phony edge the empty command, which does not match Ninja's treatment of phony outputs, so phony stays out until a stage needs it.
- `GRule` carries a description, which `emit` writes but no meaning uses.
- `Graph.spec` is stated with `GEdge.look`, the DSL's own reading of `$in`, `$out` and edge variables. It uses the same shell quoting as Ninja, because the command string is part of what the build log compares.

## Tests

- `test/stage3-diff.sh` now also compares `EdgeInfo.command` with `ninja -t commands -s` for every non-phony edge of every random manifest. The generator adds top-level `command` bindings, edge bindings named `command` and `description`, commands that use `${description}`, and top-level bindings redefined after the edges. Seed 1 compared 492 commands across 100 manifests, and seeds 7 and 99 with 300 manifests each also agree. Removing the file-scope fallback for edges without bindings made one of the 100 seed-1 manifests fail.
- `test/stage4-hello.sh` generates `examples/hello-c/build.ninja`, builds it with Ninja, runs the binary, checks that a second `ninja -n` has no work, and compares `gen --commands` with `ninja -t commands`.
- `test/MiseTest/Stage4.lean` checks hello-c's commands with `#guard`, and checks that the builder rejects undeclared inputs, edges with no outputs, duplicate sources, a rule named `phony`, an edge variable named `command`, a template that reads `$command`, and non-canonical paths.
