# Theorems and assumptions

To check what is proved, start with `Mise/Theorems.lean`. It states the end-to-end results in terms of the DSL graph a user writes. Lean checks the proofs, so a reviewer confirms two things: each statement says what its docstring says, and the definitions it uses mean what their names suggest. [trusted.md](trusted.md) lists those definitions in reading order. [theorems.pdf](theorems.pdf) gives each theorem an English translation and shows the definitions it depends on.

## Theorems

Each theorem takes a valid graph `g`. All but `well_formed` and `wrapped_run` also take `Graph.DynOK`: every depfile command reads only allowed inputs. A *reachable* state is one that a start from empty logs, followed by any source edits and any partial builds, can produce.

| Theorem | Statement |
|---|---|
| `well_formed` | The emitted manifest is well formed, so by trust item 1 Ninja reads the text `mise` writes as that manifest. |
| `correct_unique` | For any sources, the build has at most one correct result. |
| `build_correct` | From any reachable state, one build leaves contents that are correct for the current sources. |
| `rebuild_noop` | After a build, a second build runs nothing and changes nothing. |
| `rebuild_minimal` | After edits, an edge runs only when an edit or an earlier edge of the same build wrote an input that Ninja checks for it. |
| `any_order` | Any order a parallel Ninja could choose gives correct contents and runs the same edges, each at most once. |
| `wrapped_run` | A wrapped command that fails leaves the state unchanged, and every wrapped run leaves the state reachable, so the theorems above cover histories with failed commands. |

Every theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`, and the library has no `axiom` declarations. `test/MiseTest/Axioms.lean` checks this for these theorems and for the module-level theorems they are built from.

## What the proofs cover

`mise` writes the text `print (emit g)`. [trusted.md](trusted.md) leaves out `emit` and `Graph.Valid`, because the theorems hold for whatever manifest `emit` returns, and a validity check that is too strict only makes `mise` refuse more graphs. Reading `mise.toml` and expanding its conveniences are outside the proofs. Their result must pass the same validity check, so a decoding mistake gives a wrong build, never an unsound one.

The theorems fix one graph. Editing `mise.toml`, or adding or removing a file that a `source-globs` pattern matches, changes the graph, and no theorem covers a history across that change.

The supported Ninja subset is top-level bindings, `rule`, `build` with implicit outputs and implicit and order-only inputs, edge bindings, `phony` edges for aliases, and `default`, with the rule keys in `ruleKeys` (`Mise/Syntax/Ast.lean`). `dyndep`, `generator`, `pool`, `subninja`, `include`, MSVC deps, response files and Windows are out of scope.

## Assumptions

The proofs rest on five *trust items*. [testing.md](testing.md) describes the harnesses named here.

1. **Real Ninja reads and runs a manifest as the model does.** `parse_print` shows that the parser model reads `print m` as `m`, and the parser fuzzer checks that Ninja reads every manifest the model accepts in the same way. The random-graph harness checks that Ninja runs the model's edges and leaves its contents, on 1.12.1 and 1.13.2. Every manifest starts with `ninja_required_version = 1.12.1`, because Ninja 1.10.2 and 1.11.1 log the wrong mtime when a `restat` depfile edge keeps its output after `.ninja_deps` is deleted, and so rerun the edge in the next build. The model leaves out `phony` edges, so this item also assumes that Ninja runs no command for an alias and builds its inputs when asked for it.
2. **Commands are deterministic and read only declared or discovered inputs.** For depfile commands this is the hypothesis `Graph.DynOK`, which `ninja -t missingdeps` checks. `conf-sandbox` runs every command under a sandbox that kills it on a read or write it may not make, and `conf-determinism` checks that clean builds give identical products. The wrapper's `sh` runs unconfined, since macOS cannot nest one sandbox in another, and runs only shell builtins.
3. **Depfiles list every file the command read.** `conf-depfiles` traces the files each command opens. System headers are outside this check, since `-MMD` leaves them out, and are assumed fixed with the toolchain.
4. **A command that exits 0 writes every output, a command that fails changes no file, and a `restat` command keeps an output only when its contents would not change** (`Sem.keep_eq`). By default the DSL wraps every command in a script that ensures this ([usage.md](usage.md)). The item then reduces to two things: the script, `cmp`, `mv` and `rm` behave as `Mise.Model.script` models them, and no file `OUTPUT.mise-old` exists outside the script. For a rule with `wrap = false` the item stays an assumption about the command.
5. **Mtimes are faithful.** There is no clock skew, nothing edits files during a build, and each command reads its inputs at the start and writes its outputs at the end. The schedule check tests the last part. `mtime-faults` shows what breaks without it, on Ninja 1.13.2. An edit in the same mtime tick as the start of a command that read the file, a source mtime set backwards (`touch -t`, `cp -p`), or a source stamped by a slow clock leaves stale products that no later build repairs. An edit during a build leaves a stale product that the next build repairs. A source stamped ahead makes every build rerun its readers until the clock catches up.
