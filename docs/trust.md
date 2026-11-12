# Trust base

The proofs cover everything from the DSL to the abstract Ninja model, including that the printer emits text the parser model reads back to the emitted syntax tree. Reading `mise.toml` is outside the proofs, but its result must pass the same validity check as a description written with the Lean DSL, so a decoding mistake gives a wrong build, never an unsound one. `test/toml-diff.sh` checks the TOML parser against Python's `tomllib`. The following are assumed, and the tests in [testing.md](testing.md) check most of them.

1. Real Ninja implements the model and the parser model for the supported subset. `test/fuzz.sh` checks the model on random graphs: real Ninja must run the same edges and leave the same contents.
2. Commands are deterministic and read only declared or discovered inputs. For depfile commands this is the hypothesis `Graph.DynOK`; `ninja -t missingdeps` checks it.
3. Depfiles list every file the command read.
4. A `restat` command leaves an output untouched only when its contents would not change (`Sem.keep_eq`).
5. Mtimes are faithful: no clock skew, nothing edits files during a build, and each command reads its inputs at the start and writes its outputs at the end.

The supported subset is top-level bindings, `rule`, `build` with implicit outputs and implicit and order-only inputs, edge bindings, and `default`, with the rule keys listed in `Mise/Syntax/NOTES.md`. Out of scope: `dyndep`, `generator`, `pool`, `subninja`, `include`, MSVC deps, response files and Windows.
