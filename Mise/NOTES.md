# Notes on the library

These notes record the definitions chosen, what each model assumes, and where it differs from Ninja 1.13.2. The theorems and their statements are in the Lean docstrings, and the end-to-end results are in [`docs/theorems.md`](../docs/theorems.md).

## `Mise/Task` and `Mise/Spec`

`Task K V α` is an inductive *free monad* with `pure` and `fetch` constructors. `Task.run` and `Task.deps` are structural, and `Task.interp` interprets a task into any monad. `run_eq_of_agree` says a task gives the same result on stores that agree on what it fetches.

`BuildSpec K V` has `isSource` and a task per key; a source's task is never consulted. `Correct b S R` is the correctness predicate of *Build Systems à la Carte*. `cleanBuild` runs each task against a partial store (`Task.runP`), so that each recursive call on a fetched key carries a proof that its rank is smaller.

`Acyclic b` is a structure holding the rank function and the fetch-bound proofs. An existential `Prop` would make `cleanBuild` noncomputable, and the tests evaluate it. `Nonempty b.Acyclic` is the propositional form, and every theorem that takes `Acyclic b` holds for any witness. For the same reason `emitAcyclic` is a definition.

## `Mise/Syntax`: manifests, printer and parser model

- `Ast.lean`: `Path` (a `String`), `EvalString` (literal text and `${var}` references), `Rule`, `Edge`, `Stmt` and `Manifest`, a statement list in source order.
- `Print.lean`: paths escape `$`, space and `:`; values escape `$` and a leading space; references print as `${name}`.
- `Parse.lean`: the *parser model*, one statement per header line plus its indented block, lexing as `ReadIdent`, `ReadPath` and `ReadVarValue` do in Ninja's `lexer.in.re`.

`Manifest.WellFormed m` means every statement passes `Stmt.ok` in the context of the statements before it, and the parser model runs the same check. It requires that:

- identifiers, literals and paths use only characters Ninja can lex, and literals are never adjacent;
- paths are canonical, so `CanonicalizePath` leaves them unchanged;
- no top-level variable is a keyword, and no variable is `pool` or `dyndep` (`parseTimeKeys`, which Ninja reads while it parses an edge);
- rule names are new and not `phony`, rule keys are in the subset, and the last `command` binding is nonempty;
- an edge's rule is defined earlier, and it has an explicit output, with outputs distinct, new and not among its own inputs;
- `default` targets are nonempty and each was mentioned by an earlier edge.

The parser model agrees with Ninja on every input it accepts. It rejects some inputs Ninja accepts: `$`-newline continuations, `\r\n` line endings, variable references inside paths, non-canonical paths, `pool`, `include`, `subninja`, `|@` validations and rule keys outside the subset. It does not evaluate variables, and accepts any `deps` value because Ninja checks it only at build time. It follows these Ninja behaviours:

- an empty last `command` is rejected, but `${v}` with an empty `v` is accepted;
- a nonempty manifest whose last line has no newline is rejected;
- a NUL byte in a comment ends the input;
- a phony edge's own output is dropped from its inputs.

## `Mise/Frontend`: the DSL, emission and evaluation

- `Eval.lean` models Ninja's variable evaluation (`manifest_parser.cc`, `eval_env.cc`, `EdgeEnv` in `graph.cc`). `Manifest.elab` reads a manifest into `EdgeInfo` records.
- `Graph.lean` defines `Graph`, `Graph.Valid`, `Graph.spec sem` (the DSL's meaning), `emit`, and `denote sem` (a manifest's meaning through `Manifest.elab`).
- `Dsl.lean` is the builder (`source`, `rule`, `edge`, `alias`, `defaults`, and `Build.graph`, which returns a `ValidGraph`). `Emit.lean` holds the proofs.
- `Toml.lean` parses a subset of TOML and calls the same builder, so it adds no checks and no proofs. Its shorthands expand before the builder runs, and `Glob.lean` matches the glob patterns. The parser is hand-written so that the binary does not link Lean's compiler. Its recursive functions are `partial`, so there is no round-trip theorem, and `test/toml-diff.sh` tests it against Python's `tomllib` instead.

Commands are abstract, collected in `Sem V`. `sem.exec cmd vs` gives one content per output from the inputs in order, `sem.dyn` gives a depfile command's reads and outputs, and `sem.keep` says when a `restat` command may leave an output untouched. A missing entry reads as `default`, so `V` needs `Inhabited`.

### Evaluation rules

- Top-level and edge bindings are evaluated when read, in the file scope, without `$in`, `$out` or the edge's other bindings.
- An edge with no bindings uses the file scope, so a top-level `command` replaces the rule's command on those edges.
- An edge variable resolves through `in`, `in_newline`, `out`, the edge scope, the rule binding, then the file scope.
- `$in` and `$out` list explicit paths only, quoted by `GetShellEscapedString`.

Ninja rejects cyclic rule variables. The model uses fuel of the binding count plus one, which suffices for acyclic rules.

### Validity

`Graph.Valid g` is decidable:

- rule names are distinct identifiers other than `phony`, commands are nonempty, and templates use only `in`, `out` and names outside `reserved`;
- each edge names a declared rule and has an explicit output;
- paths are writable in Ninja and canonical;
- outputs are distinct, not sources, and new, and inputs are sources or earlier outputs;
- edge variables have distinct names outside `reserved` and values without newlines;
- aliases have distinct names that are neither sources nor outputs, and a nonempty list of targets, each a source or an output (`aliasesOK`);
- default targets are outputs or aliases;
- a depfile edge has one explicit output (`depfileOutsOK`), since the emitted `depfile = ${out}.d` names one file only then.

`reserved` holds `in`, `out`, `in_newline`, `ninja_required_version`, the rule keys, `pool` and `dyndep`. `Handle` and `RuleRef` have private constructors, so a description names only what it declared.

`emit` puts `ninja_required_version = 1.12.1` before the rules. This binding is the whole file scope, so every lookup the proofs make misses the file scope (`emitFile_get`), and the name is reserved. The models leave out Ninja's version check, which changes no edge.

### Aliases

`emit` writes an alias as `build NAME: phony TARGETS` after the edges. `denote` and `Manifest.medges` read only `Elab.cmdEdges`, the edges whose rule is not `phony`, so an alias changes neither the meaning nor the edges the model runs. This is exact for the aliases `Graph.Valid` allows. Ninja runs and logs nothing for a `phony` edge, and no edge reads an alias. An alias with no targets would differ, because Ninja treats its missing output as always dirty, so `aliasesOK` rejects it.

### The command wrapper

`rule` wraps every command in `wrapCommand` unless `wrap := false`. The script moves each existing output `f` to `f.mise-old` and runs the command in a subshell. If the command exits 0 and every output exists, it deletes the old files; for a `restat` rule it first moves an old file back when `cmp -s` finds it equal. Otherwise it deletes what the command wrote, moves every old file back and exits nonzero. The implicit outputs reach the script through the edge variable `mise_iouts`.

- A failure restores the old files and Ninja records nothing, so the state is unchanged.
- The wrapper moves old files aside because it cannot redirect writes: `$out` is one space-separated string, and a command names its implicit outputs itself.
- An interrupt between the rename and the restore leaves an output missing, which Ninja rebuilds. A depfile written by a failed command stays, but Ninja reads it only after a success.
- A shell comment in the command would hide the closing parenthesis of the subshell, so the command must not contain one.

`Mise.Model.script` (`Mise/Model/Cmp.lean`) models the script as one file operation per shell command, and `script_eq` computes its effect as `wrapRun`. `Sem.withCmp` sets `keep` to equality, which is the semantics the wrapper gives.

## `Mise/Model`: the Ninja model

### Definitions

- `MEdge` holds outputs, explicit and implicit inputs (`ins`), order-only inputs (`oo`), the command, and the `dyn` and `restat` flags. `MEdge.task` fetches `ins` in order and applies `sem.exec`.
- `St V` has `fs : Path → Option (V × Nat)`, `log : Path → Option (String × Nat)`, `deps` and a `clock`.
- `St.dirty` follows `DependencyScan::RecomputeOutputDirty` without `generator`. An output is dirty when it is missing, older than its newest input, unlogged, logged with another command, or logged before its newest input.
- `St.run` writes outputs, log and deps entries at `clock + 1`, and `St.edit` writes a source at a fresh time. `buildTrace` runs dirty edges in order, and decides dirtiness on each visit, so a rebuilt input makes its readers dirty, as in `Plan::CleanNode`.
- `Sched es` says no edge reads its own or a later edge's outputs, order-only inputs included, and outputs are unique.
- `St.deps` maps each output to its command's last reads. `St.effIns e o` is `ins` plus the recorded deps for a depfile edge, or `none` (dirty) with no entry.
- A path is `Allowed` for an edge when no edge outputs it or it is an input. `Reads sem es` says depfile commands fetch only allowed paths, and `DepsOK` says the same of deps entries.
- `Sem.keep` comes with `keep_eq : keep a b = true → a = b`. A `restat` run leaves an output untouched when `keep` holds (`St.kept`). A kept output's log time advances past its mtime, so for `restat` edges `St.outDirty` compares only the log time, as Ninja does.
- `St.runWrapped` runs an edge through the wrapper: the files are what `script` leaves, and the log and deps entries are written only on success.

The proofs go through `Inv sem es st`, which combines `Fresh` (times at most the clock), `DepsOK`, and `Consistent` for every edge the model would skip. A write makes every reader dirty (`edgeOK_of_write`), so each step and edit preserves `Inv`.

### Assumptions

- `sem.exec` is a function, and a static task fetches exactly `ins`.
- Only `run` and `edit` write, each at a fresh, larger time.
- Source edits target paths that no edge outputs.
- The deps entry is exactly the task's reads. Extra depfile paths only add identical rebuilds, unless a later edge writes them, which breaks idempotence.
- `Graph.DynOK` stays a hypothesis, since a C compile can include any file its contents name.

### Where the model differs from Ninja

- `ninjaBuild` builds every edge, where Ninja builds the requested or `default` targets. `Reach` covers partial builds.
- A missing input reads as `default` with mtime 0, where Ninja stops or rebuilds. The model has no deletions.
- An unwrapped command that fails after writing an output is outside the model. So is a build interrupted by a signal, after which Ninja deletes the outputs the running commands changed.
- The log records the write time, where Ninja records the start time. With no edits during a build both order the same way against every input.
- Ninja stores a command hash and the model the command string, so a hash collision would make Ninja skip an edge the model runs.
- `Manifest.medges` leaves out `phony` edges, which run no command, and ignores `generator`.
- The model records and reads a deps entry for each output. Ninja records one for each output (`src/build.cc:968-981`) but reads only the first output's entry, for the whole edge (`src/graph.cc:726-747`). `deps_uniform` and `effIns_uniform` show every output of an edge has the same entry in a reachable state. Ninja also drops the entry when the first output is newer than it (`src/graph.cc:735-743`), which never happens under the model's assumptions.
- `$out` lists every explicit output, so with outputs `a` and `b` Ninja reads the depfile `a b.d`. Ninja treats a missing depfile as empty (`src/build.cc:1010-1021`) and would miss edits the model sees, so `depfileOutsOK` asks for one explicit output.
- A parallel run is the sequence of its commands by start time, assuming each reads at the start and writes at the end. Two orders agree on contents, dirtiness and the edges they run, but not on mtimes or log times.
- In the model a command writes or keeps every output, where a real command can leave one out. Ninja counts a missing output as dirty (`src/graph.cc:300-304`), so it reruns that edge on every build, and without `restat` also its dependents (`src/graph.cc:181-185`). It can also skip an edge the model runs, when that edge reads a left-out output. `Correct` still holds, but `ninjaBuild_idem` does not. The wrapper turns a missing output into a failure that changes no file (`reach_runWrapped`), so this affects only rules with `wrap = false` (trust item 4).

`Sched` with `Reads` is the no-hazard condition of Spall et al. ([Forward build systems, formally](https://doi.org/10.1145/3497775.3503687)): unordered commands read nothing the other writes and write disjoint outputs.
