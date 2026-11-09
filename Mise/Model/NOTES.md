# Stages 5 to 7 notes: the Ninja model

Stages 6 and 7 generalised the Stage 5 model in place, so the definitions below are the current ones. With no depfile or `restat` edges they reduce to the Stage 5 model, and `ninjaBuild_sound_static` restates the Stage 5 headline exactly.

## Stage 5: the static model and incremental soundness

### Definitions

- `Basic.lean` holds the model. `MEdge` is what the model needs from an edge: all outputs, the explicit and implicit inputs (`ins`), the order-only inputs (`oo`), the evaluated command from Stage 4, whether the rule has a depfile (`dyn`), and whether it has `restat` (Stage 7). `Manifest.medges` lists them in manifest order.
- Command meanings live in `Sem V`. A static command writes `sem.exec cmd vs` from its inputs' contents; `MEdge.task` wraps it as a task that fetches `ins` in order.
- The state `St V` has `fs : Path → Option (V × Nat)` for contents and mtimes, `log : Path → Option (String × Nat)` for the build log, `deps` for the deps log (Stage 6), and a `clock`.
- `St.dirty` follows `DependencyScan::RecomputeOutputDirty` in Ninja 1.13 for edges without `generator`. An output is dirty when it is missing, when its mtime is older than the newest input (skipped for `restat` edges, Stage 7), when it has no log entry, when the logged command differs, or when the logged time is older than the newest input. An edge is dirty when any output is dirty.
- `St.run` writes every output, its log entry and its deps entry at the fresh time `clock + 1`. A `restat` run may keep an output instead (Stage 7). `St.edit` writes a source at a fresh time. `buildTrace` visits edges in order, runs the dirty ones, and returns the edges it ran; `ninjaBuild` keeps the final state.
- `Sched es` says the order is a schedule. No edge reads its own outputs or a later edge's outputs, counting order-only inputs, and no two edges share an output.

Dirtiness is decided when the model visits an edge, from the state at that moment. An edge whose input was rebuilt earlier in the same run has an input newer than its outputs, so the mtime check makes it dirty (`outDirty_of_newer`). This is how the model gets Ninja's dirty propagation, and it is the same rule Ninja's `Plan::CleanNode` applies when it rechecks an edge mid-build.

### The invariant

`Inv sem es st` has three parts. Every mtime and log time is at most the clock (`Fresh`). Every deps entry names allowed paths (`DepsOK`, trivial without depfiles). Every edge the model would skip is `Consistent`: each output holds what the command computes from the current store, and the inputs Ninja checks cover everything the command reads. Three facts carry the proofs.

- `inv_step`: running or skipping any edge of a schedule keeps `Inv`. A run writes only that edge's outputs, at a fresh time. Any other edge that depends on one of them then has a newer input and is dirty, and every other edge sees no change (`edgeOK_of_write`).
- `inv_edit`: a source edit keeps `Inv` for the same reason.
- `build_clean`: after one pass in schedule order every edge is clean. An edge is clean right after its turn, and later edges never write anything it depends on.

A clean edge under `Inv` is consistent, and consistent edges give a correct store (`correct_of_consistent`).

### Theorems

- `ninjaBuild_clean_correct`: from empty logs, a build gives contents `Correct` for `denote sem m`.
- `ninjaBuild_sound_static` (the Stage 5 headline): for a manifest with no depfile edges, start from a fresh state whose contents are `Correct`, apply any list of source edits, and build. The contents are `Correct` for the edited sources. `ninjaBuild_sound` is the general form; with depfile edges it also asks that the deps log name allowed paths and cover what each command reads.
- `ninjaBuild_eq_cleanBuild` restates soundness as equality with `cleanBuild`.
- `ninjaBuild_idem`: building the result of a build runs no edges and leaves the state unchanged.
- `ninjaBuild_after_interrupt`: stopping after any prefix of the schedule keeps `Inv`, so the next full build is correct. Writes are atomic in the model.
- `command_change_rebuilds`: take a state where every edge of `m` is clean and `Inv` holds, such as the result of a build. Change any commands while keeping each edge's inputs, outputs, depfile flag and `restat` flag. Building the new manifest gives correct contents and runs every changed edge that has an output.
- `sched_emit`: every emitted manifest is a schedule.

`ninjaBuild_sound_static` asks for less than the plan states. It needs correct contents and a fresh state, and it makes no demand on the build log. The proofs go through the weaker `Inv`, which `sound_of_inv` exposes.

### Assumptions

- `sem.exec` is a function, so static commands are deterministic. A static output's task fetches exactly the edge's explicit and implicit inputs, so static commands read only declared inputs by construction.
- Mtimes are faithful. The clock is at least every recorded mtime (`Fresh`), and the only writes are `run` and `edit`, each at a fresh, strictly larger time. Nothing changes files during a build.
- Source edits target sources: paths that no edge outputs.

### Where the model differs from Ninja

- `ninjaBuild` builds every edge. Ninja builds the requested targets, or the `default` targets when none are given, and their dependencies. The two agree when the defaults cover every edge, as in both examples. `Reach` (Stage 6) admits steps of any edge in any order, which covers builds of fewer targets.
- A missing input reads as `default` contents with mtime 0. Ninja stops with "missing and no known rule to make it" for a missing static input, and rebuilds an edge whose recorded dep is missing. The model has no deletions, so a missing file can only appear through an edit, at a fresh mtime that makes its readers dirty.
- The log entry records the time the outputs were written. Ninja records the command's start time, so an input edited while its command runs makes the edge dirty next time. The model has no edits during a build, so the two records order the same way against every input.
- Ninja stores a hash of the command, and the model stores the command string. A hash collision would make Ninja skip an edge the model runs.
- Phony edges are treated as commands with an empty command line. The DSL does not emit them.
- `generator` is ignored. Stage 7 adds `restat`.

## Stage 6: depfiles

### Front end

- A rule declared with `depfile := true` is emitted with `depfile = ${out}.d` and `deps = gcc`. `dynEdge1` adds an edge whose `mayReadGenerated` handles become order-only inputs, so Ninja builds them first.
- `Graph.isDyn` and `EdgeInfo.isDyn` say whether an edge reads the *deps log*. Ninja checks only that the evaluated `deps` binding is nonempty, and `isDyn_emit` shows that the emitted binding agrees with the DSL. `denote_emit` holds unchanged for any `Sem`.
- A depfile command means the task `sem.dyn cmd`, which fetches what the command reads and returns its outputs. The plan has each DSL edge carry its own task. Here the task is a function of the evaluated command, so `Graph` stays independent of the value type, and an example supplies the tasks for its commands in one `Sem`.

### Model

- `St.deps` maps each output to the paths its command read on its last run, which `St.run` records as `(e.task sem).deps st.content`. The model records an entry for every output of every edge, and static edges ignore it. Ninja keys the deps log by an edge's first output and writes it only for edges with `deps`.
- `St.effIns e o` is the list of paths Ninja checks for output `o`: the explicit and implicit inputs, plus the recorded deps for a depfile edge. It is `none` for a depfile edge with no entry, which makes the output dirty. All mtime checks of Stage 5 now run over `effIns`.
- A path is `Allowed` for an edge when no edge outputs it, or when it is one of the edge's inputs, order-only inputs included. `Reads sem es` is the *static-ancestor condition*: every depfile command fetches only allowed paths, on every branch. `DepsOK` says every deps entry of a depfile edge names allowed paths.

### Proof

A clean output under `Inv` has an `effIns` list that covers what its command reads now. A write to paths outside that list leaves the command's reads unchanged, so `run_eq_of_agree` from Stage 1 gives the same outputs and the same reads (`consistent_transfer`). A write inside the list makes the output dirty by the mtime check. Running an edge records its reads, and those reads avoid its own outputs under `Reads` and `Sched`, so the run leaves it consistent (`run_self`). `DepsOK` makes `build_clean` hold: an edge skipped on its turn depends only on allowed paths, which later edges never write.

### Theorems

- `reach_sound` (headline): `Reach sem es st` holds for every state reached from empty logs by source edits and by steps of any edges in any order. For such a state, a build gives correct contents and a second build runs nothing. Interrupted builds and builds of some targets are sequences of steps, so this covers them.
- `inv_of_reach`: every reachable state satisfies `Inv`.
- `fetched_up_to_date` (the scheduling lemma): when an edge's turn comes, every generated path its command reads is an output of an earlier edge, and that edge is clean.
- `reads_emit`: `Graph.DynOK` (each depfile command fetches only sources and the edge's declared inputs) gives `Reads` for the emitted manifest. `Graph.acyclic` builds the acyclicity witness under the same condition, with edge positions as ranks.
- `dsl_sound`: for a valid graph satisfying `Graph.DynOK`, after any reachable history, building the emitted manifest gives `cleanBuild` of `g.spec sem`, and a second build runs nothing.

### Assumptions

- *Trace completeness*: the model records exactly the task's reads as the deps entry. A real depfile may list more paths. Extra paths only add mtime checks, so they can make Ninja rebuild an edge the model skips, and the rebuild writes the same contents because commands are deterministic. Extra paths that later edges write would also break idempotence. The model does not cover depfiles that list paths outside the static-ancestor condition; `ninja -t missingdeps` in the harness checks for them.
- The static-ancestor condition `Graph.DynOK` stays a hypothesis. It quantifies over every branch of the task, and a C compile can include any file its contents name, so no example proves it for every store. The harness checks it on the stores it reaches.

### Tests

- `test/MiseTest/Stage6.lean` runs gen-header in the model with a `Sem` whose compile task reads the includes named in a file's contents. It checks what the deps log records and what each edit rebuilds. Adding `#include "extra.h"` rebuilds `main.o`, after which edits to `extra.h` count, and they stop counting once the include is removed and the object rebuilt. Each incremental build is compared with a build from empty logs.
- `test/stage6-props.sh` runs `test/props.py` against real Ninja: 200 random edit sequences on each example. A sequence starts with a clean build, then applies one to six edits, building after each. Edits change a source, add or remove `#include "extra.h"`, change the generator script, or change `cflags` and regenerate the manifest. After each build the harness checks that every product equals a clean build's byte for byte, that `ninja -n` has no work, and that `ninja -t missingdeps` finds nothing. `test/stage6-props.sh` with seed 1 ran 729 edits on hello-c and 696 on gen-header, and every check passed. Removing the depfile bindings from the manifest makes it fail on the fourth edit of the first sequence.

## Stage 7: minimality, early cutoff, parallel equivalence

### Restat

- A rule declared with `restat := true` is emitted with `restat = 1`. `Graph.isRestat` and `EdgeInfo.isRestat` carry the flag to the model, and `isRestat_emit` shows that the emitted binding agrees with the DSL. Ninja checks only that the binding is nonempty.
- `Sem` gains `keep : V → V → Bool` and the assumption `keep_eq : keep a b = true → a = b`. A `restat` run may leave output `o` untouched when `keep (old contents) (new contents)` holds (`St.kept`), so it does so only when the new contents equal the old. This is the plan's *Env* field for early cutoff. Both fields have defaults that never keep, so the examples of earlier stages are unchanged.
- A kept output keeps its file and mtime. Its log entry and deps entry are still rewritten, so the log time moves on while the mtime stays behind. For a `restat` edge `St.outDirty` therefore skips the comparison of the output's mtime with its inputs and keeps the comparison of the log time. This is `RecomputeOutputDirty` in Ninja 1.13, which uses the logged time in place of the output's mtime for a `restat` edge with a log entry.
- `Fresh` now also bounds every log time by the clock, because the soundness proof (`edgeOK_of_write`) compares a write with the log time where Stage 5 compared it with the output's mtime.

All Stage 5 and 6 theorems hold with `restat` edges, through the same invariant. A kept output already holds what the command computes, which is all that `run_self` needs.

### Theorems

- `trace_nodup` (at most once): in a schedule whose edges all have outputs, a build runs each edge at most once. `trace_sublist` says the edges run are a sublist of the schedule.
- `build_minimal` (minimality): build after source edits `E` from any state `st`. An edge that runs either was already dirty in `st`, or has an output for which one of the inputs Ninja checks was written after `st.clock`, by an edit in `E` or by an edge that ran earlier in the same build. The inputs Ninja checks are the static inputs and the deps recorded in `st`, so "written after `st.clock`" means changed since the edge's last run. `St.outDirty_cause` lists what "already dirty" means: a missing output, log entry or deps entry, a different logged command, or an input newer than the log entry or, without `restat`, newer than the output. `build_minimal_clean` drops the first case for a state where every edge is clean, such as the result of a build. `run_cause` is the one-edge form.
- `restat_cutoff` (early cutoff): a run that keeps every output changes no other edge's dirtiness. In `build_minimal` a kept output never serves as the written input, because its mtime stays at most `st.clock` (`St.kept_not_newer`). So an edge downstream of a kept output runs only when something else changed.
- `parallel_equiv` (parallel equivalence): under the invariant, building the edges in any order that is a permutation of the manifest's and a `Sched`, that is, any order consistent with the dependency order, gives the same contents as the manifest order and leaves every edge clean. `parallel_equiv_reach` states it for any history from empty logs, and `dsl_parallel` for emitted manifests, where the contents are `cleanBuild` of the DSL's meaning. `schedAcyclic` builds the acyclicity witness of a schedule's specification, with edge positions as ranks.

### The no-hazard condition

Spall et al. ([Forward build systems, formally](https://doi.org/10.1145/3497775.3503687)) call a build free of *hazards* when no command writes a file that another command reads or writes, unless the two are ordered. Here the condition is `Sched` together with `Reads`. `Sched` gives unique producers and puts every producer of an edge's inputs, order-only inputs included, before the edge. `Reads` (Stage 6) confines what a depfile command reads to sources and its declared inputs. Under these, two commands not ordered by the dependency order read nothing the other writes and write disjoint outputs.

### Where the model differs from Ninja

- A parallel run is modelled as the sequence of its commands in order of start time. Commands are atomic in the model, so this assumes each command reads its inputs at the start and writes its outputs at the end. Ninja starts a command only after every producer of its inputs has finished, which makes the start-time order a `Sched`.
- The final states of two orders agree on contents and on which edges are dirty. They differ in mtimes and log times, which follow the order commands ran in. The theorems do not show that two orders run the same set of edges.
- A `restat` command in the model always produces every output. Ninja also handles a `restat` command that leaves an output missing, and treats it as unchanged; the DSL's commands always write their outputs.
- Ninja records the command's start time in the log when a `restat` run keeps an output. The model records the time of the run, which orders the same way against every input because nothing changes files during a build.

### Tests

- `test/MiseTest/Stage7.lean` runs gen-header in the model with a `Sem` whose commands ignore words starting with `#` and that keeps unchanged outputs. A comment added to `config.in` runs only the generator, which keeps `build/config.h` with its old mtime, and the next build runs nothing. With the same commands and no keeping, the same edit runs all four edges. Swapping the two compiles gives the same contents.
- `examples/gen-header` now has a `restat` generator that leaves the header untouched when its contents would not change. `test/props.py` gained an edit that adds a comment to `config.in`, after which it checks that Ninja ran only the generator and left every product's mtime unchanged. Every build now picks `-j1`, `-j2` or `-j8` at random, so independent compiles run in different orders. With seed 1 the extended harness ran 680 edits on hello-c and 710 on gen-header, and every check passed. Removing `restat = 1` from the manifest makes the harness fail on the first comment edit, where Ninja ran both compiles after the generator.
