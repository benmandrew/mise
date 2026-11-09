# Stages 5 to 7 notes: the Ninja model

Stage 6 generalised the Stage 5 model in place, so the definitions below are the current ones. With no depfile edges they reduce to the Stage 5 model, and `ninjaBuild_sound_static` restates the Stage 5 headline exactly.

## Stage 5: the static model and incremental soundness

### Definitions

- `Basic.lean` holds the model. `MEdge` is what the model needs from an edge: all outputs, the explicit and implicit inputs (`ins`), the order-only inputs (`oo`), the evaluated command from Stage 4, and whether the rule has a depfile (`dyn`). `Manifest.medges` lists them in manifest order.
- Command meanings live in `Sem V`. A static command writes `sem.exec cmd vs` from its inputs' contents; `MEdge.task` wraps it as a task that fetches `ins` in order.
- The state `St V` has `fs : Path → Option (V × Nat)` for contents and mtimes, `log : Path → Option (String × Nat)` for the build log, `deps` for the deps log (Stage 6), and a `clock`.
- `St.dirty` follows `DependencyScan::RecomputeOutputDirty` in Ninja 1.13 for edges without `restat` or `generator`. An output is dirty when it is missing, when its mtime is older than the newest input, when it has no log entry, when the logged command differs, or when the logged time is older than the newest input. An edge is dirty when any output is dirty.
- `St.run` writes every output, its log entry and its deps entry at the fresh time `clock + 1`. `St.edit` writes a source at a fresh time. `buildTrace` visits edges in order, runs the dirty ones, and returns the edges it ran; `ninjaBuild` keeps the final state.
- `Sched es` says the order is a schedule. No edge reads its own outputs or a later edge's outputs, counting order-only inputs, and no two edges share an output.

Dirtiness is decided when the model visits an edge, from the state at that moment. An edge whose input was rebuilt earlier in the same run has an input newer than its outputs, so the mtime check makes it dirty (`outDirty_of_newer`). This is how the model gets Ninja's dirty propagation, and it is the same rule Ninja's `Plan::CleanNode` applies when it rechecks an edge mid-build.

### The invariant

`Inv sem es st` has three parts. Every mtime is at most the clock (`Fresh`). Every deps entry names allowed paths (`DepsOK`, trivial without depfiles). Every edge the model would skip is `Consistent`: each output holds what the command computes from the current store, and the inputs Ninja checks cover everything the command reads. Three facts carry the proofs.

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
- `command_change_rebuilds`: take a state where every edge of `m` is clean and `Inv` holds, such as the result of a build. Change any commands while keeping each edge's inputs, outputs and depfile flag. Building the new manifest gives correct contents and runs every changed edge that has an output.
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
- `restat` and `generator` are ignored; Stage 7 adds `restat`.

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
