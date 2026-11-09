# Stages 5 to 7 notes: the Ninja model

## Stage 5: the static model and incremental soundness

### Definitions

- `Basic.lean` holds the model. `MEdge` is what the model needs from an edge: all outputs, the explicit and implicit inputs, and the evaluated command from Stage 4. `Manifest.medges` lists them in manifest order.
- The state `St V` has `fs : Path → Option (V × Nat)` for contents and mtimes, `log : Path → Option (String × Nat)` for the build log, and a `clock`.
- `St.dirty` follows `DependencyScan::RecomputeOutputDirty` in Ninja 1.13 for edges without `restat` or `generator`. An output is dirty when it is missing, when its mtime is older than the newest input, when it has no log entry, when the logged command differs, or when the logged time is older than the newest input. An edge is dirty when any output is dirty.
- `St.run` writes every output and its log entry at the fresh time `clock + 1`. `St.edit` writes a source at a fresh time. `buildTrace` visits edges in order, runs the dirty ones, and returns the edges it ran; `ninjaBuild` keeps the final state.
- `Sched es` says the order is a schedule. No edge reads its own outputs or a later edge's outputs, and no two edges share an output.

Dirtiness is decided when the model visits an edge, from the state at that moment. An edge whose input was rebuilt earlier in the same run has an input newer than its outputs, so the mtime check makes it dirty (`outDirty_of_newer`). This is how the model gets Ninja's dirty propagation, and it is the same rule Ninja's `Plan::CleanNode` applies when it rechecks an edge mid-build.

### The invariant

`Inv exec es st` says every mtime is at most the clock (`Fresh`), and every edge the model would skip is `Consistent`: each output holds what `exec` computes from the edge's current inputs. Three facts carry the proofs.

- `inv_step`: running or skipping any edge of a schedule keeps `Inv`. A run writes only that edge's outputs, at a fresh time. Any other edge that reads one of them then has a newer input and is dirty, and every other edge sees no change (`edgeOK_of_write`).
- `inv_edit`: a source edit keeps `Inv` for the same reason.
- `build_clean`: after one pass in schedule order every edge is clean. An edge is clean right after its turn, and later edges never write its inputs or outputs.

A clean edge under `Inv` is consistent, and consistent edges give a correct store (`correct_of_consistent`).

### Theorems

- `ninjaBuild_clean_correct`: from an empty build log, a build gives contents `Correct` for `denote exec m`.
- `ninjaBuild_sound` (headline): start from a fresh state whose contents are `Correct`, apply any list of source edits, and build. The contents are `Correct` for the edited sources. `ninjaBuild_eq_cleanBuild` restates this as equality with `cleanBuild`.
- `ninjaBuild_idem`: building the result of a build runs no edges and leaves the state unchanged.
- `ninjaBuild_after_interrupt`: stopping after any prefix of the schedule keeps `Inv`, so the next full build is correct. Writes are atomic in the model.
- `command_change_rebuilds`: take a state where every edge of `m` is clean and `Inv` holds, such as the result of a build. Change any commands while keeping each edge's inputs and outputs. Building the new manifest gives correct contents and runs every changed edge that has an output.
- `sched_emit`: every emitted manifest is a schedule. `dsl_sound` and `dsl_clean` combine this with `denote_emit`: building `emit g` gives `cleanBuild` of `g.spec exec`.

`ninjaBuild_sound` asks for less than the plan states. It needs the contents to be correct and the state to be fresh, and it makes no demand on the build log. The proofs go through the weaker `Inv`, which `sound_of_inv` exposes.

### Assumptions

- `exec` is a function, so commands are deterministic. Each output's task fetches exactly the edge's explicit and implicit inputs, so commands read only declared inputs by construction.
- Mtimes are faithful. The clock is at least every recorded mtime (`Fresh`), and the only writes are `run` and `edit`, each at a fresh, strictly larger time. Nothing changes files during a build.
- Source edits target sources: paths that no edge outputs.

### Where the model differs from Ninja

- The model builds every edge. Ninja builds the requested targets, or the `default` targets when none are given, and their dependencies. The two agree when the defaults cover every edge, as in `examples/hello-c`.
- A missing source reads as `default` contents with mtime 0. Ninja stops with "missing and no known rule to make it".
- The log entry records the time the outputs were written. Ninja records the command's start time, so an input edited while its command runs makes the edge dirty next time. The model has no edits during a build, so the two records order the same way against every input.
- Ninja stores a hash of the command, and the model stores the command string. A hash collision would make Ninja skip an edge the model runs.
- Phony edges are treated as commands with an empty command line. The DSL does not emit them.
- `restat`, `generator` and depfiles are ignored. The DSL does not emit them in Stage 5; Stages 6 and 7 add depfiles and `restat`.
- Edges run one at a time in manifest order. Stage 7 covers other schedules.

### Tests

`test/MiseTest/Stage5.lean` runs hello-c in the model with a symbolic `exec`. It checks the edges run on a clean build, on a second build (none), after editing a `.c` file, after editing the shared header, and after deleting an object. It also checks the contents against `cleanBuild`, including after an interrupted build.
