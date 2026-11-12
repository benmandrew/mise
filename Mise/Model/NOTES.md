# Stages 5 to 7 notes: the Ninja model

Stages 6 and 7 generalised the Stage 5 model in place. Without depfile or `restat` edges it reduces to Stage 5, and `ninjaBuild_sound_static` restates the Stage 5 headline.

## Definitions

- `MEdge` (`Basic.lean`) holds outputs, explicit and implicit inputs (`ins`), order-only inputs (`oo`), the command, and the `dyn` and `restat` flags; `Manifest.medges` lists them. `MEdge.task` fetches `ins` in order and applies `sem.exec` from `Sem V`.
- `St V` has `fs : Path → Option (V × Nat)`, `log : Path → Option (String × Nat)`, `deps` (Stage 6) and a `clock`.
- `St.dirty` follows `DependencyScan::RecomputeOutputDirty` in Ninja 1.13 without `generator`: an output is dirty when missing, older than its newest input, unlogged, logged with another command, or logged before its newest input.
- `St.run` writes outputs, log and deps entries at `clock + 1`; `St.edit` writes a source at a fresh time. `buildTrace` runs dirty edges in order; `ninjaBuild` keeps the final state.
- `Sched es`: no edge reads its own or a later edge's outputs, order-only inputs included, and outputs are unique.
- Dirtiness is decided on each visit, so a rebuilt input makes readers dirty (`outDirty_of_newer`), as in `Plan::CleanNode`.
- (Stage 6) A `depfile := true` rule emits `depfile = ${out}.d` and `deps = gcc`; `dynEdge1` turns `mayReadGenerated` handles into order-only inputs. `Graph.isDyn` and `EdgeInfo.isDyn` mark edges that read the *deps log*.
- (Stage 6) A depfile command means the task `sem.dyn cmd`. The plan gives each DSL edge its own task; a function of the command keeps `Graph` independent of the value type.
- (Stage 6) `St.deps` maps each output to its command's last reads. `St.effIns e o` is `ins` plus recorded deps for a depfile edge, or `none` (dirty) with no entry.
- (Stage 6) A path is `Allowed` for an edge when no edge outputs it or it is an input. `Reads sem es`, the *static-ancestor condition*, says depfile commands fetch only allowed paths on every branch; `DepsOK` says the same of deps entries.
- (Stage 7) A `restat := true` rule emits `restat = 1`, carried by `Graph.isRestat` and `EdgeInfo.isRestat`.
- (Stage 7) `Sem` gains `keep : V → V → Bool` with `keep_eq : keep a b = true → a = b`, the plan's *Env* field for early cutoff. A `restat` run leaves an output untouched when `keep` holds (`St.kept`). Defaults never keep.
- (Stage 7) A kept output's log time advances past its mtime, so for `restat` edges `St.outDirty` compares only the log time, as Ninja does.

## Proof

`Inv sem es st` combines `Fresh` (times at most the clock), `DepsOK`, and `Consistent` for every edge the model would skip. `inv_step` and `inv_edit` preserve it because a write makes every reader dirty (`edgeOK_of_write`); `build_clean` and `correct_of_consistent` give correctness, and `sound_of_inv` exposes it. (Stage 6) `consistent_transfer` applies `run_eq_of_agree` from Stage 1, and `run_self` shows a run leaves its edge consistent.

## Theorems

- (Stage 5) `ninjaBuild_clean_correct`: from empty logs, a build gives contents `Correct` for `denote sem m`.
- (Stage 5) `ninjaBuild_sound_static`: with no depfile edges, from a fresh state with `Correct` contents, any source edits then a build give `Correct` contents. It makes no demand on the build log, less than the plan states. `ninjaBuild_sound` is the general form, also asking that deps entries be allowed and complete.
- (Stage 5) `ninjaBuild_eq_cleanBuild`: soundness as equality with `cleanBuild`.
- (Stage 5) `ninjaBuild_idem`: a second build runs nothing and changes nothing.
- (Stage 5) `ninjaBuild_after_interrupt`: any schedule prefix keeps `Inv`, given atomic writes.
- (Stage 5) `command_change_rebuilds`: from a clean state under `Inv`, changing commands but not inputs, outputs or flags gives correct contents and reruns every changed edge with an output.
- (Stage 5) `sched_emit`: every emitted manifest is a schedule.
- (Stage 6) `reach_sound` (headline): for every state with `Reach sem es st`, reached from empty logs by edits and steps of any edges in any order, a build is correct and a second build runs nothing.
- (Stage 6) `inv_of_reach`: reachable states satisfy `Inv`.
- (Stage 6) `fetched_up_to_date`: on an edge's turn, every generated path its command reads comes from an earlier, clean edge.
- (Stage 6) `reads_emit`: `Graph.DynOK` gives `Reads` for the emitted manifest, and `Graph.acyclic` builds the acyclicity witness with edge positions as ranks.
- (Stage 6) `dsl_sound`: for a valid graph with `Graph.DynOK`, after any reachable history, building the emitted manifest gives `cleanBuild` of `g.spec sem` and a second build runs nothing.
- (Stage 7) `trace_nodup`: a schedule whose edges have outputs runs each edge at most once; `trace_sublist`: the edges run are a sublist of the schedule.
- (Stage 7) `build_minimal`: an edge that runs was dirty beforehand or has a checked input written after `st.clock` by an edit or an earlier run. `St.outDirty_cause` lists the dirty cases, `build_minimal_clean` drops the first for clean states, and `run_cause` is the one-edge form.
- (Stage 7) `restat_cutoff`: a run that keeps every output changes no other edge's dirtiness, and `St.kept_not_newer` keeps a kept output out of `build_minimal`.
- (Stage 7) `wrapRun_content`, `wrapRun_kept_iff`, `wrapRun_fail` (`Cmp.lean`): the DSL's `cmp` wrapper leaves contents as the command wrote them, keeps an output's file exactly when the command wrote the old contents again, and changes no file on failure. `run_withCmp`: under `Sem.withCmp` a `restat` run writes the files as the wrapper does. No new assumption; what remains is that the script behaves as `wrapRun` says.
- (Stage 7) `parallel_equiv`: under `Inv`, any permutation of the manifest that is a `Sched` gives the same contents and leaves every edge clean. `parallel_equiv_reach` covers any history from empty logs, `dsl_parallel` covers emitted manifests, and `schedAcyclic` builds a schedule's acyclicity witness.
- (Stage 7) `parallel_same_edges`: under the same hypotheses, the edges run in the two orders are permutations of each other, so each order runs the same edges, each at most once (`trace_nodup_sched`, which needs no hypothesis on outputs). `parallel_same_edges_reach` and `dsl_same_edges` are the forms for any history and for emitted manifests. The proof uses `trace_mem_iff`: an edge runs when it was dirty before the build or an input it checks ends the build newer than the old clock. It also uses `written_iff`: an output is written when its edge ran and did not keep it, which `St.keptWith` decides from the final contents. Both orders end with the same contents, so induction along the manifest order gives the same edges. Early cutoff cannot make the orders differ: an edge that reads a `restat` output comes after its producer in every schedule, and whether that producer keeps the output depends only on its inputs' contents.

## Assumptions

- (Stage 5) `sem.exec` is a function, and a static task fetches exactly `ins`, so static commands are deterministic and read only declared inputs.
- (Stage 5) Mtimes are faithful: only `run` and `edit` write, each at a fresh, larger time, and nothing changes files during a build.
- (Stage 5) Source edits target paths that no edge outputs.
- (Stage 6) *Trace completeness*: the deps entry is exactly the task's reads. Extra depfile paths only add identical rebuilds, unless later edges write them, which breaks idempotence.
- (Stage 6) `Graph.DynOK` stays a hypothesis, since a C compile can include any file its contents name.

## Where the model differs from Ninja

- `ninjaBuild` builds every edge, where Ninja builds the requested or `default` targets. `Reach` covers partial builds.
- A missing input reads as `default` with mtime 0, where Ninja stops or rebuilds. The model has no deletions.
- The log records the write time, where Ninja records the start time, also for kept `restat` outputs. With no edits during a build both order the same way against every input.
- Ninja stores a command hash, the model the command string, so a collision would make Ninja skip an edge the model runs.
- Phony edges have an empty command; the DSL does not emit them. `generator` is ignored.
- (Stage 6) The model records deps for every output of every edge, where Ninja keys the deps log by the first output of edges with `deps`.
- (Stage 7) A parallel run is the sequence of its commands by start time, assuming each reads at the start and writes at the end. Ninja's ordering makes that sequence a `Sched`. The schedule check in `test/fuzz.py` tests both on every build (see `docs/testing.md`).
- (Stage 7) Two orders agree on contents, dirtiness and the edges they run, but not on mtimes or log times.
- (Stage 7) A `restat` command always produces every output, where Ninja treats a missing one as unchanged. The DSL's `cmp` wrapper turns a missing output into a failure, so this holds for wrapped rules.

## The no-hazard condition (Stage 7)

Spall et al. ([Forward build systems, formally](https://doi.org/10.1145/3497775.3503687)) call a build free of *hazards* when no command writes a file another unordered command reads or writes. Here that condition is `Sched` with `Reads`, so unordered commands read nothing the other writes and write disjoint outputs.

## Tests

`test/MiseTest/Stage6.lean`, `test/MiseTest/Stage7.lean` and `test/stage6-props.sh`; see `docs/testing.md`.
