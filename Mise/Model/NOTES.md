# Stages 5 to 7 notes: the Ninja model

Without depfile or `restat` edges the model reduces to the static case, whose soundness `ninjaBuild_sound_static` states.

## Definitions

- `MEdge` (`Basic.lean`) holds outputs, explicit and implicit inputs (`ins`), order-only inputs (`oo`), the command, and the `dyn` and `restat` flags; `Manifest.medges` lists them. `MEdge.task` fetches `ins` in order and applies `sem.exec` from `Sem V`.
- `St V` has `fs : Path → Option (V × Nat)`, `log : Path → Option (String × Nat)`, `deps` and a `clock`.
- `St.dirty` follows `DependencyScan::RecomputeOutputDirty` in Ninja 1.13 without `generator`: an output is dirty when missing, older than its newest input, unlogged, logged with another command, or logged before its newest input. Ninja 1.10.2 and 1.11.1 rerun a kept `restat` depfile output built without a deps entry, so the oldest supported release is 1.12.1 (`docs/testing.md`).
- `St.run` writes outputs, log and deps entries at `clock + 1`; `St.edit` writes a source at a fresh time. `buildTrace` runs dirty edges in order; `ninjaBuild` keeps the final state.
- `Sched es`: no edge reads its own or a later edge's outputs, order-only inputs included, and outputs are unique.
- Dirtiness is decided on each visit, so a rebuilt input makes readers dirty (`outDirty_of_newer`), as in `Plan::CleanNode`.
- A `depfile := true` rule emits `depfile = ${out}.d` and `deps = gcc`; `dynEdge1` turns `mayReadGenerated` handles into order-only inputs. `Graph.isDyn` and `EdgeInfo.isDyn` mark edges that read the *deps log*.
- A depfile command means the task `sem.dyn cmd`. Each domain-specific language (DSL) edge thus has its own task, and `Graph` stays independent of the value type.
- `St.deps` maps each output to its command's last reads. `St.effIns e o` is `ins` plus recorded deps for a depfile edge, or `none` (dirty) with no entry.
- A path is `Allowed` for an edge when no edge outputs it or it is an input. `Reads sem es`, the *static-ancestor condition*, says depfile commands fetch only allowed paths on every branch; `DepsOK` says the same of deps entries.
- A `restat := true` rule emits `restat = 1`, carried by `Graph.isRestat` and `EdgeInfo.isRestat`.
- `Sem` has `keep : V → V → Bool` with `keep_eq : keep a b = true → a = b`, the plan's *Env* field for *early cutoff*. A `restat` run leaves an output untouched when `keep` holds (`St.kept`). Defaults never keep.
- A kept output's log time advances past its mtime, so for `restat` edges `St.outDirty` compares only the log time, as Ninja does.

## Proof

`Inv sem es st` combines `Fresh` (times at most the clock), `DepsOK`, and `Consistent` for every edge the model would skip. `inv_step` and `inv_edit` preserve it because a write makes every reader dirty (`edgeOK_of_write`); `build_clean` and `correct_of_consistent` give correctness, and `sound_of_inv` exposes it. `consistent_transfer` applies `run_eq_of_agree` from `Mise/Task`, and `run_self` shows a run leaves its edge consistent.

## Theorems

- `ninjaBuild_clean_correct`: from empty logs, a build gives contents `Correct` for `denote sem m`.
- `ninjaBuild_sound_static`: with no depfile edges, from a fresh state with `Correct` contents, any source edits then a build give `Correct` contents. It asks nothing of the build log, less than the plan states. `ninjaBuild_sound` is the general form, which also asks that deps entries be allowed and complete.
- `ninjaBuild_eq_cleanBuild`: soundness as equality with `cleanBuild`.
- `ninjaBuild_idem`: a second build runs nothing and changes nothing.
- `ninjaBuild_after_interrupt`: any schedule prefix keeps `Inv`, given atomic writes.
- `command_change_rebuilds`: from a clean state under `Inv`, changing commands but not inputs, outputs or flags gives correct contents and reruns every changed edge with an output.
- `sched_emit`: every emitted manifest is a schedule.
- `reach_sound` (headline): for every state with `Reach sem es st`, reached from empty logs by edits and steps of any edges in any order, a build is correct and a second build runs nothing.
- `inv_of_reach`: reachable states satisfy `Inv`.
- `deps_uniform`, `effIns_uniform`: in a reachable state every output of an edge has the same deps entry and the same checked inputs, so keying the deps log by the first output, as Ninja does, changes nothing.
- `fetched_up_to_date`: on an edge's turn, every generated path its command reads comes from an earlier, clean edge.
- `reads_emit`: `Graph.DynOK` gives `Reads` for the emitted manifest, and `Graph.acyclic` builds the acyclicity witness with edge positions as ranks.
- `dsl_sound`: for a valid graph with `Graph.DynOK`, after any reachable history, building the emitted manifest gives `cleanBuild` of `g.spec sem` and a second build runs nothing.
- `trace_nodup`: a schedule whose edges have outputs runs each edge at most once; `trace_sublist`: the edges run are a sublist of the schedule.
- `build_minimal`: an edge that runs was dirty beforehand or has a checked input written after `st.clock` by an edit or an earlier run. `St.outDirty_cause` lists the dirty cases, `build_minimal_clean` drops the first for clean states, and `run_cause` is the one-edge form.
- `restat_cutoff`: a run that keeps every output changes no other edge's dirtiness, and `St.kept_not_newer` keeps a kept output out of `build_minimal`.
- `wrapRun_content`, `wrapRun_kept_iff`, `wrapRun_fail` (`Cmp.lean`): the DSL's command wrapper leaves contents as the command wrote them, keeps a `restat` output's file exactly when the command wrote the old contents again, and changes no file on failure. `run_withCmp`: under `Sem.withCmp` every run writes the files as the wrapper does.
- `script` (`Cmp.lean`) models the wrapper as one file operation per shell command (`mv -f`, `rm -f`, `[ -e ]` and `cmp -s`), with the command as a write of some outputs and an exit status. `script_eq` computes its effect as `wrapRun`, given distinct outputs, no output that is another's `.mise-old` file, and no `.mise-old` file of an output beforehand. `script_status`: it exits 0 exactly when the command did and wrote every output. `script_fail`: a failed script changes no file. `script_ok`: a successful one writes every output at the run's time, or keeps a `restat` output's file when the contents are unchanged, and changes no other file.
- `St.runWrapped` is Ninja running an edge through the wrapper: the files are what `script` leaves, and the log and deps entries are written only on success. `runWrapped_fail`: a failed run leaves the state as it was. `runWrapped_ok`: a successful run that writes what `sem` says is `St.run` under `Sem.withCmp`. `reach_runWrapped`: either way a run of a dirty edge keeps the state in `Reach`, and `Mise.Theorems.wrapped_run` states this for emitted manifests. This adds no assumption beyond two: the script, `cmp`, `mv` and `rm` behave as `script` says, and no `.mise-old` file of an output exists outside the script.
- `parallel_equiv`: under `Inv`, any permutation of the manifest that is a `Sched` gives the same contents and leaves every edge clean. `parallel_equiv_reach` covers any history from empty logs, `dsl_parallel` covers emitted manifests, and `schedAcyclic` builds a schedule's acyclicity witness.
- `parallel_same_edges`: under the same hypotheses, the edges run in the two orders are permutations of each other, so each order runs the same edges, each at most once (`trace_nodup_sched`, which needs no hypothesis on outputs). `parallel_same_edges_reach` and `dsl_same_edges` are the forms for any history and for emitted manifests. The proof uses `trace_mem_iff` (an edge runs when it was dirty before the build or an input it checks ends the build newer than the old clock) and `written_iff` (an output is written when its edge ran and did not keep it, which `St.keptWith` decides from the final contents). Both orders end with the same contents, so induction along the manifest order gives the same edges. Early cutoff cannot make the orders differ, because an edge that reads a `restat` output comes after its producer in every schedule, and whether that producer keeps the output depends only on its inputs' contents.

## Assumptions

- `sem.exec` is a function, and a static task fetches exactly `ins`, so static commands are deterministic and read only declared inputs.
- Mtimes are faithful: only `run` and `edit` write, each at a fresh, larger time, and nothing changes files during a build.
- Source edits target paths that no edge outputs.
- *Trace completeness*: the deps entry is exactly the task's reads. Extra depfile paths only add identical rebuilds, unless later edges write them, which breaks idempotence.
- `Graph.DynOK` stays a hypothesis, since a C compile can include any file its contents name.

## Where the model differs from Ninja

- `ninjaBuild` builds every edge, where Ninja builds the requested or `default` targets. `Reach` covers partial builds.
- A missing input reads as `default` with mtime 0, where Ninja stops or rebuilds. The model has no deletions; `test/MiseTest/Fuzz.lean` deletes a product by removing it from `fs`, outside `Reach`.
- `St.run` has no failing commands; `St.runWrapped` models a wrapped one, whose failure leaves the state as it was (`runWrapped_fail`), so a build with a wrapped failure is the steps of the edges that finished. An unwrapped command (`wrap = false`) that fails after writing an output is outside the model. So is a build interrupted by a signal, after which Ninja kills the running commands and deletes the outputs they changed. `docs/testing.md` describes how the harnesses test failures.
- The log records the write time, where Ninja records the start time, also for kept `restat` outputs. With no edits during a build both order the same way against every input.
- Ninja stores a command hash and the model the command string, so a collision would make Ninja skip an edge the model runs.
- `Manifest.medges` leaves out `phony` edges, which run no command. The DSL emits one per alias, and no edge reads an alias (see `Mise/Frontend/NOTES.md`). `generator` is ignored.
- The model records a deps entry for every output of every edge, and reads it only for depfile edges, separately for each output. Ninja 1.13.2 records an entry for every output of an edge with `deps` (`src/build.cc:968-981`), but reads only the first output's entry and uses it for the whole edge (`ImplicitDepLoader::LoadDepsFromLog`, `src/graph.cc:726-747`). For a `Sched` manifest this is harmless: `deps_uniform` and `effIns_uniform` give every output of an edge the same entry and checked inputs in a reachable state. Ninja also drops the entry when the first output is newer than it (`src/graph.cc:735-743`). The entry's time is the output's mtime after the run (`src/build.cc:972`), and only a run writes an output, so under the model's assumptions this never happens.
- The depfile is `${out}.d`, and `$out` lists every explicit output, so with outputs `a` and `b` Ninja reads `a b.d`. A command cannot sensibly write that file, and Ninja treats a missing depfile as empty (`src/build.cc:1010-1021`) and records no deps, so it misses edits to included files that the model sees. `Graph.check` therefore requires one explicit output on a depfile edge (`depfileOutsOK`); implicit outputs are allowed.
- A parallel run is the sequence of its commands by start time, assuming each reads at the start and writes at the end. Ninja's ordering makes that sequence a `Sched`. `docs/testing.md` describes the schedule check that tests both.
- Two orders agree on contents, dirtiness and the edges they run, but not on mtimes or log times.
- In the model a command writes or keeps every output: `Sem` gives each output a value and `St.run` writes it. A real command can leave an output out. For a `restat` edge Ninja treats an output missing before and after the run as unchanged (`src/build.cc:931-939`), which the model matches through `keep` when the output's value is `default`, as a missing file reads. But Ninja also counts a missing output as dirty (`src/graph.cc:300-304`), so it reruns that edge in every build, where the model runs it once. Without `restat`, Ninja's dirty propagation (`src/graph.cc:181-185`) also reruns the edge's dependents in every build. Ninja can also skip an edge the model runs, when that edge reads a left-out output. `Correct` holds for such commands, but idempotence (`ninjaBuild_idem`, the second half of `reach_sound`) does not. The DSL's command wrapper turns a missing output into a failure that changes no file, so a wrapped run either is a model run or changes nothing (`reach_runWrapped`), and the assumption holds for wrapped rules. For an unwrapped command no validity check can rule this out, since it depends on the command, so it is trust-base item 4. `docs/testing.md` describes the harness for this case.

## The no-hazard condition

Spall et al. ([Forward build systems, formally](https://doi.org/10.1145/3497775.3503687)) call a build free of *hazards* when no command writes a file another unordered command reads or writes. Here that condition is `Sched` with `Reads`, so unordered commands read nothing the other writes and write disjoint outputs.

## Tests

`test/MiseTest/Stage6.lean`, `test/MiseTest/Stage7.lean`, `test/stage6-props.sh` and `test/fuzz.sh` test the model. `test/mutants.sh` mutates the definitions in `Basic.lean` and checks that the random-graph harness notices; see `docs/testing.md`.
