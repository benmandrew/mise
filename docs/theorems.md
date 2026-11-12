# Theorems

To check what is proved, start with `Mise/Headline.lean`. It restates the end-to-end results in terms of the DSL graph a user writes, and each proof applies a theorem from the table below. Lean checks the proofs, so the reader's work is to confirm that each statement says what its docstring says, and that the definitions it uses mean what their names suggest. [trusted.md](trusted.md) lists those definitions with their sizes, in an order where each file uses only the ones before it. `scripts/trusted.sh` generates the list from the statements, and `scripts/check.sh` fails if it is out of date.

The library has one directory per stage, each with a `NOTES.md` giving its definitions, assumptions and deviations from Ninja. `test/MiseTest/Axioms.lean` lists the headline theorems, and `scripts/check.sh` fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`. There are no `axiom` declarations.

| Stage | Directory | Headline theorems |
|---|---|---|
| 1 | `Mise/Task` | `run_eq_of_agree`: a task gives the same result on stores that agree on what it fetches. |
| 2 | `Mise/Spec` | `correct_unique`: an acyclic build has one correct store, and `cleanBuild` computes it. |
| 3 | `Mise/Syntax` | `parse_print`: the parser model reads a printed manifest back to the same syntax tree. |
| 4 | `Mise/Frontend` | `denote_emit`: the emitted manifest, read through a model of Ninja's evaluation, means what the DSL means. |
| 5 | `Mise/Model` | `ninjaBuild_sound_static`, `ninjaBuild_idem`: an incremental build is correct, and a second build runs nothing. |
| 6 | `Mise/Model` | `reach_sound`, `dsl_sound`: the same after any history of edits and partial builds, with depfiles. |
| 7 | `Mise/Model` | `build_minimal`, `trace_nodup`, `restat_cutoff`, `parallel_equiv`, `parallel_same_edges`: only edges with a changed input run, each at most once; a `restat` run that keeps its outputs rebuilds nothing downstream; any order consistent with the dependencies gives the same contents and runs the same edges. |
