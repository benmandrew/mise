# Theorems

The library has one directory per stage, each with a `NOTES.md` giving its definitions, assumptions and deviations from Ninja. `test/MiseTest/Axioms.lean` lists the headline theorems, and `scripts/check.sh` fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`. There are no `axiom` declarations.

| Stage | Directory | Headline theorems |
|---|---|---|
| 1 | `Mise/Task` | `run_eq_of_agree`: a task gives the same result on stores that agree on what it fetches. |
| 2 | `Mise/Spec` | `correct_unique`: an acyclic build has one correct store, and `cleanBuild` computes it. |
| 3 | `Mise/Syntax` | `parse_print`: the parser model reads a printed manifest back to the same syntax tree. |
| 4 | `Mise/Frontend` | `denote_emit`: the emitted manifest, read through a model of Ninja's evaluation, means what the DSL means. |
| 5 | `Mise/Model` | `ninjaBuild_sound_static`, `ninjaBuild_idem`: an incremental build is correct, and a second build runs nothing. |
| 6 | `Mise/Model` | `reach_sound`, `dsl_sound`: the same after any history of edits and partial builds, with depfiles. |
| 7 | `Mise/Model` | `build_minimal`, `trace_nodup`, `restat_cutoff`, `parallel_equiv`: only edges with a changed input run, each at most once; a `restat` run that keeps its outputs rebuilds nothing downstream; any order consistent with the dependencies gives the same contents. |
