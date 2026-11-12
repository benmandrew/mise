# Theorems

To check what is proved, start with `Mise/Headline.lean`. It restates the end-to-end results in terms of the DSL graph a user writes, and each proof applies a theorem from the table below. Lean checks the proofs, so the reader's work is to confirm that each statement says what its docstring says, and that the definitions it uses mean what their names suggest. [trusted.md](trusted.md) lists those definitions with their sizes, in an order where each file uses only the ones before it. `scripts/trusted.sh` generates the list from the statements, and `scripts/check.sh` fails if it is out of date.

The same script writes `docs/headline.typ`, a Typst source for one PDF that covers the review without reading Lean. Build it with `scripts/trusted.sh --pdf` inside `nix develop`, which writes `docs/headline.pdf`. The PDF is not committed, and `check.sh` fails if the `.typ` file is stale. For each theorem it gives the docstring, the statement as written in the source, and an English translation. `test/MiseTest/Gloss.lean` produces that translation from the elaborated statement, with fixed phrases for the connectives and a template for each named definition. A template is the `Gloss:` line of the definition's docstring. In the translation, parentheses mark where each argument starts and ends. After the theorems come the trusted definitions in reading order, each with its docstring, template and highlighted source, and links to the definitions it uses. `check.sh` also fails if a trusted definition has no docstring. Any name without a template appears in Lean notation and is listed under Warnings at the end.

The library has one directory per stage, each with a `NOTES.md` giving its definitions, assumptions and deviations from Ninja. `test/MiseTest/Axioms.lean` lists the headline theorems, and `scripts/check.sh` fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`. There are no `axiom` declarations.

| Stage | Directory | Headline theorems |
|---|---|---|
| 1 | `Mise/Task` | `run_eq_of_agree`: a task gives the same result on stores that agree on what it fetches. |
| 2 | `Mise/Spec` | `correct_unique`: an acyclic build has one correct store, and `cleanBuild` computes it. |
| 3 | `Mise/Syntax` | `parse_print`: the parser model reads a printed manifest back to the same syntax tree. |
| 4 | `Mise/Frontend` | `denote_emit`: the emitted manifest, read through a model of Ninja's evaluation, means what the DSL means. |
| 5 | `Mise/Model` | `ninjaBuild_sound_static`, `ninjaBuild_idem`: an incremental build is correct, and a second build runs nothing. |
| 6 | `Mise/Model` | `reach_sound`, `dsl_sound`: the same after any history of edits and partial builds, with depfiles. |
| 7 | `Mise/Model` | `build_minimal`, `trace_nodup`, `restat_cutoff`, `parallel_equiv`, `parallel_same_edges`: only edges with a changed input run, each at most once; a `restat` run that keeps its outputs rebuilds nothing downstream; any order consistent with the dependencies gives the same contents and runs the same edges; `run_withCmp`, `wrapRun_kept_iff`: the DSL's command wrapper keeps a `restat` output exactly when the command wrote the old contents again, which is the model's run under `Sem.withCmp`; `script_fail`, `script_ok`, `reach_runWrapped`: a failed wrapped run changes no file and leaves the state reachable, and a successful one writes or keeps every output. |
 |
