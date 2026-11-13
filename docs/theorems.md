# Theorems

To check what is proved, start with `Mise/Theorems.lean`. It restates the end-to-end results in terms of the DSL graph a user writes, and each proof applies a theorem from the table below. Lean checks the proofs, so a reviewer has to confirm two things: that each statement says what its docstring says, and that the definitions it uses mean what their names suggest. [trusted.md](trusted.md) lists those definitions with their sizes, in an order where each file uses only the ones before it. `scripts/trusted.sh` generates the list from the statements, and `scripts/check.sh` fails if it is out of date or if a trusted definition has no docstring. What the proofs assume is in [trust.md](trust.md).

The same script writes `docs/theorems.typ`, the Typst source of a PDF for reviewing the statements without reading Lean. `scripts/trusted.sh --pdf` inside `nix develop` builds it as `docs/theorems.pdf`, which is not committed, and `check.sh` fails if the `.typ` file is stale. A theorem means only what the definitions in its statement mean, so the PDF shows the *core theorems* (those whose docstring has the line `Review: core`) with the definitions their statements depend on. Each core theorem has its docstring, its statement as written in the source, and an English translation, which `test/MiseTest/Gloss.lean` produces from the elaborated statement; its module docstring gives the rules. A named definition is translated with the template on the `Gloss:` line of its docstring, and a name without a template appears in Lean notation and is listed under Warnings at the end. The definitions follow in reading order, those a core statement names and those they name in turn, each with its docstring, highlighted source and any template the translation used. Every source location links to those lines on GitHub. The printer and the parser are shown but not expanded, since `meaning` and `test/stage3-diff.sh` cover them. A closing paragraph names every trusted declaration left out and lists the other headline theorems with their docstrings.

The library has one directory per stage, each with a `NOTES.md` giving its definitions, assumptions and deviations from Ninja. `test/MiseTest/Axioms.lean` lists the headline theorems, and `scripts/check.sh` fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`. There are no `axiom` declarations.

| Stage | Directory | Headline theorems |
|---|---|---|
| 1 | `Mise/Task` | `run_eq_of_agree`: a task gives the same result on stores that agree on what it fetches. |
| 2 | `Mise/Spec` | `correct_unique`: an acyclic build has one correct store, and `cleanBuild` computes it. |
| 3 | `Mise/Syntax` | `parse_print`: the parser model reads a printed manifest back to the same syntax tree. |
| 4 | `Mise/Frontend` | `denote_emit`: the emitted manifest, read through a model of Ninja's evaluation, means what the DSL means. |
| 5 | `Mise/Model` | `ninjaBuild_sound_static`, `ninjaBuild_idem`: an incremental build is correct, and a second build runs nothing. |
| 6 | `Mise/Model` | `reach_sound`, `dsl_sound`: the same after any history of edits and partial builds, with depfiles. |
| 7 | `Mise/Model` | `build_minimal`, `trace_nodup`: only edges with a changed input run, each at most once. |
| 7 | `Mise/Model` | `restat_cutoff`: a `restat` run that keeps its outputs rebuilds nothing downstream. |
| 7 | `Mise/Model` | `parallel_equiv`, `parallel_same_edges`: any order consistent with the dependencies gives the same contents and runs the same edges. |
| 7 | `Mise/Model` | `run_withCmp`, `wrapRun_kept_iff`: the DSL's command wrapper keeps a `restat` output exactly when the command wrote the old contents again, which is the model's run under `Sem.withCmp`. |
| 7 | `Mise/Model` | `script_fail`, `script_ok`, `reach_runWrapped`: a failed wrapped run changes no file and leaves the state reachable, and a successful one writes or keeps every output. |
