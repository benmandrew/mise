# mise

A Lean 4 front end for Ninja. Users describe a build in Lean, `mise` emits `build.ninja`, and proofs show the emitted build is correct and incrementally sound relative to an abstract model of Ninja. The full plan is in `PLAN.md` (local only, gitignored). Scope stops after Stage 7; Stages 8 and 9 are out.

## Conventions

- Lean `v4.35.0`, no Mathlib, no Batteries so far. Ask before adding Mathlib.
- Dependencies come from `flake.nix` (Lean, Ninja, Python, C compiler from nixpkgs); `.envrc` loads it. The flake fails if `lean-toolchain` and nixpkgs' `lean4` disagree, so bump both together.
- Library `Mise`, one directory per stage: `Mise/Task` (1), `Mise/Spec` (2), `Mise/Syntax` (3), `Mise/Frontend` (4), `Mise/Model` (5–7). Each has a `NOTES.md` with definitions, deviations and assumptions.
- No `axiom` declarations. Assumptions are structure fields or theorem hypotheses.
- `README.md` stays minimal: a summary, the quick start and links. User documentation lives in `docs/` (usage, theorems, trust base, testing).
- `scripts/check.sh` is the acceptance gate: build, no `sorry`/`admit`, and `#print axioms` over `test/MiseTest/Axioms.lean` showing only `propext`, `Classical.choice`, `Quot.sound`. Add every headline theorem to that file. Restate end-to-end results in `Mise/Headline.lean` and rerun `scripts/trusted.sh`, which regenerates `docs/trusted.md` and `docs/headline.typ` (`check.sh` fails if either is stale, or if a trusted definition has no docstring). Give each name a headline statement uses a `Gloss:` template in its docstring; `scripts/trusted.sh --pdf` builds the PDF (not committed).
- Lean tests live in `test/MiseTest/` (library `MiseTest`); shell tests against real Ninja live in `test/` and write to `test/out/` (gitignored).
- Proof style: generated equation lemmas for functions with nested `match` are awkward; state small unfolding lemmas via `rw [f.eq_def]; simp` (see `Mise/Syntax/RoundTrip.lean`).
- Commit per stage on a `stage-N` branch, then fast-forward `main`. Commits are signed. `PLAN.md` is never committed.

## Decisions to escalate

Adding Mathlib, weakening a headline theorem, adding an `Env` assumption the plan does not list, changing the `Task` representation, or supporting Ninja features outside the Stage 3 subset.

## Status

- Stage 1: done.
- Stage 2: done. `Acyclic` is data, not a Prop (see `Mise/Spec/NOTES.md`).
- Stage 3: done. `test/stage3-diff.sh` is the differential test against real Ninja (now also checks evaluated commands).
- Stage 4: done. `Mise/Frontend/Eval.lean` models Ninja variable evaluation; `test/stage4-hello.sh` builds `examples/hello-c`. Examples are `mise.toml` files read by the `mise` executable (`mise gen`, `mise build`); the shell tests cover TOML → `mise` → Ninja. The Lean model tests use their own DSL graphs in `test/MiseTest/Fixtures.lean`.
- Stage 5: done. Proofs go through the invariant `Inv` in `Mise/Model/Sound.lean`; `dsl_sound` is the end-to-end theorem.
- Stage 6: done. Depfile rules, a deps log in the model, `reach_sound` for any history from empty logs. `test/stage6-props.sh` is the property harness against real Ninja: edit sequences covering every ordered triple of edit kinds, in parallel, with ccache (about 80 seconds on 8 cores; `--order 2` for a 30-second run).
- Stage 7: done. `restat` with `Sem.keep`/`keep_eq`; `build_minimal` and `trace_nodup` in `Mise/Model/Minimal.lean`, `parallel_equiv` in `Mise/Model/Parallel.lean`. The harness also checks early cutoff and varies `-j`.
- TOML parser: `test/toml-diff.sh` checks `Mise/Frontend/Toml.lean` against Python's `tomllib` on random documents (`test/toml_diff.py`, printer `test/MiseTest/TomlJson.lean`). No round-trip theorem: the parser is `partial`.
- Command wrapper: `rule` wraps every command in `wrapCommand` unless `wrap := false` (TOML `wrap = false`). It restores the old outputs when the command fails or leaves an output missing, and for `restat` rules keeps an output `cmp` finds unchanged. `Mise/Model/Cmp.lean` models it as `script`; `Mise.Headline.wrapped_run` shows a failed run leaves the state unchanged. `test/wrap-outputs.sh` and `test/restat-cmp.sh` test it.
- TOML conveniences: `source-globs` (`Mise/Frontend/Glob.lean`), `foreach` builds, `%` inputs, builds in any order (sorted in `decode`) and `[aliases]`, all expanded in `Toml.lean` before `Graph.check`. Aliases are `phony` edges (`Graph.aliases`); `denote` and `medges` read `Elab.cmdEdges`, which drops them (`cmdEdges_emit`). `test/sugar.sh` tests them against real Ninja. No always-run targets: they would break `rebuild_noop`.
- Random-graph harness: `test/fuzz.sh` generates graphs and edit scripts in `test/MiseTest/Fuzz.lean`, runs the model on them, and checks real Ninja runs exactly the model's edges and leaves its contents. A failing case is shrunk to a minimal description in `test/out/fuzz/shrunk/`; `--fz PATH` tests a mutant helper.
- Model mutants: `test/mutants.sh` applies each mutant in `test/mutants.py` to a copy of the tree and rebuilds only `fuzzgen` (`Fuzz.lean` imports `Mise.Model.Basic` alone, which holds no proofs), then reports which check kills it.
- CI: `.github/workflows/ci.yml` runs per PR (`check.sh`, `ninja-matrix.sh --fuzz 150` per supported release, cheap extras); `nightly.yml` runs the heavy harnesses daily, skipped when `main` has not moved since the last successful run. Shared setup and caches in `.github/actions/setup`. Linux (`ubuntu-latest`) is the main platform; macOS runs only the Ninja conformance jobs and the macOS-only harnesses (sandbox, tracer, determinism, HFS+ mtime faults). See the CI section of `docs/testing.md`.
