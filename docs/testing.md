# Testing

Run the tests in the Nix shell (`nix develop`, or direnv with `.envrc`), so that they use the Ninja, Python and compiler that `flake.lock` pins. Shell tests write to `test/out/`. The header comment of each script gives its arguments.

## Running the harnesses

`test/harnesses.toml` is the *registry* of every harness and continuous integration (CI) job. An entry gives the command, the flake shell, the platforms, the run time and the files the harness depends on. `test/run` reads it:

- `test/run list` prints every harness and job.
- `test/run NAME` runs one harness, and `test/run NAME:quick` runs a short version. Arguments after `--` go to each harness named.
- `test/run ci.KEY` and `test/run nightly.KEY` run the harnesses of one CI job.
- `test/run lint` checks that the workflows match the registry, and that some harness lists every file under `test/` and `fuzz/`.

`test/run` enters the flake shell a harness needs and skips a harness for another platform.

## Harnesses

| Harness | What it checks |
|---|---|
| `check` | The acceptance gate, `scripts/check.sh`. It builds everything (the `#guard` tests in `test/MiseTest/` run during the build), rejects `sorry` and `admit`, checks the axioms of the theorems in `test/MiseTest/Axioms.lean`, checks that the generated docs are current and runs `test/run lint`. |
| `stage3-diff` | The parser and evaluation models read 100 random manifests as Ninja does, and both reject 17 malformed ones. |
| `stage4-hello` | `examples/hello-c` builds and runs, and the DSL's commands match `ninja -t commands`. |
| `sugar` | `source-globs`, `foreach`, `%` inputs and aliases build what they should against real Ninja. |
| `wrap-outputs`, `restat-cmp` | The command wrapper. A failed or incomplete command keeps the old outputs and mtimes, and a `restat` output with unchanged contents keeps its mtime. |
| `stage6-props` | Edit sequences on each example that cover every ordered triple of edit kinds, at random `-j`. After each build the products match a clean build, `ninja -n` has no work and `ninja -t missingdeps` finds nothing. |
| `graph-fuzz` | The random-graph harness, below. |
| `build-fuzz` | The in-process build fuzzer, below. |
| `parser-fuzz-text`, `parser-fuzz-gen` | The parser fuzzer, below. |
| `mutants`, `mutants-inproc` | Each mutant in `test/mutants.py` changes one definition in `Mise/Model/Basic.lean`, and the random-graph harness (or the in-process fuzzer) must catch it. |
| `trust-mutants` | Each mutant in `test/trust-mutants.py` weakens a definition that a statement in `Mise/Theorems.lean` uses, and a test in `test/MiseTest/` must catch it. |
| `ninja-matrix` | `stage3-diff`, `stage4-hello`, `stage6-props --order 2` and `graph-fuzz` on each supported Ninja release, 1.12.1 and 1.13.2. It also checks that 1.10.2 and 1.11.1 refuse an emitted manifest. |
| `toml-diff` | The `mise.toml` parser against Python's `tomllib` on random documents. When the Lean parser accepts a document, `tomllib` must read the same value. When only `tomllib` accepts it, the Lean error must say the feature is not supported. |
| `conf-sandbox` | Trust item 2, on macOS. Every command runs under `sandbox-exec`, which kills it on a read outside its inputs and the toolchain, or a write outside its outputs. |
| `conf-depfiles` | Trust item 3, on macOS. A tracer logs the files each command opens. Each depfile command may read, in the build directory, only its inputs and the dependencies Ninja recorded from its depfile. |
| `conf-determinism` | Trust item 2, on macOS. Two clean builds in different directories, at different times, `-j` levels and locales, give identical products. |
| `mtime-faults` | Breaks trust item 5 on purpose and records what Ninja does. It passes or fails nothing, and writes `test/out/mtime-faults/report.txt`. |

`log-old-time` is the one mutant no check catches, because it is equivalent to the model. The log time is compared only with input mtimes, and no input carries the run's own time.

A proof cannot catch a mutant that makes its theorem weaker, because the weaker theorem is still true. So `trust-mutants` replaces every library proof with `sorry` in a copy of the tree, and only the tests can catch a mutant. Its table separates kills that *evaluate*, where `decide` or `#guard` computes a false result, from kills that *elaborate*, where a test stops type-checking. A test can stop type-checking because of its shape alone, such as a constructor that gained an argument. So a test meant to catch a mutant closes its side conditions with `decide`, or with a tactic such as `reach_init` in `test/MiseTest/Reachable.lean`. Every mutant should be caught in `Boundary.lean` or `Reachable.lean`: the harness builds those two first, and the rest of `MiseTest` only for a mutant they miss.

`trust-mutants` builds mutants inside long-lived Lean processes (`test/trust-mutants.lean`), which elaborate the mutated module and the modules that import it in memory, and load the unchanged modules once. All the modules then share one environment, so the harness also runs the unmutated tree this way, and stops if that fails. `--via lake` runs `lake build` for each mutant instead, for when a Lean release changes the internal API this depends on.

The in-process build uses Lean's internal elaboration API, which has no stability promise between releases. It was written against Lean `v4.35.0` and calls `Lean.importModules` (with `loadExts := true`, after `Lean.enableInitializersExecution`, which each call clears), `Lean.Parser.parseHeader`, `Lean.Elab.IO.processCommands`, `Lean.Elab.Command.mkState` and `Lean.Environment.setMainModule`, and sets the options `debug.byAsSorry` and `Elab.async`. After a toolchain bump, run `test/run trust-mutants`. If `test/trust-mutants.lean` no longer compiles, every mutant comes back as an error naming `--via lake`. If it compiles but the API has changed meaning, the control run fails. In either case, run with `--via lake` and fix the file, or make `--via lake` the default until it is fixed.

## The random-graph harness

`test/fuzz.sh` generates random graphs with `lake exe fuzzgen` (`test/MiseTest/Fuzz.lean`), each with a sequence of steps. A step makes some edits, then builds every edge, some targets, or with one command failing. Every edge runs one helper, `test/fz.c`, and `Fuzz.lean` gives the model the same semantics. `test/fuzz.py` replays the steps against real Ninja at a random `-j`. After each build it checks four things:

- exactly the model's edges ran, each once, and Ninja failed exactly when the model says;
- every output holds the model's contents;
- `ninja -n` has no work;
- the runs form a schedule (below).

Source edits, deleting both logs, and partial and failed builds stay inside `Reach`, so the theorems cover them. Other steps (deleting a product or one log, adding or removing an edge) leave it, and for them the harness tests only the model's dirtiness rule. A failing case is shrunk to a minimal one in `test/out/fuzz/shrunk/<i>.json`, and `test/fuzz.py test/out/fuzz/shrunk <i>` replays it.

`--opts absent` gives some edges a wrapped command that leaves out outputs. The wrapper must fail each such run and change nothing. `--opts absent,nowrap` runs the same commands unwrapped, a known difference from the model ([`Mise/NOTES.md`](../Mise/NOTES.md)), so `fuzz.py` relaxes its checks with `--missing-ok`.

The *schedule check* tests the assumption behind `parallel_equiv`: a parallel run has the effect of its commands in order of start time. `fz` logs six timestamps per run and the files it read. Every run must read before its first write and start after each producer of its inputs has finished. Each command sleeps a random 0 to 20 ms, so that commands overlap.

## The fuzzers

The fuzzers link Ninja's own code and run in `nix develop .#fuzz`, which `test/run` enters.

**Parser fuzzer.** `fuzz/fuzz.sh parser --mode text|gen` links Ninja's manifest parser with the model in `fuzz/MiseFuzz/Parser.lean`. When the model accepts a manifest, Ninja must accept it and read the same edges, evaluated bindings and defaults. Inputs the model rejects are not checked, because Ninja accepts more than the subset. In `text` mode libFuzzer mutates manifest text. In `gen` mode the input bytes drive the manifest generator, so the model accepts every input. Failing inputs go to `test/out/fuzz-parser-MODE/crash`, and `--repro FILE` replays one.

**In-process build fuzzer.** `fuzz/fuzz.sh build` links Ninja 1.13.2's build logic, the model and the random-graph generator into one binary over an in-memory file system. The front of an input drives the generator and the back drives the schedule. It checks what `test/fuzz.py` checks, except the timestamps and `-t missingdeps`. A mismatch goes to `test/out/fuzz/inproc/<n>.json`, and `test/fuzz.py test/out/fuzz/inproc <n>` replays it against real Ninja. It does not cover real mtimes, real processes or the real wrapper.

## Continuous integration

`.github/workflows/ci.yml` runs on every pull request and push to `main`: `check` and `trust-mutants`, `ninja-matrix:quick` on each supported release, and the fast extras. `nightly.yml` runs the heavy harnesses daily, or on demand with `gh workflow run nightly.yml -f jobs=KEY`. Each job's step is `test/run ci.KEY` or `test/run nightly.KEY`, so the registry decides what a job runs. Linux is the main platform. macOS runs the Ninja conformance jobs and the macOS-only harnesses.

The first job of each workflow, `changed`, runs `test/run affected`. It skips a job when none of the job's files has changed since the last commit on which the job succeeded, and `test/run deps KEY` lists those files. GitHub counts a skipped job as passed for a required check.
