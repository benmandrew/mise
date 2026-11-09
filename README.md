# mise

`mise` is a Lean 4 front end for [Ninja](https://ninja-build.org/). A build is described in a Lean *domain-specific language* (DSL), `mise` emits `build.ninja` from it, and Lean proofs show that the emitted build is *correct* and *incrementally sound* relative to an abstract model of Ninja 1.13. Ninja runs every command. The project targets Lean `v4.35.0` without Mathlib, and it contains no `axiom` declarations.

## Usage

`lake build` builds the library, the Lean tests and the `gen` executable. `gen` takes an example directory, looks up the build description registered for its name in `Main.lean`, and writes `build.ninja` into that directory.

```sh
lake build
lake exe gen examples/hello-c
ninja -C examples/hello-c
```

The full form is `lake exe gen [--commands] [--set KEY=VALUE]... DIR`. `--set` passes a parameter to the description, such as `--set cflags=-O0`. `--commands` prints the command the DSL means for each edge and writes no manifest. The registered examples are `hello-c` and `gen-header`, and the second needs `python3` for its header generator.

A description is a `Build` action. This is the whole of `examples/hello-c/HelloC.lean` apart from its imports:

```lean
def build (ps : Params) : Build Unit := do
  let mainC ← source "main.c"
  let greetC ← source "greet.c"
  let greetH ← source "greet.h"
  let cc ← rule "cc" "cc $cflags -c $in -o $out" (description := "CC $out")
  let link ← rule "link" "cc $in -o $out" (description := "LINK $out")
  let cflags := [("cflags", ps.get "cflags" "-O2 -Wall")]
  let mainO ← edge1 cc "build/main.o" [mainC] (implicitIns := [greetH]) (vars := cflags)
  let greetO ← edge1 cc "build/greet.o" [greetC] (implicitIns := [greetH]) (vars := cflags)
  let hello ← edge1 link "build/hello" [mainO, greetO]
  defaults [hello]
```

`source` declares an input file, `rule` declares a Ninja rule, and `edge1` adds an edge with one output. `rule` also takes `depfile := true` for compiles whose includes the compiler reports, and `restat := true` for commands that may leave an output untouched. `examples/gen-header/GenHeader.lean` uses both, with `dynEdge1` for the compiles that read a generated header.

## Layout

- `Mise/Task` (Stage 1): tasks as a *free monad* over fetches, with lemmas on running them and listing their dependencies.
- `Mise/Spec` (Stage 2): *build specifications* and their correctness, after Mokhov et al. ([Build systems à la carte](https://doi.org/10.1145/3236774)).
- `Mise/Syntax` (Stage 3): the Ninja *abstract syntax tree* (AST), the printer, the parser model and the round-trip proof.
- `Mise/Frontend` (Stage 4): the DSL, emission to a manifest, a model of Ninja's variable evaluation, and the meaning of a manifest.
- `Mise/Model` (Stages 5–7): the Ninja model with its *build log*, *deps log* and `restat`, and the proofs about it.
- `examples/`: the `hello-c` and `gen-header` builds. `test/`: Lean tests in `test/MiseTest/` and shell tests against real Ninja.

Each `Mise/` directory has a `NOTES.md` with its definitions, deviations and assumptions.

## Headline theorems

`test/MiseTest/Axioms.lean` lists the headline theorems of every stage. `scripts/check.sh` runs `#print axioms` over that file and fails unless each of the 40 theorems depends only on `propext`, `Classical.choice` and `Quot.sound`. The main ones are below.

- Stage 1, `run_eq_of_agree`: two stores that agree on the keys a task fetches give the same result. `run_eq_interp` and `deps_eq_interp` show that running a task and listing its fetches are interpretations of the free monad.
- Stage 2, `cleanBuild_correct` and `correct_unique`: `cleanBuild` gives a correct store, and two correct stores for the same sources are equal.
- Stage 3, `parse_print`: the parser model reads the printed form of every well-formed manifest back to the same AST.
- Stage 4, `emit_wellFormed` and `denote_emit`: every valid DSL graph emits a well-formed manifest. Read back through the model of Ninja's evaluation, that manifest means exactly what the DSL means, for every command semantics.
- Stage 5, `ninjaBuild_sound_static`: for a manifest without depfile edges, building after any source edits from a fresh, correct state gives correct contents. `ninjaBuild_idem` says a second build runs nothing, and `ninjaBuild_after_interrupt` covers a build stopped after any prefix of the schedule.
- Stage 5, `command_change_rebuilds`: changing commands gives correct contents and reruns every changed edge that has an output.
- Stage 6, `reach_sound`: take any state reached from empty logs by source edits and by steps of any edges in any order. A build from it gives correct contents, and a second build runs nothing.
- Stage 6, `dsl_sound`: given `Graph.DynOK`, the emitted manifest builds to `cleanBuild` of the DSL's meaning after any reachable history.
- Stage 7, `trace_nodup`: a build runs each edge at most once.
- Stage 7, `build_minimal`: an edge runs only when it was already dirty, or when an input Ninja checks has changed since its last run.
- Stage 7, `restat_cutoff`: a `restat` run that keeps every output changes no other edge's dirtiness. This is *early cutoff*.
- Stage 7, `parallel_equiv` and `dsl_parallel`: any build order consistent with the dependency order gives the same contents as manifest order and leaves every edge clean. For an emitted manifest those contents are `cleanBuild` of the DSL's meaning.

## Tests

- `scripts/check.sh` is the acceptance gate. It runs `lake build`, rejects any `sorry` or `admit` in the Lean sources, and runs the axiom check. The Lean tests in `test/MiseTest/` are `#guard` checks, so `lake build` runs them too.
- `test/stage3-diff.sh [N] [SEED]` is the *differential test*. It writes `N` random well-formed manifests, then compares the `ninja -t query` and `ninja -t commands -s` output predicted from each AST with real Ninja's. It also checks that Ninja rejects 17 manifests the parser model rejects. Seed 1 with 100 manifests compared 492 commands, and seeds 7 and 99 with 300 manifests each also agree.
- `test/stage4-hello.sh` builds `examples/hello-c` with Ninja and runs the binary. It then checks that `ninja -n` has no work, and that `gen --commands` matches `ninja -t commands`.
- `test/stage6-props.sh` is the property harness in `test/props.py`. It runs 200 random edit sequences on each example, with `-j1`, `-j2` or `-j8` picked at random for each build. After every build it checks each product against a clean build byte for byte, checks that `ninja -n` has no work, and checks that `ninja -t missingdeps` finds nothing.

With seed 1 the harness ran 680 edits on `hello-c` and 710 on `gen-header`, about 5 minutes in all, and every check passed.

## Trust base

The proofs cover everything from the DSL to the abstract Ninja model. `denote_emit` ties the DSL's meaning to the emitted manifest's meaning, and the Stage 5–7 theorems tie that meaning to the model's builds. `emit_wellFormed` and `parse_print` show that the printer emits the text from which the parser model reads back the AST that `emit` produced.

Six assumptions remain outside the proofs. Tests check most of them.

1. Real Ninja implements the model for the supported subset. The differential test and the property harness test this.
2. Real Ninja's parser agrees with the Stage 3 parser model on every manifest the model accepts. The differential test checks this with `ninja -t query`.
3. Commands are deterministic and read only declared or discovered inputs. `Sem.exec` is a function, so static commands meet this by construction. Depfile commands must meet the *static-ancestor condition* `Graph.DynOK`, which stays a hypothesis because it quantifies over every branch of a task. `ninja -t missingdeps` in the property harness checks it on the stores the harness reaches.
4. Depfiles are complete (*trace completeness*): the deps log lists every path the command read. Extra paths only add *modification time* (mtime) checks, and the rebuilds they cause write the same contents.
5. A `restat` command leaves an output untouched only when its contents would not change (`Sem.keep_eq`). The property harness adds a comment to `config.in` and checks that only the generator ran and that every product kept its mtime.
6. Mtimes are faithful. The clock is at least every recorded mtime, so there is no clock skew, and every write gets a strictly larger time. Nothing edits files during a build. Commands are atomic, reading their inputs at the start and writing their outputs at the end, so a parallel run is the sequence of its commands in start-time order.

`Mise/Model/NOTES.md` lists the smaller differences between the model and Ninja. For example, Ninja's build log stores a hash of the command, and the model stores the command string.

## Scope

The supported Ninja subset is in `Mise/Syntax/NOTES.md`. It covers top-level bindings, `rule` blocks, `build` edges with explicit and implicit outputs and explicit, implicit and order-only inputs, edge bindings, and `default`. Rule keys are limited to `command`, `description`, `depfile`, `deps`, `restat`, `generator` and `dyndep`. The parser model rejects `$`-newline continuations, `\r\n` line endings, variable references in paths and non-canonical paths. The DSL emits no `phony` edges and no top-level bindings.

Out of scope: `dyndep`, `generator` and manifest regeneration, `pool`, `subninja` and `include`, Microsoft Visual C++ (MSVC) deps, response files, Windows, and verification of Ninja's C++ source. The parser model accepts the `generator` and `dyndep` keys, but the build model ignores `generator` and gives `dyndep` no meaning.

Every theorem here is a statement about the model of Ninja. The harnesses are the only link between that model and the Ninja binary that runs the build.
