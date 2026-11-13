# Stage 2 notes: build specifications and correctness

## Definitions

`BuildSpec K V` has `isSource : K → Bool` and `task : K → Task K V V`. Every key has a task; the task of a source key is never consulted. `Correct b S R` is the plan's predicate, with `b.isSource k = false` for `¬ isSource k`.

`Task.runP` runs a task against a partial store `(k : K) → P k → V`, given a proof that the task fetches only keys satisfying `P`. `cleanBuild` uses it so that the recursive call on each fetched key carries a proof that its rank is smaller. `runP_eq` shows `runP` agrees with `run` whenever the partial store agrees with a total one.

## Deviations from the plan

`Acyclic b` is a structure holding the rank function and the fetch-bound proofs, where the plan has "there is a rank". An existential `Prop` would make `cleanBuild` noncomputable, and the acceptance test evaluates it. `Nonempty b.Acyclic` is the propositional form. Every theorem that takes `Acyclic b` holds for any witness.

There are no added assumptions.

## Theorems

- `cleanBuild_correct`: `Correct b S (cleanBuild h S)`, via the unfolding lemmas `cleanBuild_source` and `cleanBuild_target`.
- `correct_unique`: two correct stores for the same sources are equal (induction on a rank bound, with `run_eq_of_agree` for targets).
- `correct_eq_cleanBuild`: any correct store is the clean build.

## Acceptance

`test/MiseTest/Stage2.lean` defines sources `a.c`, `c.h` and `main.c`, the target `lib.o` reading `a.c` and `c.h`, and the target `app` reading `lib.o` and `main.c`. `#guard` checks that `cleanBuild` gives `app = "link(obj(A,H),M)"`.
