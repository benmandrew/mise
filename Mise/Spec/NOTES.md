# Stage 2 notes: build specifications and correctness

## Definitions

`BuildSpec K V` has `isSource : K → Bool` and `task : K → Task K V V`. Every key has a task; the task of a source key is never consulted. `Correct b S R` is the plan's predicate, with `b.isSource k = false` standing for `¬ isSource k`.

`Task.runP` runs a task against a partial store `(k : K) → P k → V`, given a proof that the task fetches only keys satisfying `P`. `cleanBuild` uses it so that the recursive call on each fetched key carries the proof that its rank is smaller. `runP_eq` shows `runP` agrees with `run` whenever the partial store agrees with a total one.

## Deviations from the plan

`Acyclic b` is a structure (data: the rank function plus the fetch-bound proofs), where the plan reads "there is a rank". A `Prop` with an existential would make `cleanBuild` noncomputable, and Stage 2's acceptance needs `#eval cleanBuild`. `Nonempty b.Acyclic` recovers the propositional form wherever it is wanted. Every theorem that takes `Acyclic b` holds for any witness.

No assumptions were added.

## Theorems

- `cleanBuild_correct`: `Correct b S (cleanBuild h S)`, via the unfolding lemmas `cleanBuild_source` and `cleanBuild_target`.
- `correct_unique`: two correct stores for the same sources are equal. The proof is induction on a rank bound, with `run_eq_of_agree` closing the target case.
- `correct_eq_cleanBuild`: any correct store is the clean build.

## Acceptance

`test/MiseTest/Stage2.lean` defines sources `a.c`, `c.h` and `main.c`, the target `lib.o` reading `a.c` and `c.h`, and the target `app` reading `lib.o` and `main.c`. `cleanBuild` gives `app = "link(obj(A,H),M)"`, checked with `#guard`.
