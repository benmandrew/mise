# Stage 1 notes: task free monad and trace lemma

## Definitions

`Task K V α` is the inductive *free monad* from the plan, with `pure` and `fetch` constructors. `Task.bind` recurses structurally through the continuation, and the `Monad` instance uses it directly. `Task.run` and `Task.deps` are structural; `Task.interp` interprets a task into any monad.

`Task.logFetch s : K → StateM (List K) V` returns `s k` and appends `k` to the state. `interp_logFetch` proves `(t.interp (logFetch s)).run l = (t.run s, l ++ t.deps s)` for any starting log `l`, and `deps_eq_interp` specialises it to the empty log.

## Theorems

- `LawfulMonad (Task K V)` through `LawfulMonad.mk'`. The default `map`, `seq` and `seqLeft` fields reduce by `rfl`.
- `interp_pure` and `interp_bind` for lawful target monads.
- `run_eq_interp` (with `M := Id`) and `deps_eq_interp`.
- `run_eq_of_agree`, stated as in the plan, with the corollaries `run_congr_store` and `deps_congr_store` for stores that agree on every key.
- `FetchesOnly.deps_sat`: a static fetch bound holds for every key on the path a store selects.

Supporting lemmas: `run_bind` and `deps_bind` (simp), the inversion lemmas `FetchesOnly.head` and `FetchesOnly.tail`, `FetchesOnly.mono`, `FetchesOnly.bind` and `fetch_fetchesOnly`.

## Deviations from the plan

None, and no added assumptions.

## Acceptance

`test/MiseTest/Stage1.lean` builds a task that reads `foo.c` and fetches each header its `#include` lines name. `#guard` checks that two stores give the fetches `["foo.c", "a.h", "b.h"]` and `["foo.c", "c.h"]`.
