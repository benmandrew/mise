import Mise.Spec.Basic

/-! Stage 2 acceptance: three sources, two targets, one target depending on the other. -/

namespace MiseTest.Stage2
open Mise

/-- The two built files. -/
def targets : List String := ["lib.o", "app"]

/-- The build specification: `lib.o` from `a.c` and `c.h`, then `app` from `lib.o` and `main.c`. -/
def spec : BuildSpec String String where
  isSource k := !targets.contains k
  task
    | "lib.o" => do
        let a ← fetch "a.c"
        let h ← fetch "c.h"
        pure s!"obj({a},{h})"
    | "app" => do
        let o ← fetch "lib.o"
        let m ← fetch "main.c"
        pure s!"link({o},{m})"
    | _ => pure ""

/-- The rank of a key: zero for a source, one for `lib.o`, two for `app`. -/
def rank : String → Nat
  | "lib.o" => 1
  | "app" => 2
  | _ => 0

/-- Proof that `spec` is acyclic, by `rank`. -/
def acyclic : spec.Acyclic where
  rank := rank
  fetches k hk := by
    simp only [spec, targets, Bool.not_eq_false', List.contains_eq_mem, List.mem_cons,
      List.not_mem_nil, or_false, decide_eq_true_eq] at hk
    rcases hk with rfl | rfl <;>
      exact (fetch_fetchesOnly (by decide)).bind fun _ =>
        (fetch_fetchesOnly (by decide)).bind fun _ => .pure _

/-- A store with a one-letter value for each source. -/
def sources : Store String String
  | "a.c" => "A"
  | "c.h" => "H"
  | "main.c" => "M"
  | _ => "?"

#eval BuildSpec.cleanBuild acyclic sources "app"    -- "link(obj(A,H),M)"
#guard BuildSpec.cleanBuild acyclic sources "lib.o" == "obj(A,H)"
#guard BuildSpec.cleanBuild acyclic sources "app" == "link(obj(A,H),M)"
#guard BuildSpec.cleanBuild acyclic sources "main.c" == "M"

end MiseTest.Stage2
