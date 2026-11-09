import Mise

/-! Headline theorems of every stage. `scripts/check.sh` runs this file and
fails if any theorem depends on an axiom outside the standard three. -/

-- Stage 1
#print axioms Mise.Task.run_eq_of_agree
#print axioms Mise.Task.interp_bind
#print axioms Mise.Task.run_eq_interp
#print axioms Mise.Task.deps_eq_interp
#print axioms Mise.Task.FetchesOnly.deps_sat

-- Stage 2
#print axioms Mise.BuildSpec.cleanBuild_correct
#print axioms Mise.BuildSpec.correct_unique
