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

-- Stage 3
#print axioms Mise.Syntax.parse_print
#print axioms Mise.Syntax.unescape_escPath
#print axioms Mise.Syntax.unescape_renderVal

-- Stage 4
#print axioms Mise.Frontend.emit_wellFormed
#print axioms Mise.Frontend.denote_emit
#print axioms Mise.Frontend.emitAcyclic
#print axioms Mise.Frontend.emit_acyclic

-- Stage 5
#print axioms Mise.Model.ninjaBuild_clean_correct
#print axioms Mise.Model.ninjaBuild_sound
#print axioms Mise.Model.ninjaBuild_eq_cleanBuild
#print axioms Mise.Model.ninjaBuild_idem
#print axioms Mise.Model.ninjaBuild_after_interrupt
#print axioms Mise.Model.command_change_rebuilds
#print axioms Mise.Model.sched_emit
#print axioms Mise.Model.dsl_sound
#print axioms Mise.Model.dsl_clean
