import Lean

/-! The in-process build for `test/trust-mutants.py --via inproc`.

`lake env lean --run test/trust-mutants.lean PLAN` builds mutants without
starting a Lean process per module. `PLAN` is a JSON file that lists each
mutated module with its stages. A stage is a list of modules in import order;
the first also lists the modules that the stages import from outside
themselves, and the later ones list none. The process then reads
mutants from standard input, one JSON line each (`{name, module, src}`, where
`src` is the mutated text of `module`, or null for the unmutated control),
and writes one JSON line for each: its name, its errors as
`{file, line, msg}`, and the seconds it took.

The first mutant of a module loads the first stage's imports, which are
those of every stage, and later mutants of that module reuse them. Each
mutant elaborates the stage's modules from source, one after another, on the
same environment, with the mutated module's text replaced. A later stage
runs on the environment the stage before it left, so no module is
elaborated twice. A module whose import has errors is skipped, as Lake
skips it. A mutant stops at the first stage with errors; the driver puts the
test modules that kill most mutants in the first stage. -/

open Lean Elab

namespace TrustMutants

structure Module where
  name : String
  /-- The path relative to the tree, which the module's messages report. -/
  file : String
  /-- The modules of the stage that this module imports. -/
  imports : Array String
  /-- Elaborate with `debug.byAsSorry`, as the copy's library is. -/
  byAsSorry : Bool
  deriving FromJson, Inhabited

structure Stage where
  imports : Array String
  modules : Array Module
  deriving FromJson, Inhabited

structure ModulePlan where
  module : String
  stages : Array Stage
  deriving FromJson

structure Mutant where
  name : String
  module : String
  /-- The mutated text of `module`, or none for the unmutated control. -/
  src : Option String
  deriving FromJson

structure Err where
  file : String
  line : Nat
  msg : String
  deriving ToJson

def now : IO Float := return (← IO.monoNanosNow).toFloat / 1e9

/-- Elaborate one module's source on `env`: the new environment and the
module's errors. -/
def elabModule (env : Environment) (m : Module) (src : String) : IO (Environment × Array Err) := do
  let ictx := Parser.mkInputContext src m.file
  let (_, ps, msgs) ← Parser.parseHeader ictx
  -- One thread per process: the driver runs one process per CPU, and with
  -- `Elab.async` they compete for the cores and take 50% more CPU time.
  let opts := ({} : Options).setBool `Elab.async false |>.setBool `debug.byAsSorry m.byAsSorry
  let s ← IO.processCommands ictx ps (Command.mkState (env.setMainModule m.name.toName) msgs opts)
  let errs ← (s.commandState.messages.toList.filter (·.severity == .error)).toArray.mapM fun msg =>
    return ({ file := msg.fileName, line := msg.pos.line, msg := ← msg.data.toString } : Err)
  return (s.commandState.env, errs)

/-- The errors of one stage for one mutant, and the environment it leaves. -/
def runStage (env0 : Environment) (st : Stage) (srcs : Std.HashMap String String) (mt : Mutant) :
    IO (Array Err × Environment) := do
  let mut env := env0
  let mut failed : Std.HashSet String := {}
  let mut errs := #[]
  for m in st.modules do
    if m.imports.any failed.contains then
      failed := failed.insert m.name
      continue
    let src := if m.name == mt.module then mt.src.getD srcs[m.name]! else srcs[m.name]!
    let (env', es) ← elabModule env m src
    env := env'
    unless es.isEmpty do failed := failed.insert m.name
    errs := errs ++ es
  return (errs, env)

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: trust-mutants.lean PLAN")
  let plans ← IO.ofExcept <| (Json.parse (← IO.FS.readFile path)).bind (fromJson? (α := Array ModulePlan))
  let plan : Std.HashMap String (Array Stage) := plans.foldl (fun m p => m.insert p.module p.stages) {}
  initSearchPath (← findSysroot)
  let mut srcs : Std.HashMap String String := {}
  let mut envs : Std.HashMap String Environment := {}
  let stdin ← IO.getStdin
  let out ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let mt ← IO.ofExcept <| (Json.parse line).bind (fromJson? (α := Mutant))
    let some stages := plan[mt.module]? | throw (IO.userError s!"no stages for {mt.module}")
    let t ← now
    let mut errs := #[]
    -- The environment the last stage left, on which the next one runs.
    let mut last : Option Environment := none
    for st in stages do
      for m in st.modules do
        unless srcs.contains m.name do srcs := srcs.insert m.name (← IO.FS.readFile m.file)
      let env ← match last, envs[mt.module]? with
        | some env, _ => pure env
        | none, some env => pure env
        | none, none => do
          -- `importModules` clears the flag, so each call must set it again.
          enableInitializersExecution
          let env ← importModules (st.imports.map fun m => { module := m.toName }) {} (trustLevel := 1024) (loadExts := true)
          envs := envs.insert mt.module env
          pure env
      let (es, env') ← runStage env st srcs mt
      errs := es
      last := some env'
      unless errs.isEmpty do break
    out.putStrLn (Json.compress (json% {name: $(mt.name), errors: $(errs), secs: $((← now) - t)}))
    out.flush
  return 0

end TrustMutants

unsafe def main (args : List String) : IO UInt32 := TrustMutants.main args
