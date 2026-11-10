import Mise.Frontend.Toml

open Mise.Frontend

def usage : String :=
  "usage: mise gen [--commands] [--set KEY=VALUE]... [DIR]
       mise build [--set KEY=VALUE]... [DIR] [-- NINJA_ARGS...]

  gen    reads DIR/mise.toml and writes DIR/build.ninja
  build  does the same, then runs ninja in DIR with NINJA_ARGS
  DIR defaults to the current directory."

structure Opts where
  commands : Bool := false
  params : Params := []
  dirs : List String := []

/-- Read the options before `--`. -/
def parseOpts : List String → Except String Opts
  | "--commands" :: r => do pure { ← parseOpts r with commands := true }
  | "--set" :: kv :: r => do
    let o ← parseOpts r
    match kv.splitOn "=" with
    | k :: v@(_ :: _) => pure { o with params := (k, "=".intercalate v) :: o.params }
    | _ => throw s!"--set {kv}: expected KEY=VALUE"
  | ["--set"] => throw "--set: expected KEY=VALUE"
  | a :: r => do
    if a.startsWith "-" then throw s!"unknown option {a}"
    let o ← parseOpts r
    pure { o with dirs := a :: o.dirs }
  | [] => pure {}

/-- Write `DIR/build.ninja` from `DIR/mise.toml`, leaving the file alone when
its contents would not change. Returns the graph, or the exit code on error. -/
def generate (dir : System.FilePath) (ps : Params) : IO (Except UInt32 ValidGraph) := do
  let file := dir / "mise.toml"
  let text ← try IO.FS.readFile file catch e => IO.eprintln s!"mise: {e}"; return .error 2
  match Toml.load text ps with
  | .error e => IO.eprintln s!"mise: {file}: {e}"; return .error 1
  | .ok g =>
    let out := dir / "build.ninja"
    let old ← try some <$> IO.FS.readFile out catch _ => pure none
    if old != some g.ninja then
      IO.FS.writeFile out g.ninja
      IO.println s!"mise: wrote {out}"
    return .ok g

def main (args : List String) : IO UInt32 := do
  let (cmd, rest) := match args with
    | c :: r => (c, r)
    | [] => ("", [])
  let (before, ninjaArgs) := match rest.span (· != "--") with
    | (b, _ :: a) => (b, a)
    | (b, []) => (b, [])
  let opts ← match parseOpts before with
    | .ok o => pure o
    | .error e => IO.eprintln s!"mise: {e}\n{usage}"; return 2
  let dir : System.FilePath := match opts.dirs with
    | [d] => d
    | _ => "."
  if opts.dirs.length > 1 then IO.eprintln usage; return 2
  match cmd with
  | "gen" =>
    unless ninjaArgs.isEmpty do IO.eprintln usage; return 2
    if opts.commands then
      -- The command the DSL means for each edge, to compare with `ninja -t commands`.
      let file := dir / "mise.toml"
      let text ← try IO.FS.readFile file catch e => IO.eprintln s!"mise: {e}"; return 2
      match Toml.load text opts.params with
      | .error e => IO.eprintln s!"mise: {file}: {e}"; return 1
      | .ok g => for e in g.1.edges do IO.println (g.1.cmd e)
      return 0
    match ← generate dir opts.params with
    | .error c => return c
    | .ok _ => return 0
  | "build" =>
    if opts.commands then IO.eprintln usage; return 2
    match ← generate dir opts.params with
    | .error c => return c
    | .ok _ =>
      let child ← try IO.Process.spawn { cmd := "ninja", args := (if dir == "." then #[] else #["-C", dir.toString]) ++ ninjaArgs.toArray }
        catch e => IO.eprintln s!"mise: cannot run ninja: {e}"; return 127
      return (← child.wait)
  | "--help" | "-h" | "help" => IO.println usage; return 0
  | _ => IO.eprintln usage; return 2
