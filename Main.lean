import Mise.Frontend.Toml

open Mise.Frontend

def usage : String :=
  "usage: gen [--commands] [--set KEY=VALUE]... DIR\n  reads DIR/mise.toml and writes DIR/build.ninja"

/-- Split the arguments into the `--commands` flag, parameters, and the rest. -/
def parseArgs : List String → Bool × Params × List String
  | "--commands" :: r => let (_, ps, rest) := parseArgs r; (true, ps, rest)
  | "--set" :: kv :: r =>
    let (c, ps, rest) := parseArgs r
    match kv.splitOn "=" with
    | k :: v => (c, (k, "=".intercalate v) :: ps, rest)
    | [] => (c, ps, rest)
  | a :: r => let (c, ps, rest) := parseArgs r; (c, ps, a :: rest)
  | [] => (false, [], [])

def main (args : List String) : IO UInt32 := do
  let (showCmds, ps, rest) := parseArgs args
  let [dir] := rest | IO.eprintln usage; return 2
  let file := System.FilePath.mk dir / "mise.toml"
  let text ← try IO.FS.readFile file catch e => IO.eprintln s!"gen: {e}"; return 2
  match ← Toml.load text ps file.toString with
  | .error e => IO.eprintln s!"gen: {file}: {e}"; return 1
  | .ok g =>
    if showCmds then
      -- The command the DSL means for each edge, to compare with `ninja -t commands`.
      for e in g.1.edges do IO.println (g.1.cmd e)
    else
      let out := System.FilePath.mk dir / "build.ninja"
      IO.FS.writeFile out g.ninja
      IO.println s!"gen: wrote {out}"
    return 0
