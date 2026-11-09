import HelloC
import GenHeader

open Mise.Frontend

/-- Build descriptions, by example directory name. -/
def registry : List (String × (Params → Build Unit)) :=
  [("hello-c", HelloC.build), ("gen-header", GenHeader.build)]

def usage : String :=
  "usage: gen [--commands] [--set KEY=VALUE]... DIR\n  writes DIR/build.ninja for a registered example"

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
  let name := (System.FilePath.mk dir).fileName.getD dir
  let some b := registry.lookup name
    | IO.eprintln s!"gen: no build description registered for {repr name}"; return 2
  match (b ps).graph with
  | .error e => IO.eprintln s!"gen: {e}"; return 1
  | .ok g =>
    if showCmds then
      -- The command the DSL means for each edge, to compare with `ninja -t commands`.
      for e in g.1.edges do IO.println (g.1.cmd e)
    else
      let out := System.FilePath.mk dir / "build.ninja"
      IO.FS.writeFile out g.ninja
      IO.println s!"gen: wrote {out}"
    return 0
