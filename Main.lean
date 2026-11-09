import HelloC

open Mise.Frontend

/-- Build descriptions, by example directory name. -/
def registry : List (String × Build Unit) :=
  [("hello-c", HelloC.build)]

def usage : String := "usage: gen [--commands] DIR\n  writes DIR/build.ninja for a registered example"

def main (args : List String) : IO UInt32 := do
  let (showCmds, dir) := match args with
    | ["--commands", d] => (true, some d)
    | [d] => (false, some d)
    | _ => (false, none)
  let some dir := dir | IO.eprintln usage; return 2
  let name := (System.FilePath.mk dir).fileName.getD dir
  let some b := registry.lookup name
    | IO.eprintln s!"gen: no build description registered for {repr name}"; return 2
  match b.graph with
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
