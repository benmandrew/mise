import Mise.Frontend.Toml
import HelloC
import GenHeader

/-! TOML descriptions: each example's `mise.toml` emits the same manifest as
its Lean description, with and without `--set`, and malformed descriptions
are rejected with a message. `scripts/check.sh` elaborates this file on every
run, because Lake does not track the TOML files it reads. -/

namespace MiseTest.Toml
open Mise.Frontend

def ninjaOf (b : Build Unit) : Except String String := (·.ninja) <$> b.graph

def same (file : String) (b : Params → Build Unit) (ps : Params) : IO Unit := do
  let toml ← (Toml.load (← IO.FS.readFile file) ps file)
  match toml.map (·.ninja), ninjaOf (b ps) with
  | .ok a, .ok b => unless a == b do throw <| IO.userError s!"{file}: TOML and Lean manifests differ"
  | .error e, _ => throw <| IO.userError s!"{file}: {e}"
  | _, .error e => throw <| IO.userError s!"{file}: Lean description failed: {e}"

def rejects (text : String) (ps : Params := []) (msg : String) : IO Unit := do
  match ← Toml.load text ps with
  | .ok _ => throw <| IO.userError s!"accepted: {text}"
  | .error e => unless (e.splitOn msg).length > 1 do throw <| IO.userError s!"wrong error {repr e}, expected {repr msg}"

#eval same "examples/hello-c/mise.toml" HelloC.build []
#eval same "examples/hello-c/mise.toml" HelloC.build [("cflags", "-O0")]
#eval same "examples/gen-header/mise.toml" GenHeader.build []
#eval same "examples/gen-header/mise.toml" GenHeader.build [("cflags", "-O1 -DX=1")]

def base : String := "sources = [\"a.c\"]\n[[rule]]\nname = \"cc\"\ncommand = \"cc $in -o $out\"\n"

#eval rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"a.o\"]\nins = [\"b.c\"]\n") (msg := "is not a source")
#eval rejects (base ++ "[[build]]\nrule = \"ld\"\nouts = [\"a.o\"]\n") (msg := "no rule named")
#eval rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"a.o\"]\ninput = [\"a.c\"]\n") (msg := "unknown key")
#eval rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"a.c\"]\n") (msg := "already declared")
#eval rejects base [("cflags", "-O0")] (msg := "no such parameter")
#eval rejects "sources = [\"a.c\"" (msg := "expected ']'")

end MiseTest.Toml
