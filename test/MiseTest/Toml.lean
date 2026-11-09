import Mise.Frontend.Toml

/-! The TOML reader rejects malformed descriptions with a message. The
examples' `mise.toml` files are read by `mise` in the shell tests. -/

namespace MiseTest.Toml
open Mise.Frontend

def rejects (text : String) (ps : Params := []) (msg : String) : IO Unit := do
  match ← Toml.load text ps with
  | .ok _ => throw <| IO.userError s!"accepted: {text}"
  | .error e => unless (e.splitOn msg).length > 1 do throw <| IO.userError s!"wrong error {repr e}, expected {repr msg}"

def base : String := "sources = [\"a.c\"]\n[[rule]]\nname = \"cc\"\ncommand = \"cc $in -o $out\"\n"

#eval rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"a.o\"]\nins = [\"b.c\"]\n") (msg := "is not a source")
#eval rejects (base ++ "[[build]]\nrule = \"ld\"\nouts = [\"a.o\"]\n") (msg := "no rule named")
#eval rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"a.o\"]\ninput = [\"a.c\"]\n") (msg := "unknown key")
#eval rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"a.c\"]\n") (msg := "already declared")
#eval rejects base [("cflags", "-O0")] (msg := "no such parameter")
#eval rejects "sources = [\"a.c\"" (msg := "expected ']'")

end MiseTest.Toml
