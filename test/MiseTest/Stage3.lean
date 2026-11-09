import Mise.Syntax.Print
import Mise.Syntax.Parse

/-! Stage 3: a hand-written manifest with adversarial paths and values. -/

namespace MiseTest.Stage3
open Mise.Syntax

def m : Manifest := ⟨[
  .binding "ninja_required_version" [.lit "1.10"],
  .binding "builddir" [.lit " build"],
  .rule ⟨"cc", [("command", [.lit "cc -c ", .var "in", .lit " -o ", .var "out", .lit " $x  "]),
                ("depfile", [.var "out", .lit ".d"]), ("deps", [.lit "gcc"])]⟩,
  .edge { outs := ["a b.o"], implicitOuts := ["a b.o.d"], rule := "cc", ins := ["src/a:b.c"],
          implicitIns := ["hé$.h"], orderOnly := ["gen"],
          bindings := [("flags", [.lit "-O2"]), ("empty", [])] },
  .edge { outs := ["gen"], rule := "phony" },
  .default ["a b.o", "/abs/path"]
]⟩


def m' : Manifest := ⟨m.stmts.take 5 ++ [.default ["a b.o", "gen"]]⟩
#guard decide m'.WellFormed
#guard parse (print m') == some m'
#eval IO.println (print m')
#guard !decide m.WellFormed  -- `/abs/path` was never mentioned

end MiseTest.Stage3
