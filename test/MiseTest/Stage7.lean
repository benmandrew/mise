import Mise.Model.Parallel
import MiseTest.Stage6

/-! Stage 7: early cutoff and build order on gen-header in the Ninja model.
Every command ignores words starting with `#`, so a comment added to
`config.in` leaves `build/config.h` the same. The generator's rule has
`restat`, and with `keep` the model lets it leave the header untouched. -/

namespace MiseTest.Stage7
open Mise Mise.Model Mise.Frontend Mise.Syntax
open MiseTest.Stage6 (m products srcOf includes)

def strip (c : String) : String := " ".intercalate ((c.splitOn " ").filter fun w => !w.startsWith "#")

def exec (cmd : String) (vs : List String) : List String := [cmd ++ "(" ++ ",".intercalate (vs.map strip) ++ ")"]

def compile (cmd : String) : Task Path String (List String) :=
  .fetch (srcOf cmd) fun c => (fetchAll (includes c)).bind fun vs => .pure (exec cmd (c :: vs))

/-- Commands leave a file untouched when its contents would not change. -/
def sem : Sem String := { exec, dyn := compile, keep := (· == ·), keep_eq := fun _ _ h => by simpa using h }

/-- The same commands, always writing. -/
def semW : Sem String := { exec, dyn := compile }

def st0 : St String := MiseTest.Stage6.st0

def ran (sem : Sem String) (es : List MEdge) (st : St String) : List Path :=
  (buildTrace sem es st).2.map fun e => e.outs.headD ""

def b1 := ninjaBuild sem m st0
def c1 := b1.edit "config.in" "config@1 #note"

#guard m.medges.map (·.restat) == [true, false, false, false]
#guard ran sem m.medges st0 == products
-- A comment in `config.in`: the generator runs and keeps the header, and nothing else runs.
#guard ran sem m.medges c1 == ["build/config.h"]
#guard (ninjaBuild sem m c1).mtime "build/config.h" == b1.mtime "build/config.h"
-- The next build runs nothing.
#guard ran sem m.medges (ninjaBuild sem m c1) == []
-- Without keeping, the rewritten header rebuilds everything downstream.
#guard ran semW m.medges (ninjaBuild semW m st0 |>.edit "config.in" "config@1 #note") == products
-- A real change to `config.in` still reaches both compiles.
#guard ran sem m.medges (b1.edit "config.in" "config@2") == products

-- The DSL wraps the generator in the command wrapper, whose semantics is
-- `Sem.withCmp`: here the same as `sem`.
#guard (m.medges.headD default).cmd.startsWith "set -- build/config.h ; "
#guard ran semW.withCmp m.medges c1 == ["build/config.h"]
#guard (ninjaBuild semW.withCmp m c1).mtime "build/config.h" == b1.mtime "build/config.h"
#guard ran semW.withCmp m.medges (b1.edit "config.in" "config@2") == products

/-- The two compiles swapped: another order consistent with the dependencies. -/
def swapped : List MEdge :=
  match m.medges with
  | [g, a, b, l] => [g, b, a, l]
  | es => es

#guard swapped != m.medges
-- Early cutoff stops the same edges in both orders (`parallel_same_edges`).
#guard ran sem swapped c1 == ["build/config.h"]
#guard ran sem swapped (b1.edit "config.in" "config@2") == ["build/config.h", "build/util.o", "build/main.o", "build/app"]
#guard ran sem swapped (b1.edit "util.h" "util.h@2") == ["build/util.o", "build/main.o", "build/app"]
#guard products.all fun k =>
  (buildTrace sem swapped (b1.edit "util.h" "util.h@2")).1.content k ==
    (ninjaBuild sem m (b1.edit "util.h" "util.h@2")).content k

end MiseTest.Stage7
