import Mise.Task.Basic

/-! Stage 1 acceptance: a task whose dependencies depend on what it reads. -/

namespace MiseTest.Stage1
open Mise

/-- Header names from lines of the form `#include NAME`. -/
def includes (src : String) : List String :=
  (src.splitOn "\n").filterMap fun l =>
    if l.startsWith "#include " then some (String.ofList (l.toList.drop 9)) else none

/-- Read `foo.c`, then read every header it includes. -/
def compileFoo : Task String String String := do
  let src ← fetch "foo.c"
  let hs ← (includes src).mapM fetch
  pure (String.intercalate "+" (src.length.repr :: hs))

def store₁ : Store String String
  | "foo.c" => "#include a.h\n#include b.h\nint main;"
  | "a.h" => "A"
  | "b.h" => "B"
  | _ => ""

def store₂ : Store String String
  | "foo.c" => "#include c.h\nint main;"
  | "c.h" => "C"
  | _ => ""

#eval compileFoo.deps store₁   -- ["foo.c", "a.h", "b.h"]
#eval compileFoo.deps store₂   -- ["foo.c", "c.h"]
#eval compileFoo.run store₁

#guard compileFoo.deps store₁ == ["foo.c", "a.h", "b.h"]
#guard compileFoo.deps store₂ == ["foo.c", "c.h"]

end MiseTest.Stage1

