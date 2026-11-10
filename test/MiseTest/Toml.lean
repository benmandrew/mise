import Lake.Toml
import Mise.Frontend.Toml

/-! The TOML reader. The parser agrees with Lake's TOML parser on the inputs
below, and rejects what it does not support with a position. Malformed
descriptions are rejected with a message. The examples' `mise.toml` files are
read by `mise` in the shell tests. -/

namespace MiseTest.Toml
open Mise.Frontend Mise.Frontend.Toml

/-- Lake's parse, in this parser's types. -/
partial def ofLake : Lake.Toml.Value → Option Value
  | .string _ s => some (.str s)
  | .boolean _ b => some (.bool b)
  | .integer _ n => some (.int n)
  | .array _ xs => .arr <$> xs.toList.mapM ofLake
  | .table _ t => .table <$> t.items.toList.mapM fun (k, v) => (k.toString (escape := false), ·) <$> ofLake v
  | _ => none

def lake (text : String) : IO (Option Table) := do
  match ← (Lake.Toml.loadToml (Lean.Parser.mkInputContext text "t.toml")).toBaseIO with
  | .ok t => pure (t.items.toList.mapM fun (k, v) => (k.toString (escape := false), ·) <$> ofLake v)
  | .error _ => pure none

/-- Both parsers accept `text` and give the same table. -/
def agrees (text : String) : IO Unit := do
  let ours := parse text
  let theirs ← lake text
  match ours, theirs with
  | .ok a, some b => unless a == b do throw <| IO.userError s!"parsers differ on {repr text}:\n{repr a}\n{repr b}"
  | .error e, _ => throw <| IO.userError s!"rejected {repr text}: {e}"
  | _, none => throw <| IO.userError s!"Lake rejected {repr text}"

#eval agrees ""
#eval agrees "# only a comment\n\n"
#eval agrees "a = \"x\"\nb = 'y\\z'\nc = true\nd = false\ne = -12\nf = 1_000\ng = +3\nh = 0\n"
#eval agrees "s = \"tab\\t nl\\n q\\\" bs\\\\ u\\u00e9 U\\U0001F600 b\\b f\\f r\\r\"\n"
#eval agrees "\"quoted key\" = 1\n'lit key' = 2\nbare-key_1 = 3\n"
#eval agrees "xs = [\n  \"a\", # comment\n  \"b\",\n]\nys = []\nzs = [[1, 2], [\"c\"]]\n"
#eval agrees "t = { a = \"x\", b = [1, 2], c = { d = true } }\ne = {}\n"
#eval agrees "top = 1\n[params]\ncflags = \"-O2\"\n[ spaced ]\nx = 1\n"
#eval agrees "[[rule]]\nname = \"a\"\n[[rule]]\nname = \"b\"\n[other]\n[[rule]]\nname = \"c\"\n"
#eval agrees "a = 1\r\nb = \"x\" # trailing\r\n"
#eval agrees "x = \"#not a comment\"\n"

/-- Rejected, with `msg` in the error. -/
def rejectsParse (text msg : String) : Bool := match parse text with
  | .ok _ => false
  | .error e => (e.splitOn msg).length > 1

#guard rejectsParse "a.b = 1" "1:2: dotted keys are not supported"
#guard rejectsParse "[a.b]" "dotted keys"
#guard rejectsParse "a = \"\"\"x\"\"\"" "multi-line strings"
#guard rejectsParse "a = '''x'''" "multi-line strings"
#guard rejectsParse "a = 1.5" "unsupported value 1.5"
#guard rejectsParse "a = 1979-05-27" "unsupported value"
#guard rejectsParse "a = 0x1f" "unsupported value"
#guard rejectsParse "a = 01" "unsupported value"
#guard rejectsParse "a = inf" "unsupported value"
#guard rejectsParse "a = \"x" "unterminated string"
#guard rejectsParse "a = \"x\ny\"" "newline in a string"
#guard rejectsParse "a = \"\\q\"" "unknown escape"
#guard rejectsParse "a = 1\na = 2" "2:6: duplicate key \"a\""
#guard rejectsParse "a = 1 b = 2" "expected the end of the line"
#guard rejectsParse "a = [1 2]" "expected ',' or ']'"
#guard rejectsParse "a = { x = 1,\n y = 2 }" "expected a key"
#guard rejectsParse "a = { x = 1, x = 2 }" "duplicate key \"x\" in an inline table"
#guard rejectsParse "[t]\n[t]" "2:1: \"t\" is already defined"
#guard rejectsParse "t = 1\n[t]" "\"t\" is already defined"
#guard rejectsParse "t = [1]\n[[t]]" "\"t\" is already defined"
#guard rejectsParse "[[t]]\n[t]" "\"t\" is already defined"
#guard rejectsParse "a =" "expected a value"

/-- A build description rejected, with `msg` in the error. -/
def rejects (text : String) (ps : Params := []) (msg : String) : Bool := match load text ps with
  | .ok _ => false
  | .error e => (e.splitOn msg).length > 1

def base : String := "sources = [\"a.c\"]\n[[rule]]\nname = \"cc\"\ncommand = \"cc $in -o $out\"\n"

#guard (load (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"a.o\"]\nins = [\"a.c\"]\n")).isOk
#guard rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"a.o\"]\nins = [\"b.c\"]\n") (msg := "is not a source")
#guard rejects (base ++ "[[build]]\nrule = \"ld\"\nouts = [\"a.o\"]\n") (msg := "no rule named")
#guard rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"a.o\"]\ninput = [\"a.c\"]\n") (msg := "unknown key")
#guard rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"a.c\"]\n") (msg := "already declared")
#guard rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"a.o\"]\nins = [1]\n") (msg := "expected a string")
#guard rejects base [("cflags", "-O0")] (msg := "no such parameter")
#guard rejects "sources = [\"a.c\"" (msg := "expected ',' or ']'")

end MiseTest.Toml
