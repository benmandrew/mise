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
#eval agrees "#\ttab and \u00e9 in a comment\r\na = 1 #\t\r\n"

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
-- Found by `test/toml-diff.sh`: TOML forbids control characters other than
-- tab in comments, as in strings, and `tomllib` rejects them.
#guard rejectsParse "# a\x01b\n" "1:4: control character in a comment"
#guard rejectsParse "a = 1 # \x7f\n" "control character in a comment"
#guard rejectsParse "a = [1, # x\ry\n 2]" "control character in a comment"
#guard rejectsParse "a = 1 # x\r" "control character in a comment"

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

/-! The command wrapper, with `cmp` on `restat` rules. -/

/-- The commands of a description's edges. -/
def cmds (text : String) : List String := match load text with
  | .ok g => g.1.edges.map g.1.cmd
  | .error _ => []

def has (s t : String) : Bool := (s.splitOn t).length > 1

def restatBase (rule edge : String) : String :=
  "sources = [\"a.c\"]\n[[rule]]\nname = \"gen\"\ncommand = \"gen $in $out\"\nrestat = true\n" ++ rule ++
    "[[build]]\nrule = \"gen\"\nouts = [\"a.h\"]\nins = [\"a.c\"]\n" ++ edge

def plainBase (rule edge : String) : String :=
  "sources = [\"a.c\"]\n[[rule]]\nname = \"gen\"\ncommand = \"gen $in $out\"\n" ++ rule ++
    "[[build]]\nrule = \"gen\"\nouts = [\"a.h\"]\nins = [\"a.c\"]\n" ++ edge

#guard match cmds (restatBase "" "") with
  | [c] => c.startsWith "set -- a.h ; " && has c "; if ( gen a.c a.h ); then " && has c "cmp -s"
  | _ => false
-- A rule without `restat` is wrapped too, without `cmp`.
#guard match cmds (plainBase "" "") with
  | [c] => c.startsWith "set -- a.h ; " && has c "; if ( gen a.c a.h ); then " && !has c "cmp"
  | _ => false
#guard cmds (restatBase "wrap = false\n" "") == ["gen a.c a.h"]
#guard cmds (plainBase "wrap = false\n" "") == ["gen a.c a.h"]
#guard cmds (restatBase "wrap = true\n" "") == cmds (restatBase "" "")
#guard rejects (base ++ "restat-cmp = false\n") (msg := "unknown key")
-- Implicit outputs reach the wrapper through `mise_iouts`, shell-quoted.
#guard match cmds (restatBase "" "implicit-outs = [\"b c.h\"]\n") with
  | [c] => c.startsWith "set -- a.h 'b c.h'; "
  | _ => false
#guard match cmds (plainBase "" "implicit-outs = [\"b c.h\"]\n") with
  | [c] => c.startsWith "set -- a.h 'b c.h'; "
  | _ => false
#guard rejects (restatBase "" "vars = { mise_iouts = \"x\" }\n") (msg := "set by the command wrapper")
#guard rejects (plainBase "" "vars = { mise_iouts = \"x\" }\n") (msg := "set by the command wrapper")
#guard cmds (plainBase "wrap = false\n" "vars = { mise_iouts = \"x\" }\n") == ["gen a.c a.h"]

/-! `foreach`, any order, `source-globs` and aliases. -/

/-- The emitted manifest of a description, or the error. -/
def ninjaOf (text : String) (globs : List (String × List Mise.Syntax.Path) := []) : String :=
  match loadWith text [] globs with
  | .ok g => g.ninja
  | .error e => "error: " ++ e

def rules2 : String :=
  "[[rule]]\nname = \"cc\"\ncommand = \"cc -c $in -o $out\"\n[[rule]]\nname = \"ld\"\ncommand = \"cc $in -o $out\"\n"

def explicitBuild : String :=
  "sources = [\"a.c\", \"b.c\", \"x.h\"]\n" ++ rules2 ++
  "[[build]]\nrule = \"cc\"\nouts = [\"o/a.o\"]\nins = [\"a.c\"]\nimplicit-ins = [\"x.h\"]\n" ++
  "[[build]]\nrule = \"cc\"\nouts = [\"o/b.o\"]\nins = [\"b.c\"]\nimplicit-ins = [\"x.h\"]\n" ++
  "[[build]]\nrule = \"ld\"\nouts = [\"app\"]\nins = [\"o/a.o\", \"o/b.o\"]\n"

-- A `foreach` build expands to one build per match, in path order, and the
-- link may come first in the file.
#guard ninjaOf ("sources = [\"a.c\", \"b.c\", \"x.h\"]\n" ++ rules2 ++
  "[[build]]\nrule = \"ld\"\nouts = [\"app\"]\nins = [\"o/a.o\", \"o/b.o\"]\n" ++
  "[[build]]\nrule = \"cc\"\nforeach = \"%.c\"\nouts = [\"o/%.o\"]\nins = [\"%.c\"]\nimplicit-ins = [\"x.h\"]\n")
  == ninjaOf explicitBuild
-- Builds out of order are sorted; builds in order keep their order.
#guard ninjaOf ("sources = [\"a.c\", \"b.c\", \"x.h\"]\n" ++ rules2 ++
  "[[build]]\nrule = \"ld\"\nouts = [\"app\"]\nins = [\"o/a.o\", \"o/b.o\"]\n" ++
  "[[build]]\nrule = \"cc\"\nouts = [\"o/a.o\"]\nins = [\"a.c\"]\nimplicit-ins = [\"x.h\"]\n" ++
  "[[build]]\nrule = \"cc\"\nouts = [\"o/b.o\"]\nins = [\"b.c\"]\nimplicit-ins = [\"x.h\"]\n")
  == ninjaOf explicitBuild
-- `source-globs` adds the files the caller found, skipping repeats.
#guard ninjaOf ("sources = [\"x.h\"]\nsource-globs = [\"*.c\", \"a.*\"]\n" ++ rules2 ++
  "[[build]]\nrule = \"cc\"\nforeach = \"%.c\"\nouts = [\"o/%.o\"]\nins = [\"%.c\"]\nimplicit-ins = [\"x.h\"]\n" ++
  "[[build]]\nrule = \"ld\"\nouts = [\"app\"]\nins = [\"o/a.o\", \"o/b.o\"]\n")
  [("*.c", ["a.c", "b.c"]), ("a.*", ["a.c", "a.c.mise-old"])]
  == ninjaOf ("sources = [\"x.h\", \"a.c\", \"b.c\"]\n" ++ rules2 ++
  "[[build]]\nrule = \"cc\"\nouts = [\"o/a.o\"]\nins = [\"a.c\"]\nimplicit-ins = [\"x.h\"]\n" ++
  "[[build]]\nrule = \"cc\"\nouts = [\"o/b.o\"]\nins = [\"b.c\"]\nimplicit-ins = [\"x.h\"]\n" ++
  "[[build]]\nrule = \"ld\"\nouts = [\"app\"]\nins = [\"o/a.o\", \"o/b.o\"]\n")
-- A `foreach` build matches the outputs of plain builds and of earlier
-- `foreach` builds.
#guard has (ninjaOf ("sources = [\"a.y\"]\n" ++ rules2 ++
  "[[build]]\nrule = \"cc\"\nforeach = \"g/%.c\"\nouts = [\"o/%.o\"]\nins = [\"g/%.c\"]\n" ++
  "[[build]]\nrule = \"cc\"\nouts = [\"g/a.c\"]\nins = [\"a.y\"]\n"))
  "build o/a.o: cc g/a.c\n"
#guard has (ninjaOf ("sources = [\"a.y\"]\n" ++ rules2 ++
  "[[build]]\nrule = \"cc\"\nforeach = \"%.y\"\nouts = [\"g/%.c\"]\nins = [\"%.y\"]\n" ++
  "[[build]]\nrule = \"cc\"\nforeach = [\"g/%.c\"]\nouts = [\"o/%.o\"]\nins = [\"g/%.c\"]\n"))
  "build o/a.o: cc g/a.c\n"
-- In a build without `foreach`, a `%` input stands for every match.
#guard ninjaOf ("sources = [\"a.c\", \"b.c\", \"x.h\"]\n" ++ rules2 ++
  "[[build]]\nrule = \"ld\"\nouts = [\"app\"]\nins = [\"o/%.o\"]\n" ++
  "[[build]]\nrule = \"cc\"\nforeach = \"%.c\"\nouts = [\"o/%.o\"]\nins = [\"%.c\"]\nimplicit-ins = [\"x.h\"]\n")
  == ninjaOf explicitBuild
#guard rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"x\"]\nins = [\"%.h\"]\n") (msg := "no source or output matches")
#guard rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"x\"]\nins = [\"%%.c\"]\n") (msg := "must contain one %")
-- The build's own outputs are not inputs.
#guard has (ninjaOf (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"b.c\"]\nins = [\"%.c\"]\n")) "build b.c: cc a.c\n"
#guard rejects (base ++ "[[build]]\nrule = \"cc\"\nforeach = \"%.h\"\nouts = [\"%.o\"]\nins = [\"%.h\"]\n") (msg := "no source or output matches")
#guard rejects (base ++ "[[build]]\nrule = \"cc\"\nforeach = \"a.c\"\nouts = [\"%.o\"]\n") (msg := "must contain one %")
#guard rejects (base ++ "[[build]]\nrule = \"cc\"\nforeach = \"%.c\"\nouts = [\"a.o\"]\n") (msg := "no output contains %")
#guard rejects (base ++ "[[build]]\nrule = \"cc\"\nouts = [\"x\"]\nins = [\"y\"]\n" ++
  "[[build]]\nrule = \"cc\"\nouts = [\"y\"]\nins = [\"x\"]\n") (msg := "cycle: build [\"x\"] -> build [\"y\"] -> build [\"x\"]")
#guard rejects ("source-globs = [\"*.c\"]\n" ++ rules2) (msg := "was not expanded")
#guard (loadWith ("source-globs = [\"*.c\"]\n" ++ rules2) [] [("*.c", [])]) matches .error _
#guard rejects ("source-globs = [\"../*.c\"]\n" ++ rules2) (msg := "no . or .. components")
-- Aliases become `phony` edges after the builds; an alias of an alias is
-- flattened; a default may name an alias.
#guard has (ninjaOf ("defaults = [\"all\"]\n" ++ explicitBuild ++ "[aliases]\nobjs = [\"o/a.o\", \"o/b.o\"]\nall = [\"app\", \"objs\", \"o/a.o\"]\n"))
  "build objs: phony o/a.o o/b.o\nbuild all: phony app o/a.o o/b.o\ndefault all\n"
-- Defaults keep their order.
#guard has (ninjaOf ("defaults = [\"o/b.o\", \"all\", \"app\"]\n" ++ explicitBuild ++ "[aliases]\nall = [\"app\"]\n"))
  "default o/b.o all app\n"
-- An alias target with `%` stands for every match.
#guard has (ninjaOf (explicitBuild ++ "[aliases]\nobjs = [\"o/%.o\"]\n")) "build objs: phony o/a.o o/b.o\n"
#guard rejects (explicitBuild ++ "[aliases]\nobjs = [\"q/%.o\"]\n") (msg := "aliases: objs: no source or output matches")
#guard rejects (explicitBuild ++ "[aliases]\nx = [\"y\"]\ny = [\"x\"]\n") (msg := "aliases: cycle: x -> y -> x")
#guard rejects (explicitBuild ++ "[aliases]\nx = []\n") (msg := "no targets")
#guard rejects (explicitBuild ++ "[aliases]\napp = [\"o/a.o\"]\n") (msg := "already declared")
#guard rejects (explicitBuild ++ "[aliases]\nx = [\"nope\"]\n") (msg := "is not a source, a build output or an alias")
#guard rejects ("defaults = [\"a.c\"]\n" ++ explicitBuild) (msg := "is a source")
-- An edge cannot read an alias.
#guard rejects (explicitBuild ++ "[[build]]\nrule = \"ld\"\nouts = [\"z\"]\nins = [\"all\"]\n[aliases]\nall = [\"app\"]\n")
  (msg := "is not a source or a build output")

/-! The glob matcher. -/

#guard Glob.matches "*.c" "a.c"
#guard !Glob.matches "*.c" "src/a.c"
#guard !Glob.matches "*.c" ".a.c"
#guard Glob.matches ".*.c" ".a.c"
#guard Glob.matches "src/**/*.c" "src/a.c"
#guard Glob.matches "src/**/*.c" "src/x/y/a.c"
#guard !Glob.matches "src/**/*.c" "src/.x/a.c"
#guard Glob.matches "a?.h" "ab.h"
#guard !Glob.matches "a?.h" "a.h"
#guard Glob.matches "**/x" "x"
#guard (Glob.components "a/**") matches .error _
#guard (Glob.components "a**/b") matches .error _
#guard (Glob.components "/a") matches .error _

end MiseTest.Toml
