import Mise.Frontend.Toml

/-! `lake exe tomljson FILE...` parses each file with `Mise.Frontend.Toml.parse`
and prints one line per file: `ok JSON` with the value tree as canonical JSON,
or `err MESSAGE`. The JSON is what Python's
`json.dumps(v, sort_keys=True, separators=(",", ":"))` prints for the same
tree, so `test/toml_diff.py` compares the two byte for byte. -/

namespace MiseTest.TomlJson
open Mise.Frontend.Toml

def hex4 (n : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.ofList (List.replicate (4 - d.length) '0' ++ d)

/-- A JSON string with Python's `ensure_ascii` escapes: printable ASCII as is,
everything else as `\uXXXX`, with a surrogate pair above U+FFFF. -/
def jsonStr (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := out ++ match c with
      | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
      | '\x08' => "\\b" | '\x0c' => "\\f"
      | c =>
        let n := c.toNat
        if 0x20 ≤ n && n ≤ 0x7e then c.toString
        else if n < 0x10000 then "\\u" ++ hex4 n
        else
          let m := n - 0x10000
          "\\u" ++ hex4 (0xd800 + m / 0x400) ++ "\\u" ++ hex4 (0xdc00 + m % 0x400)
  return out ++ "\""

partial def json : Value → String
  | .str s => jsonStr s
  | .bool b => if b then "true" else "false"
  | .int n => toString n
  | .arr xs => "[" ++ ",".intercalate (xs.map json) ++ "]"
  | .table t => obj t
where
  obj (t : Table) : String :=
    let t := t.mergeSort fun a b => a.1 < b.1 || a.1 == b.1
    "{" ++ ",".intercalate (t.map fun (k, v) => jsonStr k ++ ":" ++ json v) ++ "}"

end MiseTest.TomlJson

open MiseTest.TomlJson Mise.Frontend.Toml in
def main (files : List String) : IO UInt32 := do
  let out ← IO.getStdout
  for f in files do
    let r : Except String Table ←
      try (parse <$> IO.FS.readFile f) catch e => pure (.error (toString e))
    match r with
    | .ok t => out.putStrLn s!"ok {json.obj t}"
    | .error e => out.putStrLn s!"err {e.replace "\n" " "}"
  return 0
