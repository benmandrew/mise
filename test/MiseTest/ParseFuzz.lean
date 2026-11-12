import MiseTest.DiffGen

/-!
# Parser fuzzer: the Lean side

`test/parser-fuzz.sh` links this module into a libFuzzer harness
(`test/parser_fuzz.cc`) together with Ninja's own manifest parser. For each
input the harness asks the parser model what the manifest means, and when
the model accepts it, checks that Ninja reads the same edges, evaluates the
same edge variables and records the same defaults. Ninja accepts more than
the model's subset, so an input the model rejects proves nothing.

Both sides print what they read in the format of `dump`: one field per
line, each `KEY LEN:VALUE`, where `LEN` is the value's length in bytes, so a
value may hold any character, newlines included.
-/

namespace MiseTest.ParseFuzz
open Mise.Syntax MiseTest.DiffTest

/-- One field of a dump. -/
def field (k v : String) : String := s!"{k} {v.utf8ByteSize}:{v}\n"

/-- The edge variables compared with Ninja's `Edge::GetBinding`, for every
edge that is not `phony`. -/
def keys : List String := ["command", "description", "depfile", "deps", "restat"]

/-- The value of each top-level `ninja_required_version` binding, evaluated
where it appears, as Ninja passes it to `CheckNinjaVersion`. -/
def versions (m : Manifest) : List String := Id.run do
  let mut st : Elab := {}
  let mut out := []
  for s in m.stmts do
    if let .binding "ninja_required_version" v := s then
      out := out ++ [evalWith (fileLook st.file) v]
    st := st.step s
  out

/-- Whether evaluating `v` on an edge reaches a rule variable that is
already being evaluated. Ninja then exits with "cycle in rule variables"
(`EdgeEnv::LookupVariable`), while the model cuts the recursion with fuel
(see `Mise/Frontend/NOTES.md`), so the harness does not compare such an
edge's variables. A variable bound in the edge's or the file's scope, and
`in`, `in_newline` and `out`, end the chain, as in `EdgeInfo.lookup`. -/
def cyclic (file : Scope) (c : EdgeInfo) : Nat → List String → String → Bool
  | 0, _, _ => true
  | fuel + 1, stack, v =>
    if v == "in" || v == "in_newline" || v == "out" then false
    else if ((c.own.getD file).get v).isSome then false
    else match c.rule.get v with
      | none => false
      | some ev => stack.contains v || ev.any fun
        | .var w => cyclic file c fuel (v :: stack) w
        | .lit _ => false

/-- What the parser model reads from a manifest: the version values, then
each edge with its rule, outputs, inputs and (unless it is `phony`) its
evaluated variables, or `cyclic` when evaluating one would reach a cycle,
then the default targets. -/
def dump (m : Manifest) : String := Id.run do
  let st := m.elab
  let mut out := String.join ((versions m).map (field "version"))
  for c in st.edges do
    let e := c.edge
    out := out ++ field "edge" e.rule
    for p in e.outs do out := out ++ field "out" p
    for p in e.implicitOuts do out := out ++ field "iout" p
    for p in e.ins do out := out ++ field "in" p
    for p in e.implicitIns do out := out ++ field "iin" p
    for p in e.orderOnly do out := out ++ field "oo" p
    if e.rule != "phony" then
      if keys.any (cyclic st.file c (c.rule.bindings.length + 2) []) then
        out := out ++ field "cyclic" ""
      else
        for k in keys do out := out ++ field k (c.binding st.file k)
  for s in m.stmts do
    if let .default ts := s then
      for t in ts do out := out ++ field "default" t
  out

/-- The parser model's reading of `b`: `dump`, the empty string when the
model rejects the manifest, or `skip` when `b` is not UTF-8. -/
@[export mise_fuzz_text]
def fuzzText (b : ByteArray) : String :=
  match String.fromUTF8? b with
  | none => "skip"
  | some s => match parse s with
    | none => ""
    | some m => dump m

/-- The manifest text that `b` chooses through `genManifest`. The model
accepts every such text. -/
@[export mise_fuzz_gen]
def fuzzGen (b : ByteArray) : String := print (genManifest.runBytes b)

end MiseTest.ParseFuzz
