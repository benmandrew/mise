import Lean
import Mise
import MiseTest.Gloss
open Lean Meta Elab Command

/-!
Lists the definitions a reader must trust for each theorem in
`Mise.Headline`, and writes two files into the directory named by the
environment variable `TRUSTED_OUT` (default `docs`):

* `trusted.md`, the list with sizes and locations;
* `headline.typ`, a Typst document with, for each theorem, its docstring, its
  statement as written in the source, and an English translation made by
  `Gloss.statement`; then every trusted definition in reading order, with its
  docstring and source.

It prints one line per problem: `missing docstring: X` for a trusted
declaration without a docstring, and `no template: X` for a constant that a
statement mentions but that has no `Gloss:` template. Run it with
`scripts/trusted.sh`, which compares the files with `docs/` under `--check`.

The walk starts from a theorem's statement and follows every `Mise`
constant it mentions, through the types and bodies of definitions and the
constructors of inductive types. It does not enter theorems, because Lean
checks their proofs; proofs inside a definition are abstracted into
auxiliary theorems when the definition is compiled, so it skips those too.
Constants outside `Mise` (Lean's core library) are not listed.
-/

namespace Trusted

def isMise (n : Name) : Bool := n.getRoot == `Mise

/-- Auxiliary constants a reader would not look up by name. -/
def isAux (env : Environment) (n : Name) : Bool :=
  n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n ||
    isMatcherCore env n || isRecCore env n

/-- Generated helpers: `ctorIdx`, and derived `Repr` instances, which
affect printing only. -/
def isGenerated (n : Name) : Bool :=
  n.components.any fun c => c == `ctorIdx || c.toString.startsWith "instRepr"

/-- The declaration a reader looks up for constant `n`: constructors and
projections map to their type, and a constant with an auxiliary prefix (such
as `Task.brecOn.go`) maps to the owner of that prefix. -/
partial def owner (env : Environment) (n : Name) : Name :=
  let pre := (List.range (n.getNumParts + 1)).filterMap fun i =>
    let p := (n.components.take i).foldl (· ++ ·) Name.anonymous
    if i > 0 && isAux env p then some p else none
  match pre.head? with
  | some p => owner env p.getPrefix
  | none =>
    if n.components.getLast? == some `ctorIdx then n.getPrefix
    else match env.find? n with
      | some (.ctorInfo c) => c.induct
      | _ => match env.getProjectionFnInfo? n with
        | some info => info.ctorName.getPrefix
        | none => n

/-- The constants a declaration mentions directly, outside proofs. -/
def next (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some (.ctorInfo c) => c.type.getUsedConstants.push c.induct
  | some (.recInfo r) => r.type.getUsedConstants
  | some (.axiomInfo a) => a.type.getUsedConstants
  | _ => #[]

/-- Every `Mise` constant reachable from `start`, outside proofs. -/
partial def reach (env : Environment) (start : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := start
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n || !isMise n then continue
    seen := seen.insert n
    todo := todo ++ next env n
  return seen

/-- The trusted declarations of theorem `thm`, by owner. -/
def trustedOf (env : Environment) (thm : Name) : NameSet :=
  match env.find? thm with
  | some (.thmInfo t) =>
    (reach env t.type.getUsedConstants).foldl (fun s n =>
      match env.find? n with
      | some (.thmInfo _) => s
      | _ => if isGenerated n then s else s.insert (owner env n)) {}
  | _ => {}

/-- The trusted declarations that `d` mentions directly. Auxiliary constants
of `d` itself (matchers, structural recursion) are looked through. -/
partial def usesOf (env : Environment) (trusted : NameSet) (d : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut out : NameSet := {}
  let mut todo := next env d
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n || !isMise n then continue
    seen := seen.insert n
    if let some (.thmInfo _) := env.find? n then continue
    let o := owner env n
    if o != d && trusted.contains o then out := out.insert o
    else if o == d || isAux env n then todo := todo ++ next env n
  return out

/-- Module, its position in import order (dependencies first), and the
declaration's range as (line, column) pairs. -/
def location (n : Name) : CommandElabM (String × Nat × Position × Position) := do
  let env ← getEnv
  let (mod, idx) := match env.getModuleIdxFor? n with
    | some i => (env.header.moduleNames[i.toNat]!.toString, i.toNat)
    | none => ("?", 0)
  let r ← liftCoreM (findDeclarationRanges? n)
  match r with
  | some r => return (mod, idx, r.range.pos, r.range.endPos)
  | none => return (mod, idx, ⟨0, 0⟩, ⟨0, 0⟩)

def modPath (mod : String) : String := mod.replace "." "/" ++ ".lean"

def sortNames (s : NameSet) : Array Name :=
  s.toArray.qsort (fun a b => a.toString < b.toString)

/-- The source text between two positions of a file. -/
def slice (lines : Array String) (a b : Position) : String := Id.run do
  let mut out : Array String := #[]
  for i in [a.line - 1 : b.line] do
    let l := lines[i]!
    let l := if i == b.line - 1 then String.ofList (l.toList.take b.column) else l
    let l := if i == a.line - 1 then String.ofList (l.toList.drop a.column) else l
    out := out.push l
  return "\n".intercalate out.toList

/-- Drop a leading docstring, and any attributes that follow it stay. -/
def dropDoc (s : String) : String :=
  if s.startsWith "/--" then
    match s.splitOn "-/" with
    | _ :: rest => ("-/".intercalate rest).trimAsciiStart.toString
    | [] => s
  else s

/-- The statement of a theorem: its source up to the `:=` that starts the
proof, outside any brackets. -/
def statementText (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut depth : Int := 0
  for h : i in [0 : cs.size] do
    let c := cs[i]
    if c == '(' || c == '[' || c == '{' || c == '⟨' then depth := depth + 1
    else if c == ')' || c == ']' || c == '}' || c == '⟩' then depth := depth - 1
    else if c == ':' && depth == 0 && cs[i + 1]? == some '=' then
      return (String.ofList (cs.toList.take i)).trimAsciiEnd.toString
  return s

/-! ## Typst output -/

/-- A Typst string literal. -/
def tq (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '\\' then "\\\\" else if c == '"' then "\\\"" else if c == '\n' then "\\n"
    else if c == '\t' then "\\t" else c.toString) ++ "\""

def tText (s : String) : String := if s.isEmpty then "" else s!"#{tq s};"
def tCode (s : String) : String := s!"#raw({tq s});"

partial def tPhrase (p : Gloss.Phrase) : String :=
  String.join (p.toList.map go)
where
  go : Gloss.Inl → String
    | .txt s => tText s
    | .code s => tCode s
    | .grp b => tText "(" ++ String.join (b.toList.map go) ++ tText ")"
    | .intro b => String.join (b.toList.map go)

/-- Inline Markdown (code, `**strong**`, `*emphasis*`) as Typst markup. -/
partial def mdInline (s : String) : String :=
  go s.toList "" ""
where
  go : List Char → String → String → String
    | [], buf, out => out ++ tText buf
    | '`' :: r, buf, out =>
      let body := r.takeWhile (· != '`')
      go ((r.dropWhile (· != '`')).drop 1) "" (out ++ tText buf ++ tCode (String.ofList body))
    | '*' :: '*' :: r, buf, out =>
      let (body, rest) := splitAt "**" r
      go rest "" (out ++ tText buf ++ "#strong[" ++ mdInline body ++ "];")
    | '*' :: c :: r, buf, out =>
      if c != ' ' && (c :: r).contains '*' then
        let body := (c :: r).takeWhile (· != '*')
        go (((c :: r).dropWhile (· != '*')).drop 1) "" (out ++ tText buf ++ "#emph[" ++ mdInline (String.ofList body) ++ "];")
      else go (c :: r) (buf.push '*') out
    | c :: r, buf, out => go r (buf.push c) out
  splitAt (sep : String) (cs : List Char) : String × List Char :=
    match (String.ofList cs).splitOn sep with
    | a :: rest => (a, (sep.intercalate rest).toList)
    | [] => ("", [])

/-- Markdown blocks: paragraphs, `#` headings, and bullet or numbered
lists. -/
def mdBlocks (doc : String) : String := Id.run do
  let mut blocks : Array (String × String) := #[]  -- kind, text
  for line in doc.splitOn "\n" do
    let t := line.trimAscii.toString
    let numbered := (t.takeWhile Char.isDigit).toString.length > 0 &&
      ((t.dropWhile Char.isDigit).toString.startsWith ". ")
    if t.isEmpty then blocks := blocks.push ("", "")
    else if t.startsWith "#" then
      blocks := (blocks.push ("h", (t.dropWhile (· == '#')).trimAscii.toString)).push ("", "")
    else if t.startsWith "* " || t.startsWith "- " then blocks := blocks.push ("-", (t.drop 2).toString)
    else if numbered then blocks := blocks.push ("+", ((t.dropWhile Char.isDigit).drop 2).toString)
    else
      let (k, s) := blocks.back?.getD ("", "")
      if k == "" then blocks := blocks.push ("p", t)
      else blocks := blocks.pop.push (k, s ++ " " ++ t)
  let mut out := ""
  for (k, s) in blocks do
    if k == "" then out := out ++ "\n"
    else if k == "h" then out := out ++ "#strong[" ++ mdInline s ++ "];\n"
    else if k == "p" then out := out ++ mdInline s ++ "\n"
    else out := out ++ k ++ " " ++ mdInline s ++ "\n"
  return out.trimAscii.toString ++ "\n"

def defLabel (n : Name) : String := tq ("def:" ++ n.toString)

def short (n : Name) : String := (n.replacePrefix `Mise .anonymous).toString

def defLink (shown : String) (target : Name) : String :=
  s!"#link(label({defLabel target}))[{tCode shown}];"

end Trusted

open Trusted in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let outDir := (← IO.getEnv "TRUSTED_OUT").getD "docs"
  let thms := sortNames <| env.constants.fold (init := {}) fun s n ci =>
    match ci with
    | .thmInfo _ => if (`Mise.Headline).isPrefixOf n && !n.isInternalDetail then s.insert n else s
    | _ => s
  -- Owners of every theorem, with locations.
  let mut all : NameSet := {}
  let mut perThm : Array (Name × Array Name) := #[]
  for t in thms do
    let ds := sortNames (trustedOf env t)
    perThm := perThm.push (t, ds)
    all := ds.foldl (·.insert ·) all
  let mut rows : Array (Nat × String × Position × Position × Name) := #[]
  for d in all.toArray do
    let (m, i, a, b) ← location d
    rows := rows.push (i, m, a, b, d)
  rows := rows.qsort fun x y => x.1 < y.1 || (x.1 == y.1 && x.2.2.1.line < y.2.2.1.line)
  let sorted := rows.map fun (_, m, a, b, d) => (m, a.line, b.line, d)
  let total := sorted.foldl (fun acc r => acc + (r.2.2.1 - r.2.1 + 1)) 0
  let mods := (sorted.map (·.1)).toList.eraseDups
  /- Markdown. -/
  let mut out := "# Trusted definitions\n\n"
  out := out ++ "Generated by `scripts/trusted.sh` from `test/MiseTest/Trusted.lean`; do not edit. `scripts/check.sh` fails if this file is out of date.\n\n"
  out := out ++ s!"The theorems in `Mise/Headline.lean` are checked by Lean, so their meaning rests on the statements and on the definitions below. The list follows every `Mise` constant a statement mentions, through definitions and inductive types but not into proofs. Lean's core library is not listed. There are {sorted.size} declarations, {total} lines in all, across {mods.length} files.\n\n"
  let shortThm (t : Name) := (t.replacePrefix `Mise.Headline .anonymous).toString
  let sets := perThm.map fun (t, ds) => (t, ds.foldl (fun (acc : NameSet) d => acc.insert d) {})
  out := out ++ "## By theorem\n\nThe number of declarations each theorem depends on, by file. A blank cell means none.\n\n"
  out := out ++ "| File | " ++ " | ".intercalate (perThm.toList.map fun (t, _) => s!"`{shortThm t}`") ++ " |\n"
  out := out ++ "|---|" ++ String.join (perThm.toList.map fun _ => "---|") ++ "\n"
  for m in mods do
    let ds := sorted.filter (·.1 == m) |>.map (·.2.2.2)
    let cells := sets.toList.map fun (_, set) =>
      let k := (ds.filter set.contains).size
      if k == 0 then "" else toString k
    out := out ++ s!"| `{modPath m}` | " ++ " | ".intercalate cells ++ " |\n"
  let totals := perThm.toList.map fun (_, ds) => toString ds.size
  out := out ++ "| **Total** | " ++ " | ".intercalate totals ++ " |\n"
  out := out ++ "\n## By file\n\nRead in this order: each file uses only the ones above it.\n\n| Declaration | Lines | Size |\n|---|---|---|\n"
  for (m, a, b, d) in sorted do
    out := out ++ s!"| `{d.replacePrefix `Mise .anonymous}` | `{modPath m}:{a}`–{b} | {b - a + 1} |\n"
  IO.FS.writeFile (outDir ++ "/trusted.md") out
  /- Problems. -/
  let mut report : Array String := #[]
  for (_, _, _, d) in sorted do
    if (← liftCoreM (findDocString? env d)).isNone then
      report := report.push s!"missing docstring: {d}"
  /- Typst. -/
  let mut files : Std.HashMap String (Array String) := {}
  let readLines (m : String) (files : Std.HashMap String (Array String)) :
      IO (Array String × Std.HashMap String (Array String)) := do
    match files[m]? with
    | some ls => return (ls, files)
    | none =>
      let ls := ((← IO.FS.readFile (modPath m)).splitOn "\n").toArray
      return (ls, files.insert m ls)
  let mut typ := "// Generated by scripts/trusted.sh from test/MiseTest/Trusted.lean; do not edit.\n"
  typ := typ ++ "// scripts/check.sh fails if this file is out of date. Build the PDF with `scripts/trusted.sh --pdf`.\n"
  typ := typ ++ "#import \"headline-style.typ\": *\n#show: doc\n\n"
  -- Introduction: the module docstring of `Mise/Headline.lean`.
  let (hl, files') ← readLines "Mise.Headline" files
  files := files'
  let hsrc := "\n".intercalate hl.toList
  let modDoc := match hsrc.splitOn "/-!" with
    | _ :: r :: _ => ((r.splitOn "-/").head!).trimAscii.toString
    | _ => ""
  typ := typ ++ "= Introduction\n\n" ++ mdBlocks modDoc ++ "\n#how-to-read\n\n"
  -- Theorems, in source order.
  let mut thmRows : Array (Nat × Name) := #[]
  for t in thms do
    let (_, _, a, _) ← location t
    thmRows := thmRows.push (a.line, t)
  thmRows := thmRows.qsort (·.1 < ·.1)
  let mut noTemplate : NameSet := {}
  let mut omits : NameSet := {}
  let mut noSingular : NameSet := {}
  typ := typ ++ "= Theorems\n\n"
  for (_, t) in thmRows do
    let (m, _, a, b) ← location t
    let (ls, files') ← readLines m files
    files := files'
    let src := statementText (dropDoc (slice ls a b))
    let doc := ((← liftCoreM (findDocString? env t)).getD "")
    let ty := (env.find? t).get!.type
    let (st, s) ← liftTermElabM (Gloss.statement ty |>.run {})
    noTemplate := s.missing.foldl (·.insert ·) noTemplate
    omits := s.omits.foldl (·.insert ·) omits
    noSingular := s.noSingular.foldl (·.insert ·) noSingular
    typ := typ ++ s!"#theorem-heading({tq (shortThm t)}, {tq (modPath m)}, {a.line})\n\n"
    typ := typ ++ mdBlocks doc ++ "\n#part[Statement]\n" ++
      s!"#raw(lang: \"lean\", block: true, {tq src})\n\n#part[In English]\n#english[\n"
    if !st.vars.isEmpty then
      typ := typ ++ "#part-sub[For all]\n"
      for (vs, ty) in st.vars do
        let names := Gloss.andList (vs.toList.map Gloss.code)
        let verb := if vs.size == 1 then " ranges over " else " range over "
        typ := typ ++ "- " ++ tPhrase (names ++ Gloss.txt verb ++ ty ++ Gloss.txt ".") ++ "\n"
    if !st.hyps.isEmpty then
      typ := typ ++ "#part-sub[Assume]\n"
      for (h, p) in st.hyps do
        let tag := match h with
          | some h => Gloss.txt "(" ++ Gloss.code h ++ Gloss.txt ") "
          | none => #[]
        typ := typ ++ "- " ++ tPhrase (tag ++ p ++ Gloss.txt ".") ++ "\n"
    typ := typ ++ "#part-sub[Then]\n"
    for p in st.conclude do
      typ := typ ++ "- " ++ tPhrase (p ++ Gloss.txt ".") ++ "\n"
    typ := typ ++ "]\n"
    -- The `Mise` names in the statement, linked to their definitions.
    let named := sortNames <| ty.getUsedConstants.foldl (fun s n =>
      if isMise n && all.contains (owner env n) then s.insert n else s) {}
    let links := named.toList.map fun n => defLink (short n) (owner env n)
    typ := typ ++ "#part[Names in the statement]\n" ++ ", ".intercalate links ++
      s!". The statement rests on {(perThm.find? (·.1 == t)).map (·.2.size) |>.getD 0} trusted declarations in all.\n\n"
  -- Trusted definitions, in reading order.
  typ := typ ++ "= Trusted definitions\n\n#trusted-intro(" ++ toString sorted.size ++ ", " ++ toString total ++ ")\n\n"
  for m in mods do
    typ := typ ++ s!"== {tCode (modPath m)}\n\n"
    for (m', _, _, d) in sorted do
      if m' != m then continue
      let (_, _, a, b) ← location d
      let (ls, files') ← readLines m files
      files := files'
      let src := dropDoc (slice ls a b)
      let doc := (← liftCoreM (findDocString? env d)).getD ""
      let g := Gloss.Glosses.parse doc
      typ := typ ++ s!"#def-heading({tq (short d)}, {defLabel d}, {tq (modPath m)}, {a.line}, {b.line})\n\n"
      typ := typ ++ (if g.rest.isEmpty then "#no-doc\n" else mdBlocks g.rest)
      for (k, t?) in [("Template", g.main), ("Template, first component", g.fst),
          ("Template, second component", g.snd), ("Template, as a function", g.fn),
          ("Template, singular", g.one)] do
        if let some t := t? then typ := typ ++ s!"\n#template({tq k}, {tq t})\n"
      typ := typ ++ s!"\n#raw(lang: \"lean\", block: true, {tq src})\n"
      let uses := sortNames (usesOf env all d)
      if !uses.isEmpty then
        typ := typ ++ "#uses[" ++ ", ".intercalate (uses.toList.map fun u => defLink (short u) u) ++ "]\n"
      typ := typ ++ "\n"
  for n in sortNames noTemplate do
    report := report.push s!"no template: {n}"
  for n in sortNames omits do
    report := report.push s!"template omits argument: {n}"
  for n in sortNames noSingular do
    report := report.push s!"no singular noun: {n}"
  if !noTemplate.isEmpty || !omits.isEmpty then
    typ := typ ++ "= Warnings\n\n"
    if !noTemplate.isEmpty then
      typ := typ ++ "#warnings-intro\n\n"
      for n in sortNames noTemplate do
        typ := typ ++ "- " ++ tCode n.toString ++ "\n"
    if !omits.isEmpty then
      typ := typ ++ "\n#omits-intro\n\n"
      for n in sortNames omits do
        typ := typ ++ "- " ++ tCode n.toString ++ "\n"
  IO.FS.writeFile (outDir ++ "/headline.typ") typ
  for r in report do IO.println r
