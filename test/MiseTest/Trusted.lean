import Lean
import Mise
import MiseTest.Gloss
open Lean Meta Elab Command

/-!
Lists the definitions a reader must trust for each theorem in
`Mise.Headline`, and writes two files into the directory named by the
environment variable `TRUSTED_OUT` (default `docs`):

* `trusted.md`, the list with sizes and locations;
* `headline.typ`, a Typst document for review. Each core theorem (its
  docstring has the line `Review: core`) appears with its docstring, its
  statement as written in the source with each name linked to its
  definition, and an English translation made by
  `Gloss.statement`. Then come, in reading order, the definitions the core
  statements name and the ones those name in turn, except that the printer
  and parser are not expanded.

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

/-- A phrase as Typst markup. `target n` is the definition that words from
the template of `n` link to, if it is in the document. -/
partial def tPhrase (target : Name → Option Name) (p : Gloss.Phrase) : String :=
  String.join (p.toList.map go)
where
  go : Gloss.Inl → String
    | .txt s => tText s
    | .code s => tCode s
    | .grp b => tText "(" ++ String.join (b.toList.map go) ++ tText ")"
    | .intro b | .cx b => String.join (b.toList.map go)
    | .link n b =>
      let body := String.join (b.toList.map go)
      match target n with
      | some t => s!"#link(label({tq ("def:" ++ t.toString)}))[{body}];"
      | none => body

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

/-- A core theorem carries the line `Review: core` in its docstring; the PDF
gives it in full, with the definitions its statement names. -/
def isCore (doc : String) : Bool :=
  (doc.splitOn "\n").any (·.trimAscii.toString == "Review: core")

/-- A docstring without its `Review:` line. -/
def reviewDoc (doc : String) : String :=
  ("\n".intercalate ((doc.splitOn "\n").filter fun l =>
    !l.trimAscii.toString.startsWith "Review:")).trimAscii.toString

/-- Modules whose definitions the PDF does not expand: the printer and the
parser, which `meaning` covers by round trip and `test/stage3-diff.sh` tests
against Ninja. -/
def notExpanded (mod : String) : Bool :=
  mod == "Mise.Syntax.Print" || mod == "Mise.Syntax.Parse"

def short (n : Name) : String := (n.replacePrefix `Mise .anonymous).toString

/-- Where a file's source is published. Links use `main`, not a commit, so
that `docs/headline.typ` does not change with every commit. -/
def sourceBase : String := "https://github.com/benmandrew/mise/blob/main/"

/-- A link to lines `a` to `b` of `file`, as a Typst string literal. -/
def sourceUrl (file : String) (a b : Nat) : String :=
  tq (sourceBase ++ file ++ (if a == b then s!"#L{a}" else s!"#L{a}-L{b}"))

/-- Where the source of `decl` names a constant. Lean's reference index (the
`.ilean` file `lake build` writes next to each module) records every
identifier the elaborator resolved: the constant, its position, and the
declaration it occurs in. Each result is the constant, the line (from 0), and
the first and last column, for usages on one line. -/
def usagesIn (ilean : Json) (decl : Name) : Except String (Array (Name × Nat × Nat × Nat)) := do
  let v ← (← ilean.getObjVal? "version").getNat?
  if v != 5 then throw s!"unknown .ilean version {v}"
  let refs ← (← ilean.getObjVal? "references").getObj?
  let mut out := #[]
  for (k, info) in refs.toList do
    let some c := ((← Json.parse k).getObjVal? "c").toOption | continue
    let n ← (← c.getObjVal? "n").getStr?
    let some us := (info.getObjVal? "usages").toOption | continue
    for u in ← us.getArr? do
      let u ← u.getArr?
      if h : u.size < 5 then continue else
      if (← u[4].getStr?) != decl.toString then continue
      let sl ← u[0].getNat?
      if (← u[2].getNat?) != sl then continue
      out := out.push (n.toName, sl, ← u[1].getNat?, ← u[3].getNat?)
  return out

/-- A statement as Typst arguments for `lean-linked`: the pieces of its
source, each with the label of the definition it names or `none`. `start` is
the statement's offset in the file, `offset l c` the offset of line `l`,
column `c`, `us` the usages in the theorem, and `target` the shown
definition a constant belongs to, if any. -/
def linkedParts (stmt : String) (start : Nat) (offset : Nat → Nat → Nat)
    (us : Array (Name × Nat × Nat × Nat)) (target : Name → Option Name) :
    Except String String := do
  let cs := stmt.toList.toArray
  let mut spans : Array (Nat × Nat × Name) := #[]
  for (n, l, a, b) in us do
    let (s, e) := (offset l a, offset l b)
    if s < start || e > start + cs.size then continue
    let some d := target n | continue
    let text := String.ofList (cs.extract (s - start) (e - start)).toList
    -- The index and the source must agree: the text at the position is the
    -- last part of the constant's name.
    if text != n.getString! then throw s!"{n} at {l + 1}:{a + 1} reads `{text}`"
    spans := spans.push (s - start, e - start, d)
  spans := spans.qsort (·.1 < ·.1)
  let mut parts : Array String := #[]
  let mut i := 0
  for (s, e, d) in spans do
    if s < i then continue
    if s > i then parts := parts.push s!"({tq (String.ofList (cs.extract i s).toList)}, none)"
    parts := parts.push s!"({tq (String.ofList (cs.extract s e).toList)}, {defLabel d})"
    i := e
  if i < cs.size then parts := parts.push s!"({tq (String.ofList (cs.extract i cs.size).toList)}, none)"
  return ", ".intercalate parts.toList

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
  -- Introduction: the module docstring of `Mise/Headline.lean`, without its
  -- title, which the document's own title replaces.
  let (hl, files') ← readLines "Mise.Headline" files
  files := files'
  let hsrc := "\n".intercalate hl.toList
  let modDoc := match hsrc.splitOn "/-!" with
    | _ :: r :: _ => ((r.splitOn "-/").head!).trimAscii.toString
    | _ => ""
  let modDoc := "\n".intercalate ((modDoc.splitOn "\n").filter (!·.trimAscii.toString.startsWith "#"))
  typ := typ ++ "#intro[\n" ++ mdBlocks modDoc ++ "]\n\n"
  -- Theorems, in source order, split into core and others.
  let mut thmRows : Array (Nat × Name) := #[]
  for t in thms do
    let (_, _, a, _) ← location t
    thmRows := thmRows.push (a.line, t)
  thmRows := thmRows.qsort (·.1 < ·.1)
  let mut core : Array Name := #[]
  for (_, t) in thmRows do
    if isCore ((← liftCoreM (findDocString? env t)).getD "") then core := core.push t
  -- The definitions shown: those a core statement names (depth 1), and the
  -- ones they name in turn (depth 2), except inside the syntax modules.
  let named (t : Name) : NameSet := ((env.find? t).get!.type.getUsedConstants).foldl (fun s n =>
    if isMise n && all.contains (owner env n) then s.insert (owner env n) else s) {}
  let mut depth1 : NameSet := {}
  for t in core do depth1 := (named t).foldl (·.insert ·) depth1
  let mut depth2 : NameSet := {}
  for d in sortNames depth1 do
    let (m, _, _, _) ← location d
    if notExpanded m then continue
    for u in sortNames (usesOf env all d) do
      let (mu, _, _, _) ← location u
      if !depth1.contains u && !notExpanded mu then depth2 := depth2.insert u
  let shown := depth2.foldl (·.insert ·) depth1
  let omitted := sorted.filter (!shown.contains ·.2.2.2)
  report := report.push s!"review: {depth1.size} definitions at depth 1, {depth2.size} at depth 2, {omitted.size} omitted"
  let mut noTemplate : NameSet := {}
  let mut omits : NameSet := {}
  let mut noSingular : NameSet := {}
  let mut used : Std.HashSet (Name × Gloss.Which) := {}
  let ileanPath : System.FilePath := ".lake/build/lib/lean/Mise/Headline.ilean"
  let ilean ← match Json.parse (← IO.FS.readFile ileanPath) with
    | .ok j => pure j
    | .error e => throwError s!"{ileanPath}: {e}"
  typ := typ ++ "= Core theorems\n\n"
  for t in core do
    let (m, _, a, b) ← location t
    let (ls, files') ← readLines m files
    files := files'
    let whole := slice ls a b
    let body := dropDoc whole
    let src := statementText body
    -- Offsets count characters; the index counts UTF-16 units, which agree
    -- while the file has no character outside the Basic Multilingual Plane.
    if ls.any (·.toList.any (·.toNat > 0xFFFF)) then
      throwError s!"{m}: a character outside the BMP breaks the link positions"
    let lineStart := ls.foldl (fun acc l => acc.push (acc.back! + l.length + 1)) #[0]
    let offset (l c : Nat) := lineStart[l]! + c
    let start := offset (a.line - 1) a.column + (whole.length - body.length)
    let us ← match usagesIn ilean t with
      | .ok us => pure us
      | .error e => throwError s!"{ileanPath}: {e}"
    let target (n : Name) := let o := owner env n; if shown.contains o then some o else none
    let parts ← match linkedParts src start offset us target with
      | .ok p => pure p
      | .error e => throwError s!"{t}: {e}"
    let doc := reviewDoc ((← liftCoreM (findDocString? env t)).getD "")
    let ty := (env.find? t).get!.type
    let (st, s) ← liftTermElabM (Gloss.statement ty |>.run {})
    noTemplate := s.missing.foldl (·.insert ·) noTemplate
    omits := s.omits.foldl (·.insert ·) omits
    noSingular := s.noSingular.foldl (·.insert ·) noSingular
    used := s.used.fold (·.insert ·) used
    let ph := tPhrase (fun n => let o := owner env n; if shown.contains o then some o else none)
    typ := typ ++ s!"#theorem-heading({tq (shortThm t)}, {tq (modPath m)}, {a.line}, {sourceUrl (modPath m) a.line b.line})\n\n"
    typ := typ ++ mdBlocks doc ++ s!"\n#lean-linked({parts})\n\n#english[\n"
    -- The variables on one line; their types come at their first mention.
    let has := st.has.toList.map fun (v, ps) =>
      Gloss.code v ++ Gloss.txt " has " ++ Gloss.joinWith ", " " and " (ps.toList.map Gloss.txt)
    let forAll := Gloss.txt "For all " ++ Gloss.joinWith ", " " and " (st.vars.toList.map Gloss.code) ++
      (if has.isEmpty then #[] else Gloss.txt ", where " ++ Gloss.joinWith ", " " and " has) ++
      Gloss.txt "."
    if !st.vars.isEmpty then typ := typ ++ "#line-par[" ++ ph forAll ++ "]\n"
    if !st.defs.isEmpty then
      let ds := st.defs.toList.map fun (n, p) => Gloss.code n ++ Gloss.txt " for " ++ p
      typ := typ ++ "#line-par[" ++ ph (Gloss.txt "Write " ++ Gloss.joinWith ", " ", and " ds ++ Gloss.txt ".") ++ "]\n"
    if !st.hyps.isEmpty then
      typ := typ ++ "#part-sub[Assume]\n"
      for (h, p) in st.hyps do
        let tag := match h with
          | some h => Gloss.txt "(" ++ Gloss.code h ++ Gloss.txt ") "
          | none => #[]
        typ := typ ++ "- " ++ ph (tag ++ p ++ Gloss.txt ".") ++ "\n"
    typ := typ ++ "#part-sub[Then]\n"
    for p in st.conclude do
      typ := typ ++ "- " ++ ph (p ++ Gloss.txt ".") ++ "\n"
    typ := typ ++ "]\n\n"
  -- Definitions, in reading order.
  typ := typ ++ "= Definitions\n\n#defs-intro\n\n"
  for m in mods do
    let here := sorted.filter fun (m', _, _, d) => m' == m && shown.contains d
    if here.isEmpty then continue
    typ := typ ++ s!"#file-heading({tq (modPath m)})\n\n"
    for (_, _, _, d) in here do
      let (_, _, a, b) ← location d
      let (ls, files') ← readLines m files
      files := files'
      let src := dropDoc (slice ls a b)
      let doc := (← liftCoreM (findDocString? env d)).getD ""
      let g := Gloss.Glosses.parse doc
      -- Only the templates the English of a core theorem uses: the others
      -- would repeat the docstring with nothing to check them against.
      let gl := [(Gloss.Which.main, g.main), (.fst, g.fst), (.snd, g.snd), (.fn, g.fn),
        (.one, g.one)].filterMap fun (w, t?) =>
          if used.contains (d, w) then t?.map fun t => s!"({tq w.key}, {tq t})" else none
      typ := typ ++ s!"#def-head({tq (short d)}, {defLabel d}, {tq (modPath m)}, {a.line}, {b.line}, {sourceUrl (modPath m) a.line b.line}, ({", ".intercalate gl}{if gl.length == 1 then "," else ""}))[\n"
      typ := typ ++ (if g.rest.isEmpty then "#no-doc\n" else mdBlocks g.rest) ++ "]\n"
      typ := typ ++ s!"#raw(lang: \"lean\", block: true, {tq src})\n\n"
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
