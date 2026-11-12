/-!
# Glob patterns for `source-globs`

A pattern is a relative path whose components may use `*` (any run of
characters, `/` excluded), `?` (one character) and the whole component
`**` (zero or more directories). A wildcard does not match a leading `.`,
so hidden files and directories need a component that starts with `.`.

`expand` lists the files a pattern matches under a directory, reading only
the directories the pattern can reach. It is outside the proofs: the paths
it returns are declared with `source`, and the graph they end up in must
pass `Graph.check` like any other.
-/

namespace Mise.Frontend.Glob

/-- Whether one component matches a component pattern of `*` and `?`. -/
partial def matchSeg : List Char → List Char → Bool
  | [], [] => true
  | '*' :: ps, cs => matchSeg ps cs || match cs with
    | _ :: cs' => matchSeg ('*' :: ps) cs'
    | [] => false
  | '?' :: ps, _ :: cs => matchSeg ps cs
  | p :: ps, c :: cs => p == c && matchSeg ps cs
  | _, _ => false

/-- Whether a file or directory name matches a component pattern. A name
that starts with `.` matches only a pattern that starts with `.`. -/
def matchName (pat name : String) : Bool :=
  (!name.startsWith "." || pat.startsWith ".") && matchSeg pat.toList name.toList

/-- Whether a component pattern has a wildcard. -/
def isWild (c : String) : Bool := c.any fun ch => ch == '*' || ch == '?'

/-- Check a pattern and split it into components. -/
def components (pat : String) : Except String (List String) := do
  if pat.isEmpty then throw "empty pattern"
  if pat.startsWith "/" then throw s!"{repr pat}: must be relative"
  let cs := pat.splitOn "/"
  for c in cs do
    if c.isEmpty then throw s!"{repr pat}: empty component"
    if c == "." || c == ".." then throw s!"{repr pat}: no . or .. components"
    if c != "**" && (c.splitOn "**").length > 1 then throw s!"{repr pat}: ** must be a whole component"
    if c.any (· == '\\') then throw s!"{repr pat}: no backslashes"
  if cs.getLast? == some "**" then throw s!"{repr pat}: must not end in **"
  pure cs

/-- Whether a relative path matches a pattern's components. -/
partial def matchComps : List String → List String → Bool
  | [], [] => true
  | "**" :: ps, ns => matchComps ps ns || match ns with
    | n :: ns' => !n.startsWith "." && matchComps ("**" :: ps) ns'
    | [] => false
  | p :: ps, n :: ns => matchName p n && matchComps ps ns
  | _, _ => false

/-- Whether a relative path matches a pattern. -/
def «matches» (pat path : String) : Bool :=
  match components pat with
  | .ok cs => matchComps cs (path.splitOn "/")
  | .error _ => false

/-- The files under `root` that a pattern matches, as paths relative to
`root` joined with `/`, sorted and without repeats. A symbolic link to a
file counts as a file; `**` does not descend into a symbolic link to a
directory, so a link cycle cannot make it loop. -/
partial def expand (root : System.FilePath) (pat : String) : IO (List String) := do
  let cs ← IO.ofExcept ((components pat).mapError IO.userError)
  let out ← go cs [] (pure #[])
  pure ((out.qsort (· < ·)).toList.foldr (fun p acc => if acc.head? == some p then acc else p :: acc) [])
where
  dirOf (rel : List String) : System.FilePath := rel.foldl (fun (d : System.FilePath) (c : String) => d / c) root
  join (rel : List String) : String := "/".intercalate rel
  realDir (p : System.FilePath) : IO Bool := do
    match ← (p.symlinkMetadata.toBaseIO) with
    | .ok m => pure (m.type == .dir)
    | .error _ => pure false
  entries (rel : List String) : IO (Array String) := do
    let d := dirOf rel
    if !(← d.isDir) then return #[]
    let es ← d.readDir
    pure (es.map (·.fileName))
  go : List String → List String → IO (Array String) → IO (Array String)
    | [], rel, acc => do
      let p := dirOf rel
      if (← p.pathExists) && !(← p.isDir) then pure ((← acc).push (join rel)) else acc
    | "**" :: cs, rel, acc => do
      let acc ← go cs rel acc
      let mut acc := acc
      for n in ← entries rel do
        if !n.startsWith "." && (← realDir (dirOf (rel ++ [n]))) then
          acc ← go ("**" :: cs) (rel ++ [n]) (pure acc)
      pure acc
    | c :: cs, rel, acc => do
      if !isWild c then go cs (rel ++ [c]) acc
      else
        let mut acc ← acc
        for n in ← entries rel do
          if matchName c n then acc ← go cs (rel ++ [n]) (pure acc)
        pure acc

end Mise.Frontend.Glob
