import Lean
open Lean Meta

/-!
The walk over trusted definitions, shared by `MiseTest.Trusted` (which lists
them) and `MiseTest.MutantGen` (which mutates them). It needs only `Lean`, so
a change to `Mise` does not rebuild it.

The walk starts from a set of constants and follows every `Mise` constant
they mention, through the types and bodies of definitions and the
constructors of inductive types. It does not enter theorems, because Lean
checks their proofs; proofs inside a definition are abstracted into
auxiliary theorems when the definition is compiled, so it skips those too.
It stops at the implementation definitions in `implementation`, which the
theorems constrain. Constants outside `Mise` (Lean's core library) are not
followed.
-/

namespace Trusted

def isMise (n : Name) : Bool := n.getRoot == `Mise

/-- Definitions a reader need not check, with the reason. A statement may
name them, but the walk does not enter them. -/
def implementation : List (Name × String) :=
  [(`Mise.Frontend.emit, "The theorems hold for whatever manifest `emit g` is. The text `mise` writes is `print (emit g)` (`ValidGraph.ninja`), and `well_formed` and trust item 1 say how Ninja reads it."),
   (`Mise.Frontend.Graph.Valid, "Every theorem assumes `g.Valid`, and `mise` refuses a graph that fails it (`Build.graph` returns a `ValidGraph`). A check that is too strict makes `mise` refuse more graphs, and cannot make a theorem false.")]

/-- Assumptions of `docs/theorems.md` that are stated in terms of definitions,
with the definitions they name. -/
def assumptions : List (String × List Name) :=
  [("trust item 1", [`Mise.Syntax.print, `Mise.Syntax.Manifest.WellFormed])]

def isImplementation (n : Name) : Bool := implementation.any (·.1 == n)

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
    if isImplementation (owner env n) then continue
    todo := todo ++ next env n
  return seen

/-- The trusted declarations reachable from `start`, by owner. A matcher is
looked through, since Lean shares one matcher among definitions that match
the same way, and its owner may be any of them. -/
def trustedFrom (env : Environment) (start : Array Name) : NameSet :=
  (reach env start).foldl (fun s n =>
    match env.find? n with
    | some (.thmInfo _) => s
    | _ =>
      if isGenerated n || isMatcherCore env n || isImplementation (owner env n) then s
      else s.insert (owner env n)) {}

/-- The trusted declarations of theorem `thm`, by owner. -/
def trustedOf (env : Environment) (thm : Name) : NameSet :=
  match env.find? thm with
  | some (.thmInfo t) => trustedFrom env t.type.getUsedConstants
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
    if isMatcherCore env n then todo := todo ++ next env n; continue
    let o := owner env n
    if o != d && trusted.contains o then out := out.insert o
    else if o == d || isAux env n then todo := todo ++ next env n
  return out

def sortNames (s : NameSet) : Array Name :=
  s.toArray.qsort (fun a b => a.toString < b.toString)

end Trusted
