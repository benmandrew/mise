import Lean

/-! Triage of the mutants that survive `test/trust-mutants.py`.

`lake env lean --run test/MiseTest/MutantCheck.lean IN OUT`, in the prepared
copy, reads a JSON array of mutants (`{name, file, start, stop, text}`: the
bytes `start`–`stop` of `file` become `text`) and appends one JSON line per
mutant to `OUT` as it finishes.

For each file, it elaborates the file again, one command at a time. At the
command that a mutant edits, which declares `D`, it elaborates the edited
command once more with `D` renamed to `D_mutant`, so that both are in one
environment, and then

1. evaluates `D` and `D_mutant` on random arguments. The first arguments on
   which they differ are a witness, shrunk while they still differ, which
   becomes a test that kills the mutant: `D` on them gives the original's
   result. The arguments are built from their types: a structure or an
   inductive from a random constructor, a function as a finite table, a
   type parameter as `Nat`. A value drawn for a type is reused for later
   values of that type in the same sample, so that two arguments are often
   equal. Strings and characters are drawn from the literals in the file
   and a few characters of Ninja's syntax. The drawing and the comparison
   run as compiled code (see "The runtime" below), at about 30 µs a sample.
2. when no witness turns up, tries to prove `∀ xs, D xs = D_mutant xs`
   (`↔` for a proposition) with a few tactic scripts. A proof makes the
   mutant equivalent. Library theorems have no proofs in the copy, so a proof
   may use Lean's own theorems and the equation lemmas of definitions, and
   not a theorem of `Mise`.

The verdict is `distinguished` (with `test`), `equivalent` (with the
tactic), or `undecided` (with why). -/

open Lean Meta Elab

namespace MutantCheck

structure Mutant where
  name : String
  file : String
  start : Nat
  stop : Nat
  text : String
  deriving FromJson

structure Result where
  name : String
  verdict : String
  decl : String := ""
  /-- The witness, the tactic, or why neither was found. -/
  detail : String := ""
  /-- A test that kills a distinguished mutant. -/
  test : String := ""
  /-- The random samples evaluated. -/
  samples : Nat := 0
  deriving ToJson

/-- The heartbeats (in thousands) of one proof attempt. -/
def proofHeartbeats : Nat := 100000

/-! ## Comparing `D` and `D_mutant` -/

/-- `decide (lhs = rhs)`, or `decide (lhs ↔ rhs)` for propositions, unfolding
each side once when that is what makes it decidable. -/
def compare (lhs rhs : Expr) : MetaM Expr := do
  let ty ← inferType lhs
  if ← isProp ty then
    try mkDecide (mkIff lhs rhs)
    catch _ =>
      let some l ← unfoldDefinition? lhs | throwError "cannot decide {lhs}"
      let some r ← unfoldDefinition? rhs | throwError "cannot decide {rhs}"
      mkDecide (mkIff l r)
  else
    try mkDecide (← mkEq lhs rhs)
    catch _ => mkAppM ``BEq.beq #[lhs, rhs]

/-- Evaluate a list of `Bool` terms. Compiling a large term can take more
than the default heartbeats, so there is no limit. -/
unsafe def evalBools (bs : Array Expr) : MetaM (List Bool) := do
  let e ← mkListLit (mkConst ``Bool) bs.toList
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
    evalExpr (List Bool) (← mkAppM ``List #[mkConst ``Bool]) e (checkMeta := false)

unsafe def evalNat (e : Expr) : MetaM Nat :=
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
    evalExpr Nat (mkConst ``Nat) e (checkMeta := false)

unsafe def evalString (e : Expr) : MetaM String :=
  withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) do
    evalExpr String (mkConst ``String) e (checkMeta := false)

/-- The value of `e` as text, when its type has a `Repr` instance. -/
unsafe def showValue (e : Expr) : MetaM (Option String) := do
  if ← isProp (← inferType e) then
    let b ← evalBools #[← mkDecide e]
    return some (toString b[0]!)
  try return some (← evalString (← mkAppM ``reprStr #[e]))
  catch _ => return none

/-- `e` as a test can write it: names from the root namespace, no field
notation, proofs shown. -/
def ppTest (e : Expr) : MetaM String :=
  withTheReader Core.Context (fun c => { c with currNamespace := .anonymous, openDecls := [] }) do
  withOptions (fun o => o.setBool `pp.fieldNotation false |>.setBool `pp.proofs true
    |>.setBool `pp.funBinderTypes true |>.setBool `pp.analyze true) do
    return toString (← ppExpr e)

/-- A test that `lhs` has the value it has. -/
unsafe def testOf (lhs : Expr) : MetaM String := do
  let call ← ppTest lhs
  let ty ← whnf (← inferType lhs)
  if ← isProp (← inferType lhs) then
    let b := (← evalBools #[← mkDecide lhs])[0]!
    return if b then s!"example : {call} := by decide" else s!"example : ¬ ({call}) := by decide"
  if ty.isConstOf ``Bool then
    let b := (← evalBools #[lhs])[0]!
    return if b then s!"#guard {call}" else s!"#guard !({call})"
  match ← showValue lhs with
  | some v => return s!"#guard {call} == {v}"
  | none => return s!"-- {call} differs; its type has no `Repr` instance"

/-! ## The runtime

Evaluating a term means compiling it first, and compiling 150 random
arguments as literals takes seconds. So the samples are drawn and evaluated
by compiled code: `prelude` below, which the checker elaborates once into
each file's environment, and a decoder per argument type, which it compiles
once per mutant. A sample is a tree of `V`s, drawn by `MutantCheckRt.gen`
from a table of `Sch`s that describes the argument types; the decoders turn
it into values of those types, and `chk` compares `D` and `D_mutant` on
them. A witness comes back as `V`s, which `decode` turns into terms.

`V` and `Sch` are declared twice, in `prelude` and here, and must stay the
same: the checker passes values between the two by their memory layout. -/

def prelude : String := r#"
namespace MutantCheckRt

/-- A value of any argument type: its decoder knows the type. -/
inductive V where
  | nat (n : Nat)
  | char (c : Char)
  | str (s : String)
  | list (xs : Array V)
  | fn (dflt : V) (tbl : Array (V × V))
  | ctor (i : Nat) (fs : Array V)
  | dflt

instance : Inhabited V := ⟨.dflt⟩

/-- The shape of an argument type; a field or element names its type by its
index in the table. A constructor lists whether it is recursive, and its
fields with whether each has a default value. -/
inductive Sch where
  | nat
  | char
  | str
  | list (t : Nat)
  | fn (dom cod : Nat)
  | ind (recursive : Bool) (ctors : Array (Bool × Array (Nat × Bool)))

instance : Inhabited Sch := ⟨.nat⟩

structure S where
  gen : StdGen
  /-- The values drawn so far in this sample, by type. -/
  pool : Array (Array V)

abbrev G := StateM S

def rand (n : Nat) : G Nat := do
  if n ≤ 1 then return 0
  let s ← get
  let (k, g) := randNat s.gen 0 (n - 1)
  set { s with gen := g }
  return k

def pick {α : Type} [Inhabited α] (xs : Array α) : G α := do
  return xs[← rand xs.size]!

def genStr (strs : Array String) (chars : Array Char) (size : Nat) : G V := do
  if (← rand 3) == 0 && !strs.isEmpty then return .str (← pick strs)
  let n ← rand (size + 3)
  let mut out := String.ofList []
  -- Mostly letters, which most checks of names and paths accept.
  for _ in [0:n] do
    let c ← if (← rand 3) == 0 then pick chars else pick #['a', 'b', 'c']
    out := out.push c
  return .str out

mutual

/-- A random value of type `t`. One time in three it is a value drawn before
for that type, so that two arguments are often equal. -/
partial def gen (sch : Array Sch) (strs : Array String) (chars : Array Char) (t size depth : Nat) : G V := do
  if depth > 40 then return .dflt
  let pool := (← get).pool.getD t #[]
  if !pool.isEmpty && (← rand 3) == 0 then return ← pick pool
  let v ← genNew sch strs chars t size depth
  modify fun s => { s with pool := s.pool.modify t (·.push v) }
  return v

partial def genNew (sch : Array Sch) (strs : Array String) (chars : Array Char) (t size depth : Nat) : G V := do
  match sch.getD t .nat with
  | .nat => return .nat (← rand (if size == 0 then 3 else 6))
  | .char => return .char (← pick chars)
  | .str => genStr strs chars size
  | .list e =>
    let n ← rand (if size == 0 then 2 else 4)
    let mut xs := #[]
    for _ in [0:n] do xs := xs.push (← gen sch strs chars e (size - 1) (depth + 1))
    return .list xs
  | .fn a b =>
    -- A finite table over a default.
    let d ← gen sch strs chars b size (depth + 1)
    let mut tbl := #[]
    for _ in [0:(← rand 3)] do
      let x ← gen sch strs chars a size (depth + 1)
      let y ← gen sch strs chars b size (depth + 1)
      tbl := tbl.push (x, y)
    return .fn d tbl
  | .ind recursive cs =>
    if cs.isEmpty then return .dflt
    -- A random constructor; at size 0, one that is not recursive if any.
    let k ← rand cs.size
    let order := (List.range cs.size).map fun i => (i + k) % cs.size
    let i := if size == 0 then (order.find? fun i => !(cs[i]!).1).getD k else k
    let sz := if recursive then size - 1 else size
    let mut fs := #[]
    for (ft, hasDflt) in (cs[i]!).2 do
      -- A field with a default takes it half the time.
      if hasDflt && (← rand 2) == 0 then fs := fs.push .dflt
      else fs := fs.push (← gen sch strs chars ft sz (depth + 1))
    return .ctor i fs

end

/-- Draw `samples` samples of the argument types `args`, at sizes from 0 to
4, until `chk` finds one on which `D` and `D_mutant` differ: the samples
drawn, those that some type's condition rejected, and the witness. -/
def search (chk : Array V → Option Bool) (sch : Array Sch) (args : Array Nat) (strs : Array String)
    (chars : Array Char) (seed samples : Nat) : Nat × Nat × Option (Array V) := Id.run do
  let mut s : S := { gen := mkStdGen seed, pool := #[] }
  let mut rejected := 0
  let n := if args.isEmpty then 1 else samples
  for i in [0:n] do
    s := { s with pool := Array.replicate sch.size #[] }
    let (vs, s') := Id.run ((args.mapM fun t => gen sch strs chars t (i * 5 / samples) 0).run s)
    s := s'
    match chk vs with
    | none => rejected := rejected + 1
    | some true => pure ()
    | some false => return (i + 1, rejected, some vs)
  return (n, rejected, none)

def decNat : V → Option Nat
  | .nat n => some n
  | _ => none

def decChar : V → Option Char
  | .char c => some c
  | _ => none

def decStr : V → Option String
  | .str s => some s
  | _ => none

def decList {α : Type} (d : V → Option α) : V → Option (List α)
  | .list xs => xs.toList.mapM d
  | _ => none

def decArray {α : Type} (d : V → Option α) : V → Option (Array α)
  | .list xs => xs.mapM d
  | _ => none

/-- `fun x => if x = a₀ then b₀ else if x = a₁ then b₁ else … d`. -/
def decFn {α β : Type} [DecidableEq α] (da : V → Option α) (db : V → Option β) : V → Option (α → β)
  | .fn d tbl => do
    let d ← db d
    let tbl ← tbl.toList.mapM fun p => do return (← da p.1, ← db p.2)
    return fun x => tbl.foldr (fun p r => if x = p.1 then p.2 else r) d
  | _ => none

/-- `fun _ => d`, for a domain without `DecidableEq`. -/
def decConst {α β : Type} (db : V → Option β) : V → Option (α → β)
  | .fn d _ => do
    let d ← db d
    return fun _ => d
  | _ => none

def ctorOf : V → Option (Nat × Array V)
  | .ctor i fs => some (i, fs)
  | _ => none

def field (fs : Array V) (j : Nat) : V := fs.getD j .dflt

def withDflt {α : Type} (d : V → Option α) (x : α) : V → Option α
  | .dflt => some x
  | v => d v

end MutantCheckRt
"#

/-- `MutantCheckRt.V`, with the same layout. -/
inductive V where
  | nat (n : Nat)
  | char (c : Char)
  | str (s : String)
  | list (xs : Array V)
  | fn (dflt : V) (tbl : Array (V × V))
  | ctor (i : Nat) (fs : Array V)
  | dflt
  deriving BEq, Hashable

instance : Inhabited V := ⟨.dflt⟩

/-- `MutantCheckRt.Sch`, with the same layout. -/
inductive Sch where
  | nat
  | char
  | str
  | list (t : Nat)
  | fn (dom cod : Nat)
  | ind (recursive : Bool) (ctors : Array (Bool × Array (Nat × Bool)))

instance : Inhabited Sch := ⟨.nat⟩

def rt (n : Name) : Name := `MutantCheckRt ++ n
def vTy : Expr := mkConst (rt `V)
def arrayV : Expr := mkApp (mkConst ``Array [0]) vTy
def optTy (t : Expr) : Expr := mkApp (mkConst ``Option [0]) t
def mkSomeE (t v : Expr) : Expr := mkApp2 (mkConst ``Option.some [0]) t v
def mkNoneE (t : Expr) : Expr := mkApp (mkConst ``Option.none [0]) t
def mkBindE (a b x f : Expr) : Expr := mkAppN (mkConst ``Option.bind [0, 0]) #[a, b, x, f]
def mkFieldE (fs : Expr) (j : Nat) : Expr := mkApp2 (mkConst (rt `field)) fs (mkRawNatLit j)

def mkCharLit (c : Char) : Expr := mkApp (mkConst ``Char.ofNat) (mkRawNatLit c.toNat)

/-! ## Building the decoders -/

/-- How a constructor's field gets its value. -/
inductive FieldKind where
  | inst
  | prop
  /-- From the sample, or from the field's default value when it has one. -/
  | data (dflt : Option Expr)

/-- The kind of field `idx` of a constructor of `induct`, of type `dom`. -/
def fieldKind (induct : Name) (us : List Level) (params : Array Expr) (idx : Nat) (dom : Expr)
    (bi : BinderInfo) : MetaM FieldKind := do
  if bi.isInstImplicit then return .inst
  if ← isProp dom then return .prop
  let env ← getEnv
  let names := if isStructure env induct then getStructureFields env induct else #[]
  let some fn := names[idx]? >>= (getDefaultFnForField? env induct ·) | return .data none
  let d := mkAppN (mkConst fn us) params
  -- A default that depends on other fields is left out.
  if (← whnf (← inferType d)).isForall then return .data none
  let some d ← unfoldDefinition? d | return .data none
  let d := d.headBeta
  return .data (some (if d.isAppOfArity ``id 2 then d.appArg! else d))

/-- An argument type: its shape, and for an inductive the constructors the
shape lists, for a function type whether its domain has `DecidableEq`. -/
structure TInfo where
  ty : Expr
  sch : Sch := .nat
  ctors : Array Name := #[]
  eq : Bool := false
  deriving Inhabited

structure BState where
  pre : Name
  infos : Array TInfo := #[]
  ids : Std.HashMap Expr Nat := {}
  failed : Std.HashMap Expr String := {}
  /-- The decoder of each type, `V → Option ty`. -/
  bodies : Array (Option Expr) := #[]

abbrev BM := StateRefT BState MetaM

def decConst (pre : Name) (k : Nat) : Expr := mkConst (pre ++ .mkSimple s!"dec{k}")

/-- Whether a field's type `dom` mentions one of the earlier fields `fvs`. -/
def dependsOn (dom : Expr) (fvs : Array Expr) : Bool :=
  dom.hasAnyFVar fun f => fvs.any (·.fvarId! == f)

mutual

/-- The type of `t`'s index in the table, built with its decoder. -/
partial def schemaOf (ty : Expr) : BM Nat := do
  let ty ← whnf (← instantiateMVars ty)
  if let some k := (← get).ids[ty]? then return k
  if let some e := (← get).failed[ty]? then throwError e
  let k := (← get).infos.size
  modify fun s => { s with ids := s.ids.insert ty k, infos := s.infos.push { ty }, bodies := s.bodies.push none }
  try
    let (info, body) ← schemaNew ty
    modify fun s => { s with infos := s.infos.set! k info, bodies := s.bodies.set! k (some body) }
    return k
  catch e =>
    let msg ← e.toMessageData.toString
    modify fun s => { s with ids := s.ids.erase ty, failed := s.failed.insert ty msg }
    throw e

partial def schemaNew (ty : Expr) : BM (TInfo × Expr) := do
  unless (← whnf (← inferType ty)) == mkSort Level.one do throwError "{ty} is not in `Type`"
  let pre := (← get).pre
  if ty.isForall then
    let .forallE _ dom cod _ := ty | unreachable!
    if cod.hasLooseBVars then throwError "no generator for the dependent function type {ty}"
    let a ← schemaOf dom
    let b ← schemaOf cod
    let inst ← try some <$> synthInstance (mkApp (mkConst ``DecidableEq [1]) dom) catch _ => pure none
    let body := match inst with
      | some i => mkAppN (mkConst (rt `decFn)) #[dom, cod, i, decConst pre a, decConst pre b]
      | none => mkAppN (mkConst (rt `decConst)) #[dom, cod, decConst pre b]
    return ({ ty, sch := .fn a b, eq := inst.isSome }, body)
  if ty.isConstOf ``Nat then return ({ ty, sch := .nat }, mkConst (rt `decNat))
  if ty.isConstOf ``Char then return ({ ty, sch := .char }, mkConst (rt `decChar))
  if ty.isConstOf ``String then return ({ ty, sch := .str }, mkConst (rt `decStr))
  if ty.isAppOfArity ``List 1 || ty.isAppOfArity ``Array 1 then
    let e ← schemaOf ty.appArg!
    let f := if ty.isAppOfArity ``List 1 then `decList else `decArray
    return ({ ty, sch := .list e }, mkApp2 (mkConst (rt f)) ty.appArg! (decConst pre e))
  let .const c us := ty.getAppFn | throwError "no generator for {ty}"
  let some (.inductInfo iv) := (← getEnv).find? c | throwError "no generator for {ty}"
  if iv.numIndices > 0 || iv.isUnsafe then throwError "no generator for the indexed family {ty}"
  let params := ty.getAppArgs.extract 0 iv.numParams
  let mut ctors := #[]
  let mut shapes := #[]
  let mut chains := #[]
  let mut err := m!"no constructor of {ty} could be built"
  for cn in iv.ctors do
    let ci ← getConstInfoCtor cn
    try
      let t ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams us) params
      let rec' ← forallTelescopeReducing t fun xs _ =>
        xs.anyM fun x => return ((← inferType x).find? (·.isConstOf c)).isSome
      let (chain, fl) ← withLocalDeclD `fs arrayV fun fs => do
        let (e, fl) ← ctorChain cn us params fs ty t #[] #[] 0
        return (← mkLambdaFVars #[fs] e, fl)
      ctors := ctors.push cn
      shapes := shapes.push (rec', fl)
      chains := chains.push chain
    catch e => err := e.toMessageData
  if ctors.isEmpty then throwError err
  -- `fun v => (ctorOf v).bind fun p => if p.1 = 0 then chain₀ p.2 else …`
  let pTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat) arrayV
  let body ← withLocalDeclD `v vTy fun v => withLocalDeclD `p pTy fun p => do
    let p1 := mkApp3 (mkConst ``Prod.fst [0, 0]) (mkConst ``Nat) arrayV p
    let p2 := mkApp3 (mkConst ``Prod.snd [0, 0]) (mkConst ``Nat) arrayV p
    let mut r := mkNoneE ty
    for i in (List.range chains.size).reverse do
      let c := mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) p1 (mkRawNatLit i)
      let inst := mkApp2 (mkConst ``instDecidableEqNat) p1 (mkRawNatLit i)
      r := mkAppN (mkConst ``ite [1]) #[optTy ty, c, inst, (chains[i]!).beta #[p2], r]
    let f ← mkLambdaFVars #[p] r
    mkLambdaFVars #[v] (mkBindE pTy ty (mkApp (mkConst (rt `ctorOf)) v) f)
  return ({ ty, sch := .ind iv.isRec shapes, ctors }, body)

/-- The decoder of constructor `ctor`'s fields from the array `fs`, as a term
of type `Option ty`, and the shape of those fields. `t` is the rest of the
constructor's type, `vals` the fields so far and `fvs` those that are local. -/
partial def ctorChain (ctor : Name) (us : List Level) (params : Array Expr) (fs ty t : Expr)
    (vals fvs : Array Expr) (j : Nat) : BM (Expr × Array (Nat × Bool)) := do
  let .forallE n dom body bi ← whnf t
    | return (mkSomeE ty (mkAppN (mkConst ctor us) (params ++ vals)), #[])
  let dom := dom.consumeTypeAnnotations
  let induct := (← getConstInfoCtor ctor).induct
  match ← fieldKind induct us params vals.size dom bi with
  | .inst =>
    let v ← synthInstance dom
    ctorChain ctor us params fs ty (body.instantiate1 v) (vals.push v) fvs j
  | .prop =>
    -- `if h : p then rest else none`: a sample whose condition fails is rejected.
    let inst ← try synthInstance (mkApp (mkConst ``Decidable) dom)
      catch _ => throwError "cannot decide the condition {dom} of {ctor}"
    withLocalDeclD `h dom fun h => do
      let (rest, fl) ← ctorChain ctor us params fs ty (body.instantiate1 h) (vals.push h) (fvs.push h) j
      let e := mkAppN (mkConst ``dite [1]) #[optTy ty, dom, inst, ← mkLambdaFVars #[h] rest,
        .lam `h (mkNot dom) (mkNoneE ty) .default]
      return (e, fl)
  | .data dflt =>
    if dependsOn dom fvs then throwError "the type {dom} of a field of {ctor} depends on another field"
    let k ← schemaOf dom
    let pre := (← get).pre
    withLocalDeclD n dom fun x => do
      let (rest, fl) ← ctorChain ctor us params fs ty (body.instantiate1 x) (vals.push x) (fvs.push x) (j + 1)
      let dec := match dflt with
        | some d => mkAppN (mkConst (rt `withDflt)) #[dom, decConst pre k, d]
        | none => decConst pre k
      let e := mkBindE dom ty (mkApp dec (mkFieldE fs j)) (← mkLambdaFVars #[x] rest)
      return (e, #[(k, dflt.isSome)] ++ fl)

end

/-- A `Bool` term that compares `a` and `b` by an equality their type
decides, or none when it has none. -/
def leafCmp? (a b : Expr) : MetaM (Option Expr) := do
  if ← isProp (← inferType a) then return some (← compare a b)
  try return some (← mkDecide (← mkEq a b)) catch _ => pure ()
  try return some (← mkAppM ``BEq.beq #[a, b]) catch _ => return none

/-- How to compare two values whose type decides no equality: a function
on a sampled point, a structure field by field. -/
inductive Split where
  | point (dom : Expr)
  | fields (projs : Array (Expr → MetaM Expr))
  | list (elem : Expr)

def split? (a : Expr) : MetaM (Option Split) := do
  let ty ← whnf (← inferType a)
  if let .forallE _ dom cod _ := ty then
    return if cod.hasLooseBVars then none else some (.point dom)
  if ty.isAppOfArity ``List 1 then return some (.list ty.appArg!)
  let .const c _ := ty.getAppFn | return none
  let env ← getEnv
  unless isStructure env c do return none
  let mut projs := #[]
  for f in getStructureFields env c do
    let pa ← mkProjection a f
    let fty ← inferType pa
    -- Proofs are equal, and instances are not data.
    if ← isProp fty then continue
    if (← isClass? fty).isSome then continue
    projs := projs.push fun x => mkProjection x f
  return some (.fields projs)

/-- The comparison of the pairs `ps`, in order, as a term of type
`Option Bool`: the conjunction of the comparisons `acc` so far and of the
pairs, with the points that a function's comparison draws from `vs`. -/
partial def cmpChain (vs : Expr) (ps : List (Expr × Expr)) (tids : Array Nat) (acc : Array Expr) :
    BM (Expr × Array Nat) := do
  match ps with
  | [] =>
    let all := acc.foldl (fun x y => mkApp2 (mkConst ``and) x y) (mkConst ``Bool.true)
    return (mkSomeE (mkConst ``Bool) all, tids)
  | (a, b) :: rest =>
    if let some c ← leafCmp? a b then return ← cmpChain vs rest tids (acc.push c)
    match ← split? a with
    | some (.point dom) =>
      let k ← schemaOf dom
      let pre := (← get).pre
      withLocalDeclD `x dom fun x => do
        let (e, tids') ← cmpChain vs ((mkApp a x, mkApp b x) :: rest) (tids.push k) acc
        return (mkBindE dom (mkConst ``Bool) (mkApp (decConst pre k) (mkFieldE vs tids.size)) (← mkLambdaFVars #[x] e), tids')
    | some (.fields projs) =>
      let ps' ← projs.toList.mapM fun f => return (← f a, ← f b)
      cmpChain vs (ps' ++ rest) tids acc
    | some (.list elem) =>
      -- `List.isEqv a b fun x y => …`, with no points to draw.
      let f ← withLocalDeclD `x elem fun x => withLocalDeclD `y elem fun y => do
        let (e, tids') ← cmpChain vs [(x, y)] tids #[]
        if tids'.size != tids.size then throwError "cannot compare lists of functions"
        mkLambdaFVars #[x, y] e.appArg!
      let c := mkApp4 (mkConst ``List.isEqv [0]) elem a b f
      cmpChain vs rest tids (acc.push c)
    | none => throwError "cannot compare values of type {← inferType a}"

/-- Whether `dom`, the type of an argument, is a type former. -/
def isTypeFormer (dom : Expr) : MetaM Bool := do
  let dom' ← whnf dom
  if !dom'.isForall then return false
  if !(← whnf (← inferType dom)).isSort then return false
  forallTelescope dom' fun _ r => return r.isSort

/-- `chk`'s body: decode the arguments of `D` from `vs`, as `D`'s type `t`
asks for them, and compare `D` and `D'` on them. Also the type of each
argument drawn from the sample. -/
partial def chkChain (D D' : Name) (us : List Level) (vs t : Expr) (args fvs : Array Expr) (tids : Array Nat) :
    BM (Expr × Array Nat) := do
  let .forallE n dom body bi ← whnf t |
    cmpChain vs [(mkAppN (mkConst D us) args, mkAppN (mkConst D' us) args)] tids #[]
  let dom' ← whnf dom
  if bi.isInstImplicit then
    let v ← synthInstance dom
    return ← chkChain D D' us vs (body.instantiate1 v) (args.push v) fvs tids
  if dom'.isSort then
    if dom'.isProp then throwError "takes a proposition as an argument"
    -- A type parameter is `Nat`.
    return ← chkChain D D' us vs (body.instantiate1 (mkConst ``Nat)) (args.push (mkConst ``Nat)) fvs tids
  if ← isProp dom then throwError "takes a proof of {dom}"
  if ← isTypeFormer dom then throwError "takes a type former"
  if dependsOn dom fvs then throwError "the type {dom} of an argument depends on another argument"
  let k ← schemaOf dom
  let pre := (← get).pre
  withLocalDeclD n dom fun x => do
    let (rest, tids') ← chkChain D D' us vs (body.instantiate1 x) (args.push x) (fvs.push x) (tids.push k)
    let e := mkBindE dom (mkConst ``Bool) (mkApp (decConst pre k) (mkFieldE vs tids.size)) (← mkLambdaFVars #[x] rest)
    return (e, tids')

/-- The compiled comparison of `D` and `D'`, the shapes of the argument
types, and the type of each argument the sample holds. -/
unsafe def build (D D' : Name) (pre : Name) : MetaM ((Array V → Option Bool) × Array TInfo × Array Nat) := do
  let info ← getConstInfo D
  let us := info.levelParams.map fun _ => Level.zero
  let ty := info.type.instantiateLevelParams info.levelParams us
  let ((chk, tids), st) ← (withLocalDeclD `vs arrayV fun vs => do
      let (e, tids) ← chkChain D D' us vs ty #[] #[] #[]
      return (← mkLambdaFVars #[vs] e, tids) : BM _).run { pre }
  let names := (List.range st.infos.size).map fun k => (decConst pre k).constName!
  if !names.isEmpty then
    let decls := (List.range st.infos.size).map fun k =>
      let ty := (st.infos[k]!).ty
      ({ name := names[k]!, levelParams := [], type := .forallE `v vTy (optTy ty) .default,
         value := (st.bodies[k]!).getD (.lam `v vTy (mkNoneE ty) .default),
         hints := .opaque, safety := .«unsafe», all := names } : DefinitionVal)
    addDecl (.mutualDefnDecl decls)
    compileDecls names.toArray
  let chkName := pre ++ `chk
  let chkTy := Expr.forallE `vs arrayV (optTy (mkConst ``Bool)) .default
  let chkDecl : DefinitionVal :=
    { name := chkName, levelParams := [], type := chkTy, value := chk
      hints := .opaque, safety := .«unsafe», all := [chkName] }
  addDecl (.defnDecl chkDecl)
  compileDecls #[chkName]
  let f ← IO.ofExcept <| (← getEnv).evalConst (Array V → Option Bool) (← getOptions) chkName (checkMeta := false)
  return (f, st.infos, tids)

/-! ## Decoding a witness -/

/-- A proof of the closed proposition `p` by `decide`, when it holds. -/
def decideProof (p : Expr) : MetaM Expr := do
  let r ← withTransparency .all (whnf (← mkDecide p))
  unless r.isConstOf ``Bool.true do throwError "the proposition {p} does not hold"
  mkDecideProof p

/-- The term of type `infos[k]` that `v` describes, as its decoder reads it. -/
partial def decode (infos : Array TInfo) (k : Nat) (v : V) : MetaM Expr := do
  let info := infos[k]!
  match info.sch, v with
  | .nat, .nat n => return mkNatLit n
  | .char, .char c => return mkCharLit c
  | .str, .str s => return mkStrLit s
  | .list e, .list xs =>
    let xs ← xs.mapM (decode infos e)
    if info.ty.isAppOfArity ``List 1 then mkListLit info.ty.appArg! xs.toList
    else mkArrayLit info.ty.appArg! xs.toList
  | .fn a b, .fn d tbl =>
    let .forallE n dom cod _ := info.ty | throwError "not a function type"
    let d ← decode infos b d
    if !info.eq || tbl.isEmpty then return .lam `_ dom d .default
    let tbl ← tbl.mapM fun (x, y) => return (← decode infos a x, ← decode infos b y)
    withLocalDeclD n dom fun x => do
      let mut r := d
      for (a, b) in tbl.reverse do r ← mkAppOptM ``ite #[cod, ← mkEq x a, none, b, r]
      mkLambdaFVars #[x] r
  | .ind _ shapes, .ctor i fs =>
    let ctor := info.ctors[i]!
    let .const _ us := info.ty.getAppFn | throwError "not an inductive"
    let ci ← getConstInfoCtor ctor
    let params := info.ty.getAppArgs.extract 0 ci.numParams
    let mut t ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams us) params
    let mut vals := #[]
    let mut j := 0
    while true do
      let .forallE _ dom body bi ← whnf t | break
      let dom := dom.consumeTypeAnnotations
      let x ← match ← fieldKind ci.induct us params vals.size dom bi with
        | .inst => synthInstance dom
        | .prop => decideProof dom
        | .data dflt =>
          let f := fs.getD j .dflt
          let k' := (shapes[i]!).2[j]!.1
          j := j + 1
          match dflt, f with
          | some d, .dflt => pure d
          | _, _ => decode infos k' f
      vals := vals.push x
      t := body.instantiate1 x
    return mkAppN (mkConst ctor us) (params ++ vals)
  | _, _ => throwError "the sample does not fit the type {info.ty}"

/-- The arguments of `D` that the sample `vs` describes. -/
def decodeArgs (D : Name) (infos : Array TInfo) (tids : Array Nat) (vs : Array V) : MetaM (Array Expr × Nat) := do
  let info ← getConstInfo D
  let us := info.levelParams.map fun _ => Level.zero
  let mut t := info.type.instantiateLevelParams info.levelParams us
  let mut args := #[]
  let mut j := 0
  while true do
    let .forallE _ dom body bi ← whnf t | break
    let x ← if bi.isInstImplicit then synthInstance dom
      else if (← whnf dom).isSort then pure (mkConst ``Nat)
      else do
        let x ← decode infos tids[j]! vs[j]!
        j := j + 1
        pure x
    args := args.push x
    t := body.instantiate1 x
  return (args, j)

/-- The first pair of parts of `a` and `b` that differ, in `cmpChain`'s
order, with the sampled `points` for functions. -/
unsafe def leafDiff (a b : Expr) : StateT (List Expr) MetaM (Option (Expr × Expr)) := do
  if let some c ← leafCmp? a b then
    return if (← evalBools #[c]) == [false] then some (a, b) else none
  match ← split? a with
  | some (.point _) =>
    let x :: rest ← get | throwError "too few points"
    set rest
    leafDiff (mkApp a x) (mkApp b x)
  | some (.fields projs) =>
    for f in projs do
      if let some d ← leafDiff (← f a) (← f b) then return some d
    return none
  | some (.list elem) =>
    let la ← mkAppM ``List.length #[a]
    let lb ← mkAppM ``List.length #[b]
    let n ← evalNat la
    if n != (← evalNat lb) then return some (la, lb)
    -- The first element that differs, when the type has a default to index with.
    let some _ ← (try some <$> synthInstance (mkApp (mkConst ``Inhabited [1]) elem) catch _ => pure none)
      | return some (a, b)
    for i in [0:n] do
      let ai ← mkAppM ``getElem! #[a, mkNatLit i]
      let bi ← mkAppM ``getElem! #[b, mkNatLit i]
      if let some d ← leafDiff ai bi then return some d
    return some (a, b)
  | none => throwError "cannot compare values of type {← inferType a}"

/-! ## Shrinking a witness -/

/-- The values one step smaller than `v`. Some do not decode, such as a
field's sub-value of another type, and `chk` rejects those. -/
partial def shrinksV : V → Array V
  | .nat n => if n == 0 then #[] else #[.nat 0, .nat (n - 1)]
  | .char c => if c == 'a' then #[] else #[.char 'a']
  | .str s =>
    if s.isEmpty then #[] else
    let as := String.ofList (s.toList.map fun _ => 'a')
    #[.str "", .str (s.drop 1).toString, .str (s.dropEnd 1).toString] ++ (if as != s then #[.str as] else #[])
  | .list xs =>
    (List.range xs.size).toArray.map (fun i => .list (xs.eraseIdx! i)) ++
      (List.range xs.size).toArray.flatMap fun i => (shrinksV xs[i]!).map fun x => .list (xs.set! i x)
  | .fn d tbl =>
    (List.range tbl.size).toArray.map (fun i => .fn d (tbl.eraseIdx! i)) ++
      (shrinksV d).map (.fn · tbl) ++
      (List.range tbl.size).toArray.flatMap fun i =>
        let (a, b) := tbl[i]!
        (shrinksV a).map (fun a => .fn d (tbl.set! i (a, b))) ++ (shrinksV b).map fun b => .fn d (tbl.set! i (a, b))
  | .ctor i fs =>
    -- A field in place of the value, as a smaller value of a recursive type.
    fs.filter (· matches .ctor ..) ++
      (List.range fs.size).toArray.flatMap fun j =>
        (if fs[j]! matches .dflt then #[] else #[.ctor i (fs.set! j .dflt)]) ++
          (shrinksV fs[j]!).map fun f => .ctor i (fs.set! j f)
  | .dflt => #[]

/-- The strings in `v`. -/
partial def strsIn : V → Array String
  | .str s => #[s]
  | .list xs | .ctor _ xs => xs.flatMap strsIn
  | .fn d tbl => strsIn d ++ tbl.flatMap fun (a, b) => strsIn a ++ strsIn b
  | _ => #[]

partial def replaceStr (s s' : String) : V → V
  | .str x => .str (if x == s then s' else x)
  | .list xs => .list (xs.map (replaceStr s s'))
  | .ctor i xs => .ctor i (xs.map (replaceStr s s'))
  | .fn d tbl => .fn (replaceStr s s' d) (tbl.map fun (a, b) => (replaceStr s s' a, replaceStr s s' b))
  | v => v

/-- Shrink the sample `vs` while `chk` still finds that `D` and `D_mutant`
differ on it. A string that occurs more than once shrinks everywhere at
once, since a witness often needs two arguments to be equal. -/
partial def shrink (chk : Array V → Option Bool) (vs : Array V) : Array V := Id.run do
  let mut cur := vs
  let mut budget := 20000
  let mut progress := true
  while progress && budget > 0 do
    progress := false
    let strs := (cur.flatMap strsIn).toList.eraseDups
    let cands := strs.toArray.flatMap (fun s => (shrinksV (.str s)).filterMap fun
        | .str s' => some (cur.map (replaceStr s s'))
        | _ => none) ++
      (List.range cur.size).toArray.flatMap fun i => (shrinksV cur[i]!).map (cur.set! i ·)
    for c in cands do
      budget := budget - 1
      if chk c == some false then
        cur := c
        progress := true
        break
      if budget == 0 then break
  return cur

/-! ## Searching for a witness -/

/-- `MutantCheckRt.search`, from the file's environment. -/
abbrev SearchFn := (Array V → Option Bool) → Array Sch → Array Nat → Array String → Array Char → Nat → Nat →
  Nat × Nat × Option (Array V)

/-- Search for arguments on which `D` and `D'` differ: the shrunk witness
and its test, or why there can be none; and the samples drawn. -/
unsafe def distinguish (D D' : Name) (strs : Array String) (chars : Array Char) (seed samples : Nat) :
    MetaM (Except String (Option (String × String)) × Nat × Nat) := do
  let pre := rt (.mkSimple s!"m{seed}")
  let (chk, infos, tids) ← try build D D' pre
    catch e => return (.error s!"cannot sample: {(← e.toMessageData.toString).take 300}", 0, 0)
  let search ← IO.ofExcept <| (← getEnv).evalConst SearchFn (← getOptions) (rt `search) (checkMeta := false)
  let (n, rejected, w) := search chk (infos.map (·.sch)) tids strs chars seed samples
  let some vs := w
    | if n > 0 && rejected == n then
        return (.error s!"every one of {n} samples failed a condition of its type", n, rejected)
      return (.ok none, n, rejected)
  let vs := shrink chk vs
  let us := (← getConstInfo D).levelParams.map fun _ => Level.zero
  let (args, j) ← decodeArgs D infos tids vs
  let points ← (List.range (tids.size - j)).mapM fun i => decode infos tids[j + i]! vs[j + i]!
  -- The part that differs; the compiled comparison and the terms must agree.
  let some (lhs, rhs) ← (leafDiff (mkAppN (mkConst D us) args) (mkAppN (mkConst D' us) args)).run' points
    | return (.error "the decoded witness does not differ; a bug in `decode`", n, rejected)
  let o ← showValue lhs
  let m ← showValue rhs
  let what := s!"{← ppTest lhs}: {o.getD "?"}, mutant: {m.getD "?"}"
  return (.ok (some (what, ← testOf lhs)), n, rejected)


/-! ## Proving `D` and `D_mutant` equal -/

/-- Equation lemmas and the like, which Lean generates from a definition, so
that their proofs are real in the copy too. -/
def generated (c : Name) : Bool :=
  match c with
  | .str _ s => s == "eq_def" || s == "eq_unfold" || s == "induct" || s == "induct_unfolding" ||
      s == "fun_cases" || s == "fun_cases_unfolding" || s.startsWith "eq_" && (s.drop 3).all Char.isDigit ||
      s == "splitter" || s == "inj" || s == "injEq" || s == "sizeOf_spec" || s == "noConfusion"
  | _ => false

/-- A theorem of `Mise` that the proof `pf` uses: the copy has no proof
of it. -/
def libraryTheorem? (env : Environment) (pf : Expr) : Option Name :=
  pf.getUsedConstants.find? fun c =>
    c.getRoot == `Mise && !generated c && match env.find? c with
      | some (.thmInfo _) => true
      | _ => false

def tactics (D D' : Name) : List String :=
  let d := toString D
  let d' := toString D'
  [ "intros; rfl",
    s!"intros; simp only [{d}, {d'}]",
    s!"intros; simp [{d}, {d'}]",
    s!"intros; fun_induction {d} <;> simp_all [{d}, {d'}]",
    s!"intros; unfold {d} {d'}; grind",
    s!"intros; simp [{d}, {d'}] <;> grind",
    s!"intros; fun_induction {d} <;> grind [{d}, {d'}]" ]

/-- Prove `D` and `D'` equal: the tactic that does, or why each failed. -/
def prove (D D' : Name) : TermElabM (Except (List String) String) := do
  let info ← getConstInfo D
  let us := info.levelParams.map mkLevelParam
  let stmt ← forallTelescope info.type fun xs r => do
    let lhs := mkAppN (mkConst D us) xs
    let rhs := mkAppN (mkConst D' us) xs
    mkForallFVars xs (← if ← isProp r then pure (mkIff lhs rhs) else mkEq lhs rhs)
  let debug := (← IO.getEnv "MUTANT_DEBUG").isSome
  let mut whys := []
  for tac in tactics D D' do
    -- A sequence parses as one tactic only in parentheses.
    let stx ← match Parser.runParserCategory (← getEnv) `tactic s!"({tac})" with
      | .ok stx => pure stx
      | .error e => whys := whys ++ [s!"`{tac}` does not parse: {e}"]; continue
    let why ← withoutModifyingEnv do
      let msgs ← Core.getMessageLog
      -- A timeout is a runtime exception, which plain `try` does not catch.
      tryCatchRuntimeEx (do
        let mvar ← mkFreshExprMVar stmt
        let rest ← withCurrHeartbeats <|
          withTheReader Core.Context (fun c => { c with maxHeartbeats := proofHeartbeats * 1000 }) <|
          Term.withoutErrToSorry <| Tactic.run mvar.mvarId! (Tactic.evalTactic stx)
        let errs := (← Core.getMessageLog).toList.filter (·.severity == .error)
        Core.setMessageLog msgs
        if let some e := errs.head? then return some (← e.data.toString)
        if !rest.isEmpty then return some s!"{rest.length} goals remain"
        let pf ← instantiateMVars mvar
        if pf.hasSorry then return some "the proof is incomplete"
        if let some c := libraryTheorem? (← getEnv) pf then
          return some s!"the proof uses {c}, which has no proof in the copy"
        addDecl (.thmDecl { name := D' ++ `eq_original, levelParams := info.levelParams, type := stmt, value := pf })
        return none) fun e => do
        Core.setMessageLog msgs
        return some (← e.toMessageData.toString)
    match why with
    | none => return .ok tac
    | some w =>
      if debug then IO.eprintln s!"{D'}: `{tac}`: {w}"
      whys := whys ++ [s!"`{tac}`: {(" ".intercalate (w.splitOn "\n")).take 120}"]
  return .error whys

/-! ## The copy -/

/-- `D` with its last component suffixed, so that the copy lives next to it. -/
def mutantName (D : Name) : Name :=
  match D with
  | .str p s => .str p (s ++ "_mutant")
  | n => n

/-- Rename `D` to `D_mutant` in `stx`: an identifier whose leading components
are a suffix of `D` refers to `D` (`ok`, `Stmt.ok`, `Reach.init`), and one
whose later component is `D`'s last is a call in field notation (`rest.ok`). -/
def rename (D : Name) (stx : Syntax) : Syntax :=
  let last := match D with | .str _ s => s | _ => ""
  Id.run <| stx.replaceM fun s => pure <|
    if !s.isIdent then none else
    let cs := s.getId.components
    let cs' := cs.zipIdx.map fun (c, i) =>
      let pre := (cs.take (i + 1)).foldl (· ++ ·) .anonymous
      match c with
      | .str .anonymous x => if x == last && (pre.isSuffixOf D || i > 0) then Name.mkSimple (x ++ "_mutant") else c
      | _ => c
    if cs' == cs then none else some (mkIdentFrom s (cs'.foldl (· ++ ·) .anonymous))

/-- The literals in the definitions of the file so far: strings, and the
characters of strings and of character literals. -/
partial def litsOf (e : Expr) : StateM (Std.HashSet Expr × Std.HashSet String × Std.HashSet Char) Unit := do
  if (← get).1.contains e then return
  modify fun (v, ss, cs) => (v.insert e, ss, cs)
  match e with
  | .lit (.strVal s) => modify fun (v, ss, cs) => (v, ss.insert s, s.toList.foldl (·.insert ·) cs)
  | .app f a =>
    if f.isConstOf ``Char.ofNat then
      if let .lit (.natVal n) := a then modify fun (v, ss, cs) => (v, ss, cs.insert (Char.ofNat n))
    litsOf f; litsOf a
  | .lam _ t b _ | .forallE _ t b _ => litsOf t; litsOf b
  | .letE _ t v b _ => litsOf t; litsOf v; litsOf b
  | .mdata _ b | .proj _ _ b => litsOf b
  | _ => pure ()

def literals (env : Environment) : Array String × Array Char :=
  let base : Std.HashSet Char := "ab/.: $|=\n-_{}".toList.foldl (·.insert ·) {}
  let go : StateM _ Unit := do
    for (n, ci) in env.constants.map₂.toList do
      if (`MutantCheckRt).isPrefixOf n then continue
      if let some v := ci.value? then litsOf v
  let ((), (_, ss, cs)) := go.run ({}, {}, base)
  (ss.toArray.qsort (· < ·), cs.toArray.qsort (· < ·))

/-! ## The driver -/

def seedOf (s : String) : Nat := (hash s).toNat

/-- The declaration that `cmd` adds, named by its `declId`, among the
constants `added`. -/
def declOf (cmd : Syntax) (added : Array Name) : Option Name := do
  let id ← cmd.find? (·.getKind == ``Lean.Parser.Command.declId)
  let n := id[0].getId
  added.find? fun c => n.isSuffixOf c && !c.isInternalDetail

unsafe def check (samples : Nat) (st : Command.State) (D : Name) (cmdSrc : String) (m : Mutant) (off : Nat) :
    IO Result := do
  let r : Result := { name := m.name, verdict := "undecided", decl := toString D }
  let bytes := cmdSrc.toUTF8
  let a := m.start - off
  let b := m.stop - off
  let src := String.fromUTF8! (bytes.extract 0 a) ++ m.text ++ String.fromUTF8! (bytes.extract b bytes.size)
  let ictx := Parser.mkInputContext src s!"<{m.name}>"
  let scope := st.scopes.head!
  let pmctx : Parser.ParserModuleContext :=
    { env := st.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (stx, _, msgs) := Parser.parseCommand ictx pmctx {} {}
  if msgs.hasErrors then return { r with detail := "the edited declaration does not parse" }
  let stx := rename D stx
  let ctx : Command.Context := { fileName := ictx.fileName, fileMap := ictx.fileMap, snap? := none, cancelTk? := none }
  let st0 := { st with messages := {} }
  let D' := mutantName D
  let (strs, chars) := literals st.env
  let act : Command.CommandElabM Result := do
    Command.elabCommandTopLevel stx
    let errs := (← get).messages.toList.filter (·.severity == .error)
    if let some e := errs.head? then
      return { r with detail := s!"the copy does not elaborate: {(← e.data.toString).take 200}" }
    if !(← getEnv).contains D' then return { r with detail := s!"the copy does not declare {D'}" }
    Command.liftTermElabM do
      -- The samples together take more than one command's heartbeats.
      let (res, n, rejected) ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) <|
        distinguish D D' strs chars (seedOf m.name) samples
      match res with
      | .ok (some (what, test)) =>
        return { r with verdict := "distinguished", detail := what, test, samples := n }
      | _ =>
        let why := match res with
          | .error e => e
          | _ => s!"no difference in {n} samples" ++ (if rejected > 0 then s!" ({rejected} rejected by a condition)" else "")
        match ← prove D D' with
        | .ok tac => return { r with verdict := "equivalent", detail := s!"by {tac}", samples := n }
        | .error _ => return { r with detail := s!"{why}; no proof found", samples := n }
  match ← (EIO.toIO' ((act ctx).run st0)) with
  | .ok (res, _) => return res
  | .error e => return { r with detail := s!"internal error: {(← e.toMessageData.toString).take 200}" }

unsafe def checkFile (samples : Nat) (path : String) (ms : Array Mutant) (out : IO.FS.Handle) : IO Unit := do
  let input ← IO.FS.readFile path
  let ictx := Parser.mkInputContext input path
  let (header, ps, msgs) ← Parser.parseHeader ictx
  let opts := ({} : Options).setBool `debug.byAsSorry true |>.setBool `Elab.async false
  -- `importModules` clears the flag, so each file must set it again.
  enableInitializersExecution
  let (env, msgs) ← processHeader header opts msgs ictx (leakEnv := true)
  let mut fs : Frontend.State := { commandState := Command.mkState env msgs opts, parserState := ps, cmdPos := ps.pos }
  -- The runtime of the search, before the file's first command.
  let rs ← IO.processCommands (Parser.mkInputContext prelude "<MutantCheckRt>") {} fs.commandState
  if let some e := rs.commandState.messages.toList.find? (·.severity == .error) then
    throw (IO.userError s!"the runtime does not elaborate in {path}: {← e.data.toString}")
  fs := { fs with commandState := { rs.commandState with messages := fs.commandState.messages } }
  let mut todo := ms.qsort (·.start < ·.start)
  let bytes := input.toUTF8
  while !todo.isEmpty do
    let before := fs.commandState.env.constants.map₂.toList.map (·.1)
    let (done, fs') ← (Frontend.processCommand.run { inputCtx := ictx }).run fs
    fs := fs'
    let cmd := fs.commands.back!
    let (some a, some b) := (cmd.getPos?, cmd.getTailPos?) | if done then break else continue
    let (here, later) := todo.partition fun m => a.byteIdx ≤ m.start && m.stop ≤ b.byteIdx
    let missed := later.filter (·.stop ≤ a.byteIdx)
    todo := later.filter (·.stop > a.byteIdx)
    for m in missed do
      out.putStrLn (toJson ({ name := m.name, verdict := "undecided", detail := "the edit is not inside one command" } : Result)).compress
      out.flush
    if !here.isEmpty then
      let old : Std.HashSet Name := before.foldl (·.insert ·) {}
      let added := fs.commandState.env.constants.map₂.toList.map (·.1) |>.filter (!old.contains ·)
      let cmdSrc := String.fromUTF8! (bytes.extract a.byteIdx b.byteIdx)
      for m in here do
        let res ← match declOf cmd added.toArray with
          | some D => check samples fs.commandState D cmdSrc m a.byteIdx
          | none => pure { name := m.name, verdict := "undecided", detail := "the edited command declares nothing" }
        out.putStrLn (toJson res).compress
        out.flush
    if done then break
  for m in todo do
    out.putStrLn (toJson ({ name := m.name, verdict := "undecided", detail := "no command holds the edit" } : Result)).compress
    out.flush

unsafe def main (args : List String) : IO UInt32 := do
  let [inp, outp] := args | throw (IO.userError "usage: MutantCheck.lean IN OUT")
  let ms ← IO.ofExcept <| (Json.parse (← IO.FS.readFile inp)).bind (fromJson? (α := Array Mutant))
  initSearchPath (← findSysroot)
  let samples := ((← IO.getEnv "MUTANT_SAMPLES").bind String.toNat?).getD 100000
  let out ← IO.FS.Handle.mk outp .append
  let files := ms.foldl (fun (acc : Array String) m => if acc.contains m.file then acc else acc.push m.file) #[]
  for f in files do
    checkFile samples f (ms.filter (·.file == f)) out
  return 0

end MutantCheck

unsafe def main (args : List String) : IO UInt32 := MutantCheck.main args
