import Lean
import Mise
import MiseTest.TrustWalk
open Lean Meta Elab

/-!
Generates mutants of the definitions that the theorems in `Mise.Theorems`
are stated in, for `test/trust-mutants.py`. Run it with
`lake env lean test/MiseTest/MutantGen.lean` in a built tree; it writes JSON
to the file named by the environment variable `MUTANTS_OUT` (default
`test/out/trust-mutants/generated.json`).

The targets are the trusted declarations of `MiseTest.TrustWalk`. The
generator elaborates each target's source file again, keeping the info
trees, so that it knows the type of every subterm. It then walks the syntax
of each target and proposes these edits:

* replace a proposition with `True` or `False`. When the proposition is one
  side of `∧`, the antecedent of `→`, or one side of `∨`, the edit that
  leaves the other side alone is written as deleting this side;
* replace a `Bool` condition with `true` or `false` (a definition's body, an
  `if` condition, an operand of `&&`, `||`, `!` or of `= true`);
* delete a constructor of an inductive proposition;
* swap `<` with `≤`, and `>` with `≥`;
* put `.take 0` or `.take 1` on a list: a definition's body, an argument of
  an application, or the right side of `∈` (`.take 1` only, since `.take 0`
  there is `False`);
* replace an explicit argument of an application with another explicit
  argument of the same type.

Edits that give the same proposition as another edit are skipped: `False`
for one side of `∧` gives the same as `False` for the whole, and so on.

## Polarity

Each edit pushes its declaration `D` in a known direction or in none:
`True` makes `D` hold more often, a dropped constructor less often, and a
swapped argument in no known direction. The walk over the syntax tracks the
sign of each subterm in `D`: it flips on the left of `→` and under `¬`, and
an argument of a constant takes the sign of that constant's parameter.

The sign of `D` in a theorem comes from a walk over the theorem's statement
(`walk`), which unfolds every `Mise` definition that is a proposition or a
`Bool`, and walks the constructors of inductive propositions. A `Mise`
constant that is data (a list, a state) is not unfolded, and every trusted
declaration reachable from it gets both signs. So does a constant under `↔`,
`=` or an `if` condition.

The product of the two signs says whether the edit makes the theorem hold
more often (weaker), less often (stronger), or neither is known. An edit is
kept when it weakens at least one theorem or its effect on one is unknown.
A proof cannot catch an edit that only weakens theorems, since the weaker
theorem is still true, so the tests in `test/MiseTest/` must. An edit that
only strengthens theorems is the proofs' job, and is dropped.
-/

namespace MutantGen

/-! ## Signs -/

/-- The signs seen for a constant or a variable: positive, negative. -/
abbrev Signs := Bool × Bool

def Signs.add (s : Signs) (p : Int) : Signs := (s.1 || p ≥ 0, s.2 || p ≤ 0)

/-- `1` when only positive, `-1` when only negative, `0` otherwise. -/
def Signs.pol : Signs → Int
  | (true, false) => 1
  | (false, true) => -1
  | _ => 0

def Signs.show : Signs → String
  | (true, false) => "+"
  | (false, true) => "-"
  | (true, true) => "±"
  | (false, false) => ""

/-! ## The walk over a statement -/

structure WState where
  consts : NameMap Signs := {}
  fvars : Std.HashMap FVarId Signs := {}
  /-- Constants whose trusted closure already has both signs. -/
  both : NameSet := {}
  fuel : Nat := 1000000

abbrev WalkM := StateRefT WState MetaM

def noteC (c : Name) (p : Int) : WalkM Unit :=
  modify fun s => { s with consts := s.consts.insert c (((s.consts.find? c).getD (false, false)).add p) }

def noteF (x : FVarId) (p : Int) : WalkM Unit :=
  modify fun s => { s with fvars := s.fvars.insert x ((s.fvars.getD x (false, false)).add p) }

/-- Give both signs to every trusted declaration reachable from `c`. -/
def noteAll (c : Name) : WalkM Unit := do
  if (← get).both.contains c then return
  modify fun s => { s with both := s.both.insert c }
  let env ← getEnv
  for n in (Trusted.reach env #[c]).toArray do
    noteC (Trusted.owner env n) 0

def boolLit? (e : Expr) : Option Bool :=
  if e.isConstOf ``Bool.true then some true else if e.isConstOf ``Bool.false then some false else none

mutual

/-- Record the sign of every `Mise` constant and free variable in `e`, where
`e` has sign `p` (`0` for both). -/
partial def walk (stack : List (Name × Array Expr)) (e : Expr) (p : Int) : WalkM Unit := do
  let s ← get
  if s.fuel == 0 then throwError "MutantGen: the walk ran out of fuel"
  set { s with fuel := s.fuel - 1 }
  match e.consumeMData.headBeta with
  | .forallE n t b bi =>
    walk stack t (if ← isProp t then -p else 0)
    withLocalDecl n bi t fun x => walk stack (b.instantiate1 x) p
  | .lam n t b bi =>
    walk stack t 0
    withLocalDecl n bi t fun x => walk stack (b.instantiate1 x) p
  | .letE _ _ v b _ =>
    walk stack v 0
    walk stack (b.instantiate1 v) p
  | .proj _ _ s => walk stack s 0
  | .fvar x => noteF x p
  | e => if e.isApp || e.isConst then walkApp stack e p

partial def walkApp (stack : List (Name × Array Expr)) (e : Expr) (p : Int) : WalkM Unit := do
  let f := e.getAppFn
  let args := e.getAppArgs
  let n := args.size
  let a (i : Nat) := args[i]!
  let rest (i : Nat) : WalkM Unit := do
    for x in args.extract i n do walk stack x 0
  let .const c lvls := f | do
    if let .fvar x := f then noteF x p
    rest 0
  if (c == ``And || c == ``Or || c == ``and || c == ``or) && n == 2 then
    walk stack (a 0) p; walk stack (a 1) p
  else if (c == ``Not || c == ``not) && n == 1 then walk stack (a 0) (-p)
  else if c == ``Exists && n == 2 then walk stack (a 1) p
  else if c == ``Decidable.decide && n == 2 then walk stack (a 0) p
  else if (c == ``ite || c == ``dite) && n == 5 then
    walk stack (a 1) 0; walk stack (a 3) p; walk stack (a 4) p
  else if c == ``cond && n == 4 then
    walk stack (a 1) 0; walk stack (a 2) p; walk stack (a 3) p
  else if c == ``Eq && n == 3 && (a 0).isConstOf ``Bool then
    match boolLit? (a 2), boolLit? (a 1) with
    | some b, _ => walk stack (a 1) (if b then p else -p)
    | _, some b => walk stack (a 2) (if b then p else -p)
    | _, _ => rest 0
  -- `x ∈ l` for a list `l` holds more often when `l` is longer.
  else if c == ``Membership.mem && n == 5 && (a 1).isAppOfArity ``List 1 then
    walk stack (a 3) p; walk stack (a 4) 0
  else if let some mi ← getMatcherInfo? c then
    if n < mi.arity then rest 0
    else
      for i in [mi.getFirstDiscrPos : mi.getFirstDiscrPos + mi.numDiscrs] do walk stack (a i) 0
      for i in [mi.getFirstAltPos : mi.getFirstAltPos + mi.altInfos.size] do walk stack (a i) p
      rest mi.arity
  else if !Trusted.isMise c then rest 0
  else
    let env ← getEnv
    let o := Trusted.owner env c
    if Trusted.isImplementation o then rest 0; return
    noteC o p
    -- A recursive occurrence. An inductive's parameters are the same as in
    -- the occurrence being unfolded, so they are not walked again.
    if let some (_, ps) := stack.find? (·.1 == c) then
      for i in [0:n] do
        if ps[i]? != some (a i) then walk stack (a i) 0
      return
    let ty ← whnfD (← inferType e)
    if !(ty.isProp || ty.isConstOf ``Bool) then noteAll c; rest 0; return
    match env.find? c with
    | some (.inductInfo i) =>
      if n < i.numParams then noteAll c; rest 0; return
      let ps := args.extract 0 i.numParams
      for ctor in i.ctors do
        let some (.ctorInfo ci) := env.find? ctor | pure ()
        let t ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams lvls) ps
        forallTelescope t fun xs concl => do
          for x in xs do
            let xt ← inferType x
            walk ((c, ps) :: stack) xt (if ← isProp xt then p else 0)
          for b in concl.getAppArgs.extract i.numParams concl.getAppArgs.size do walk ((c, ps) :: stack) b 0
      rest i.numParams
    | some (.defnInfo _) =>
      if let some pi := env.getProjectionFnInfo? c then
        if n > pi.numParams then
          let s ← whnf (a pi.numParams)
          if s.isAppOf pi.ctorName then
            if let some fld := s.getAppArgs[pi.numParams + pi.i]? then
              walk stack (mkAppN fld (args.extract (pi.numParams + 1) n)) p
              return
        noteAll c; rest 0
      else if ← isRecursiveDefinition c then
        let some eqn ← getUnfoldEqnFor? c (nonRec := true) | do noteAll c; rest 0
        let t ← inferType (mkConst eqn lvls)
        let k := t.getForallBinderNames.length
        if n < k then noteAll c; rest 0; return
        match (← instantiateForall t (args.extract 0 k)).eq? with
        | some (_, _, rhs) => walk ((c, #[]) :: stack) (mkAppN rhs (args.extract k n)) p
        | none => noteAll c; rest 0
      else
        match ← delta? e (· == c) with
        | some e' => walk ((c, #[]) :: stack) e' p
        | none => noteAll c; rest 0
    | _ => noteAll c; rest 0

end

/-- The signs of the trusted declarations in a statement. -/
def signsOf (t : Expr) : MetaM (NameMap Signs) := do
  let (_, s) ← (walk [] t 1).run {}
  return s.consts

/-- The sign of each parameter of `c` in `c` itself, `0` when unknown. -/
def paramPols (c : Name) : MetaM (Array Int) := do
  let some ci := (← getEnv).find? c | return #[]
  try
    forallTelescope ci.type fun xs _ => do
      let (_, s) ← (walkApp [] (mkAppN (mkConst c (ci.levelParams.map mkLevelParam)) xs) 1).run {}
      return xs.map fun x => (s.fvars.getD x.fvarId! (false, false)).pol
  catch _ => return #[]

/-! ## Edits -/

structure Edit where
  decl : Name
  kind : String
  start : Nat
  stop : Nat
  text : String
  /-- `1` when the edit makes the declaration hold more often, `-1` less
  often, `0` when neither is known. -/
  eff : Int
  what : String
  line : Nat
  col : Nat

/-- The term elaborated at a syntax range: the first, outermost one. -/
abbrev Infos := Std.HashMap (Nat × Nat) (ContextInfo × TermInfo)

/-- A subterm's elaborated form. -/
structure Term where
  expr : Expr
  ty : Expr
  /-- The subterm is a proof or a type, which an edit should not touch. -/
  skip : Bool

/-- Where a subterm sits, which decides the edits it gets. -/
inductive Place where
  /-- A declaration's body or a branch of it. -/
  | top
  /-- Any other place where a proposition may be replaced. -/
  | cond
  | andOp | orOp | impAnte | impCons | notOp | allBody | exBody
  /-- A `Bool` condition. -/
  | bool
  /-- The list on the right of `∈`. -/
  | coll
  /-- An explicit argument of an application. -/
  | arg
  /-- No edit here: the head of an application, a constructor's conclusion. -/
  | none
  deriving BEq

structure GCtx where
  src : String
  fileMap : FileMap
  infos : Infos
  decl : Name

structure GState where
  edits : Array Edit := #[]
  pols : NameMap (Array Int) := {}

abbrev GenM := ReaderT GCtx (StateRefT GState MetaM)

def range? (s : Syntax) : Option (Nat × Nat) :=
  match s.getPos?, s.getTailPos? with
  | some a, some b => some (a.byteIdx, b.byteIdx)
  | _, _ => none

def termOf (s : Syntax) : GenM (Option Term) := do
  let some r := range? s | return none
  let some (ci, ti) := (← read).infos[r]? | return none
  try
    ci.runMetaM ti.lctx do
      let e ← instantiateMVars ti.expr
      let t ← instantiateMVars (← inferType e)
      let tr ← whnfR t
      return some { expr := e, ty := tr, skip := (← isProp t) || (tr.isSort && !tr.isProp) }
  catch _ => return none

def textOf (s : Syntax) : GenM String := do
  let some (a, b) := range? s | return ""
  return String.Pos.Raw.extract (← read).src ⟨a⟩ ⟨b⟩

def slice (a b : Nat) : GenM String :=
  return String.Pos.Raw.extract (← read).src ⟨a⟩ ⟨b⟩

/-- One line of at most 60 characters. -/
def brief (s : String) : String :=
  let s := " ".intercalate ((s.splitOn "\n").map fun l => l.trimAscii.toString)
  if s.length > 60 then String.ofList (s.toList.take 57) ++ "…" else s

def emit (kind : String) (a b : Nat) (text : String) (eff : Int) (what : String) : GenM Unit := do
  let c ← read
  let pos := c.fileMap.toPosition ⟨a⟩
  let e : Edit := { decl := c.decl, kind, start := a, stop := b, text, eff, what, line := pos.line, col := pos.column }
  modify fun s => { s with edits := s.edits.push e }

def isAtomic (t : String) : Bool := !t.any fun c => c == ' ' || c == '\n'

/-- `t` in parentheses, unless it is one token. -/
def paren (t : String) : String := if isAtomic t then t else s!"({t})"

/-- The edits of the subterm `s` itself, with sign `p` in the declaration.
`True` is written `(A ∨ True)` and `False` `(A ∧ False)`, and likewise for
`Bool`, so that the variables in `A` keep the types `A` gives them. -/
def sitesAt (s : Syntax) (p : Int) (place : Place) (t : Option Term) : GenM Unit := do
  let some (a, b) := range? s | return
  let some t := t | return
  if t.skip then return
  let txt ← textOf s
  let yes := s!"({paren txt} ∨ True)"
  let no := s!"({paren txt} ∧ False)"
  if t.ty.isProp then
    if place == .none || place == .bool || txt == "True" || txt == "False" then return
    let skipT := place == .orOp || place == .impCons || place == .notOp || place == .allBody
    let skipF := place == .andOp || place == .impAnte || place == .notOp || place == .exBody
    if !skipT then
      if place == .andOp || place == .impAnte then emit "drop" a b yes p s!"drop `{brief txt}`"
      else emit "true" a b yes p s!"`{brief txt}` → `True`"
    if !skipF then
      if place == .orOp then emit "drop" a b no (-p) s!"drop `{brief txt}`"
      else emit "false" a b no (-p) s!"`{brief txt}` → `False`"
  else if t.ty.isConstOf ``Bool then
    if (place == .top || place == .bool) && txt != "true" && txt != "false" then
      emit "true" a b s!"({paren txt} || true)" p s!"`{brief txt}` → `true`"
      emit "false" a b s!"({paren txt} && false)" (-p) s!"`{brief txt}` → `false`"
  else if t.ty.isAppOfArity ``List 1 then
    let take (k : Nat) := s!"({paren txt}.take {k})"
    if place == .top || place == .arg then
      emit "take0" a b (take 0) (-p) s!"`{brief txt}` → `{brief (take 0)}`"
    if place == .top || place == .arg || place == .coll then
      emit "take1" a b (take 1) (-p) s!"`{brief txt}` → `{brief (take 1)}`"

def cmpSwap : List (String × String × Int) :=
  [("<", "≤", 1), ("≤", "<", -1), (">", "≥", 1), ("≥", ">", -1)]

/-- The sign of each explicit argument of the application `s`, from the
parameter signs of its head constant. -/
def argPols (s : Syntax) (args : Array Syntax) (ts : Array (Option Term)) : GenM (Array Int) := do
  let zeros := args.map fun _ => (0 : Int)
  let some app ← termOf s | return zeros
  let some c := app.expr.getAppFn.constName? | return zeros
  let pp ← match (← get).pols.find? c with
    | some pp => pure pp
    | none => do
      let pp ← paramPols c
      modify fun st => { st with pols := st.pols.insert c pp }
      pure pp
  let eargs := app.expr.getAppArgs
  return ts.map fun t? => match t? with
    | some t => match eargs.findIdx? (· == t.expr) with
      | some i => pp[i]?.getD 0
      | none => 0
    | none => 0

partial def walkS (s : Syntax) (p : Int) (place : Place) : GenM Unit := do
  let k := s.getKind
  if k == ``Lean.Parser.Term.paren then return ← walkS s[1] p place
  if s.isAtom || s.isMissing then return
  if k == ``Lean.Parser.Term.byTactic || k == ``Lean.Parser.Termination.suffix ||
      k == ``Lean.Parser.Command.docComment then return
  let t ← termOf s
  -- In a constructor, a term that mentions the inductive itself keeps its
  -- shape: `(I x ∧ False)` and `((∀ v, I v) ∨ True)` are nested
  -- occurrences, which the kernel rejects, and `I` must keep its
  -- parameters. While the constructor is elaborated, `I` is a local, not a
  -- constant, so match it by name.
  let decl := (← read).decl
  let self := decl.componentsRev.head?
  let nested := (← isInductive decl) &&
    (s.find? fun x => x.isIdent && some x.getId == self).isSome
  if nested && k == ``Lean.Parser.Term.app && s[0].isIdent && some s[0].getId == self then
    return ← walkS s[0] 0 .none
  unless nested do sitesAt s p place t
  let kids : GenM Unit := do for c in s.getArgs do walkS c 0 .cond
  let isPropAt (x : Syntax) : GenM Bool := return (← termOf x).any (·.ty.isProp)
  match k with
  | `«term_∧_» => walkS s[0] p .andOp; walkS s[2] p .andOp
  | `«term_∨_» => walkS s[0] p .orOp; walkS s[2] p .orOp
  | `«term¬_» => walkS s[1] (-p) .notOp
  | `«term_↔_» => walkS s[0] 0 .cond; walkS s[2] 0 .cond
  | ``Lean.Parser.Term.arrow =>
    if ← isPropAt s[0] then walkS s[0] (-p) .impAnte; walkS s[2] p .impCons
    else kids
  | `Lean.«term∃__,_» => walkS s[2][1] p .coll; walkS s[4] p .exBody
  | `Lean.«term∀__,_» => walkS s[2][1] (-p) .coll; walkS s[4] p .allBody
  | `«term∃_,_» => walkS s[3] p .exBody
  | ``Lean.Parser.Term.forall =>
    for b in s[1].getArgs do
      if b.getKind == ``Lean.Parser.Term.explicitBinder && b[2].getNumArgs > 1 then
        if ← isPropAt b[2][1] then walkS b[2][1] (-p) .cond
    walkS s[4] p .allBody
  | `«term_∈_» => walkS s[0] 0 .cond; walkS s[2] p .coll
  | `«term_∉_» => walkS s[0] 0 .cond; walkS s[2] (-p) .coll
  | `«term_=_» =>
    match s[2].getId, s[0].getId with
    | `true, _ => walkS s[0] p .bool
    | `false, _ => walkS s[0] (-p) .bool
    | _, `true => walkS s[2] p .bool
    | _, `false => walkS s[2] (-p) .bool
    | _, _ => kids
  | `«term_&&_» | `«term_||_» => walkS s[0] p .bool; walkS s[2] p .bool
  | `«term!_» => walkS s[1] (-p) .bool
  | `termIfThenElse =>
    let br := if place == .top || place == .bool then place else .cond
    walkS s[1] 0 .bool; walkS s[3] p br; walkS s[5] p br
  | `«term_<_» | `«term_≤_» | `«term_>_» | `«term_≥_» =>
    if let some (a, b) := range? s[1] then
      let op := s[1].getAtomVal
      if let some (_, new, d) := cmpSwap.find? (·.1 == op) then
        emit "cmp" a b new (d * p) s!"`{brief (← textOf s)}`: `{op}` → `{new}`"
    kids
  | ``Lean.Parser.Term.fun =>
    if s[1].getKind == ``Lean.Parser.Term.basicFun then walkS s[1][3] p .cond else kids
  | ``Lean.Parser.Term.match =>
    for alt in s[5][0].getArgs do walkS alt[3] p (if place == .top then .top else .cond)
    for d in s[3].getArgs do walkS d 0 .cond
  | ``Lean.Parser.Term.app =>
    walkS s[0] 0 .none
    -- A recursive call keeps its arguments, so that it still terminates.
    if s[0].isIdent && some s[0].getId == (← read).decl.componentsRev.head? then return
    let args := s[1].getArgs
    let ts ← args.mapM termOf
    let pp ← argPols s args ts
    for h : i in [0:args.size] do
      let x := args[i]
      if x.getKind == ``Lean.Parser.Term.namedArgument then walkS x[3] 0 .cond
      else if x.getKind != ``Lean.Parser.Term.ellipsis then walkS x (pp[i]! * p) .arg
    -- Replace argument `j` with argument `i` of the same type.
    for h : j in [0:args.size] do
      for h' : i in [0:args.size] do
        if i == j then continue
        let (some ti, some tj) := (ts[i]!, ts[j]!) | continue
        if ti.skip || tj.skip || ti.ty != tj.ty then continue
        let (xi, xj) := (args[i]!, args[j]!)
        let (si, sj) := (← textOf xi, ← textOf xj)
        if si == sj || si.any (· == '\n') then continue
        let some (a, b) := range? xj | continue
        emit "dup" a b si 0 s!"`{brief sj}` → `{brief si}` in `{brief (← textOf s)}`"
  | _ => kids

/-- The spine of a constructor's type: each antecedent of `→` is a
hypothesis, with the inductive's own sign. The conclusion gets no edits. -/
partial def walkSpine (t : Syntax) : GenM Unit := do
  let k := t.getKind
  if k == ``Lean.Parser.Term.arrow then
    if (← termOf t[0]).any (·.ty.isProp) then walkS t[0] 1 .impAnte
    walkSpine t[2]
  else if k == ``Lean.Parser.Term.forall then walkSpine t[4]
  else if k == ``Lean.Parser.Term.paren then walkSpine t[1]

def lineStart (src : ByteArray) (a : Nat) : Nat := Id.run do
  let mut i := a
  while i > 0 && src[i - 1]! != '\n'.toUInt8 do i := i - 1
  return i

def lineEnd (src : ByteArray) (b : Nat) : Nat := Id.run do
  let mut i := b
  while i < src.size && src[i]! != '\n'.toUInt8 do i := i + 1
  return min (i + 1) src.size

def walkDecl (cmd : Syntax) : GenM Unit := do
  let d := cmd[1]
  match d.getKind with
  | `Lean.Parser.Command.definition | `Lean.Parser.Command.abbrev | `Lean.Parser.Command.instance =>
    for v in d.getArgs do
      if v.getKind == ``Lean.Parser.Command.declValSimple then walkS v[1] 1 .top
      else if v.getKind == ``Lean.Parser.Command.declValEqns then
        for alt in v[0][0][0].getArgs do walkS alt[3] 1 .top
      else if v.getKind == ``Lean.Parser.Command.whereStructInst then walkS v 0 .cond
  | `Lean.Parser.Command.inductive =>
    let some info := (← getEnv).find? (← read).decl | return
    if !(← forallTelescope info.type fun _ r => return r.isProp) then return
    let src := (← read).src.toUTF8
    for c in d[4].getArgs do
      if c.getKind != ``Lean.Parser.Command.ctor then continue
      if let some (a, b) := range? c then
        emit "rule" (lineStart src a) (lineEnd src b) "" (-1) s!"drop rule `{c[3].getId}`"
      let sig := c[4]
      for b in sig[0].getArgs do
        if b[2].getNumArgs > 1 then
          if (← termOf b[2][1]).any (·.ty.isProp) then walkS b[2][1] 1 .cond
      if sig[1].getNumArgs > 0 then walkSpine sig[1][0][1]
  | _ => pure ()

/-! ## Driver -/

unsafe def enableInitializersUnsafe : IO Unit := enableInitializersExecution

/-- `importModules` refuses to run the imported modules' initializers until
this is called. -/
@[implemented_by enableInitializersUnsafe] opaque enableInitializers : IO Unit

/-- Elaborate a source file again, keeping the info trees. -/
def elabFile (path : String) : IO (Infos × Array Syntax × FileMap × String × Nat) := do
  enableInitializers
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let opts := ({} : Options).setBool `debug.byAsSorry true
  let (env, messages) ← processHeader header opts messages inputCtx (leakEnv := true)
  let s ← IO.processCommands inputCtx parserState (Command.mkState env messages opts)
  let errs := s.commandState.messages.toList.filter (·.severity == .error)
  for m in errs.take 3 do IO.eprintln (← m.toString)
  let errors := errs.length
  let mut infos : Infos := {}
  for t in s.commandState.infoState.trees do
    infos := t.foldInfo (init := infos) fun ci i acc => match i with
      | .ofTermInfo ti => match range? ti.stx with
        | some r => if acc.contains r then acc else acc.insert r (ci, ti)
        | none => acc
      | _ => acc
  return (infos, s.commands, inputCtx.fileMap, input, errors)

/-- `n` without `Mise` and the namespace of its stage. -/
def shortName (n : Name) : String :=
  let n := n.replacePrefix `Mise .anonymous
  let n := [`Model, `Frontend, `Syntax, `Theorems].foldl (fun n ns => n.replacePrefix ns .anonymous) n
  n.toString

def main : MetaM Unit := do
  let env ← getEnv
  let out := (← IO.getEnv "MUTANTS_OUT").getD "test/out/trust-mutants/generated.json"
  let thms := Trusted.sortNames <| env.constants.fold (init := {}) fun s n ci =>
    match ci with
    | .thmInfo _ => if (`Mise.Theorems).isPrefixOf n && !n.isInternalDetail then s.insert n else s
    | _ => s
  let mut trusted : NameMap NameSet := {}
  let mut signs : NameMap (NameMap Signs) := {}
  let mut targets : NameSet := {}
  for t in thms do
    let some (.thmInfo ti) := env.find? t | continue
    let tr := Trusted.trustedOf env t
    trusted := trusted.insert t tr
    targets := tr.foldl (·.insert ·) targets
    signs := signs.insert t (← signsOf ti.type)
  -- Targets by source file.
  let mut byFile : Std.HashMap String (Array (Name × Position)) := {}
  for d in Trusted.sortNames targets do
    let some idx := env.getModuleIdxFor? d | continue
    let mod := env.header.moduleNames[idx.toNat]!
    let some r ← findDeclarationRanges? d | continue
    let path := mod.toString.replace "." "/" ++ ".lean"
    byFile := byFile.insert path ((byFile.getD path #[]).push (d, r.selectionRange.pos))
  let mut st : GState := {}
  let mut rows : Array Json := #[]
  for (path, decls) in byFile.toArray.qsort (·.1 < ·.1) do
    let (infos, cmds, fm, src, errors) ← elabFile path
    if errors > 0 then throwError "MutantGen: {path} has {errors} errors when elaborated again"
    for (d, pos) in decls do
      let b := (fm.ofPosition pos).byteIdx
      let inside (c : Syntax) : Bool := match range? c with
        | some (x, y) => x ≤ b && b < y
        | none => false
      let some cmd := cmds.find? inside | continue
      let before := st.edits.size
      let ((), st') ← ((walkDecl cmd).run { src, fileMap := fm, infos, decl := d }).run st
      st := st'
      let mut seen : Std.HashSet (Nat × Nat × String) := {}
      -- Name each edit by its kind and its place among the edits of that
      -- kind in the declaration, in source order: line numbers differ
      -- between the real tree and the copy, whose proofs are replaced.
      let mut count : Std.HashMap String Nat := {}
      let edits := (st.edits.extract before st.edits.size).qsort fun x y =>
        x.start < y.start || x.start == y.start && x.stop < y.stop
      for e in edits do
        if seen.contains (e.start, e.stop, e.text) then continue
        seen := seen.insert (e.start, e.stop, e.text)
        let k := count.getD e.kind 0 + 1
        count := count.insert e.kind k
        let mut effects : Array (String × Json) := #[]
        let mut keep := false
        for t in thms do
          if !((trusted.find? t).getD {}).contains d then continue
          let sg := (((signs.find? t).getD {}).find? d).map (·.pol) |>.getD 0
          let v := if e.eff == 0 || sg == 0 then "unknown" else if e.eff * sg > 0 then "weaker" else "stronger"
          if v != "stronger" then keep := true
          effects := effects.push ((t.replacePrefix `Mise.Theorems .anonymous).toString, toJson v)
        let name := s!"{shortName d}:{e.kind}.{k}"
        rows := rows.push <| Json.mkObj [
          ("name", toJson name), ("decl", toJson (shortName d)), ("file", toJson path),
          ("start", toJson e.start), ("stop", toJson e.stop), ("text", toJson e.text),
          ("kind", toJson e.kind), ("what", toJson e.what), ("line", toJson e.line),
          ("eff", toJson e.eff), ("effects", Json.mkObj effects.toList), ("keep", toJson keep)]
  let polarity := Json.mkObj <| (Trusted.sortNames targets).toList.map fun d =>
    (shortName d, Json.mkObj <| thms.toList.filterMap fun t =>
      if !((trusted.find? t).getD {}).contains d then none
      else
        let sg := (((signs.find? t).getD {}).find? d).getD (true, true)
        some ((t.replacePrefix `Mise.Theorems .anonymous).toString, toJson sg.show))
  IO.FS.createDirAll (System.FilePath.mk out).parent.get!
  IO.FS.writeFile out (Json.mkObj [("mutants", Json.arr rows), ("polarity", polarity)]).pretty
  let kept := rows.filter fun r => (r.getObjValAs? Bool "keep").toOption == some true
  IO.println s!"{rows.size} edits, {kept.size} kept, over {targets.size} declarations; wrote {out}"

end MutantGen

#eval MutantGen.main
