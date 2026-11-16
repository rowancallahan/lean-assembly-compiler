/- Higher-order arguments by specialisation (NOTES §27).

`frontx_hof h`: in the body of `h`, every call `F a₁ … aₙ` of a recursive definition `F` (`List.map`, `foldl`,
`foldr`, `filter`, `any`, `all`, `find?`, a user higher-order definition, …) where some argument is a function
known at compile time (a lambda, a named function, a partial application, `f ∘ g`; it may capture first-order
variables of `h`, which become parameters) is replaced by a call of a FIRST-ORDER copy `h.hof<k>`:

  `h.hof<k> c₁ … cₘ y₁ … yₚ := F a₁ … aₙ`  (the `cᵢ` captured variables, the `yⱼ` the arguments that are not fixed)
  `h.hof<k>.eq : h.hof<k> c y = <F's unfolding equation at a, recursive calls with the same fixed arguments folded
                                 to h.hof<k>, the known function applied and beta-reduced>`

and `h.hof : h ys = <h's body with the calls replaced>`.  Calls of non-recursive user definitions with a known
function argument are unfolded (`Array.find arr p := findHelper arr p 0`); `Function.comp` is unfolded when applied;
`Array.foldl f a xs` is first rewritten to `xs.toList.foldl f a` (`Array.foldl_toList`).  Calls nested in a copy's
body (or in a known function) are specialised in turn.  Every equation is kernel-checked: the copies are definitions
and the equations are Lean's own unfolding equations of `F` and `h` (the folding is definitional), apart from the
rewriting steps, which are `simp` proofs (`hofSimp`).  So the existing translators compile the copies, and their
theorems transport along `h.hof` to the original `h`.

`frontx_hof_entry g [measure μ]` (for `g : ByteArray → R` whose body is one higher-order call on `xs.data.toList`,
`xs.data.toList.map UInt8.toNat` or `xs.data`): `frontx_hof g`, then the copy as a function of the input block
(`frontx_view`, or `h.hof<k>.ba` for an `Array UInt8` parameter), `frontx_compile` with the measure (default
`B.size - i`), `g.hof.entry : g xs = <copy> xs 0 …` (`rfl`), and `frontx_entry g from g.hof.entry`. -/
import Lean
import Riscv.Frontx.Translate

namespace Proven.Frontx
open Lean Meta Elab Term Command

/-- unfolding equations with the function argument outside the `match` (Lean's `List.any`/`all` match on it too) -/
theorem hof_any_eq {α : Type u} (l : List α) (p : α → Bool) :
    l.any p = match l with | [] => false | h :: t => p h || t.any p := by cases l <;> rfl
theorem hof_all_eq {α : Type u} (l : List α) (p : α → Bool) :
    l.all p = match l with | [] => true | h :: t => p h && t.all p := by cases l <;> rfl

theorem hof_flatMap_eq {α : Type u} {β : Type v} (f : α → List β) (l : List α) :
    l.flatMap f = match l with | [] => [] | x :: xs => f x ++ xs.flatMap f := by cases l <;> simp

/-- the unfolding equation used for `F` -/
def hofEqnFor (F : Name) : MetaM (Option Name) := do
  if F == ``List.any then return some ``hof_any_eq
  if F == ``List.all then return some ``hof_all_eq
  if F == ``List.flatMap then return some ``hof_flatMap_eq
  getUnfoldEqnFor? F (nonRec := true)

/-- heads that are never specialised: control flow, matchers and recursors are handled by the translators -/
def hofSkip : List Name :=
  [``ite, ``dite, ``cond, ``Decidable.decide, ``Function.comp, ``Bind.bind, ``Pure.pure, ``Exists, ``Subtype,
   ``Id.run, ``letFun, ``Eq.mpr, ``Eq.mp, ``cast, ``Eq.rec, ``Eq.ndrec, ``absurd, ``False.elim, ``WellFounded.fix]

/-- core definitions that are unfolded (non-recursive wrappers around a recursive one) -/
def hofUnfold : List Name := [``List.countP, ``List.count]

/-- an argument whose type returns a sort (a motive, a type family) -/
def returnsSort (ty : Expr) : MetaM Bool := forallTelescopeReducing ty fun _ b => return (← whnfR b).isSort

/-- a function known at compile time: function-typed, not a proof / type family, and no free variable of it is a
function (an unknown function parameter of the caller) -/
def knownFn (a : Expr) : MetaM Bool := do
  let ty ← whnfR (← inferType a)
  unless ty.isForall do return false
  if ← isProof a then return false
  if ← returnsSort ty then return false
  for fv in (collectFVars {} a).fvarIds do
    let t ← whnfR (← fv.getType)
    if t.isForall && !(← isProp t) then return false
  return true

/-- `Function.comp f g x` ↦ `f (g x)`, beta -/
def unfoldComp (e : Expr) : Expr :=
  (e.replace fun e =>
    if e.isAppOf ``Function.comp && e.getAppNumArgs ≥ 6 then
      let a := e.getAppArgs
      some (mkAppN (mkApp a[3]! (mkApp a[4]! a[5]!)) (a.extract 6 a.size))
    else none).headBeta

structure HofSt where
  /-- specialisations made so far: (`F`, fixed arguments abstracted over the captured variables) ↦ copy -/
  cache : Array (Name × Expr × Name) := #[]
  count : Nat := 0
  log : Array MessageData := #[]

abbrev HofM := StateRefT HofSt TermElabM

/-- the fixed positions of a call `F args`: types, instances, proofs, known functions (and everything they depend
on, i.e. arguments that occur in the type of a fixed one) -/
def fixedPos (F : Expr) (args : Array Expr) : MetaM (Array Bool) := do
  let fty ← inferType F
  let bis ← forallBoundedTelescope fty (some args.size) fun xs _ => xs.mapM fun x => x.fvarId!.getBinderInfo
  args.mapIdxM fun j a => do
    if bis[j]? == some .instImplicit then return true
    if (← isType a) || (← isProof a) then return true
    knownFn a

/-- a `simp only` rewrite of an equation's right-hand side with the given lemmas (`true`: right to left) and
definitions to unfold (their equation lemmas); returns the new side and a proof `rhs = rhs'` (none: unchanged) -/
def hofSimp (rhs : Expr) (lemmas : List (Name × Bool)) (unf : Array Name := #[]) (zeta := false) : TermElabM (Expr × Option Expr) := do
  let thms ← lemmas.foldlM (fun s (n, inv) => s.addConst n (inv := inv)) ({} : SimpTheorems)
  let thms ← unf.foldlM (fun s n => s.addDeclToUnfold n) thms
  let ctx ← Simp.mkContext (config := { zeta }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let (r, _) ← simp rhs ctx
  if r.expr == rhs then return (rhs, none)
  return (r.expr, some (← r.getProof))

/-- before specialising: `Array.foldl f a xs` ↦ `xs.toList.foldl f a`; a fold over a list literal unrolled; a `map`
fused into the consumer that follows it (one loop, no intermediate list) -/
def hofPre : List (Name × Bool) :=
  [(``Array.foldl_toList, true), (``List.foldl_nil, false), (``List.foldl_cons, false), (``List.map_map, false),
   (``List.foldl_map, false), (``List.foldr_map, false), (``List.any_map, false), (``List.all_map, false),
   (``List.countP_map, false)]
/-- `a || r` / `a && r` whose `r` holds a recursive call (marked by `hofMark`, definitionally): as `if`s, so the call
is a tail call -/
def hofOr (a b : Bool) : Bool := a || b
def hofAnd (a b : Bool) : Bool := a && b
theorem hof_or (a b : Bool) : hofOr a b = (if a = true then true else b) := by cases a <;> rfl
theorem hof_and (a b : Bool) : hofAnd a b = (if a = true then b else false) := by cases a <;> rfl

partial def hofMark (c : Name) (e : Expr) : Expr :=
  e.replace fun e =>
    if (e.isAppOfArity ``or 2 || e.isAppOfArity ``and 2) && (e.appArg!.find? (·.isConstOf c)).isSome then
      some (mkApp2 (mkConst (if e.isAppOfArity ``or 2 then ``hofOr else ``hofAnd)) (hofMark c e.appFn!.appArg!)
        (hofMark c e.appArg!))
    else none

theorem hof_some_bind {α β : Type u} (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl

theorem hof_option_failure {α : Type u} : (failure : Option α) = none := rfl

/-- after: list literals appended (`f x ++ r` with `f x = [a, b]`); `a || r`, `a && r` as `if`s (tail calls); `do` in `Option` (`pure`, `failure`, the join
points of `do` inlined) -/
def hofPost : List (Name × Bool) := [(``List.cons_append, false), (``List.nil_append, false), (``pure_bind, false),
  (``Option.pure_def, false), (``hof_option_failure, false), (``hof_some_bind, false), (``hof_or, false), (``hof_and, false), (``cond_eq_if, false)]

/-- `rhs` rewritten by `hofSimp`, then the proof `lhs = rhs` (`pf`) extended -/
def hofSimpEq (pf rhs : Expr) (lemmas : List (Name × Bool)) (unf : Array Name := #[]) (zeta := false) : TermElabM (Expr × Expr) := do
  let (rhs', np?) ← hofSimp rhs lemmas unf zeta
  match np? with
  | none => return (rhs, pf)
  | some np => return (rhs', ← mkEqTrans pf np)

/-- user definitions applied in `e` to a closed constructor term (a stage, a byte expression, a predicate known
at compile time): they are evaluated by their equation lemmas (partial evaluation of an interpreter on a known
program) -/
partial def evalConsts (skip : Name → Bool) (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let rec go (e : Expr) (acc : Array Name) : MetaM (Array Name) := do
    match e with
    | .app .. =>
      let acc ← e.getAppArgs.foldlM (fun acc a => go a acc) acc
      let some c := e.getAppFn.constName? | go e.getAppFn acc
      if acc.contains c || skip c then return acc
      unless (← userConst c) && (env.find? c matches some (.defnInfo _)) do return acc
      if (← isMatcher c) || isAuxRecursor env c then return acc
      let closedCtor (a : Expr) : Bool := !a.hasLooseBVars && !a.hasFVar &&
        (a.getAppFn.constName?.map env.isConstructor).getD false
      return if e.getAppArgs.any closedCtor then acc.push c else acc
    | .lam _ t b _ | .forallE _ t b _ => go b (← go t acc)
    | .letE _ t v b _ => go b (← go v (← go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b acc
    | _ => return acc
  go e #[]

/-- rewrite with `lemmas` and evaluate (`evalConsts`) until nothing changes -/
def hofEvalEq (skip : Name → Bool) (pf rhs : Expr) (lemmas : List (Name × Bool) := []) (zeta := false) : TermElabM (Expr × Expr) := do
  let mut rhs := rhs
  let mut pf := pf
  for _ in [0:16] do
    let cs ← evalConsts skip rhs
    let (rhs', pf') ← hofSimpEq pf rhs lemmas cs zeta
    if rhs' == rhs then break
    unless cs.isEmpty do logInfo m!"frontx_hof: evaluated {cs} on known arguments"
    rhs := rhs'; pf := pf'
  return (rhs, pf)

/-- for a matcher `m` on one `Bool` with two alternatives without variables: the lemma
`m.hof_ite : m (fun _ => α) b x y = if b = true then x () else y ()` (proved by cases), added once -/
def boolMatchLemma (m : Name) : TermElabM (Option Name) := do
  let lN := m ++ `hof_ite
  if (← getEnv).contains lN then return some lN
  let some mi ← getMatcherInfo? m | return none
  unless mi.numDiscrs == 1 && mi.altNumParams.size == 2 && mi.altNumParams.all (· ≤ 1) do return none
  let info ← getConstInfo m
  let some ui := mi.uElimPos? | return none
  let lvlParam := Level.param `u
  let lvls := (info.levelParams.map fun _ => levelZero).set ui lvlParam
  let ty ← withLocalDeclD `α (mkSort lvlParam) fun α => withLocalDeclD `b (mkConst ``Bool) fun b => do
    let fty ← mkArrow (mkConst ``Unit) α
    withLocalDeclD `x fty fun x => withLocalDeclD `y fty fun y => do
      let motive ← withLocalDeclD `_d (mkConst ``Bool) fun d => mkLambdaFVars #[d] α
      let lhs := mkAppN (mkConst m lvls) #[motive, b, x, y]
      unless (← isTypeCorrect lhs) do throwError "frontx_hof: {m} does not fit"
      let c ← mkEq b (mkConst ``Bool.true)
      let rhs := mkAppN (mkConst ``ite [lvlParam]) #[α, c, ← synthInstance (mkApp (mkConst ``Decidable) c),
        mkApp x (mkConst ``Unit.unit), mkApp y (mkConst ``Unit.unit)]
      mkForallFVars #[α, b, x, y] (← mkEq lhs rhs)
  let ty ← instantiateMVars ty
  let s ← saveState
  try
    let pf ← byTac ty (← `(tactic| (intro _ b _ _; cases b <;> rfl)))
    addDecl (.thmDecl { name := lN, levelParams := [`u], type := ty, value := pf })
    return some lN
  catch _ => s.restore; return none

/-- the `Bool` matchers in `e` (with their `hof_ite` lemmas) -/
def boolMatchLemmas (e : Expr) : TermElabM (List (Name × Bool)) := do
  let mut out := []
  for c in e.getUsedConstants do
    if ← isMatcher c then
      if let some l ← boolMatchLemma c then out := (l, false) :: out
  return out

mutual
/-- replace the higher-order calls in `e` (under binders) by calls of first-order copies -/
partial def hofSites (owner : Name) (depth : Nat) (e : Expr) : HofM Expr := do
  let post (e : Expr) : HofM TransformStep := do
    let e := unfoldComp e
    let .const F lvls := e.getAppFn | return .done e
    if F == owner || hofSkip.contains F then return .done e
    let args := e.getAppArgs
    let env ← getEnv
    let some (.defnInfo _) := env.find? F | return .done e
    if (← isMatcher F) || isAuxRecursor env F || isRecCore env F || (← isProjectionFn F) then return .done e
    let fixed ← fixedPos (mkConst F lvls) args
    unless (← (List.range args.size).anyM fun j => do
      return fixed[j]! && !(← isType args[j]!) && !(← isProof args[j]!) && (← knownFn args[j]!)) do return .done e
    -- non-recursive: unfold (user definitions and the wrappers in `hofUnfold`)
    let some eqn ← hofEqnFor F | return .done e
    let eqnInfo ← getConstInfo eqn
    let eqTy := eqnInfo.type.instantiateLevelParams eqnInfo.levelParams lvls
    let some (_, _, rhs) := (← instantiateForall eqTy args).eq? | return .done e
    let isRec := (rhs.find? (·.isConstOf F)).isSome
    unless isRec do
      unless (← userConst F) || hofUnfold.contains F do return .done e
      modify fun s => { s with log := s.log.push m!"unfolded {F}" }
      return .visit (unfoldComp (← Core.betaReduce rhs))
    if depth > 8 then throwError "frontx_hof: specialisation of {F} does not terminate (depth 8)"
    return .done (← specialise owner depth F lvls args fixed)
  Meta.transform e (post := post)

/-- the copy for one call `F args` (fixed positions `fixed`): defined, its equation proved, the call returned -/
partial def specialise (owner : Name) (depth : Nat) (F : Name) (lvls : List Level) (args : Array Expr)
    (fixed : Array Bool) : HofM Expr := do
  -- captured variables: the free variables of the fixed arguments (and of their types), in context order
  let mut fvs : FVarIdSet := {}
  for j in [0:args.size] do
    if fixed[j]! then fvs := (collectFVars {} args[j]!).fvarIds.foldl (·.insert ·) fvs
  let lctx ← getLCtx
  let mut changed := true
  while changed do
    changed := false
    for fv in fvs.toList do
      for fv' in (collectFVars {} (← instantiateMVars (← fv.getType))).fvarIds do
        unless fvs.contains fv' do fvs := fvs.insert fv'; changed := true
  let caps := (fvs.toArray.qsort fun a b => (lctx.get! a).index < (lctx.get! b).index).map mkFVar
  let key ← mkLambdaFVars caps (mkAppN (mkConst F lvls) ((args.zip fixed).map fun (a, f) => if f then a else mkConst ``Unit.unit))
  let vpos := (List.range args.size).filter (!fixed[·]!)
  if let some (_, _, cN) := (← get).cache.find? fun (F', k, _) => F' == F && k == key then
    return mkAppN (mkConst cN) (caps ++ vpos.toArray.map (args[·]!))
  let k := (← get).count + 1
  modify fun s => { s with count := k }
  let cN := owner ++ Name.mkSimple s!"hof{k}"
  modify fun s => { s with cache := s.cache.push (F, key, cN) }
  -- the copy `cN caps ys := F args[ys]`
  let ytys ← vpos.toArray.mapM fun j => inferType args[j]!
  let (cTy, cVal) ← withLocalDeclsDND (vpos.toArray.mapIdx fun i _ => (Name.mkSimple s!"y{i}", ytys[i]!)) fun ys => do
    let args' := Id.run do
      let mut a := args
      for (j, y) in vpos.zip ys.toList do a := a.set! j y
      a
    let body := mkAppN (mkConst F lvls) args'
    return (← mkForallFVars (caps ++ ys) (← inferType body), ← mkLambdaFVars (caps ++ ys) body)
  addAndCompile (.defnDecl (mkDefinitionValEx cN [] cTy cVal (.regular 1) .safe [cN]))
  enableRealizationsForConst cN
  -- its equation: `F`'s unfolding equation, the recursive calls with the same fixed arguments folded
  let some eqn ← hofEqnFor F | throwError "frontx_hof: no unfolding equation for {F}"
  let eqnInfo ← getConstInfo eqn
  let eqTy := eqnInfo.type.instantiateLevelParams eqnInfo.levelParams lvls
  let (ty, pf) ← forallTelescope cTy fun xs _ => do
    let cs := xs.extract 0 caps.size
    let ys := xs.extract caps.size xs.size
    let sub (e : Expr) := e.replaceFVars caps cs
    let args' := Id.run do
      let mut a := args.map sub
      for (j, y) in vpos.zip ys.toList do a := a.set! j y
      a
    let some (_, _, rhs) := (← instantiateForall eqTy args').eq? | throwError "frontx_hof: bad equation of {F}"
    let rhs := rhs.replace fun e =>
      if e.isAppOfArity F args'.size then
        let ea := e.getAppArgs
        if (List.range args'.size).all fun j => !fixed[j]! || ea[j]! == args'[j]! then
          some (mkAppN (mkConst cN) (cs ++ vpos.toArray.map (ea[·]!)))
        else none
      else none
    let rhs := unfoldComp (← Core.betaReduce rhs)
    let lhs := mkAppN (mkConst cN) xs
    let pf0 ← mkExpectedTypeHint (mkAppN (mkConst eqn lvls) args') (← mkEq lhs rhs)
    let cache := (← get).cache
    let skip (n : Name) := n == cN || n == owner || cache.any (·.2.2 == n)
    let (rhs, pf) ← hofEvalEq skip pf0 rhs
    -- nested higher-order calls (in the known function's body, now inlined)
    let rhs' := hofMark cN (← hofSites cN (depth + 1) rhs)
    let pf ← mkExpectedTypeHint pf (← mkEq lhs rhs')
    let (rhs, pf) ← hofEvalEq skip pf rhs' (hofPost ++ (← boolMatchLemmas rhs')) (zeta := true)
    if (rhs.find? (·.isConstOf F)).isSome then
      throwError "frontx_hof: a recursive call of {F} changes a fixed argument{indentExpr rhs}"
    return (← mkForallFVars xs (← mkEq lhs rhs), ← mkLambdaFVars xs pf)
  let ty ← instantiateMVars ty
  let pf ← instantiateMVars pf
  addDecl (.thmDecl { name := cN ++ `eq, levelParams := [], type := ty, value := pf })
  modify fun s => { s with log := s.log.push m!"{cN} := {F} at the fixed arguments; {cN ++ `eq} : {ty}" }
  return mkAppN (mkConst cN) (caps ++ vpos.toArray.map (args[·]!))
end

/-- `frontx_hof h`; returns the right-hand side of `h.hof` and the copies -/
def hofRun (hN : Name) : TermElabM (Expr × Array Name) := do
  let info ← getConstInfoDefn hN
  unless info.levelParams.isEmpty do throwError "frontx_hof: {hN} is universe polymorphic"
  let some eqn ← getUnfoldEqnFor? hN (nonRec := true) | throwError "frontx_hof: no unfolding equation for {hN}"
  let eqTy := (← getConstInfo eqn).type
  let act : HofM (Expr × Expr × Expr) := forallTelescope eqTy fun xs body => do
    let some (_, lhs, rhs) := body.eq? | throwError "frontx_hof: bad equation of {hN}"
    let (rhs1, pf1) ← (hofEvalEq (· == hN) (mkAppN (mkConst eqn) xs) rhs hofPre : TermElabM _)
    let rhs' ← hofSites hN 0 rhs1
    if rhs' == rhs1 then throwError "frontx_hof: no call with a known function argument in {hN}{indentExpr rhs}"
    let pf ← mkExpectedTypeHint pf1 (← mkEq lhs rhs')
    return (← mkForallFVars xs (← mkEq lhs rhs'), ← mkLambdaFVars xs pf, ← mkLambdaFVars xs rhs')
  let ((ty, pf, rhs), st) ← act.run {}
  let ty ← instantiateMVars ty
  addDecl (.thmDecl { name := hN ++ `hof, levelParams := [], type := ty, value := ← instantiateMVars pf })
  for m in st.log do logInfo m!"frontx_hof: {m}"
  logInfo m!"frontx_hof: {hN ++ `hof} : {ty}"
  return (rhs, st.cache.map (·.2.2))

elab "frontx_hof " h:ident : command => liftTermElabM do
  discard <| hofRun (← realizeGlobalConstNoOverloadWithInfo h)

/-- the copy `c` with its `Array UInt8` parameter (position `p`) as a byte array: `c.ba B …  := c … B.data …`,
`c.ba.eq` (sizes and reads of `B.data` are those of `B`, definitionally) -/
def hofByteArray (c : Name) (p : Nat) : TermElabM Name := do
  let info ← getConstInfoDefn c
  let gN := c ++ `ba
  let eqTy := (← getConstInfo (c ++ `eq)).type
  let (gTy, gVal, ty, pf) ← forallTelescope info.type fun xs res => do
    withLocalDeclD `B (mkConst ``ByteArray) fun B => do
      let ps := (xs.set! p B)
      let args := xs.set! p (mkApp (mkConst ``ByteArray.data) B)
      let gTy ← mkForallFVars ps res
      let gVal ← mkLambdaFVars ps (mkAppN (mkConst c) args)
      addAndCompile (.defnDecl (mkDefinitionValEx gN [] gTy gVal (.regular 1) .safe [gN]))
      enableRealizationsForConst gN
      let some (_, _, rhs) := (← instantiateForall eqTy args).eq? | throwError "frontx_hof: bad equation"
      let dB := mkApp (mkConst ``ByteArray.data) B
      let rhs ← Meta.transform rhs (post := fun e => do
        if e.isAppOfArity c xs.size && e.getAppArgs[p]! == dB then
          return .done (mkAppN (mkConst gN) (e.getAppArgs.set! p B))
        if e.isAppOfArity ``Array.size 2 && e.appArg! == dB then
          return .done (mkApp (mkConst ``ByteArray.size) B)
        if e.isAppOfArity ``GetElem.getElem 8 && e.getArg! 5 == dB then
          let a := e.getAppArgs
          return .done (mkAppN (mkConst ``GetElem.getElem [levelZero, levelZero, levelZero])
            #[mkConst ``ByteArray, mkConst ``Nat, mkConst ``UInt8,
              ← withLocalDeclD `xs (mkConst ``ByteArray) fun xs => withLocalDeclD `i (mkConst ``Nat) fun i => do
                mkLambdaFVars #[xs, i] (← mkAppM ``LT.lt #[i, mkApp (mkConst ``ByteArray.size) xs]),
              ← synthInstance (← mkAppM ``GetElem #[mkConst ``ByteArray, mkConst ``Nat, mkConst ``UInt8,
                ← withLocalDeclD `xs (mkConst ``ByteArray) fun xs => withLocalDeclD `i (mkConst ``Nat) fun i => do
                  mkLambdaFVars #[xs, i] (← mkAppM ``LT.lt #[i, mkApp (mkConst ``ByteArray.size) xs])]),
              B, a[6]!, a[7]!])
        return .done e)
      if (rhs.find? (· == dB)).isSome then throwError "frontx_hof: {B}.data is used otherwise{indentExpr rhs}"
      let lhs := mkAppN (mkConst gN) ps
      let pf ← mkExpectedTypeHint (mkAppN (mkConst (c ++ `eq)) args) (← mkEq lhs rhs)
      return (gTy, gVal, ← mkForallFVars ps (← mkEq lhs rhs), ← mkLambdaFVars ps pf)
  let _ := (gTy, gVal)
  addDecl (.thmDecl { name := gN ++ `eq, levelParams := [], type := ← instantiateMVars ty, value := ← instantiateMVars pf })
  logInfo m!"frontx_hof: {gN ++ `eq} : {ty}"
  return gN

syntax "frontx_hof_entry " ident (" measure " term)? (" with " term)? : command
elab_rules : command
  | `(frontx_hof_entry $g:ident $[measure $μ?]? $[with $inv?]?) => do
  let gN ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo g
  -- the specialisation, then the shape of the entry's body: one call of a copy
  let (c, cmds, entryTy) ← liftTermElabM do
    let (rhs, _) ← hofRun gN
    lambdaTelescope rhs fun xs body => do
      unless xs.size == 1 && (← whnfR (← inferType xs[0]!)).isConstOf ``ByteArray do
        throwError "frontx_hof_entry: expected one ByteArray parameter"
      let B := xs[0]!
      let .const c _ := body.getAppFn | throwError "frontx_hof_entry: the body is not a call of a copy{indentExpr body}"
      unless (← getEnv).contains (c ++ `eq) do throwError "frontx_hof_entry: {c} is not a copy"
      let args := body.getAppArgs
      let dl ← mkAppM ``Array.toList #[mkApp (mkConst ``ByteArray.data) B]
      let dlN ← mkAppM ``List.map #[mkConst ``UInt8.toNat, dl]
      let some p ← (List.range args.size).findM? fun j => do
          return args[j]! == mkApp (mkConst ``ByteArray.data) B || (← isDefEq args[j]! dl) || (← isDefEq args[j]! dlN)
        | throwError "frontx_hof_entry: no argument is the input (`xs.data.toList`, `….map UInt8.toNat`, `xs.data`)"
      let others := (List.range args.size).filter (· != p) |>.map (args[·]!)
      if args[p]! == mkApp (mkConst ``ByteArray.data) B then
        let gc ← hofByteArray c p
        let rhs' := mkAppN (mkConst gc) (args.set! p B)
        return (gc, false, ← mkForallFVars xs (← mkEq (mkApp (mkConst gN) B) rhs'))
      else
        let vN := c ++ `view
        return (vN, true, ← mkForallFVars xs (← mkEq (mkApp (mkConst gN) B)
          (mkAppN (mkConst vN) (#[B, mkNatLit 0] ++ others.toArray))))
  let cI := mkIdent c
  if cmds then
    let cc := mkIdent (c.getPrefix)
    let ce := mkIdent (c.getPrefix ++ `eq)
    elabCommand (← `(frontx_view $cc from $ce))
  -- the measure: given, or `B.size - i` over all the copy's parameters
  let nps ← liftTermElabM do forallTelescope (← getConstInfo c).type fun xs _ => return xs.size
  let μ ← match μ? with
    | some μ => pure μ
    | none => do
      let us := (List.range (nps - 2)).toArray.map fun _ => mkIdent `_
      `(fun B i $us* => ByteArray.size B - i)
  let ceq := mkIdent (c ++ `eq)
  match inv? with
  | some inv => elabCommand (← `(frontx_compile $cI from $ceq measure $μ with $inv))
  | none => elabCommand (← `(frontx_compile $cI from $ceq measure $μ))
  let eN := gN ++ `hof ++ `entry
  liftTermElabM do
    let entryTy ← instantiateMVars entryTy
    let hI := mkIdent (gN ++ `hof)
    addThm eN entryTy (← `(tactic| (intros; rw [$hI:ident]; rfl)))
  let eI := mkIdent eN
  elabCommand (← `(frontx_entry $g from $eI))

end Proven.Frontx
