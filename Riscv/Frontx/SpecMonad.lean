/- Monads by specialisation (NOTES §29).

`frontx_monad h`: pure monadic code in a concrete monad (`Id`, `Except ε`, `Option`, `StateM σ`, `StateT σ (Except ε)`,
`ReaderT ρ m`, or a definition polymorphic in `[Monad m]` / `[MonadState σ m]` / `[MonadExcept ε m]` used at one
of them) becomes first-order code, the monad unfolded at compile time:

- a **site** is `StateT.run (F a) s` / `ReaderT.run (F a) r` (context with an extra value: the state, the
  environment), or `F a` whose type is `Except ε α` / `Option α` / `Id α` with an instance or a known function
  among its arguments, or `forIn l b f` over a list with a known body `f` (a `for x in l do` block);
- a recursive `F` gets a copy `h.mon<k> c₁ … cₘ y₁ … yₚ [s] := C[F a]` (`C` the context, `[s]` its extra value;
  `Id` stripped from the type), whose equation is `F`'s own unfolding equation under `C` (`congrArg`), the
  monad's `bind`/`pure`/`get`/`set`/`modify`/`read`/`throw`/`tryCatch` rewritten by Lean's `run` lemmas and the
  ones below (`simp`, kernel-checked), `C` pushed into `if`s and into `match`es (`monPushMatch`: proved by the
  matcher itself), and the recursive calls `C[F a']` with the same fixed arguments folded to the copy
  (definitional).  Non-recursive monadic definitions are unfolded (their equation lemmas).  So the state is an
  extra parameter and part of the result, `Except` the §16 tag-byte payload, and `for` a first-order loop.
- `h.mon : h ys = <h's body, the monad unfolded, the sites replaced>`; `frontx_monad_entry g` (as
  `frontx_hof_entry`) compiles the copy on the input and adds `g.mon.entry`, `frontx_entry g`.

Known functions (the predicate of `count p`) are specialised by the same step (§27's fixed positions). -/
import Lean
import Riscv.Frontx.SpecHof

namespace Proven.Frontx
open Lean Meta Elab Term Command

/-! ## The rewriting lemmas (all `rfl` or by cases) -/

section
universe u v w
variable {σ ρ ε α β : Type u} {m : Type u → Type v}

theorem mon_st_run_ite [Monad m] (c : Prop) [Decidable c] (a b : StateT σ m α) (s : σ) :
    (ite c a b).run s = ite c (a.run s) (b.run s) := by split <;> rfl
theorem mon_st_run_dite [Monad m] (c : Prop) [Decidable c] (a : c → StateT σ m α) (b : ¬c → StateT σ m α) (s : σ) :
    (dite c a b).run s = dite c (fun h => (a h).run s) (fun h => (b h).run s) := by split <;> rfl
theorem mon_rd_run_ite [Monad m] (c : Prop) [Decidable c] (a b : ReaderT ρ m α) (r : ρ) :
    (ite c a b).run r = ite c (a.run r) (b.run r) := by split <;> rfl
theorem mon_rd_run_dite [Monad m] (c : Prop) [Decidable c] (a : c → ReaderT ρ m α) (b : ¬c → ReaderT ρ m α) (r : ρ) :
    (dite c a b).run r = dite c (fun h => (a h).run r) (fun h => (b h).run r) := by split <;> rfl
theorem mon_ite_bind [Monad m] (c : Prop) [Decidable c] (a b : m α) (f : α → m β) :
    (ite c a b >>= f) = ite c (a >>= f) (b >>= f) := by split <;> rfl
theorem mon_dite_bind [Monad m] (c : Prop) [Decidable c] (a : c → m α) (b : ¬c → m α) (f : α → m β) :
    (dite c a b >>= f) = dite c (fun h => a h >>= f) (fun h => b h >>= f) := by split <;> rfl
theorem mon_fst_ite (c : Prop) [Decidable c] (a b : α × β) : (ite c a b).1 = ite c a.1 b.1 := by split <;> rfl
theorem mon_snd_ite (c : Prop) [Decidable c] (a b : α × β) : (ite c a b).2 = ite c a.2 b.2 := by split <;> rfl

theorem mon_mfst_ite (c : Prop) [Decidable c] (a b : MProd α β) : (ite c a b).1 = ite c a.1 b.1 := by split <;> rfl
theorem mon_msnd_ite (c : Prop) [Decidable c] (a b : MProd α β) : (ite c a b).2 = ite c a.2 b.2 := by split <;> rfl
theorem mon_mfst_mk (a : α) (b : β) : (MProd.mk a b).1 = a := rfl
theorem mon_msnd_mk (a : α) (b : β) : (MProd.mk a b).2 = b := rfl
theorem mon_fst_mk (a : α) (b : β) : (a, b).1 = a := rfl
theorem mon_snd_mk (a : α) (b : β) : (a, b).2 = b := rfl

theorem mon_id_pure (a : α) : (pure a : Id α) = a := rfl
theorem mon_id_bind (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl
theorem mon_id_run (x : Id α) : Id.run x = x := rfl
theorem mon_id_map (f : α → β) (x : Id α) : (f <$> x) = f x := rfl

theorem mon_exc_pure (a : α) : (pure a : Except ε α) = .ok a := rfl
theorem mon_exc_ok_bind (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl
theorem mon_exc_error_bind (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e := rfl
theorem mon_exc_throw (e : ε) : (throw e : Except ε α) = .error e := rfl
theorem mon_exc_try_ok (a : α) (h : ε → Except ε α) : tryCatch (Except.ok a) h = .ok a := rfl
theorem mon_exc_try_error (e : ε) (h : ε → Except ε α) : tryCatch (Except.error e) h = h e := rfl
theorem mon_exc_try_ite (c : Prop) [Decidable c] (a b : Except ε α) (h : ε → Except ε α) :
    tryCatch (ite c a b) h = ite c (tryCatch a h) (tryCatch b h) := by split <;> rfl
theorem mon_exc_map_ok (f : α → β) (a : α) : (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl
theorem mon_exc_map_error (f : α → β) (e : ε) : (f <$> (Except.error e : Except ε α)) = .error e := rfl

theorem mon_opt_pure (a : α) : (pure a : Option α) = some a := rfl
theorem mon_opt_some_bind (a : α) (f : α → Option β) : (some a >>= f) = f a := rfl
theorem mon_opt_none_bind (f : α → Option β) : ((none : Option α) >>= f) = none := rfl
theorem mon_opt_failure : (failure : Option α) = none := rfl

theorem mon_st_run_throw (e : ε) (s : σ) : (throw e : StateT σ (Except ε) α).run s = .error e := rfl
theorem mon_st_run_try (x : StateT σ (Except ε) α) (h : ε → StateT σ (Except ε) α) (s : σ) :
    (tryCatch x h).run s = tryCatch (x.run s) (fun e => (h e).run s) := rfl
theorem mon_rd_run_throw (e : ε) (r : ρ) : (throw e : ReaderT ρ (Except ε) α).run r = .error e := rfl
theorem mon_rd_run_try (x : ReaderT ρ (Except ε) α) (h : ε → ReaderT ρ (Except ε) α) (r : ρ) :
    (tryCatch x h).run r = tryCatch (x.run r) (fun e => (h e).run r) := rfl
theorem mon_st_run_lift_exc (x : Except ε α) (s : σ) :
    (liftM x : StateT σ (Except ε) α).run s = (x >>= fun a => .ok (a, s)) := rfl
theorem mon_st_run_monadLift_exc (x : Except ε α) (s : σ) :
    (monadLift x : StateT σ (Except ε) α).run s = (x >>= fun a => .ok (a, s)) := rfl
theorem mon_rd_run_monadLift_exc (x : Except ε α) (r : ρ) :
    (monadLift x : ReaderT ρ (Except ε) α).run r = x := by cases x <;> rfl
theorem mon_rd_run_read [Monad m] (r : ρ) : (read : ReaderT ρ m ρ).run r = pure r := rfl
theorem mon_rd_run_readThe [Monad m] (r : ρ) : (readThe ρ : ReaderT ρ m ρ).run r = pure r := rfl
theorem mon_st_run_getThe [Monad m] (s : σ) : (getThe σ : StateT σ m σ).run s = pure (s, s) := rfl
theorem mon_st_run_modifyThe [Monad m] (f : σ → σ) (s : σ) :
    (modifyThe σ f : StateT σ m PUnit).run s = pure (⟨⟩, f s) := rfl

theorem mon_rd_run_modify {σ : Type u} [Monad m] [MonadStateOf σ m] (f : σ → σ) (r : ρ) :
    (modify f : ReaderT ρ m PUnit).run r = (modify f : m PUnit) := rfl
theorem mon_rd_run_get {σ : Type u} [Monad m] [MonadStateOf σ m] (r : ρ) :
    (get : ReaderT ρ m σ).run r = (get : m σ) := rfl
theorem mon_rd_run_set {σ : Type u} [Monad m] [MonadStateOf σ m] (x : σ) (r : ρ) :
    (set x : ReaderT ρ m PUnit).run r = (set x : m PUnit) := rfl
theorem mon_rd_run_throwSt (e : ε) (r : ρ) : (throw e : ReaderT ρ (StateT σ (Except ε)) α).run r = throw e := rfl

theorem mon_et_run_ite [Monad m] (c : Prop) [Decidable c] (a b : ExceptT ε m α) :
    (ite c a b).run = ite c a.run b.run := by split <;> rfl
theorem mon_et_run_monadLift [Monad m] (x : m α) : (monadLift x : ExceptT ε m α).run = Except.ok <$> x := rfl
theorem mon_opt_map_some (f : α → β) (a : α) : (f <$> some a) = some (f a) := rfl
theorem mon_opt_map_bind (f : α → β) (x : Option α) (g : β → Option γ) :
    ((f <$> x) >>= g) = x >>= fun a => g (f a) := by cases x <;> rfl
theorem mon_opt_bind_pure (x : Option α) : (x >>= fun a => some a) = x := by cases x <;> rfl

/-- an `ExceptT ε m` action bound in `m` (`match ← action with …` of `runCatch`): its `run` (definitional) -/
theorem mon_bind_et_ite [Monad m] (c : Prop) [Decidable c] (a b : ExceptT ε m α) (k : Except ε α → m β) :
    ((ite c a b : ExceptT ε m α) >>= k : m β) = (ExceptT.run (ite c a b) >>= k) := rfl
theorem mon_bind_et_bind [Monad m] (x : ExceptT ε m γ) (f : γ → ExceptT ε m α) (k : Except ε α → m β) :
    (((x >>= f : ExceptT ε m α)) >>= k : m β) = (ExceptT.run (x >>= f) >>= k) := rfl

/-- a `StateT` action applied to a state as a function (`block 0`): its `run` -/
theorem mon_st_bind_app [Monad m] (x : StateT σ m α) (f : α → StateT σ m β) (s : σ) :
    (x >>= f) s = (x >>= f).run s := rfl

/-- `for x in l do` as a `match` on the list (the loop's unfolding equation) -/
theorem mon_forIn_list_eq {γ : Type w} [Monad m] (l : List γ) (b : β) (f : γ → β → m (ForInStep β)) :
    forIn l b f = match l with
      | [] => pure b
      | a :: as => f a b >>= fun r => match r with
        | .done b => pure b
        | .yield b => forIn as b f := by
  cases l
  · rfl
  · exact List.forIn_cons _ _ _ _
end

/-- the lemma set; the `run` lemmas of Lean core and the ones above -/
def monLemmas : List (Name × Bool) :=
  [(``StateT.run_bind, false), (``StateT.run_pure, false), (``StateT.run_get, false), (``StateT.run_set, false),
   (``StateT.run_modify, false), (``StateT.run_modifyGet, false), (``StateT.run_map, false),
   (``ReaderT.run_bind, false), (``ReaderT.run_pure, false), (``ReaderT.run_read, false), (``ReaderT.run_map, false),
   (``mon_st_run_ite, false), (``mon_st_run_dite, false), (``mon_rd_run_ite, false), (``mon_rd_run_dite, false),
   (``mon_ite_bind, false), (``mon_dite_bind, false), (``mon_fst_ite, false), (``mon_snd_ite, false),
   (``mon_mfst_ite, false), (``mon_msnd_ite, false), (``mon_mfst_mk, false), (``mon_msnd_mk, false),
   (``mon_fst_mk, false), (``mon_snd_mk, false),
   (``mon_id_pure, false), (``mon_id_bind, false), (``mon_id_run, false), (``mon_id_map, false),
   (``mon_exc_pure, false), (``mon_exc_ok_bind, false), (``mon_exc_error_bind, false), (``mon_exc_throw, false),
   (``mon_exc_try_ok, false), (``mon_exc_try_error, false), (``mon_exc_try_ite, false),
   (``mon_exc_map_ok, false), (``mon_exc_map_error, false),
   (``mon_opt_pure, false), (``mon_opt_some_bind, false), (``mon_opt_none_bind, false), (``mon_opt_failure, false),
   (``mon_st_run_throw, false), (``mon_st_run_try, false), (``mon_rd_run_throw, false), (``mon_rd_run_try, false),
   (``mon_st_run_lift_exc, false), (``mon_st_run_monadLift_exc, false), (``mon_rd_run_monadLift_exc, false),
   (``mon_rd_run_read, false), (``mon_rd_run_readThe, false), (``mon_st_run_getThe, false),
   (``mon_st_run_modifyThe, false), (``mon_rd_run_modify, false), (``mon_rd_run_get, false),
   (``mon_rd_run_set, false), (``mon_rd_run_throwSt, false),
   (``ExceptT.run_bind, false), (``ExceptT.run_pure, false), (``ExceptT.run_throw, false),
   (``mon_et_run_ite, false), (``mon_bind_et_ite, false), (``mon_bind_et_bind, false), (``mon_et_run_monadLift, false), (``mon_opt_map_some, false),
   (``mon_opt_map_bind, false), (``mon_opt_bind_pure, false), (``bind_pure, false),
   (``mon_st_bind_app, false), (``List.forIn_cons, false), (``List.forIn_nil, false),
   (``pure_bind, false), (``bind_assoc, false), (``Function.comp_apply, false), (``cond_eq_if, false)]

/-! ## Pushing a context into a `match` -/

/-- `C[match d with | pᵢ => aᵢ]` ↦ `match d with | pᵢ => C[aᵢ]` for the argument `pos` of `e` (motive made constant),
proved by the matcher itself with the motive `fun d => C[match d …] = match d …` (each alternative `rfl`: a matcher
reduces on its own patterns) -/
def pushMatchCtx (ctx : Expr → Expr) (x ety : Expr) : MetaM (Option (Expr × Expr)) := do
  let some ma ← matchMatcherApp? x | return none
  unless ma.remaining.isEmpty do return none
  let some ui := ma.uElimPos? | return none
  let mkMatcher (motiveBody : Array Expr → MetaM Expr) (lvl : Level) : MetaM Expr := do
    let f := mkAppN (mkConst ma.matcherName (ma.matcherLevels.set! ui lvl).toList) ma.params
    let .forallE _ mty _ _ ← whnfD (← inferType f) | throwError "pushMatch: matcher type"
    let motive ← forallTelescope mty fun ds _ => do mkLambdaFVars ds (← motiveBody ds)
    return mkApp f motive
  let m' := mkAppN (← mkMatcher (fun _ => pure ety) (← getLevel ety)) ma.discrs
  let mut alts' := #[]
  let mut fty ← inferType m'
  for alt in ma.alts do
    let .forallE _ aty b _ ← whnfD fty | throwError "pushMatch: alternative type"
    let a' ← forallTelescope aty fun ys _ => do mkLambdaFVars ys (ctx (mkAppN alt ys).headBeta)
    alts' := alts'.push a'
    fty := b.instantiate1 a'
  let rhs := mkAppN m' alts'
  let mOld := mkAppN (mkConst ma.matcherName ma.matcherLevels.toList) ma.params
  let mNew := m'.getAppFn
  let mNewPre := m'.getAppArgs.extract 0 (ma.params.size + 1)
  let pm ← mkMatcher (fun ds => do
      mkEq (ctx (mkAppN (mkApp mOld ma.motive) (ds ++ ma.alts))) (mkAppN mNew (mNewPre ++ ds ++ alts'))) levelZero
  let pm := mkAppN pm ma.discrs
  let mut pty ← inferType pm
  let mut palts := #[]
  for alt in ma.alts do
    let .forallE _ aty b _ ← whnfD pty | throwError "pushMatch: alternative type (proof)"
    let pa ← forallTelescope aty fun ys body => do
      mkLambdaFVars ys (← mkExpectedTypeHint (← mkEqRefl (ctx (mkAppN alt ys).headBeta)) body)
    palts := palts.push pa
    pty := b.instantiate1 pa
  return some (rhs, mkAppN pm palts)

def pushMatch (e : Expr) (pos : Nat) : MetaM (Option (Expr × Expr)) := do
  let args := e.getAppArgs
  let some x := args[pos]? | return none
  pushMatchCtx (fun y => mkAppN e.getAppFn (args.set! pos y)) x (← inferType e)

/-- contexts a `match` is pushed out of: head, position of the argument -/
def monPushHeads : List (Name × Nat) :=
  [(``StateT.run, 3), (``ReaderT.run, 3), (``Prod.fst, 2), (``Prod.snd, 2), (``Bind.bind, 4), (``Id.run, 1),
   (``ExceptT.run, 3), (``tryCatch, 4), (``Functor.map, 5), (``MProd.fst, 2), (``MProd.snd, 2)]

simproc_decl monPushMatch (_) := fun e => do
  let some c := e.getAppFn.constName? | return .continue
  -- a `match` on a `match` (constant motive): the outer one pushed into the inner one
  if let some ma ← matchMatcherApp? e then
    if ma.discrs.size == 1 && ma.remaining.isEmpty && (← isMatcherApp ma.discrs[0]!) then
      let mt ← instantiateMVars ma.motive
      if mt.isLambda && !mt.bindingBody!.hasLooseBVars then
        if let some (rhs, pf) ← pushMatch e (ma.params.size + 1) then
          return .visit { expr := rhs, proof? := some pf }
    return .continue
  let some (_, pos) := monPushHeads.find? (·.1 == c) | return .continue
  let some (rhs, pf) ← pushMatch e pos | return .continue
  return .visit { expr := rhs, proof? := some pf }

/-- `match (if c then a else b) with alts` ↦ `if c then match a with alts else match b with alts` (`apply_ite`;
the `match` on a constructor then reduces) -/
simproc_decl monMatchIte (_) := fun e => do
  let some ma ← matchMatcherApp? e | return .continue
  unless ma.discrs.size == 1 && ma.remaining.isEmpty do return .continue
  let d := ma.discrs[0]!
  unless d.isAppOfArity ``ite 5 do return .continue
  let f ← withLocalDeclD `d d.getAppArgs[0]! fun x => do
    mkLambdaFVars #[x] (mkAppN (mkAppN (mkAppN (mkConst ma.matcherName ma.matcherLevels.toList) ma.params)
      #[ma.motive, x]) ma.alts)
  let ety ← inferType e
  if (← inferType f).bindingBody!.hasLooseBVars then return .continue
  let da := d.getAppArgs
  let αl ← getLevel da[0]!
  let βl ← getLevel ety
  let pf := mkAppN (mkConst ``apply_ite [αl, βl]) #[da[0]!, ety, f, da[1]!, da[2]!, da[3]!, da[4]!]
  let rhs := mkAppN (mkConst ``ite [βl]) #[ety, da[1]!, da[2]!, (mkApp f da[3]!).headBeta, (mkApp f da[4]!).headBeta]
  return .visit { expr := rhs, proof? := some pf }

/-- `rhs` simplified by the monad lemmas (+ `extra`, definitions `unf` unfolded, `match`es pushed out),
`pf : lhs = rhs` extended -/
def monSimpEq (pf rhs : Expr) (extra : List (Name × Bool) := []) (unf : Array Name := #[]) :
    TermElabM (Expr × Expr) := do
  let thms ← (monLemmas ++ extra).foldlM (fun s (n, inv) => s.addConst n (inv := inv)) ({} : SimpTheorems)
  let thms ← unf.foldlM (fun s n => s.addDeclToUnfold n) thms
  let ctx ← Simp.mkContext (config := { zeta := true, maxSteps := 200000 }) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let procs : Simp.SimprocsArray := #[]
  let procs ← procs.add ``monPushMatch false
  let procs ← procs.add ``monMatchIte false
  let (r, _) ← simp rhs ctx (simprocs := procs)
  -- `Id T` ↦ `T` in the types (definitional), so that lemmas about `T` apply
  let e' := r.expr.replace fun e => if e.isAppOfArity ``Id 1 then some e.appArg! else none
  if e' == rhs then return (rhs, pf)
  let pf' ← if r.expr == rhs then pure pf else mkEqTrans pf (← r.getProof)
  let some (_, lhs, _) := (← inferType pf').eq? | throwError "monSimpEq: not an equation"
  return (e', ← mkExpectedTypeHint pf' (← mkEq lhs e'))

/-- §27's `Bool`-matcher lemmas, for the matchers whose discriminant is a `Bool` (others are skipped) -/
def monBoolMatchLemmas (e : Expr) : TermElabM (List (Name × Bool)) := do
  let mut out := []
  for c in e.getUsedConstants do
    if ← isMatcher c then
      let ty := (← getConstInfo c).type
      let isBool ← forallTelescope ty fun xs _ => do
        let some mi ← getMatcherInfo? c | return false
        let some d := xs[mi.numParams + 1]? | return false
        return (← whnfR (← inferType d)).isConstOf ``Bool
      if isBool then
        if let some l ← boolMatchLemma c then out := (l, false) :: out
  return out

/-! ## Sites and copies -/

/-- the context of a site: `run` (`StateT.run · s`, `ReaderT.run · r`: head, its arguments before the action, the
extra value) or bare -/
structure MonCtx where
  /-- the `run` layers, innermost first: head, its arguments before the action -/
  layers : Array (Name × List Level × Array Expr) := #[]

/-- `x` under the layers, with the extra values `ss` (innermost first) -/
def MonCtx.wrap (c : MonCtx) (ss : Array Expr) (x : Expr) : Expr := Id.run do
  let mut x := x
  for ((h, ls, pre), s) in c.layers.zip ss do x := mkAppN (mkConst h ls) (pre ++ #[x, s])
  return x

/-- `run` layers around an action: the action, the layers (innermost first), the extra values -/
partial def peelRuns (e : Expr) (c : MonCtx := {}) (ss : Array Expr := #[]) : Expr × MonCtx × Array Expr :=
  if e.isAppOfArity ``StateT.run 5 || e.isAppOfArity ``ReaderT.run 5 then
    match e.getAppFn with
    | .const h hl =>
      let (x, c', ss') := peelRuns (e.getArg! 3) {} #[]
      (x, { layers := c'.layers ++ #[(h, hl, e.getAppArgs.extract 0 3)] ++ c.layers }, ss' ++ #[e.getArg! 4] ++ ss)
    | _ => (e, c, ss)
  else (e, c, ss)

/-- `Id T` ↦ `T` -/
def stripId (t : Expr) : Expr := if t.isAppOfArity ``Id 1 then t.appArg! else t

/-- a monad application `m α` whose head is a concrete monad (so a site in bare context) -/
def concreteMonadTy (t : Expr) : MetaM Bool := do
  let t ← instantiateMVars t
  return t.isAppOfArity ``Except 2 || t.isAppOfArity ``Option 1 || t.isAppOfArity ``Id 1

/-- the definitions that are unfolded instead of specialised (non-recursive user definitions at a site) -/
abbrev MonM := StateRefT HofSt TermElabM

/-- §27's fixed positions, and type formers (the monad `m`) -/
def monFixedPos (F : Expr) (args : Array Expr) : MetaM (Array Bool) := do
  let fx ← fixedPos F args
  args.mapIdxM fun j a => do
    if fx[j]! then return true
    let t ← inferType a
    return (← whnfR t).isForall && (← returnsSort t)

/-- the unfolding equation of `F` (the loop of `forIn` over a list as a `match`) -/
def monEqnFor (F : Name) : MetaM (Option Name) := do
  if F == ``ForIn.forIn then return some ``mon_forIn_list_eq
  hofEqnFor F

/-- `F args` is a site: a user definition (or `forIn` over a list) with a known function or an instance among its
arguments, in a `run` context or with a concrete monadic type -/
def monSiteOk (F : Name) (lvls : List Level) (args : Array Expr) (ctx : MonCtx) : MetaM (Option (Array Bool)) := do
  let env ← getEnv
  if F == ``ForIn.forIn then
    -- `@forIn m ρ α inst β l b f` over a list
    unless args.size == 8 do return none
    unless (← whnfR (← inferType args[5]!)).isAppOfArity ``List 1 do return none
    unless ← knownFn args[7]! do return none
    return some #[true, true, true, true, true, false, false, true]
  let some (.defnInfo _) := env.find? F | return none
  if (← isMatcher F) || isAuxRecursor env F || isRecCore env F || (← isProjectionFn F) then return none
  if hofSkip.contains F then return none
  unless ← userConst F do return none
  let fixed ← monFixedPos (mkConst F lvls) args
  let bis ← forallBoundedTelescope (← inferType (mkConst F lvls)) (some args.size) fun xs _ =>
    xs.mapM fun x => x.fvarId!.getBinderInfo
  let hasInst := bis.any (· == .instImplicit)
  let hasFn ← (List.range args.size).anyM fun j => do
    return fixed[j]! && !(← isType args[j]!) && !(← isProof args[j]!) && (← knownFn args[j]!)
  if !ctx.layers.isEmpty || hasInst || hasFn then return some fixed
  return none

/-- `F`'s unfolding equation at the call `site`: its right-hand side and the proof `site = rhs` (the equation's
arguments and universe levels found by unification) -/
def monEqnAt (eqn : Name) (site : Expr) : MetaM (Option (Expr × Expr)) := do
  let info ← getConstInfo eqn
  let lvls ← mkFreshLevelMVarsFor info
  let (mvs, _, body) ← forallMetaTelescope (info.type.instantiateLevelParams info.levelParams lvls)
  let some (_, lhs, rhs) := body.eq? | return none
  unless ← isDefEq lhs site do return none
  let pf ← instantiateMVars (mkAppN (mkConst eqn lvls) mvs)
  let rhs ← instantiateMVars rhs
  if pf.hasExprMVar || rhs.hasExprMVar then return none
  return some (rhs, ← mkExpectedTypeHint pf (← mkEq site rhs))

mutual
/-- replace the sites in `e` by calls of the copies (or unfold non-recursive definitions: returned in `unf`) -/
partial def monSites (owner : Name) (depth : Nat) (e : Expr) : MonM (Expr × Array Name) := do
  let unf ← IO.mkRef (#[] : Array Name)
  let site (F : Name) (lvls : List Level) (args : Array Expr) (ctx : MonCtx) (ss : Array Expr) : MonM (Option Expr) := do
    if F == owner then return none
    let some fixed ← monSiteOk F lvls args ctx | do
      -- a non-recursive user definition whose body is monadic code (`Id.run do …`, `forIn`, `bind`): unfolded
      let isCopy := (← get).cache.any (·.2.2 == F) || (← getEnv).contains (F ++ `eq)
      if (← userConst F) && !isCopy && !(← isMatcher F) && ((← getEnv).find? F matches some (.defnInfo _)) then
        if let some eqn ← getUnfoldEqnFor? F (nonRec := true) then
          let ty := (← getConstInfo eqn).type
          let rt ← whnfR (← inferType (mkAppN (mkConst F lvls) args))
          let monadic := [``Id.run, ``ForIn.forIn, ``Bind.bind, ``StateT.run, ``ReaderT.run].any (fun c =>
            (ty.find? (·.isConstOf c)).isSome) ||
            [``Except, ``Option, ``StateT, ``ReaderT, ``ExceptT, ``Id].any rt.isAppOf
          let isRec ← forallTelescope ty fun _ b => return ((b.eq?.map (·.2.2)).bind (·.find? (·.isConstOf F))).isSome
          if monadic && !isRec then
            unf.modify (·.push F)
      return none
    let some eqn ← monEqnFor F | return none
    let some (rhs, _) ← monEqnAt eqn (mkAppN (mkConst F lvls) args) | return none
    unless (rhs.find? (·.isConstOf F)).isSome do
      unf.modify (·.push F)
      return none
    if depth > 8 then throwError "frontx_monad: specialisation of {F} does not terminate (depth 8)"
    return some (← monSpecialise owner depth F lvls args fixed ctx ss eqn)
  -- `StateT.run (F a) s`, `ReaderT.run (F a) r` (before the subterms)
  let pre (e : Expr) : MonM TransformStep := do
    let (x, c, ss) := peelRuns e
    if c.layers.isEmpty then return .continue
    let x := unfoldComp x
    if let .const F lvls := x.getAppFn then
      if let some r ← site F lvls x.getAppArgs c ss then
        return .done r
    return .continue
  let post (e : Expr) : MonM TransformStep := do
    let e := unfoldComp e
    let .const F lvls := e.getAppFn | return .done e
    -- a bare site has a type that is not a `run` context's monad
    let t ← whnfR (← inferType e)
    if t.isAppOf ``StateT || t.isAppOf ``ReaderT || t.isAppOf ``ExceptT then return .done e
    if let some r ← site F lvls e.getAppArgs {} #[] then return .done r
    return .done e
  let e' ← Meta.transform e (pre := pre) (post := post)
  return (e', ← unf.get)

/-- the copy for one site: defined, its equation proved, the site's replacement returned -/
partial def monSpecialise (owner : Name) (depth : Nat) (F : Name) (lvls : List Level) (args : Array Expr)
    (fixed : Array Bool) (ctx : MonCtx) (extraArr : Array Expr) (eqn : Name) : MonM Expr := do
  -- captured variables: the free variables of the fixed arguments (and of their types), in context order
  let mut fvs : FVarIdSet := {}
  for j in [0:args.size] do
    if fixed[j]! then fvs := (collectFVars {} args[j]!).fvarIds.foldl (·.insert ·) fvs
  for (_, _, pre) in ctx.layers do
    for a in pre do fvs := (collectFVars {} a).fvarIds.foldl (·.insert ·) fvs
  let lctx ← getLCtx
  let mut changed := true
  while changed do
    changed := false
    for fv in fvs.toList do
      for fv' in (collectFVars {} (← instantiateMVars (← fv.getType))).fvarIds do
        unless fvs.contains fv' do fvs := fvs.insert fv'; changed := true
  let caps := (fvs.toArray.qsort fun a b => (lctx.get! a).index < (lctx.get! b).index).map mkFVar
  let key ← mkLambdaFVars caps (mkAppN (mkConst F lvls) ((args.zip fixed).map fun (a, f) => if f then a else mkConst ``Unit.unit))
  let key := ctx.layers.foldl (fun k (h, _, _) => mkApp k (mkConst h)) key
  let vpos := (List.range args.size).filter (!fixed[·]!)
  let site := mkAppN (mkConst F lvls) args
  if let some (_, _, cN) := (← get).cache.find? fun (F', k, _) => F' == F && k == key then
    return mkAppN (mkConst cN) (caps ++ vpos.toArray.map (args[·]!) ++ extraArr)
  let k := (← get).count + 1
  modify fun s => { s with count := k }
  let cN := owner ++ Name.mkSimple s!"mon{k}"
  modify fun s => { s with cache := s.cache.push (F, key, cN) }
  let ytys ← vpos.toArray.mapM fun j => inferType args[j]!
  let etys ← extraArr.mapM fun x => inferType x
  let decls := (vpos.toArray.mapIdx fun i _ => (Name.mkSimple s!"y{i}", ytys[i]!)) ++
    (etys.map fun t => (`s, t))
  -- the copy `cN caps ys [s] := C[F args[ys]]`
  let (cTy, cVal) ← withLocalDeclsDND decls fun zs => do
    let ys := zs.extract 0 vpos.length
    let ss := zs.extract vpos.length zs.size
    let args' := Id.run do
      let mut a := args
      for (j, y) in vpos.zip ys.toList do a := a.set! j y
      a
    let body := ctx.wrap ss (mkAppN (mkConst F lvls) args')
    let ty := stripId (← instantiateMVars (← inferType body))
    return (← mkForallFVars (caps ++ zs) ty, ← mkLambdaFVars (caps ++ zs) body)
  addAndCompile (.defnDecl (mkDefinitionValEx cN [] cTy cVal (.regular 1) .safe [cN]))
  enableRealizationsForConst cN
  let _ := site
  let (ty, pf) ← forallTelescope cTy fun xs _ => do
    let cs := xs.extract 0 caps.size
    let ys := xs.extract caps.size (caps.size + vpos.length)
    let ss := xs.extract (caps.size + vpos.length) xs.size
    let sub (e : Expr) := e.replaceFVars caps cs
    let args' := Id.run do
      let mut a := args.map sub
      for (j, y) in vpos.zip ys.toList do a := a.set! j y
      a
    let ctx' : MonCtx := { layers := ctx.layers.map fun (h, l, pre) => (h, l, pre.map sub) }
    let some (rhs, pfE) ← monEqnAt eqn (mkAppN (mkConst F lvls) args') | throwError "frontx_monad: bad equation of {F}"
    let lhs := mkAppN (mkConst cN) xs
    let rhs := ctx'.wrap ss rhs
    let pf0 ← mkExpectedTypeHint (← mkCongrArg (← withLocalDeclD `z (← inferType (mkAppN (mkConst F lvls) args'))
      fun z => mkLambdaFVars #[z] (ctx'.wrap ss z)) pfE) (← mkEq lhs rhs)
    -- the monad unfolded, the recursive sites folded, nested sites specialised, until nothing changes
    let cache := (← get).cache
    let skip (n : Name) := n == cN || n == owner || cache.any (·.2.2 == n)
    let fold (rhs : Expr) : MetaM Expr := do
      Meta.transform rhs (post := fun e => do
        let (x, c, extra) := peelRuns e
        unless c.layers.map (·.1) == ctx.layers.map (·.1) do return .done e
        if x.isAppOfArity F args'.size then
          let ea := x.getAppArgs
          if (List.range args'.size).all fun j => !fixed[j]! || ea[j]! == args'[j]! then
            return .done (mkAppN (mkConst cN) (cs ++ vpos.toArray.map (ea[·]!) ++ extra))
        return .done e)
    let mut rhs := rhs
    let mut pf := pf0
    for _ in [0:12] do
      let cs ← evalConsts skip rhs
      let (r1, p1) ← monSimpEq pf rhs (← monBoolMatchLemmas rhs) cs
      let r2 ← fold r1
      let (r3, unf) ← monSites cN (depth + 1) r2
      let p3 ← mkExpectedTypeHint p1 (← mkEq lhs r3)
      let (r4, p4) ← if unf.isEmpty then pure (r3, p3) else monSimpEq p3 r3 [] unf
      if r4 == rhs then break
      rhs := r4; pf := p4
    let rhsM := hofMark cN rhs
    let pfM ← mkExpectedTypeHint pf (← mkEq lhs rhsM)
    let (rhsF, pfF) ← hofEvalEq skip pfM rhsM (hofPost ++ (← monBoolMatchLemmas rhsM)) (zeta := true)
    if (rhsF.find? (·.isConstOf F)).isSome then
      throwError "frontx_monad: {F} is left in the copy (a recursive call that changes a fixed argument, or a context that is not the copy's){indentExpr rhsF}"
    return (← mkForallFVars xs (← mkEq lhs rhsF), ← mkLambdaFVars xs pfF)
  let ty ← instantiateMVars ty
  let pf ← instantiateMVars pf
  addDecl (.thmDecl { name := cN ++ `eq, levelParams := [], type := ty, value := pf })
  modify fun s => { s with log := s.log.push m!"{cN} := {F} at the fixed arguments; {cN ++ `eq} : {ty}" }
  return mkAppN (mkConst cN) (caps ++ vpos.toArray.map (args[·]!) ++ extraArr)
end

/-- a body `K[c]` with one call `c` of a copy `cN` (the code after a loop: the `match` of an early `return`, a
projection): the continuation is absorbed into a new copy `cK caps zs := K[cN zs]`, whose equation is `cN`'s under
`K` (`congrArg`, `K` pushed into the `match`es, the monad lemmas), the calls `K[cN zs']` folded to `cK` -/
def monAbsorb (owner : Name) (rhs : Expr) : MonM (Option Expr) := do
  let copies := (← get).cache.map (·.2.2)
  let isCall (t : Expr) : Bool := match t.getAppFn with
    | .const n _ => copies.contains n
    | _ => false
  if isCall rhs then return none
  let some c := rhs.find? isCall | return none
  let cN := c.getAppFn.constName!
  let K ← kabstract rhs c
  if (K.find? isCall).isSome then return none
  let cargs := c.getAppArgs
  let nC ← forallTelescope (← getConstInfo cN).type fun ys _ => pure ys.size
  unless cargs.size == nC do return none
  let lctx ← getLCtx
  let caps := ((collectFVars {} K).fvarIds.qsort fun a b => (lctx.get! a).index < (lctx.get! b).index).map mkFVar
  let k := (← get).count + 1
  modify fun s => { s with count := k }
  let cK := owner ++ Name.mkSimple s!"mon{k}"
  let ztys ← cargs.mapM fun x => inferType x
  let (cTy, cVal) ← withLocalDeclsDND (ztys.mapIdx fun i t => (Name.mkSimple s!"z{i}", t)) fun zs => do
    let body := K.instantiate1 (mkAppN (mkConst cN) zs)
    return (← mkForallFVars (caps ++ zs) (← inferType body), ← mkLambdaFVars (caps ++ zs) body)
  addAndCompile (.defnDecl (mkDefinitionValEx cK [] cTy cVal (.regular 1) .safe [cK]))
  enableRealizationsForConst cK
  let (ty, pf) ← forallTelescope cTy fun xs ety => do
    let cs := xs.extract 0 caps.size
    let zs := xs.extract caps.size xs.size
    let K' := K.replaceFVars caps cs
    let lhs := mkAppN (mkConst cK) xs
    let some (_, _, R) := (← instantiateForall (← getConstInfo (cN ++ `eq)).type zs).eq? | throwError "frontx_monad: {cN}.eq"
    let pfN := mkAppN (mkConst (cN ++ `eq)) zs
    let pf0 ← mkExpectedTypeHint (← mkCongrArg (← withLocalDeclD `h (← inferType (mkAppN (mkConst cN) zs)) fun h =>
      mkLambdaFVars #[h] (K'.instantiate1 h)) pfN) (← mkEq lhs (K'.instantiate1 R))
    let (rhs1, pf1) ← match ← pushMatchCtx K'.instantiate1 R ety with
      | some (r, p) => pure (r, ← mkEqTrans pf0 p)
      | none => pure (K'.instantiate1 R, pf0)
    let fold (e : Expr) : MetaM Expr := Meta.transform e (post := fun t => do
      if let some c' := t.find? fun u => u.isAppOfArity cN nC then
        if t == K'.instantiate1 c' then return .done (mkAppN (mkConst cK) (cs ++ c'.getAppArgs))
      return .done t)
    let mut rhs := rhs1
    let mut pf := pf1
    for _ in [0:8] do
      let (r1, p1) ← monSimpEq pf rhs (← monBoolMatchLemmas rhs)
      let r2 ← fold r1
      let p2 ← mkExpectedTypeHint p1 (← mkEq lhs r2)
      if r2 == rhs then break
      rhs := r2; pf := p2
    if (rhs.find? (·.isConstOf cN)).isSome then
      throwError "frontx_monad: the code after {cN} could not be absorbed{indentExpr rhs}"
    return (← mkForallFVars xs (← mkEq lhs rhs), ← mkLambdaFVars xs pf)
  addDecl (.thmDecl { name := cK ++ `eq, levelParams := [], type := ← instantiateMVars ty, value := ← instantiateMVars pf })
  modify fun s => { s with cache := s.cache.push (cK, mkConst cK, cK),
                           log := s.log.push m!"{cK} := the code after {cN}; {cK ++ `eq} : {ty}" }
  return some (mkAppN (mkConst cK) (caps ++ cargs))

/-- a copy called as `cK args` where an argument is a closed value that every recursive call passes again
unchanged (the "not returned yet" state `⟨none, ()⟩` of a loop with an early `return`): a new copy without that
parameter, its equation `cK`'s at the value, simplified, the calls folded -/
def monConstArgs (owner : Name) (call : Expr) : MonM (Option Expr) := do
  let .const cK _ := call.getAppFn | return none
  unless (← getEnv).contains (cK ++ `eq) do return none
  let args := call.getAppArgs
  let eqTy := (← getConstInfo (cK ++ `eq)).type
  let nP ← forallTelescope eqTy fun xs _ => pure xs.size
  unless nP == args.size do return none
  -- the positions: a closed argument that is not a scalar or a list, passed unchanged by every recursive call
  let calls ← forallTelescope eqTy fun xs b => do
    let some (_, _, r) := b.eq? | return #[]
    let rec go (e : Expr) (acc : Array (Array Expr)) : Array (Array Expr) :=
      let acc := if e.isAppOfArity cK nP then acc.push e.getAppArgs else acc
      match e with
      | .app f a => go a (go f acc)
      | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
      | .letE _ t v b _ => go b (go v (go t acc))
      | .mdata _ b => go b acc
      | .proj _ _ b => go b acc
      | _ => acc
    return go r #[]
  let pos := (List.range args.size).filter fun j =>
    !args[j]!.hasFVar && !args[j]!.hasLooseBVars && !args[j]!.hasMVar && args[j]!.isApp &&
      calls.all fun ca => ca[j]! == args[j]!
  let pos ← pos.filterM fun j => do return (← classify (← inferType args[j]!)).isNone
  if pos.isEmpty then return none
  let k := (← get).count + 1
  modify fun s => { s with count := k }
  let cC := owner ++ Name.mkSimple s!"mon{k}"
  let keep := (List.range args.size).filter (!pos.contains ·)
  let (cTy, cVal, ty, pf) ← forallTelescope eqTy fun xs b => do
    let some (_, _, r) := b.eq? | throwError "frontx_monad: {cK}.eq"
    let sub (e : Expr) := e.replaceFVars (pos.toArray.map (xs[·]!)) (pos.toArray.map (args[·]!))
    let ps := keep.toArray.map (xs[·]!)
    let full := mkAppN (mkConst cK) (sub <$> xs)
    let cTy ← mkForallFVars ps (← inferType full)
    let cVal ← mkLambdaFVars ps full
    addAndCompile (.defnDecl (mkDefinitionValEx cC [] cTy cVal (.regular 1) .safe [cC]))
    enableRealizationsForConst cC
    let lhs := mkAppN (mkConst cC) ps
    let r := sub r
    let pf0 ← mkExpectedTypeHint (mkAppN (mkConst (cK ++ `eq)) (sub <$> xs)) (← mkEq lhs r)
    let (r1, pf1) ← monSimpEq pf0 r
    let r2 ← Meta.transform r1 (post := fun t => do
      if t.isAppOfArity cK nP && pos.all (fun j => t.getAppArgs[j]! == args[j]!) then
        return .done (mkAppN (mkConst cC) (keep.toArray.map (t.getAppArgs[·]!)))
      return .done t)
    if (r2.find? (·.isConstOf cK)).isSome then throwError "frontx_monad: {cK} left after dropping constant arguments{indentExpr r2}"
    let pf2 ← mkExpectedTypeHint pf1 (← mkEq lhs r2)
    return (cTy, cVal, ← mkForallFVars ps (← mkEq lhs r2), ← mkLambdaFVars ps pf2)
  let _ := (cTy, cVal)
  addDecl (.thmDecl { name := cC ++ `eq, levelParams := [], type := ← instantiateMVars ty, value := ← instantiateMVars pf })
  modify fun s => { s with cache := s.cache.push (cC, mkConst cC, cC),
                           log := s.log.push m!"{cC} := {cK} at its constant arguments {pos}; {cC ++ `eq} : {ty}" }
  return some (mkAppN (mkConst cC) (keep.toArray.map (args[·]!)))

/-- `frontx_monad h`; returns the right-hand side of `h.mon` -/
def monRun (hN : Name) : TermElabM Expr := do
  let info ← getConstInfoDefn hN
  unless info.levelParams.isEmpty do throwError "frontx_monad: {hN} is universe polymorphic"
  let some eqn ← getUnfoldEqnFor? hN (nonRec := true) | throwError "frontx_monad: no unfolding equation for {hN}"
  let eqTy := (← getConstInfo eqn).type
  let act : MonM (Expr × Expr × Expr) := forallTelescope eqTy fun xs body => do
    let some (_, lhs, rhs) := body.eq? | throwError "frontx_monad: bad equation of {hN}"
    let (rhs0, pf0) ← (hofEvalEq (· == hN) (mkAppN (mkConst eqn) xs) rhs hofPre : TermElabM _)
    let mut rhs := rhs0
    let mut pf := pf0
    for _ in [0:12] do
      let (r1, p1) ← monSimpEq pf rhs
      let (r2, unf) ← monSites hN 0 r1
      let p2 ← mkExpectedTypeHint p1 (← mkEq lhs r2)
      let (r3, p3) ← if unf.isEmpty then pure (r2, p2) else monSimpEq p2 r2 [] unf
      if r3 == rhs then break
      rhs := r3; pf := p3
    if let some r ← monAbsorb hN rhs then
      pf ← mkExpectedTypeHint pf (← mkEq lhs r)
      rhs := r
    if let some r ← monConstArgs hN rhs then
      pf ← mkExpectedTypeHint pf (← mkEq lhs r)
      rhs := r
    if rhs == rhs0 then throwError "frontx_monad: nothing to specialise in {hN}{indentExpr rhs0}"
    return (← mkForallFVars xs (← mkEq lhs rhs), ← mkLambdaFVars xs pf, ← mkLambdaFVars xs rhs)
  let ((ty, pf, rhs), st) ← act.run {}
  let ty ← instantiateMVars ty
  addDecl (.thmDecl { name := hN ++ `mon, levelParams := [], type := ty, value := ← instantiateMVars pf })
  for m in st.log do logInfo m!"frontx_monad: {m}"
  logInfo m!"frontx_monad: {hN ++ `mon} : {ty}"
  return rhs

elab "frontx_monad " h:ident : command => liftTermElabM do
  discard <| monRun (← realizeGlobalConstNoOverloadWithInfo h)

syntax "frontx_monad_entry " ident (" measure " term)? (" with " term)? : command
elab_rules : command
  | `(frontx_monad_entry $g:ident $[measure $μ?]? $[with $inv?]?) => do
  let gN ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo g
  -- the specialisation, then the shape of the entry's body: one call of a copy
  let (c, cmds, entryTy) ← liftTermElabM do
    let rhs ← monRun gN
    lambdaTelescope rhs fun xs body => do
      unless xs.size == 1 && (← whnfR (← inferType xs[0]!)).isConstOf ``ByteArray do
        throwError "frontx_monad_entry: expected one ByteArray parameter"
      let B := xs[0]!
      let .const c _ := body.getAppFn | throwError "frontx_monad_entry: the body is not a call of a copy{indentExpr body}"
      unless (← getEnv).contains (c ++ `eq) do throwError "frontx_monad_entry: {c} is not a copy"
      let args := body.getAppArgs
      let dl ← mkAppM ``Array.toList #[mkApp (mkConst ``ByteArray.data) B]
      let dlN ← mkAppM ``List.map #[mkConst ``UInt8.toNat, dl]
      let some p ← (List.range args.size).findM? fun j => do
          return args[j]! == mkApp (mkConst ``ByteArray.data) B || (← isDefEq args[j]! dl) || (← isDefEq args[j]! dlN)
        | throwError "frontx_monad_entry: no argument is the input (`xs.data.toList`, `….map UInt8.toNat`, `xs.data`)"
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
  let eN := gN ++ `mon ++ `entry
  liftTermElabM do
    let entryTy ← instantiateMVars entryTy
    let hI := mkIdent (gN ++ `mon)
    addThm eN entryTy (← `(tactic| (intros; rw [$hI:ident]; rfl)))
  let eI := mkIdent eN
  elabCommand (← `(frontx_entry $g from $eI))

/-- `frontx_monad_fn g [requires P]` for `g : ByteArray → R` whose monadic body has no loop: `frontx_monad g`, the
first-order body as `g.monb xs (_ : Nat)` (equation `g.monb.eq` from `g.mon`; the extra parameter is the entry
convention of §16's `…At` functions, unused), `frontx_compile`, `g.mon.entry : g xs = g.monb xs 0`, `frontx_entry g` -/
syntax "frontx_monad_fn " ident (" requires " term)? : command
elab_rules : command
  | `(frontx_monad_fn $g:ident $[requires $req?]?) => do
  let gN ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo g
  let bN := gN ++ `monb
  liftTermElabM do
    let rhs ← monRun gN
    let (ty, val, eqTy, eqPf, enTy) ← lambdaTelescope rhs fun xs body => do
      unless xs.size == 1 do throwError "frontx_monad_fn: expected one ByteArray parameter"
      withLocalDeclD `i (mkConst ``Nat) fun i => do
        let ps := xs.push i
        let ty ← mkForallFVars ps (← inferType body)
        let val ← mkLambdaFVars ps body
        addAndCompile (.defnDecl (mkDefinitionValEx bN [] ty val (.regular 1) .safe [bN]))
        let lhs := mkAppN (mkConst bN) ps
        let eqTy ← mkForallFVars ps (← mkEq lhs body)
        let eqPf ← mkLambdaFVars ps (← mkEqRefl lhs)
        let enTy ← mkForallFVars xs (← mkEq (mkAppN (mkConst gN) xs) (mkAppN (mkConst bN) (xs.push (mkNatLit 0))))
        return (ty, val, eqTy, eqPf, enTy)
    let _ := (ty, val)
    addDecl (.thmDecl { name := bN ++ `eq, levelParams := [], type := eqTy, value := eqPf })
    let enN := gN ++ `mon ++ `entry
    let monN := gN ++ `mon
    let enPf ← forallTelescope enTy fun xs _ => do mkLambdaFVars xs (mkAppN (mkConst monN) xs)
    addDecl (.thmDecl { name := enN, levelParams := [], type := enTy, value := enPf })
  let bI := mkIdent bN
  let beq := mkIdent (bN ++ `eq)
  match req? with
  | some r => elabCommand (← `(frontx_compile $bI from $beq measure fun _ _ => 0 requires $r))
  | none => elabCommand (← `(frontx_compile $bI from $beq measure fun _ _ => 0))
  let eI := mkIdent (gN ++ `mon ++ `entry)
  elabCommand (← `(frontx_entry $g from $eI))

end Proven.Frontx
