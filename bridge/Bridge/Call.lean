/- Bridge.Call: program defs.  The stored theorem per def is `f = <emitted value>` (λ form, the value nano emits,
`lamX params body`), proved in Lean by `rfl` or `funext; cases` (DENOTES_SPIKE §5 H1); its type is
`@Eq.{1} (piX params res) f value`.  From it, by transfer + iterated beta:
* `HeadTy.call` (typing of `f xs`), and
* `FactsM.call` (a call computes the body at the arguments), DISCHARGED.

STATUS: proved, no sorry. -/
import Bridge.Iota2

namespace Bridge.Call
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

/-- a def's type, binder shapes `ps` (first parameter outermost) -/
def piPs (ps : List Sh) (r : Sh) : E := ps.foldr (fun s a => .forallE (trM (shTy s)) a false) (trM (shTy r))
/-- its value: `λ`s over the body (nano's `lamX`, at shapes) -/
def lamSh (ps : List Sh) (b : X) : X := ps.foldr (fun s a => .lam (shTy s) a) b

variable (M) in
def piS (ps : List Sh) (r : Sh) : S := ps.foldr (fun s B => O.piR 1 (tyS M s) fun _ => B) (tyS M r)

def pushAll (xs : List S) (ρ : Nat → S) : Nat → S := xs.foldl (fun ρ x => push x ρ) ρ

theorem strip_lamSh (b : X) : ∀ ps : List Sh, strip ps.length (lamSh ps b) = some b
  | [] => rfl
  | _ :: ps => strip_lamSh b ps

theorem pushAll_ρE (enc : ExprSpec.V → S) (junk : S) :
    ∀ (vs l : List ExprSpec.V), pushAll (vs.map enc) (ρE enc junk l) = ρE enc junk (vs.reverse ++ l)
  | [], l => rfl
  | v :: vs, l => by
    show pushAll (vs.map enc) (push (enc v) (ρE enc junk l)) = _
    rw [← ρE_cons, pushAll_ρE enc junk vs (v :: l)]; simp

theorem piPs_D {ρ : Nat → S} (r : Sh) : ∀ ps, D O M.cval ρ (piPs ps r) (piS M ps r)
  | [] => shTy_tyS M r
  | s :: ps => .pi (shTy_tyS M s) (fun _ _ => piPs_D r ps) (np rfl)

variable (L : SetLaws O)
include L

theorem piS_univ (H : EncEnv env) (ρ : Nat → S) (r : Sh) : ∀ ps, O.mem (piS M ps r) (O.univ 1)
  | [] => tyS_univ L H ρ r
  | s :: ps => L.piR_mem_univ (by decide) (tyS_univ L H ρ s) fun _ _ => piS_univ H ρ r ps

/-- applying a member of `piS ps r` to typed arguments lands in `⟦r⟧` -/
theorem app_piS (r : Sh) : ∀ {ps : List Sh} {F : S} {xs : List S}, O.mem F (piS M ps r) →
    Fa2D (fun X s => O.mem X (tyS M s)) xs ps → O.mem (xs.foldl O.app F) (tyS M r)
  | [], _, [], hF, .nil => hF
  | _ :: ps, F, x :: xs, hF, .cons hx hxs =>
    app_piS r (ps := ps) (F := O.app F x) (xs := xs) (L.app_mem_piR hF hx (np rfl)) hxs

omit L in
theorem tenv_pushAll : ∀ {ps : List Sh} {xs : List S} {l : List Sh} {ρ : Nat → S}, TEnv M l ρ →
    Fa2D (fun X s => O.mem X (tyS M s)) xs ps → TEnv M (ps.reverse ++ l) (pushAll xs ρ)
  | [], [], _, _, h, .nil => h
  | s :: ps, x :: xs, l, ρ, h, .cons hx hxs => by
    have := tenv_pushAll (ps := ps) (xs := xs) (TEnv.push h hx) hxs
    show TEnv M ((s :: ps).reverse ++ l) (pushAll xs (push x ρ))
    simpa using this

/-- a λ-chain whose body is typed at all typed arguments is in `piS` -/
theorem lam_piS (r : Sh) (b : X) : ∀ {ps : List Sh} {ρ : Nat → S} {Lv : S},
    (∀ xs, Fa2D (fun X s => O.mem X (tyS M s)) xs ps → ∀ R, D O M.cval (pushAll xs ρ) (trM b) R → O.mem R (tyS M r)) →
    D O M.cval ρ (trM (lamSh ps b)) Lv → O.mem Lv (piS M ps r)
  | [], ρ, Lv, hb, h => hb [] .nil Lv h
  | s :: ps, ρ, Lv, hb, h => by
    obtain ⟨A, F, hA, hF, -, rfl⟩ := lam_inv h
    obtain rfl := D_functional L hA (shTy_tyS M s)
    exact L.lamR_mem fun x hx => lam_piS r b (ps := ps) (ρ := push x ρ)
      (fun xs hxs R hR => hb (x :: xs) (.cons hx hxs) R hR) (hF x hx)

/-- iterated beta: a λ-chain applied to typed arguments is the body at the pushed environment -/
theorem app_lamSh (b : X) : ∀ {ps : List Sh} {ρ : Nat → S} {Lv : S} {xs : List S},
    D O M.cval ρ (trM (lamSh ps b)) Lv → Fa2D (fun X s => O.mem X (tyS M s)) xs ps →
    D O M.cval (pushAll xs ρ) (trM b) (xs.foldl O.app Lv)
  | [], _, _, [], h, .nil => h
  | s :: ps, ρ, Lv, x :: xs, h, .cons hx hxs => by
    obtain ⟨A, F, hA, hF, -, rfl⟩ := lam_inv h
    obtain rfl := D_functional L hA (shTy_tyS M s)
    show D O M.cval (pushAll xs (push x ρ)) (trM b) (xs.foldl O.app (O.app _ x))
    rw [L.app_lamR_pos (by simp [regime]) hx]
    exact app_lamSh b (hF x hx) hxs

/-- the program's defs in the env: type `piPs ps r`, value `lamSh ps b`, stored equation `f = value` -/
structure DefEnv (env : List Const) (sig : Sig) (P : Prog) : Prop where
  form : ∀ {n ps r body}, sig n = some (ps, r) → P.lookup n = some body → ∃ b, body = lamSh ps b
  ty : ∀ {n ps r}, sig n = some (ps, r) → HasTy env n [] (piPs ps r)
  eq : ∀ {n ps r body}, sig n = some (ps, r) → P.lookup n = some body →
    HasTy env (n ++ ".eq") [] (eqE 1 (piPs ps r) (.const n []) (trM body))

omit L in
theorem fa2_typed (encTy : ∀ {s v}, VSh s v → O.mem (encM M v) (tyS M s)) :
    ∀ {ps vs}, Typed.Fa2 VSh ps vs → Fa2D (fun X s => O.mem X (tyS M s)) (vs.map (encM M)) ps
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h t => .cons (encTy h) (fa2_typed encTy t)

/-- **`HeadTy.call`, discharged** -/
theorem call_ty (HD : DefEnv env sig P) {n : String} {ps : List Sh} {r : Sh} {Xs : List S}
    (hs : sig n = some (ps, r)) (hXs : Fa2D (fun X s => O.mem X (tyS M s)) Xs ps) :
    O.mem (Xs.foldl O.app (M.cval n [])) (tyS M r) :=
  app_piS L r (mem_ty M L (HD.ty hs) (ρ := fun _ => M.cval "Nat" []) (piPs_D r ps)) hXs

/-- **`FactsM.call`, discharged** (the typing of the body comes from `wf_mem`, hence `HeadTy` and `PWf`) -/
theorem call_field (H : EncEnv env) (HD : DefEnv env sig P) (HT : HeadTy M sig) (hP : PWf sig P) {junk : S}
    {n : String} {ps : List Sh} {r : Sh} {vs : List ExprSpec.V} {body b : X} {v : ExprSpec.V}
    (hs : sig n = some (ps, r)) (hvs : Typed.Fa2 VSh ps vs) (hl : P.lookup n = some body)
    (hst : strip vs.length body = some b)
    (ih : ∀ R, D O M.cval (ρE (encM M) junk vs.reverse) (trM b) R → R = encM M v) :
    (vs.map (encM M)).foldl O.app (M.cval n []) = encM M v := by
  have encTy : ∀ {s v}, VSh s v → O.mem (encM M v) (tyS M s) := fun {s v} hv => by
    rw [← tyE_tyS M hv]; exact (encM_mem (M := M) (L := L) H (fun _ => junk) v).1
  obtain ⟨b', rfl⟩ := HD.form hs hl
  rw [← fa2_len hvs, strip_lamSh] at hst; cases hst
  obtain ⟨hPs, b'', ps', hwb⟩ : True ∧ True ∧ True ∧ Wf sig ps.reverse b r := by
    obtain ⟨ps2, r2, b2, hs2, hst2, hw2⟩ := hP.defs hl
    rw [hs] at hs2; cases hs2
    rw [strip_lamSh] at hst2; cases hst2
    exact ⟨trivial, trivial, trivial, hw2⟩
  let ρ0 : Nat → S := ρE (encM M) junk []
  obtain ⟨ty, hc, hty⟩ := HD.eq hs hl
  have h0 : Inhab M ρ0 (ty []) := inhab_const M hc [] ρ0
  rw [hty] at h0
  obtain ⟨Sv, av, bv, hS, ha, hb, k⟩ := h0.eq_ex L
  obtain rfl := D_functional L hS (piPs_D r ps)
  cases ha
  have hbody : ∀ xs, Fa2D (fun X s => O.mem X (tyS M s)) xs ps → ∀ R,
      D O M.cval (pushAll xs ρ0) (trM b) R → O.mem R (tyS M r) := fun xs hxs R hR =>
    wf_mem L HT hwb _ (by simpa using tenv_pushAll (l := []) (fun i s h => by simp at h) hxs) R hR
  have hbv := lam_piS L r b hbody hb
  have hav := mem_ty M L (HD.ty hs) (ρ := ρ0) (piPs_D r ps)
  have heq := k (piS_univ L H ρ0 r ps) hav hbv
  have hxs := fa2_typed encTy hvs
  rw [heq]
  have hD := app_lamSh L b hb hxs
  rw [pushAll_ρE (encM M) junk vs [], List.append_nil] at hD
  exact ih _ hD

end Bridge.Call
