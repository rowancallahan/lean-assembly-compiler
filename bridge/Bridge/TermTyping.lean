/- Bridge.TermTyping: typing soundness for WELL-FORMED TERMS in the trimmed model (finding (c) of DENOTES_SPIKE §11):
a `Wf` term, at a variable environment whose entries are in their shapes' type sets, denotes a member of its
shape's type set.  This is what the iota facts (Nat.casesOn, Prod.casesOn) need: the branch λs must be in their
∀-types, i.e. their bodies typed at ALL arguments.

The per-HEAD typings are the fields of `HeadTy` (each one a routine computation through the head's declared type,
as `MiniModel.litU_fact` / `EvMini.encM_mem` do); the structural cases (variables, `let`-redexes, the two
casesOn with their λ branches, calls, argument lists) are proved here.  `HeadTy.litU/litN/pair/nil` are
discharged at the end from `EncEnv`/`LitEnv`.

STATUS: proved, no sorry (`HeadTy` fields other than the discharged ones are hypotheses). -/
import Bridge.EvMini

namespace Bridge.TT
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM

variable {S : Type} {O : SetOps S} {env : List Const} (M : Model O env)

/-- the type set of a shape -/
def tyS : Sh → S
  | .uw => M.cval "UInt64" []
  | .nt => M.cval "Nat" []
  | .ls => O.app (M.cval "List" [0]) (M.cval "UInt8" [])
  | .bf => M.cval "Buf" []
  | .p a b => O.app (O.app (M.cval "Prod" [0, 0]) (tyS a)) (tyS b)

theorem shTy_tyS {ρ : Nat → S} : ∀ s, D O M.cval ρ (trM (shTy s)) (tyS M s)
  | .uw => .const | .nt => .const | .ls => .app .const .const | .bf => .const
  | .p a b => .app (.app .const (shTy_tyS a)) (shTy_tyS b)

theorem tyE_tyS : ∀ {s v}, VSh s v → tyE M v = tyS M s
  | _, _, .uw _ => rfl | _, _, .nt _ => rfl | _, _, .ls _ => rfl | _, _, .bf _ => rfl
  | _, _, .p hx hy => by simp [tyE, tyS, tyE_tyS hx, tyE_tyS hy]

/-- a variable environment typed by binder shapes -/
def TEnv (Γ : List Sh) (ρ : Nat → S) : Prop := ∀ i s, Γ[i]? = some s → O.mem (ρ i) (tyS M s)

variable {M} in
theorem TEnv.push {Γ : List Sh} {ρ : Nat → S} {s : Sh} {x : S} (h : TEnv M Γ ρ) (hx : O.mem x (tyS M s)) :
    TEnv M (s :: Γ) (Mini.push x ρ) := by
  intro i s' hi
  cases i with
  | zero => simp at hi; subst hi; exact hx
  | succ i => exact h i s' (by simpa using hi)

/-- the per-head typings: one routine declared-type computation each -/
structure HeadTy (M : Model O env) (sig : Sig) : Prop where
  litU : ∀ {ρ k R}, k < UInt64.size →
    D O M.cval ρ (trM (apps (.c "OfNat.ofNat" [0]) [U, .nat k, .app (.c "UInt64.instOfNat" []) (.nat k)])) R →
    O.mem R (tyS M .uw)
  litN : ∀ {ρ k R},
    D O M.cval ρ (trM (apps (.c "OfNat.ofNat" [0]) [.c "Nat" [], .nat k, .app (.c "instOfNatNat" []) (.nat k)])) R →
    O.mem R (tyS M .nt)
  bin : ∀ {ρ op n i H X Y}, binHead op = (n, i) → n ∈ binList →
    D O M.cval ρ (trM (apps (.c n [0, 0, 0]) [U, U, U, i])) H →
    O.mem X (tyS M .uw) → O.mem Y (tyS M .uw) → O.mem (O.app (O.app H X) Y) (tyS M .uw)
  /-- ite: the condition's operands are typed (`a`, `b` at shape `o`); then the head with its condition and
  instance maps two members of `⟦r⟧` into `⟦r⟧` -/
  ite : ∀ {ρ r n cmp a b c d H X Y}, condX n cmp a b = (c, d) → iteOk n cmp a b →
    (∀ A, D O M.cval ρ (trM a) A → O.mem A (tyS M (if n then .nt else .uw))) →
    (∀ B, D O M.cval ρ (trM b) B → O.mem B (tyS M (if n then .nt else .uw))) →
    D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) H →
    O.mem X (tyS M r) → O.mem Y (tyS M r) → O.mem (O.app (O.app H X) Y) (tyS M r)
  pair : ∀ {ρ A B H X Y}, D O M.cval ρ (trM (apps (.c "Prod.mk" [0, 0]) [shTy A, shTy B])) H →
    O.mem X (tyS M A) → O.mem Y (tyS M B) → O.mem (O.app (O.app H X) Y) (tyS M (.p A B))
  /-- Prod.casesOn with motive `λ _. R`: a pair and a curried branch in `⟦l → r → R⟧` give a member of `⟦R⟧` -/
  cases : ∀ {ρ l r R H P Lb}, D O M.cval ρ (trM (apps (.c "Prod.casesOn" [1, 0, 0])
      [shTy l, shTy r, .lam (shTy (.p l r)) (shTy R)])) H →
    O.mem P (tyS M (.p l r)) →
    O.mem Lb (O.piR 1 (tyS M l) fun _ => O.piR 1 (tyS M r) fun _ => tyS M R) →
    O.mem (O.app (O.app H P) Lb) (tyS M R)
  /-- Nat.casesOn with motive `λ _. R` -/
  natC : ∀ {ρ R H N Z Lb}, D O M.cval ρ (trM (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy R)])) H →
    O.mem N (tyS M .nt) → O.mem Z (tyS M R) → O.mem Lb (O.piR 1 (tyS M .nt) fun _ => tyS M R) →
    O.mem (O.app (O.app (O.app H N) Z) Lb) (tyS M R)
  nil : ∀ {ρ R}, D O M.cval ρ (trM (apps (.c "List.nil" [0]) [.c "UInt8" []])) R → O.mem R (tyS M .ls)
  prim : ∀ {p n ps r Xs}, primInfo p = (n, ps, r) → n ∈ primList → p ≠ 5 → p ≠ 0 → p ≤ 9 →
    Fa2D (fun X s => O.mem X (tyS M s)) Xs (ps.map psSh) → O.mem (Xs.foldl O.app (M.cval n [])) (tyS M r)
  bnew : O.mem (M.cval "bnew" []) (tyS M .bf)
  /-- a program def: its stored type `piX params (shTy res)` -/
  call : ∀ {n ps r Xs}, sig n = some (ps, r) → n ∉ Typed.reserved →
    Fa2D (fun X s => O.mem X (tyS M s)) Xs ps → O.mem (Xs.foldl O.app (M.cval n [])) (tyS M r)

variable {M} (L : SetLaws O)
include L

/-- a branch λ `λ (x : shTy s). body` whose body is typed at every typed argument is in the ∀-type -/
theorem lam_mem {ρ : Nat → S} {s : Sh} {body : X} {Bv : S → S} {Lv : S}
    (h : D O M.cval ρ (trM (.lam (shTy s) body)) Lv)
    (hb : ∀ x, O.mem x (tyS M s) → ∀ R, D O M.cval (Mini.push x ρ) (trM body) R → O.mem R (Bv x)) :
    O.mem Lv (O.piR 1 (tyS M s) Bv) := by
  obtain ⟨A, F, hA, hF, -, rfl⟩ := lam_inv h
  obtain rfl := D_functional L hA (shTy_tyS M s)
  exact L.lamR_mem fun x hx => hb x hx _ (hF x hx)

/-- **typing soundness for well-formed terms** -/
theorem wf_mem {sig : Sig} (HT : HeadTy M sig) {Γ : List Sh} {e : X} {s : Sh} (hw : Wf sig Γ e s) :
    ∀ ρ, TEnv M Γ ρ → ∀ R, D O M.cval ρ (trM e) R → O.mem R (tyS M s) := by
  refine Wf.rec (motive_1 := fun Γ e s _ => ∀ ρ, TEnv M Γ ρ → ∀ R, D O M.cval ρ (trM e) R → O.mem R (tyS M s))
    (motive_2 := fun Γ as ss _ => ∀ ρ, TEnv M Γ ρ → ∀ Xs, Fa2D (fun a X => D O M.cval ρ (trM a) X) as Xs →
      Fa2D (fun X s => O.mem X (tyS M s)) Xs ss)
    ?bv ?lt ?litU ?litN ?bin ?ite ?mk ?cases ?natCases ?nil ?prim ?bnew ?call ?lnil ?lcons hw
  case bv =>
    intro Γ e i s h1 h2 ρ hρ R hR; subst h1; cases hR; exact hρ i s h2
  case lt =>
    intro Γ e v b s r h1 _ _ ihv ihb ρ hρ R hR; subst h1
    obtain ⟨Lv, Xv, hL, hv, rfl⟩ := app_inv hR
    have hX := ihv ρ hρ Xv hv
    obtain ⟨A, F, hA, hF, hP, rfl⟩ := lam_inv hL
    obtain rfl := D_functional L hA (shTy_tyS M s)
    have e' : O.app (O.lamR (regime false) (tyS M s) F) Xv = F Xv := L.app_lamR_pos (by simp [regime]) hX
    rw [e']; exact ihb _ (hρ.push hX) _ (hF Xv hX)
  case litU =>
    intro Γ e k h1 hk ρ hρ R hR; subst h1; exact HT.litU hk hR
  case litN =>
    intro Γ e k h1 ρ hρ R hR; subst h1; exact HT.litN hR
  case bin =>
    intro Γ e op n i a b h1 h2 h3 _ _ _ _ iha ihb ρ hρ R hR; subst h1
    obtain ⟨H, A, B, hH, hA, hB, rfl⟩ := EvM.two_args (l := [U, U, U, i]) hR
    exact HT.bin h2 h3 hH (iha ρ hρ A hA) (ihb ρ hρ B hB)
  case ite =>
    intro Γ e r n cmp a b c d t el h1 h2 h3 _ _ _ _ iha ihb iht ihe ρ hρ R hR; subst h1
    obtain ⟨H, A, B, hH, hA, hB, rfl⟩ := EvM.two_args (l := [shTy r, c, d]) hR
    exact HT.ite h2 h3 (iha ρ hρ) (ihb ρ hρ) hH (iht ρ hρ A hA) (ihe ρ hρ B hB)
  case mk =>
    intro Γ e a b A B h1 _ _ iha ihb ρ hρ R hR; subst h1
    obtain ⟨H, X1, X2, hH, h1', h2', rfl⟩ := EvM.two_args (l := [_, _]) hR
    exact HT.pair hH (iha ρ hρ X1 h1') (ihb ρ hρ X2 h2')
  case cases =>
    intro Γ e l r R v body h1 _ _ ihv ihb ρ hρ Rv hR; subst h1
    obtain ⟨H, P, Lv, hH, hP, hL, rfl⟩ := EvM.two_args (l := [_, _, _]) hR
    refine HT.cases hH (ihv ρ hρ P hP) ?_
    obtain ⟨A, F, hA, hF, -, rfl⟩ := lam_inv hL
    obtain rfl := D_functional L hA (shTy_tyS M l)
    refine L.lamR_mem fun x hx => ?_
    exact lam_mem L (hF x hx) fun y hy R' hR' => ihb _ ((hρ.push hx).push hy) R' hR'
  case natCases =>
    intro Γ e R d z sb h1 _ _ _ ihd ihz ihs ρ hρ Rv hR; subst h1
    rw [show [X.lam (.c "Nat" []) (shTy R), d, z, X.lam (.c "Nat" []) sb] =
      [X.lam (.c "Nat" []) (shTy R), d] ++ [z, X.lam (.c "Nat" []) sb] from rfl] at hR
    obtain ⟨H1, Z, Lv, hH1, hZ, hL, rfl⟩ := EvM.two_args hR
    obtain ⟨H, N, hH, hN, rfl⟩ := app_inv hH1
    refine HT.natC hH (ihd ρ hρ N hN) (ihz ρ hρ Z hZ) ?_
    exact lam_mem (s := .nt) L hL fun x hx R' hR' => ihs _ (hρ.push hx) R' hR'
  case nil =>
    intro Γ e h1 ρ hρ R hR; subst h1; exact HT.nil hR
  case prim =>
    intro Γ e p n ps r as h1 h2 h3 h4 h5 h6 _ ihl ρ hρ R hR; subst h1
    rw [trM_apps] at hR
    obtain ⟨H, Xs, hH, hXs, rfl⟩ := D_foldl_inv _ _ _ hR
    rw [D_const_inv hH]
    exact HT.prim h2 h3 h4 h5 h6 (ihl ρ hρ Xs (fa2_map_tr hXs))
  case bnew =>
    intro Γ e h1 ρ hρ R hR; subst h1; cases hR; exact HT.bnew
  case call =>
    intro Γ e n as ps r h1 h2 h3 _ ihl ρ hρ R hR; subst h1
    rw [trM_apps] at hR
    obtain ⟨H, Xs, hH, hXs, rfl⟩ := D_foldl_inv _ _ _ hR
    rw [D_const_inv hH]
    exact HT.call h3 h2 (ihl ρ hρ Xs (fa2_map_tr hXs))
  case lnil =>
    intro Γ ρ hρ Xs hXs; cases hXs; exact .nil
  case lcons =>
    intro Γ a as s ss _ _ iha ihl ρ hρ Xs hXs
    cases hXs with
    | cons hX hXs => exact .cons (iha ρ hρ _ hX) (ihl ρ hρ _ hXs)

end Bridge.TT
