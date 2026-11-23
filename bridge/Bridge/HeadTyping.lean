/- Bridge.HeadTyping: `HeadTy` fields discharged in the trimmed model, from the heads' Lean types: `litU`, `litN`,
`pair`, `nil`, `bnew`, `natC` (Nat.casesOn with motive `λ _. R`: motive application by beta, `Nat.succ n ∈ Nat`).
Open: `bin` (needs the stored `outParam Type = Type` + instance types), `ite` (Eq/LT conditions, Decidable
instances, `dropHead` weakening), `cases` (Prod.casesOn, same pattern as `natC`), `prim`, `call` (monomorphic
arrow types, routine).

STATUS: proved, no sorry. -/
import Bridge.TermTyping

namespace Bridge.HT
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env} (L : SetLaws O)
include L

theorem tyS_univ (H : EncEnv env) (ρ : Nat → S) : ∀ s, O.mem (tyS M s) (O.univ 1)
  | .uw => univ1 (M := M) (L := L) H H.u64 ρ
  | .nt => univ1 (M := M) (L := L) H H.nat ρ
  | .ls => (encM_mem (M := M) (L := L) H ρ (.l [])).2
  | .bf => univ1 (M := M) (L := L) H H.buf ρ
  | .p a b => by
    have dQ : D O M.cval ρ (.forallE (.sort 1) (.forallE (.sort 1) (.sort 1) false) false)
        (O.piR (regime false) (O.univ 1) fun _ => O.piR (regime false) (O.univ 1) fun _ => O.univ 1) :=
      .pi .sort (fun _ _ => .pi .sort (fun _ _ => .sort) (np rfl)) (np rfl)
    have g1 := L.app_mem_piR (mem_ty M L H.prod dQ) (tyS_univ H ρ a) (np rfl)
    exact L.app_mem_piR g1 (tyS_univ H ρ b) (np rfl)

theorem litU_ty (H : EncEnv env) (HL : LitEnv env) {ρ : Nat → S} {k : Nat} {R : S} (hk : k < UInt64.size)
    (hR : D O M.cval ρ (trM (apps (.c "OfNat.ofNat" [0]) [U, .nat k, .app (.c "UInt64.instOfNat" []) (.nat k)])) R) :
    O.mem R (tyS M .uw) := by
  rw [litU_field M L HL hk hR]; exact (encM_mem (M := M) (L := L) H ρ _).1

/-- `instOfNatNat : (n : Nat) → OfNat Nat n` -/
def InstN (env : List Const) : Prop :=
  HasTy env "instOfNatNat" [] (.forallE tNat (.app (.app (.const "OfNat" [0]) tNat) (.bvar 0)) false)

theorem litN_ty (H : EncEnv env) (HL : LitEnv env) (HN : InstN env) {ρ : Nat → S} {k : Nat} {R : S}
    (hR : D O M.cval ρ (trM (apps (.c "OfNat.ofNat" [0]) [.c "Nat" [], .nat k, .app (.c "instOfNatNat" []) (.nat k)])) R) :
    O.mem R (tyS M .nt) := by
  obtain ⟨F, I, hF, hI, rfl⟩ := app_inv hR
  obtain ⟨G, n1, hG, hn1, rfl⟩ := app_inv hF
  obtain ⟨Hd, Nv, hHd, hNv, rfl⟩ := app_inv hG
  obtain ⟨J, n2, hJ, hn2, rfl⟩ := app_inv hI
  cases hHd; cases hNv; cases hJ
  rw [D_functional L hn1 (lit_denotes M ρ k), D_functional L hn2 (lit_denotes M ρ k)]
  have hx := natEnc_mem' (M := M) (L := L) H ρ k
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have dI : D O M.cval ρ (.forallE tNat (.app (.app (.const "OfNat" [0]) tNat) (.bvar 0)) false) _ :=
    .pi .const (fun _ _ => .app (.app .const .const) .bvar) (np rfl)
  have hIx := mem_app' L dI (mem_ty M L HN dI) .const hx (.app (.app .const .const) .bvar)
  have dTy : D O M.cval ρ (.forallE (.sort 1) (.forallE tNat
      (.forallE (.app (.app (.const "OfNat" [0]) (.bvar 1)) (.bvar 0)) (.bvar 2) false) false) false)
      (O.piR 1 (O.univ 1) fun α => O.piR 1 (M.cval "Nat" []) fun n =>
        O.piR 1 (O.app (O.app (M.cval "OfNat" [0]) α) n) fun _ => α) :=
    .pi .sort (fun _ _ => .pi .const (fun _ _ => .pi (.app (.app .const .bvar) .bvar) (fun _ _ => .bvar) (np rfl))
      (np rfl)) (np rfl)
  have hH := mem_closed L M HL.ofNatH (ls := [0]) (ρ := ρ) dTy
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR hH hNu (np rfl)) hx (np rfl)) hIx (np rfl)

theorem pair_ty (H : EncEnv env) {ρ : Nat → S} {A B : Sh} {Hv X Y : S}
    (hH : D O M.cval ρ (trM (apps (.c "Prod.mk" [0, 0]) [shTy A, shTy B])) Hv)
    (hX : O.mem X (tyS M A)) (hY : O.mem Y (tyS M B)) : O.mem (O.app (O.app Hv X) Y) (tyS M (.p A B)) := by
  obtain ⟨F, Bv, hF, hB, rfl⟩ := app_inv hH
  obtain ⟨G, Av, hG, hA, rfl⟩ := app_inv hF
  cases hG
  rw [D_functional L hA (shTy_tyS M A), D_functional L hB (shTy_tyS M B)]
  have dP : D O M.cval ρ (.forallE (.sort 1) (.forallE (.sort 1) (.forallE (.bvar 1) (.forallE (.bvar 1)
      (.app (.app (.const "Prod" [0, 0]) (.bvar 3)) (.bvar 2)) false) false) false) false)
      (O.piR (regime false) (O.univ 1) fun a => O.piR (regime false) (O.univ 1) fun b =>
        O.piR (regime false) a fun _ => O.piR (regime false) b fun _ => O.app (O.app (M.cval "Prod" [0, 0]) a) b) :=
    .pi .sort (fun _ _ => .pi .sort (fun _ _ => .pi .bvar (fun _ _ => .pi .bvar
      (fun _ _ => .app (.app .const .bvar) .bvar) (np rfl)) (np rfl)) (np rfl)) (np rfl)
  have h1 := L.app_mem_piR (mem_ty M L H.pmk dP) (tyS_univ (M := M) L H ρ A) (np rfl)
  have h2 := L.app_mem_piR h1 (tyS_univ (M := M) L H ρ B) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR h2 hX (np rfl)) hY (np rfl)

theorem nil_ty (H : EncEnv env) {ρ : Nat → S} {R : S}
    (hR : D O M.cval ρ (trM (apps (.c "List.nil" [0]) [.c "UInt8" []])) R) : O.mem R (tyS M .ls) := by
  rw [nil_field M hR]; exact (encM_mem (M := M) (L := L) H ρ _).1

theorem bnew_ty (hb : HasTy env "bnew" [] (.const "Buf" [])) {ρ : Nat → S} : O.mem (M.cval "bnew" []) (tyS M .bf) :=
  mem_ty M L hb (ρ := ρ) .const

/-- `Nat.casesOn.{u} : {motive : Nat → Sort u} → (t : Nat) → motive Nat.zero → ((n : Nat) → motive (Nat.succ n)) →
motive t`, at `u = 1` -/
def CasesNEnv (env : List Const) : Prop :=
  HasTy env "Nat.casesOn" [1] (.forallE (.forallE tNat (.sort 1) false) (.forallE tNat
    (.forallE (.app (.bvar 1) (.const "Nat.zero" []))
      (.forallE (.forallE tNat (.app (.bvar 3) (.app (.const "Nat.succ" []) (.bvar 0))) false)
        (.app (.bvar 3) (.bvar 2)) false) false) false) false)

theorem natC_ty (H : EncEnv env) (HC : CasesNEnv env) {ρ : Nat → S} {R : Sh} {Hv N Z Lb : S}
    (hH : D O M.cval ρ (trM (apps (.c "Nat.casesOn" [1]) [.lam (.c "Nat" []) (shTy R)])) Hv)
    (hN : O.mem N (tyS M .nt)) (hZ : O.mem Z (tyS M R)) (hL : O.mem Lb (O.piR 1 (tyS M .nt) fun _ => tyS M R)) :
    O.mem (O.app (O.app (O.app Hv N) Z) Lb) (tyS M R) := by
  obtain ⟨Hd, Mv, hHd, hM, rfl⟩ := app_inv hH
  cases hHd
  obtain ⟨A, F, hA, hF, -, rfl⟩ := lam_inv hM
  cases hA
  have hF' : ∀ x, O.mem x (M.cval "Nat" []) → F x = tyS M R := fun x hx => D_functional L (hF x hx) (shTy_tyS M R)
  have hRu := tyS_univ (M := M) L H ρ R
  set_option linter.unusedVariables false in
  have hzero := natEnc_mem' (M := M) (L := L) H ρ 0
  have hsucc : ∀ n, O.mem n (M.cval "Nat" []) → O.mem (O.app (M.cval "Nat.succ" []) n) (M.cval "Nat" []) := by
    intro n hn
    have dP : D O M.cval ρ (.forallE tNat tNat false) _ := .pi .const (fun _ _ => .const) (np rfl)
    exact mem_app' L dP (mem_ty M L H.succ dP) .const hn .const
  have hMv : ∀ x, O.mem x (M.cval "Nat" []) → O.app (O.lamR (regime false) (M.cval "Nat" []) F) x = tyS M R :=
    fun x hx => by rw [L.app_lamR_pos (by simp [regime]) hx, hF' x hx]
  -- the type of Nat.casesOn at ρ
  let Mt := O.lamR (regime false) (M.cval "Nat" []) F
  have dT : D O M.cval ρ (.forallE (.forallE tNat (.sort 1) false) (.forallE tNat
      (.forallE (.app (.bvar 1) (.const "Nat.zero" []))
        (.forallE (.forallE tNat (.app (.bvar 3) (.app (.const "Nat.succ" []) (.bvar 0))) false)
          (.app (.bvar 3) (.bvar 2)) false) false) false) false)
      (O.piR 1 (O.piR 1 (M.cval "Nat" []) fun _ => O.univ 1) fun m => O.piR 1 (M.cval "Nat" []) fun t =>
        O.piR 1 (O.app m (M.cval "Nat.zero" [])) fun _ =>
          O.piR 1 (O.piR 1 (M.cval "Nat" []) fun n => O.app m (O.app (M.cval "Nat.succ" []) n)) fun _ => O.app m t) :=
    .pi (.pi .const (fun _ _ => .sort) (np rfl)) (fun _ _ => .pi .const (fun _ _ => .pi (.app .bvar .const)
      (fun _ _ => .pi (.pi .const (fun _ _ => .app .bvar (.app .const .bvar)) (np rfl)) (fun _ _ => .app .bvar .bvar)
        (np rfl)) (np rfl)) (np rfl)) (np rfl)
  have hHm := mem_ty M L HC dT
  have hMt : O.mem Mt (O.piR 1 (M.cval "Nat" []) fun _ => O.univ 1) :=
    L.lamR_mem fun x hx => by rw [hF' x hx]; exact hRu
  have g1 := L.app_mem_piR hHm hMt (np rfl)
  have g2 := L.app_mem_piR g1 hN (np rfl)
  have hZ' : O.mem Z (O.app Mt (M.cval "Nat.zero" [])) := by
    show O.mem Z (O.app (O.lamR (regime false) (M.cval "Nat" []) F) (natEnc M 0)); rw [hMv _ hzero]; exact hZ
  have g3 := L.app_mem_piR g2 hZ' (np rfl)
  have hL' : O.mem Lb (O.piR 1 (M.cval "Nat" []) fun n => O.app Mt (O.app (M.cval "Nat.succ" []) n)) := by
    rw [L.piR_congr (B' := fun _ => tyS M R) fun n hn => hMv _ (hsucc n hn)]; exact hL
  have g4 := L.app_mem_piR g3 hL' (np rfl)
  rwa [hMv N hN] at g4

end Bridge.HT
