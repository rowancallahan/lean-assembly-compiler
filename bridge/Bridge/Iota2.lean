/- Bridge.Iota2: `FactsM.litN` (transfer from `br_litN : ∀ n : Nat, @OfNat.ofNat Nat n (instOfNatNat n) = n`) and
Prod.casesOn: `HeadTy.cases` (typing through its declared type) and `FactsM.cases` (transfer from
`prod_c : ∀ (A B R : Type) (f : A → B → R) (a : A) (b : B),
  @Prod.casesOn A B (fun _ => R) (Prod.mk a b) f = f a b`).

STATUS: proved, no sorry. -/
import Bridge.Iota

namespace Bridge.Iota2
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Iota

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env} (L : SetLaws O)
include L

/-- `OfNat.ofNat.{0} T n inst ∈ T` (through the declared type in `LitEnv`) -/
theorem ofNat_mem (HL : LitEnv env) {ρ : Nat → S} {T n i : S} (hT : O.mem T (O.univ 1))
    (hn : O.mem n (M.cval "Nat" [])) (hi : O.mem i (O.app (O.app (M.cval "OfNat" [0]) T) n)) :
    O.mem (O.app (O.app (O.app (M.cval "OfNat.ofNat" [0]) T) n) i) T := by
  have dTy : D O M.cval ρ (.forallE (.sort 1) (.forallE tNat
      (.forallE (.app (.app (.const "OfNat" [0]) (.bvar 1)) (.bvar 0)) (.bvar 2) false) false) false)
      (O.piR 1 (O.univ 1) fun α => O.piR 1 (M.cval "Nat" []) fun n =>
        O.piR 1 (O.app (O.app (M.cval "OfNat" [0]) α) n) fun _ => α) :=
    .pi .sort (fun _ _ => .pi .const (fun _ _ => .pi (.app (.app .const .bvar) .bvar) (fun _ _ => .bvar) (np rfl))
      (np rfl)) (np rfl)
  have hH := mem_closed L M HL.ofNatH (ls := [0]) (ρ := ρ) dTy
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR hH hT (np rfl)) hn (np rfl)) hi (np rfl)

/-- **`FactsM.litN`, discharged** -/
theorem litN_field (H : EncEnv env) (HL : LitEnv env) (HN : InstN env)
    (hb : HasTy env "br_litN" [] (piN [(tNat, true)] (eqE 1 tNat
      (.app (.app (.app (.const "OfNat.ofNat" [0]) tNat) (.bvar 0)) (.app (.const "instOfNatNat" []) (.bvar 0)))
      (.bvar 0))))
    {ρ : Nat → S} {k : Nat} {R : S}
    (hR : D O M.cval ρ (trM (apps (.c "OfNat.ofNat" [0]) [.c "Nat" [], .nat k, .app (.c "instOfNatNat" []) (.nat k)])) R) :
    R = encM M (.n k) := by
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
  obtain ⟨ty, hc, hty⟩ := hb
  exact transferN L M hc (ls := []) hty ρ (.cons .const hx .nil) .const
    (.app (.app (.app .const .const) .bvar) (.app .const .bvar)) .bvar hNu (ofNat_mem (ρ := ρ) L HL hNu hx hIx) hx

/-! ## Prod.casesOn -/

/-- `Prod.casesOn.{u,v,w} : {α : Type v} → {β : Type w} → {motive : Prod α β → Sort u} → (t : Prod α β) →
((fst : α) → (snd : β) → motive (Prod.mk fst snd)) → motive t`, at `[1, 0, 0]` -/
def CasesPEnv (env : List Const) : Prop :=
  let P (a b : Nat) : E := .app (.app (.const "Prod" [0, 0]) (.bvar a)) (.bvar b)
  HasTy env "Prod.casesOn" [1, 0, 0] (.forallE (.sort 1) (.forallE (.sort 1) (.forallE (.forallE (P 1 0) (.sort 1) false)
    (.forallE (P 2 1) (.forallE (.forallE (.bvar 3) (.forallE (.bvar 3) (.app (.bvar 3)
        (.app (.app (.app (.app (.const "Prod.mk" [0, 0]) (.bvar 5)) (.bvar 4)) (.bvar 1)) (.bvar 0))) false) false)
      (.app (.bvar 2) (.bvar 1)) false) false) false) false) false)

/-- `Prod.mk A B a b ∈ Prod A B` -/
theorem mk_mem (H : EncEnv env) {ρ : Nat → S} {A B a b : S} (hA : O.mem A (O.univ 1)) (hB : O.mem B (O.univ 1))
    (ha : O.mem a A) (hb : O.mem b B) :
    O.mem (O.app (O.app (O.app (O.app (M.cval "Prod.mk" [0, 0]) A) B) a) b) (O.app (O.app (M.cval "Prod" [0, 0]) A) B) := by
  have dP : D O M.cval ρ (.forallE (.sort 1) (.forallE (.sort 1) (.forallE (.bvar 1) (.forallE (.bvar 1)
      (.app (.app (.const "Prod" [0, 0]) (.bvar 3)) (.bvar 2)) false) false) false) false)
      (O.piR (regime false) (O.univ 1) fun a => O.piR (regime false) (O.univ 1) fun b =>
        O.piR (regime false) a fun _ => O.piR (regime false) b fun _ => O.app (O.app (M.cval "Prod" [0, 0]) a) b) :=
    .pi .sort (fun _ _ => .pi .sort (fun _ _ => .pi .bvar (fun _ _ => .pi .bvar
      (fun _ _ => .app (.app .const .bvar) .bvar) (np rfl)) (np rfl)) (np rfl)) (np rfl)
  have h1 := L.app_mem_piR (mem_ty M L H.pmk dP) hA (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR h1 hB (np rfl)) ha (np rfl)) hb (np rfl)

theorem prod_univ (H : EncEnv env) {ρ : Nat → S} {A B : S} (hA : O.mem A (O.univ 1)) (hB : O.mem B (O.univ 1)) :
    O.mem (O.app (O.app (M.cval "Prod" [0, 0]) A) B) (O.univ 1) := by
  have dQ : D O M.cval ρ (.forallE (.sort 1) (.forallE (.sort 1) (.sort 1) false) false)
      (O.piR (regime false) (O.univ 1) fun _ => O.piR (regime false) (O.univ 1) fun _ => O.univ 1) :=
    .pi .sort (fun _ _ => .pi .sort (fun _ _ => .sort) (np rfl)) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (mem_ty M L H.prod dQ) hA (np rfl)) hB (np rfl)

/-- Prod.casesOn typing, motive a set function equal to `T` on the pair type -/
theorem casesP_set (H : EncEnv env) (HP : CasesPEnv env) {ρ : Nat → S} {A B T Pv Lb : S} {F : S → S}
    (hA : O.mem A (O.univ 1)) (hB : O.mem B (O.univ 1)) (hT : O.mem T (O.univ 1))
    (hF : ∀ x, O.mem x (O.app (O.app (M.cval "Prod" [0, 0]) A) B) → F x = T)
    (hP : O.mem Pv (O.app (O.app (M.cval "Prod" [0, 0]) A) B)) (hL : O.mem Lb (O.piR 1 A fun _ => O.piR 1 B fun _ => T)) :
    O.mem (O.app (O.app (O.app (O.app (O.app (M.cval "Prod.casesOn" [1, 0, 0]) A) B)
      (O.lamR (regime false) (O.app (O.app (M.cval "Prod" [0, 0]) A) B) F)) Pv) Lb) T := by
  let PS (a b : S) := O.app (O.app (M.cval "Prod" [0, 0]) a) b
  let Mt := O.lamR (regime false) (PS A B) F
  have hMv : ∀ x, O.mem x (PS A B) → O.app Mt x = T := fun x hx => by
    rw [L.app_lamR_pos (by simp [regime]) hx, hF x hx]
  have dT : D O M.cval ρ (.forallE (.sort 1) (.forallE (.sort 1) (.forallE (.forallE
      (.app (.app (.const "Prod" [0, 0]) (.bvar 1)) (.bvar 0)) (.sort 1) false)
      (.forallE (.app (.app (.const "Prod" [0, 0]) (.bvar 2)) (.bvar 1)) (.forallE (.forallE (.bvar 3) (.forallE (.bvar 3)
        (.app (.bvar 3) (.app (.app (.app (.app (.const "Prod.mk" [0, 0]) (.bvar 5)) (.bvar 4)) (.bvar 1)) (.bvar 0)))
        false) false)
      (.app (.bvar 2) (.bvar 1)) false) false) false) false) false)
      (O.piR 1 (O.univ 1) fun a => O.piR 1 (O.univ 1) fun b => O.piR 1 (O.piR 1 (PS a b) fun _ => O.univ 1) fun m =>
        O.piR 1 (PS a b) fun t => O.piR 1 (O.piR 1 a fun x => O.piR 1 b fun y =>
          O.app m (O.app (O.app (O.app (O.app (M.cval "Prod.mk" [0, 0]) a) b) x) y)) fun _ => O.app m t) :=
    .pi .sort (fun _ _ => .pi .sort (fun _ _ => .pi (.pi (.app (.app .const .bvar) .bvar) (fun _ _ => .sort) (np rfl))
      (fun _ _ => .pi (.app (.app .const .bvar) .bvar) (fun _ _ => .pi (.pi .bvar (fun _ _ => .pi .bvar
        (fun _ _ => .app .bvar (.app (.app (.app (.app .const .bvar) .bvar) .bvar) .bvar)) (np rfl)) (np rfl))
        (fun _ _ => .app .bvar .bvar) (np rfl)) (np rfl)) (np rfl)) (np rfl)) (np rfl)
  have hMt : O.mem Mt (O.piR 1 (PS A B) fun _ => O.univ 1) := L.lamR_mem fun x hx => by rw [hF x hx]; exact hT
  have g := L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L HP dT) hA (np rfl)) hB (np rfl))
    hMt (np rfl)) hP (np rfl)
  have hL' : O.mem Lb (O.piR 1 A fun x => O.piR 1 B fun y =>
      O.app Mt (O.app (O.app (O.app (O.app (M.cval "Prod.mk" [0, 0]) A) B) x) y)) := by
    rw [L.piR_congr (B' := fun _ => O.piR 1 B fun _ => T) fun x hx =>
      L.piR_congr fun y hy => hMv _ (mk_mem (M := M) (ρ := ρ) L H hA hB hx hy)]
    exact hL
  have g2 := L.app_mem_piR g hL' (np rfl)
  rwa [hMv Pv hP] at g2

/-- **`HeadTy.cases`, discharged** -/
theorem cases_ty (H : EncEnv env) (HP : CasesPEnv env) {ρ : Nat → S} {l r R : Sh} {Hv Pv Lb : S}
    (hH : D O M.cval ρ (trM (apps (.c "Prod.casesOn" [1, 0, 0]) [shTy l, shTy r, .lam (shTy (.p l r)) (shTy R)])) Hv)
    (hP : O.mem Pv (tyS M (.p l r))) (hL : O.mem Lb (O.piR 1 (tyS M l) fun _ => O.piR 1 (tyS M r) fun _ => tyS M R)) :
    O.mem (O.app (O.app Hv Pv) Lb) (tyS M R) := by
  obtain ⟨H2, Mv, hH2, hM, rfl⟩ := app_inv hH
  obtain ⟨H1, Bv, hH1, hB, rfl⟩ := app_inv hH2
  obtain ⟨H0, Av, hH0, hA, rfl⟩ := app_inv hH1
  cases hH0
  rw [D_functional L hA (shTy_tyS M l), D_functional L hB (shTy_tyS M r)]
  obtain ⟨A', F, hA', hF, -, rfl⟩ := lam_inv hM
  obtain rfl := D_functional L hA' (shTy_tyS M (.p l r))
  exact casesP_set (M := M) (ρ := ρ) L H HP (tyS_univ (M := M) L H ρ l) (tyS_univ (M := M) L H ρ r) (tyS_univ (M := M) L H ρ R)
    (fun x hx => D_functional L (hF x hx) (shTy_tyS M R)) hP hL

/-- the stored `prod_c`, motive `fun _ => R` -/
def ProdCEnv (env : List Const) : Prop :=
  HasTy env "prod_c" [] (piN [(.sort 1, true), (.sort 1, true), (.sort 1, true),
      (.forallE (.bvar 2) (.forallE (.bvar 2) (.bvar 2) false) false, true), (.bvar 3, true), (.bvar 3, true)]
    (eqE 1 (.bvar 3)
      (.app (.app (.app (.app (.app (.const "Prod.casesOn" [1, 0, 0]) (.bvar 5)) (.bvar 4))
          (.lam (.app (.app (.const "Prod" [0, 0]) (.bvar 5)) (.bvar 4)) (.bvar 4) false))
        (.app (.app (.app (.app (.const "Prod.mk" [0, 0]) (.bvar 5)) (.bvar 4)) (.bvar 1)) (.bvar 0))) (.bvar 2))
      (.app (.app (.bvar 2) (.bvar 1)) (.bvar 0))))

/-- **`FactsM.cases`, discharged** -/
theorem cases_field (H : EncEnv env) (HP : CasesPEnv env) (HC : ProdCEnv env) {ρ : Nat → S} {l r Rs : Sh}
    {body : X} {Hv Lb R : S} {xv yv : ExprSpec.V} (hx : VSh l xv) (hy : VSh r yv)
    (hH : D O M.cval ρ (trM (apps (.c "Prod.casesOn" [1, 0, 0]) [shTy l, shTy r, .lam (shTy (.p l r)) (shTy Rs)])) Hv)
    (hLD : D O M.cval ρ (trM (.lam (shTy l) (.lam (shTy r) body))) Lb)
    (hL : O.mem Lb (O.piR 1 (tyS M l) fun _ => O.piR 1 (tyS M r) fun _ => tyS M Rs))
    (hR : R = O.app (O.app Hv (encM M (.p xv yv))) Lb) :
    D O M.cval (push (encM M yv) (push (encM M xv) ρ)) (trM body) R := by
  obtain ⟨H2, Mv, hH2, hM, rfl⟩ := app_inv hH
  obtain ⟨H1, Bv, hH1, hB, rfl⟩ := app_inv hH2
  obtain ⟨H0, Av, hH0, hA, rfl⟩ := app_inv hH1
  cases hH0
  rw [D_functional L hA (shTy_tyS M l), D_functional L hB (shTy_tyS M r)] at *
  obtain ⟨A', F, hA', hF, -, rfl⟩ := lam_inv hM
  obtain rfl := D_functional L hA' (shTy_tyS M (.p l r))
  have hF' : ∀ z, O.mem z (tyS M (.p l r)) → F z = tyS M Rs := fun z hz => D_functional L (hF z hz) (shTy_tyS M Rs)
  have hlu := tyS_univ (M := M) L H ρ l
  have hru := tyS_univ (M := M) L H ρ r
  have hRu := tyS_univ (M := M) L H ρ Rs
  have hxm : O.mem (encM M xv) (tyS M l) := by rw [← tyE_tyS M hx]; exact (encM_mem (M := M) (L := L) H ρ xv).1
  have hym : O.mem (encM M yv) (tyS M r) := by rw [← tyE_tyS M hy]; exact (encM_mem (M := M) (L := L) H ρ yv).1
  have hpair : encM M (.p xv yv) = O.app (O.app (O.app (O.app (M.cval "Prod.mk" [0, 0]) (tyS M l)) (tyS M r))
      (encM M xv)) (encM M yv) := by simp [encM, tyE_tyS M hx, tyE_tyS M hy]
  have hPm := mk_mem (M := M) (ρ := ρ) L H hlu hru hxm hym
  obtain ⟨ty, hc, hty⟩ := HC
  -- telescope: A B R f a b
  let ρ' := push (encM M yv) (push (encM M xv) (push Lb (push (tyS M Rs) (push (tyS M r) (push (tyS M l) ρ)))))
  have hmot : D O M.cval (push (encM M xv) (push Lb (push (tyS M Rs) (push (tyS M r) (push (tyS M l) ρ)))) |>
      push (encM M yv)) (.lam (.app (.app (.const "Prod" [0, 0]) (.bvar 5)) (.bvar 4)) (.bvar 4) false)
      (O.lamR (regime false) (tyS M (.p l r)) F) := by
    rw [L.lamR_congr hF']
    exact .lam (.app (.app .const .bvar) .bvar) (fun z _ => .bvar) (np rfl)
  have hlhs := casesP_set (M := M) (ρ := ρ) L H HP hlu hru hRu hF' hPm hL
  have hrhs : O.mem (O.app (O.app Lb (encM M xv)) (encM M yv)) (tyS M Rs) :=
    L.app_mem_piR (L.app_mem_piR hL hxm (np rfl)) hym (np rfl)
  have key := transferN L M hc (ls := []) hty ρ
    (.cons .sort hlu (.cons .sort hru (.cons .sort hRu (.cons (.pi .bvar (fun _ _ => .pi .bvar (fun _ _ => .bvar) (np rfl))
      (np rfl)) hL (.cons .bvar hxm (.cons .bvar hym .nil))))))
    .bvar (.app (.app (.app (.app (.app .const .bvar) .bvar) hmot) (.app (.app (.app (.app .const .bvar) .bvar) .bvar) .bvar)) .bvar)
    (.app (.app .bvar .bvar) .bvar) hRu hlhs hrhs
  simp only [push] at key
  subst hR
  rw [hpair, key]
  obtain ⟨A1, G, hA1, hG, -, rfl⟩ := lam_inv hLD
  obtain rfl := D_functional L hA1 (shTy_tyS M l)
  rw [L.app_lamR_pos (by simp [regime]) hxm]
  obtain ⟨A2, G2, hA2, hG2, -, hGe⟩ := lam_inv (hG _ hxm)
  obtain rfl := D_functional L hA2 (shTy_tyS M r)
  rw [hGe, L.app_lamR_pos (by simp [regime]) hym]; exact hG2 _ hym

end Bridge.Iota2
