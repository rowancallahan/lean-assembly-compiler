/- Bridge.Ite: the `ite` fact for UInt64 `==` (the `condX false 1` case), DISCHARGED.  Stored theorems:
`ite_t : ∀ (R : Type) (t e : R), @ite R (true = true) (instDecidableEqBool true true) t e = t`, `ite_f` (`false`, `= e`),
`deqB : DecidableEq Bool = ((a b : Bool) → Decidable (a = b))` (`rfl`; the instance's type is an abbreviation), and
`Cmp.br_beq` for the condition's value.  Typing through `ite.{1}`, `Eq.{1}`, `Decidable` (the level issue (a) of
§11 does not show in the trimmed model).  Open: `<` (`decLt`, needs the `dropHead` weakening) and the Nat versions.

STATUS: proved, no sorry. -/
import Bridge.Cmp

namespace Bridge.Ite
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Iota2 Bridge.Asm Bridge.Add
  Bridge.Cmp

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def eqB (a b : E) : E := .app (.app (.app (.const "Eq" [1]) tB) a) b
def decB (a b : E) : E := .app (.app (.const "instDecidableEqBool" []) a) b
def iteE (R c d t e : E) : E := .app (.app (.app (.app (.app (.const "ite" [1]) R) c) d) t) e

structure IteEnv (env : List Const) : Prop where
  eqT : HasTy env "Eq" [1] (.forallE (.sort 1) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort 0) false) false) false)
  dec : HasTy env "Decidable" [] (.forallE (.sort 0) (.sort 1) false)
  instB : HasTy env "instDecidableEqBool" [] (.app (.const "DecidableEq" [1]) tB)
  deqB : HasTy env "deqB" [] (eqE 2 (.sort 1) (.app (.const "DecidableEq" [1]) tB)
    (.forallE tB (.forallE tB (.app (.const "Decidable" []) (eqB (.bvar 1) (.bvar 0))) false) false))
  iteT : HasTy env "ite" [1] (.forallE (.sort 1) (.forallE (.sort 0) (.forallE (.app (.const "Decidable" []) (.bvar 0))
    (.forallE (.bvar 2) (.forallE (.bvar 3) (.bvar 4) false) false) false) false) false)
  ite_t : HasTy env "ite_t" [] (piN [(.sort 1, true), (.bvar 0, true), (.bvar 1, true)]
    (eqE 1 (.bvar 2) (iteE (.bvar 2) (eqB tt tt) (decB tt tt) (.bvar 1) (.bvar 0)) (.bvar 1)))
  ite_f : HasTy env "ite_f" [] (piN [(.sort 1, true), (.bvar 0, true), (.bvar 1, true)]
    (eqE 1 (.bvar 2) (iteE (.bvar 2) (eqB ff tt) (decB ff tt) (.bvar 1) (.bvar 0)) (.bvar 0)))

variable (L : SetLaws O)
include L

theorem eqB_mem (HC : CmpEnv env) (HI : IteEnv env) {ρ : Nat → S} {a b : S} (ha : O.mem a (M.cval "Bool" []))
    (hb : O.mem b (M.cval "Bool" [])) :
    O.mem (O.app (O.app (O.app (M.cval "Eq" [1]) (M.cval "Bool" [])) a) b) (O.univ 0) := by
  have dE : D O M.cval ρ (.forallE (.sort 1) (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort 0) false) false) false)
      (O.piR 1 (O.univ 1) fun α => O.piR 1 α fun _ => O.piR 1 α fun _ => O.univ 0) :=
    .pi .sort (fun _ _ => .pi .bvar (fun _ _ => .pi .bvar (fun _ _ => .sort) (np rfl)) (np rfl)) (np rfl)
  have hBu : O.mem (M.cval "Bool" []) (O.univ 1) := mem_ty M L HC.bool (ρ := ρ) .sort
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L HI.eqT dE) hBu (np rfl)) ha (np rfl)) hb (np rfl)

theorem dec_univ (HI : IteEnv env) {ρ : Nat → S} {p : S} (hp : O.mem p (O.univ 0)) :
    O.mem (O.app (M.cval "Decidable" []) p) (O.univ 1) := by
  have dD : D O M.cval ρ (.forallE (.sort 0) (.sort 1) false) (O.piR 1 (O.univ 0) fun _ => O.univ 1) :=
    .pi .sort (fun _ _ => .sort) (np rfl)
  exact L.app_mem_piR (mem_ty M L HI.dec dD) hp (np rfl)

/-- `instDecidableEqBool a b ∈ Decidable (a = b)`, through the stored unfolding `deqB` -/
theorem decB_mem (HC : CmpEnv env) (HB : BeqEnv env) (HI : IteEnv env) {ρ : Nat → S} {a b : S}
    (ha : O.mem a (M.cval "Bool" [])) (hb : O.mem b (M.cval "Bool" [])) :
    O.mem (O.app (O.app (M.cval "instDecidableEqBool" []) a) b)
      (O.app (M.cval "Decidable" []) (O.app (O.app (O.app (M.cval "Eq" [1]) (M.cval "Bool" [])) a) b)) := by
  have hBu : O.mem (M.cval "Bool" []) (O.univ 1) := mem_ty M L HC.bool (ρ := ρ) .sort
  let PI := O.piR (regime false) (M.cval "Bool" []) fun x => O.piR (regime false) (M.cval "Bool" []) fun y =>
    O.app (M.cval "Decidable" []) (O.app (O.app (O.app (M.cval "Eq" [1]) (M.cval "Bool" [])) x) y)
  have dPI : D O M.cval ρ (.forallE tB (.forallE tB (.app (.const "Decidable" []) (eqB (.bvar 1) (.bvar 0))) false) false) PI :=
    .pi .const (fun _ _ => .pi .const (fun _ _ => .app .const (.app (.app (.app .const .const) .bvar) .bvar)) (np rfl))
      (np rfl)
  have dDQ : D O M.cval ρ (.forallE (.sort 1) (.sort 1) false) (O.piR 1 (O.univ 1) fun _ => O.univ 1) :=
    .pi .sort (fun _ _ => .sort) (np rfl)
  have hl : O.mem (O.app (M.cval "DecidableEq" [1]) (M.cval "Bool" [])) (O.univ 1) :=
    L.app_mem_piR (mem_ty M L HB.deq dDQ) hBu (np rfl)
  have hr : O.mem PI (O.univ 1) := L.piR_mem_univ (by decide) hBu fun x hx =>
    L.piR_mem_univ (by decide) hBu fun y hy => dec_univ L HI (ρ := ρ) (eqB_mem L HC HI (ρ := ρ) hx hy)
  obtain ⟨ty, hc, hty⟩ := HI.deqB
  have key := transferN L M hc (ls := []) (ts := []) hty ρ .nil .sort (.app .const .const) dPI (L.univ_mem_univ 1) hl hr
  have hI := mem_ty M L HI.instB (ρ := ρ) (.app .const .const)
  rw [key] at hI
  exact L.app_mem_piR (L.app_mem_piR hI ha (np rfl)) hb (np rfl)

/-- `ite.{1} R c d t e ∈ R` -/
theorem ite_mem (HI : IteEnv env) {ρ : Nat → S} {R c d t e : S} (hR : O.mem R (O.univ 1)) (hc : O.mem c (O.univ 0))
    (hd : O.mem d (O.app (M.cval "Decidable" []) c)) (ht : O.mem t R) (he : O.mem e R) :
    O.mem (O.app (O.app (O.app (O.app (O.app (M.cval "ite" [1]) R) c) d) t) e) R := by
  have dT : D O M.cval ρ (.forallE (.sort 1) (.forallE (.sort 0) (.forallE (.app (.const "Decidable" []) (.bvar 0))
      (.forallE (.bvar 2) (.forallE (.bvar 3) (.bvar 4) false) false) false) false) false)
      (O.piR 1 (O.univ 1) fun α => O.piR 1 (O.univ 0) fun c => O.piR 1 (O.app (M.cval "Decidable" []) c) fun _ =>
        O.piR 1 α fun _ => O.piR 1 α fun _ => α) :=
    .pi .sort (fun _ _ => .pi .sort (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .pi .bvar (fun _ _ => .pi .bvar
      (fun _ _ => .bvar) (np rfl)) (np rfl)) (np rfl)) (np rfl)) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L HI.iteT dT) hR (np rfl))
    hc (np rfl)) hd (np rfl)) ht (np rfl)) he (np rfl)

/-- **the `ite` fact for UInt64 `==`** -/
theorem iteEqU_field (H : EncEnv env) (HL : LitEnv env) (HN : InstN env) (HC : CmpEnv env) (HB : BeqEnv env)
    (HI : IteEnv env)
    (hbl : HasTy env "br_litN" [] (piN [(tNat, true)] (eqE 1 tNat
      (.app (.app (.app (.const "OfNat.ofNat" [0]) tNat) (.bvar 0)) (.app (.const "instOfNatNat" []) (.bvar 0)))
      (.bvar 0))))
    {ρ : Nat → S} {r : Sh} {a b c d : X} {va vb : ExprSpec.V} {Hv Xt Xe : S}
    (hcd : condX false 1 a b = (c, d)) (hva : VSh .uw va) (hvb : VSh .uw vb)
    (iha : ∀ A, D O M.cval ρ (trM a) A → A = encM M va) (ihb : ∀ B, D O M.cval ρ (trM b) B → B = encM M vb)
    (hH : D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) Hv)
    (hXt : O.mem Xt (tyS M r)) (hXe : O.mem Xe (tyS M r)) :
    O.app (O.app Hv Xt) Xe = if cmpV 1 va vb then Xt else Xe := by
  cases hva with | uw x => ?_
  cases hvb with | uw y => ?_
  simp only [condX, ↓reduceIte, Bool.false_eq_true, Prod.mk.injEq] at hcd
  obtain ⟨rfl, rfl⟩ := hcd
  -- invert the head
  obtain ⟨H2, Dv, hH2, hD, rfl⟩ := app_inv hH
  obtain ⟨H1, Cv, hH1, hC, rfl⟩ := app_inv hH2
  obtain ⟨H0, Rv, hH0, hRv, rfl⟩ := app_inv hH1
  cases hH0
  rw [D_functional L hRv (shTy_tyS M r)]
  -- the condition
  obtain ⟨C2, Tv, hC2, hT, rfl⟩ := app_inv hC
  obtain ⟨C1, Qv, hC1, hQ, rfl⟩ := app_inv hC2
  obtain ⟨C0, Bv, hC0, hBv, rfl⟩ := app_inv hC1
  cases hC0; cases hBv; cases hT
  obtain ⟨Q2, Bb, hQ2, hBb, rfl⟩ := app_inv hQ
  obtain ⟨Q1, Aa, hQ1, hAa, rfl⟩ := app_inv hQ2
  obtain ⟨Q0, Iv, hQ0, hIv, rfl⟩ := app_inv hQ1
  obtain ⟨Qh, Uv, hQh, hUv, rfl⟩ := app_inv hQ0
  cases hQh; cases hUv
  obtain ⟨I1, Dq, hI1, hDq, rfl⟩ := app_inv hIv
  obtain ⟨I0, Uw, hI0, hUw, rfl⟩ := app_inv hI1
  cases hI0; cases hUw; cases hDq
  rw [iha _ hAa, ihb _ hBb, beqU_set L H HL HN HC HB hbl ρ x y]
  -- the instance
  obtain ⟨D1, Q', hD1, hQ', rfl⟩ := app_inv hD
  obtain ⟨D0, Q'', hD0, hQ'', rfl⟩ := app_inv hD1
  cases hD0; cases hQ'
  obtain ⟨Q2', Bb', hQ2', hBb', rfl⟩ := app_inv hQ''
  obtain ⟨Q1', Aa', hQ1', hAa', rfl⟩ := app_inv hQ2'
  obtain ⟨Q0', Iv', hQ0', hIv', rfl⟩ := app_inv hQ1'
  obtain ⟨Qh', Uv', hQh', hUv', rfl⟩ := app_inv hQ0'
  cases hQh'; cases hUv'
  obtain ⟨I1', Dq', hI1', hDq', rfl⟩ := app_inv hIv'
  obtain ⟨I0', Uw', hI0', hUw', rfl⟩ := app_inv hI1'
  cases hI0'; cases hUw'; cases hDq'
  rw [iha _ hAa', ihb _ hBb', beqU_set L H HL HN HC HB hbl ρ x y]
  -- the transfer
  have hRu := tyS_univ (M := M) L H ρ r
  have hTb := mem_ty M L HC.btrue (ρ := ρ) .const
  have hBm := bool_mem (M := M) L HC ρ (x == y)
  have hc := eqB_mem L HC HI (ρ := ρ) hBm hTb
  have hd := decB_mem L HC HB HI (ρ := ρ) hBm hTb
  have hlhs := ite_mem L HI (ρ := ρ) hRu hc hd hXt hXe
  simp only [cmpV, ↓reduceIte]
  cases hxy : x == y
  · obtain ⟨ty, hc', hty⟩ := HI.ite_f
    simp only [boolEnc, hxy, Bool.false_eq_true, ↓reduceIte] at hlhs ⊢
    exact transferN L M hc' (ls := []) hty ρ (.cons .sort hRu (.cons .bvar hXt (.cons .bvar hXe .nil))) .bvar
      (.app (.app (.app (.app (.app .const .bvar) (.app (.app (.app .const .const) .const) .const))
        (.app (.app .const .const) .const)) .bvar) .bvar) .bvar hRu hlhs hXe
  · obtain ⟨ty, hc', hty⟩ := HI.ite_t
    simp only [boolEnc, hxy, ↓reduceIte] at hlhs ⊢
    exact transferN L M hc' (ls := []) hty ρ (.cons .sort hRu (.cons .bvar hXt (.cons .bvar hXe .nil))) .bvar
      (.app (.app (.app (.app (.app .const .bvar) (.app (.app (.app .const .const) .const) .const))
        (.app (.app .const .const) .const)) .bvar) .bvar) .bvar hRu hlhs hXt

end Bridge.Ite
