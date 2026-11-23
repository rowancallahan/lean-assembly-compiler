/- Bridge.IteNat: the `ite` fact and head typing for Nat `==` (`condX true 1`: all 3 Nat-operand ites in C's emitted
Expr, in defs s22, o32, o38), DISCHARGED.  Stored theorem: `br_nbeq : ∀ a b : Nat,
@BEq.beq Nat (instBEqOfDecidableEq Nat instDecidableEqNat) a b = Nat.beq a b`; the ite itself reuses `Ite.ite_t/f`.

STATUS: proved, no sorry. -/
import Bridge.Final8

namespace Bridge.IteNat
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Iota2 Bridge.Asm Bridge.Add
  Bridge.Cmp Bridge.Ite Bridge.Final

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def beqN (a b : E) : E := .app (.app (.app (.app (.const "BEq.beq" [0]) tNat)
  (.app (.app (.const "instBEqOfDecidableEq" [0]) tNat) (.const "instDecidableEqNat" []))) a) b

structure NatEqEnv (env : List Const) : Prop where
  decN : HasTy env "instDecidableEqNat" [] (.app (.const "DecidableEq" [1]) tNat)
  brNbeq : HasTy env "br_nbeq" [] (piN [(tNat, true), (tNat, true)]
    (eqE 1 tB (beqN (.bvar 1) (.bvar 0)) (bin2 "Nat.beq" (.bvar 1) (.bvar 0))))

variable (L : SetLaws O)
include L

/-- `BEq.beq Nat inst X Y ∈ Bool` -/
theorem beqN_mem (H : EncEnv env) (HB : BeqEnv env) (HN : NatEqEnv env) {ρ : Nat → S} {X Y : S}
    (hX : O.mem X (M.cval "Nat" [])) (hY : O.mem Y (M.cval "Nat" [])) :
    O.mem (O.app (O.app (O.app (O.app (M.cval "BEq.beq" [0]) (M.cval "Nat" []))
      (O.app (O.app (M.cval "instBEqOfDecidableEq" [0]) (M.cval "Nat" [])) (M.cval "instDecidableEqNat" []))) X) Y)
      (M.cval "Bool" []) := by
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have dD : D O M.cval ρ (.app (.const "DecidableEq" [1]) tNat) _ := .app .const .const
  have hDec := mem_ty M L HN.decN dD
  have dI : D O M.cval ρ (.forallE (.sort 1) (.forallE (.app (.const "DecidableEq" [1]) (.bvar 0))
      (.app (.const "BEq" [0]) (.bvar 1)) false) false)
      (O.piR 1 (O.univ 1) fun a => O.piR 1 (O.app (M.cval "DecidableEq" [1]) a) fun _ => O.app (M.cval "BEq" [0]) a) :=
    .pi .sort (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .app .const .bvar) (np rfl)) (np rfl)
  have hI := L.app_mem_piR (L.app_mem_piR (mem_ty M L HB.ofDec dI) hNu (np rfl)) hDec (np rfl)
  have dH : D O M.cval ρ (.forallE (.sort 1) (.forallE (.app (.const "BEq" [0]) (.bvar 0))
      (.forallE (.bvar 1) (.forallE (.bvar 2) tB false) false) false) false)
      (O.piR 1 (O.univ 1) fun a => O.piR 1 (O.app (M.cval "BEq" [0]) a) fun _ => O.piR 1 a fun _ =>
        O.piR 1 a fun _ => M.cval "Bool" []) :=
    .pi .sort (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .pi .bvar (fun _ _ => .pi .bvar (fun _ _ => .const)
      (np rfl)) (np rfl)) (np rfl)) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L HB.beqH dH) hNu (np rfl)) hI (np rfl))
    hX (np rfl)) hY (np rfl)

/-- **Nat `==` on encodings** -/
theorem beqN_set (H : EncEnv env) (HC : CmpEnv env) (HB : BeqEnv env) (HN : NatEqEnv env) (ρ : Nat → S) (x y : Nat) :
    O.app (O.app (O.app (O.app (M.cval "BEq.beq" [0]) (M.cval "Nat" []))
      (O.app (O.app (M.cval "instBEqOfDecidableEq" [0]) (M.cval "Nat" [])) (M.cval "instDecidableEqNat" [])))
      (encM M (.n x))) (encM M (.n y)) = boolEnc M (x == y) := by
  have hBu := univ1 (M := M) (L := L) H HC.bool ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  obtain ⟨ty, hc, hty⟩ := HN.brNbeq
  have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn x) (.cons .const (hn y) .nil)) .const
    (.app (.app (.app (.app .const .const) (.app (.app .const .const) .const)) .bvar) .bvar)
    (.app (.app .const .bvar) .bvar) hBu
    (beqN_mem (ρ := ρ) L H HB HN (hn _) (hn _))
    (nnb_app (ρ := ρ) L H HC HC.beq (hn _) (hn _))
  simp only [push] at key
  show O.app (O.app _ (natEnc M x)) (natEnc M y) = _
  rw [key, beq_set L H HC ρ]

/-- typing of the Nat-`==` ite head -/
theorem iteEqN_ty (E : Env2 env sig P) (HN : NatEqEnv env) {ρ : Nat → S} {r : Sh} {a b c d : X} {Hv X Y : S}
    (hcd : condX true 1 a b = (c, d))
    (ha : ∀ A, D O M.cval ρ (trM a) A → O.mem A (tyS M .nt)) (hb : ∀ B, D O M.cval ρ (trM b) B → O.mem B (tyS M .nt))
    (hH : D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) Hv)
    (hX : O.mem X (tyS M r)) (hY : O.mem Y (tyS M r)) : O.mem (O.app (O.app Hv X) Y) (tyS M r) := by
  simp only [condX, ↓reduceIte, Prod.mk.injEq] at hcd
  obtain ⟨rfl, rfl⟩ := hcd
  obtain ⟨H2, Dv, hH2, hD, rfl⟩ := app_inv hH
  obtain ⟨H1, Cv, hH1, hC, rfl⟩ := app_inv hH2
  obtain ⟨H0, Rv, hH0, hRv, rfl⟩ := app_inv hH1
  cases hH0
  rw [D_functional L hRv (shTy_tyS M r)]
  obtain ⟨C2, Tv, hC2, hT, rfl⟩ := app_inv hC
  obtain ⟨C1, Qv, hC1, hQ, rfl⟩ := app_inv hC2
  obtain ⟨C0, Bv, hC0, hBv, rfl⟩ := app_inv hC1
  cases hC0; cases hBv; cases hT
  obtain ⟨D1, Q', hD1, hQ', rfl⟩ := app_inv hD
  obtain ⟨D0, Q'', hD0, hQ'', rfl⟩ := app_inv hD1
  cases hD0; cases hQ'
  obtain rfl := D_functional L hQ'' hQ
  obtain ⟨Q2, Bb, hQ2, hBb, rfl⟩ := app_inv hQ
  obtain ⟨Q1, Aa, hQ1, hAa, rfl⟩ := app_inv hQ2
  obtain ⟨Q0, Iv, hQ0, hIv, rfl⟩ := app_inv hQ1
  obtain ⟨Qh, Uv, hQh, hUv, rfl⟩ := app_inv hQ0
  cases hQh; cases hUv
  obtain ⟨I1, Dq, hI1, hDq, rfl⟩ := app_inv hIv
  obtain ⟨I0, Uw, hI0, hUw, rfl⟩ := app_inv hI1
  cases hI0; cases hUw; cases hDq
  have hTb := mem_ty M L E.cmp.btrue (ρ := ρ) .const
  have hQm := beqN_mem L E.enc E.beqE HN (ρ := ρ) (ha _ hAa) (hb _ hBb)
  exact ite_mem L E.iteE (ρ := ρ) (tyS_univ (M := M) L E.enc ρ r) (eqB_mem L E.cmp E.iteE (ρ := ρ) hQm hTb)
    (decB_mem L E.cmp E.beqE E.iteE (ρ := ρ) hQm hTb) hX hY

/-- **the `ite` fact for Nat `==`** -/
theorem iteEqN_field (E : Env2 env sig P) (HN : NatEqEnv env)
    {ρ : Nat → S} {r : Sh} {a b c d : X} {va vb : ExprSpec.V} {Hv Xt Xe : S}
    (hcd : condX true 1 a b = (c, d)) (hva : VSh .nt va) (hvb : VSh .nt vb)
    (iha : ∀ A, D O M.cval ρ (trM a) A → A = encM M va) (ihb : ∀ B, D O M.cval ρ (trM b) B → B = encM M vb)
    (hH : D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) Hv)
    (hXt : O.mem Xt (tyS M r)) (hXe : O.mem Xe (tyS M r)) :
    O.app (O.app Hv Xt) Xe = if cmpV 1 va vb then Xt else Xe := by
  have H := E.enc
  have HC := E.cmp
  have HB := E.beqE
  have HI := E.iteE
  cases hva with | nt x => ?_
  cases hvb with | nt y => ?_
  simp only [condX, ↓reduceIte, Prod.mk.injEq] at hcd
  obtain ⟨rfl, rfl⟩ := hcd
  obtain ⟨H2, Dv, hH2, hD, rfl⟩ := app_inv hH
  obtain ⟨H1, Cv, hH1, hC, rfl⟩ := app_inv hH2
  obtain ⟨H0, Rv, hH0, hRv, rfl⟩ := app_inv hH1
  cases hH0
  rw [D_functional L hRv (shTy_tyS M r)]
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
  rw [iha _ hAa, ihb _ hBb, beqN_set L H HC HB HN ρ x y]
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
  rw [iha _ hAa', ihb _ hBb', beqN_set L H HC HB HN ρ x y]
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

end Bridge.IteNat
