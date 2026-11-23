/- Bridge.IteLt: the `ite` fact and head typing for UInt64 `<` (`condX false 2`, operands without leading unused
`let`s, i.e. `a.dropHead = a`: true of all 238 `<`-ites in C's emitted Expr), DISCHARGED.  Stored theorems:
`ite_lt_t : ∀ (R : Type) (x y : Nat) (t e : R), Nat.blt x 2^64 = true → Nat.blt y 2^64 = true → Nat.blt x y = true →
  @ite R (UInt64.ofNat x < UInt64.ofNat y) (UInt64.decLt (UInt64.ofNat x) (UInt64.ofNat y)) t e = t` and `ite_lt_f`
(`Nat.blt x y = false`, `= e`).

STATUS: proved, no sorry. -/
import Bridge.Final

namespace Bridge.IteLt
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Iota2 Bridge.Asm Bridge.Add
  Bridge.Cmp Bridge.Ite Bridge.Final

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def ltU (a b : E) : E := .app (.app (.app (.app (.const "LT.lt" [0]) tU) (.const "instLTUInt64" [])) a) b
def decLtU (a b : E) : E := .app (.app (.const "UInt64.decLt" []) a) b
def bltG (a b : E) (v : E) : E := eqE 1 tB (bin2 "Nat.blt" a b) v

def iteLtTy (res : E) (v : E) : E :=
  piN [(.sort 1, true), (tNat, true), (tNat, true), (.bvar 2, true), (.bvar 3, true),
      (guard (.bvar 3), true), (guard (.bvar 3), true), (bltG (.bvar 5) (.bvar 4) v, true)]
    (eqE 1 (.bvar 7) (iteE (.bvar 7) (ltU (ofN (.bvar 6)) (ofN (.bvar 5))) (decLtU (ofN (.bvar 6)) (ofN (.bvar 5)))
      (.bvar 4) (.bvar 3)) res)

structure LtEnv (env : List Const) : Prop where
  ltC : HasTy env "LT" [0] (.forallE (.sort 1) (.sort 1) false)
  ltH : HasTy env "LT.lt" [0] (.forallE (.sort 1) (.forallE (.app (.const "LT" [0]) (.bvar 0))
    (.forallE (.bvar 1) (.forallE (.bvar 2) (.sort 0) false) false) false) false)
  instLt : HasTy env "instLTUInt64" [] (.app (.const "LT" [0]) tU)
  decLt : HasTy env "UInt64.decLt" [] (.forallE tU (.forallE tU (.app (.const "Decidable" []) (ltU (.bvar 1) (.bvar 0)))
    false) false)
  iteLtT : HasTy env "ite_lt_t" [] (iteLtTy (.bvar 4) tt)
  iteLtF : HasTy env "ite_lt_f" [] (iteLtTy (.bvar 3) ff)

variable (L : SetLaws O)
include L

theorem lt_mem (HL : LtEnv env) (H : EncEnv env) {ρ : Nat → S} {a b : S} (ha : O.mem a (M.cval "UInt64" []))
    (hb : O.mem b (M.cval "UInt64" [])) :
    O.mem (O.app (O.app (O.app (O.app (M.cval "LT.lt" [0]) (M.cval "UInt64" [])) (M.cval "instLTUInt64" [])) a) b)
      (O.univ 0) := by
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have dT : D O M.cval ρ (.forallE (.sort 1) (.forallE (.app (.const "LT" [0]) (.bvar 0))
      (.forallE (.bvar 1) (.forallE (.bvar 2) (.sort 0) false) false) false) false)
      (O.piR 1 (O.univ 1) fun α => O.piR 1 (O.app (M.cval "LT" [0]) α) fun _ => O.piR 1 α fun _ =>
        O.piR 1 α fun _ => O.univ 0) :=
    .pi .sort (fun _ _ => .pi (.app .const .bvar) (fun _ _ => .pi .bvar (fun _ _ => .pi .bvar (fun _ _ => .sort)
      (np rfl)) (np rfl)) (np rfl)) (np rfl)
  have hI := mem_ty M L HL.instLt (ρ := ρ) (.app .const .const)
  exact L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (L.app_mem_piR (mem_ty M L HL.ltH dT) hUu (np rfl)) hI (np rfl))
    ha (np rfl)) hb (np rfl)

theorem decLt_mem (HL : LtEnv env) {ρ : Nat → S} {a b : S} (ha : O.mem a (M.cval "UInt64" []))
    (hb : O.mem b (M.cval "UInt64" [])) :
    O.mem (O.app (O.app (M.cval "UInt64.decLt" []) a) b) (O.app (M.cval "Decidable" [])
      (O.app (O.app (O.app (O.app (M.cval "LT.lt" [0]) (M.cval "UInt64" [])) (M.cval "instLTUInt64" [])) a) b)) := by
  have dT : D O M.cval ρ (.forallE tU (.forallE tU (.app (.const "Decidable" []) (ltU (.bvar 1) (.bvar 0))) false) false)
      (O.piR 1 (M.cval "UInt64" []) fun x => O.piR 1 (M.cval "UInt64" []) fun y => O.app (M.cval "Decidable" [])
        (O.app (O.app (O.app (O.app (M.cval "LT.lt" [0]) (M.cval "UInt64" [])) (M.cval "instLTUInt64" [])) x) y)) :=
    .pi .const (fun _ _ => .pi .const (fun _ _ => .app .const (.app (.app (.app (.app .const .const) .const) .bvar) .bvar))
      (np rfl)) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (mem_ty M L HL.decLt dT) ha (np rfl)) hb (np rfl)

/-- invert the `<` ite head: its condition and instance at the operands' denotations -/
theorem ltHead_inv {ρ : Nat → S} {r : Sh} {a b : X} {Hv : S} (ha0 : a.dropHead = a) (hb0 : b.dropHead = b)
    (hH : D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, (condX false 2 a b).1, (condX false 2 a b).2])) Hv) :
    ∃ A B, D O M.cval ρ (trM a) A ∧ D O M.cval ρ (trM b) B ∧
      Hv = O.app (O.app (O.app (M.cval "ite" [1]) (tyS M r))
        (O.app (O.app (O.app (O.app (M.cval "LT.lt" [0]) (M.cval "UInt64" [])) (M.cval "instLTUInt64" [])) A) B))
        (O.app (O.app (M.cval "UInt64.decLt" []) A) B) := by
  simp only [condX, Bool.false_eq_true, ↓reduceIte, show (2 : Nat) ≠ 1 by decide, ha0, hb0] at hH
  obtain ⟨H2, Dv, hH2, hD, rfl⟩ := app_inv hH
  obtain ⟨H1, Cv, hH1, hC, rfl⟩ := app_inv hH2
  obtain ⟨H0, Rv, hH0, hRv, rfl⟩ := app_inv hH1
  cases hH0
  obtain ⟨C3, Bv, hC3, hB, rfl⟩ := app_inv hC
  obtain ⟨C2, Av, hC2, hA, rfl⟩ := app_inv hC3
  obtain ⟨C1, Iv, hC1, hI, rfl⟩ := app_inv hC2
  obtain ⟨C0, Uv, hC0, hU, rfl⟩ := app_inv hC1
  cases hC0; cases hU; cases hI
  obtain ⟨D1, Bv', hD1, hB', rfl⟩ := app_inv hD
  obtain ⟨D0, Av', hD0, hA', rfl⟩ := app_inv hD1
  cases hD0
  obtain rfl := D_functional L hA' hA
  obtain rfl := D_functional L hB' hB
  exact ⟨_, _, hA, hB, by rw [D_functional L hRv (shTy_tyS M r)]⟩

/-- **typing of the UInt64-`<` ite head** -/
theorem iteLtU_ty (E : Env2 env sig P) (HL : LtEnv env) {ρ : Nat → S} {r : Sh} {a b c d : X} {Hv X Y : S}
    (hcd : condX false 2 a b = (c, d)) (ha0 : a.dropHead = a) (hb0 : b.dropHead = b)
    (ha : ∀ A, D O M.cval ρ (trM a) A → O.mem A (tyS M .uw)) (hb : ∀ B, D O M.cval ρ (trM b) B → O.mem B (tyS M .uw))
    (hH : D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) Hv)
    (hX : O.mem X (tyS M r)) (hY : O.mem Y (tyS M r)) : O.mem (O.app (O.app Hv X) Y) (tyS M r) := by
  rw [← show (condX false 2 a b).1 = c from congrArg Prod.fst hcd, ← show (condX false 2 a b).2 = d from
    congrArg Prod.snd hcd] at hH
  obtain ⟨A, B, hA, hB, rfl⟩ := ltHead_inv L ha0 hb0 hH
  exact ite_mem L E.iteE (ρ := ρ) (tyS_univ (M := M) L E.enc ρ r) (lt_mem L HL E.enc (ρ := ρ) (ha _ hA) (hb _ hB))
    (decLt_mem L HL (ρ := ρ) (ha _ hA) (hb _ hB)) hX hY

/-- **the `ite` fact for UInt64 `<`** -/
theorem iteLtU_field (E : Env2 env sig P) (HL : LtEnv env) (hbl : HasTy env "br_litN" [] brLitNTy)
    {ρ : Nat → S} {r : Sh} {a b c d : X} {va vb : ExprSpec.V} {Hv Xt Xe : S}
    (hcd : condX false 2 a b = (c, d)) (ha0 : a.dropHead = a) (hb0 : b.dropHead = b)
    (hva : VSh .uw va) (hvb : VSh .uw vb)
    (iha : ∀ A, D O M.cval ρ (trM a) A → A = encM M va) (ihb : ∀ B, D O M.cval ρ (trM b) B → B = encM M vb)
    (hH : D O M.cval ρ (trM (apps (.c "ite" [1]) [shTy r, c, d])) Hv)
    (hXt : O.mem Xt (tyS M r)) (hXe : O.mem Xe (tyS M r)) :
    O.app (O.app Hv Xt) Xe = if cmpV 2 va vb then Xt else Xe := by
  cases hva with | uw x => ?_
  cases hvb with | uw y => ?_
  rw [← show (condX false 2 a b).1 = c from congrArg Prod.fst hcd, ← show (condX false 2 a b).2 = d from
    congrArg Prod.snd hcd] at hH
  obtain ⟨A, B, hA, hB, rfl⟩ := ltHead_inv L ha0 hb0 hH
  rw [iha _ hA, ihb _ hB]
  have hRu := tyS_univ (M := M) L E.enc ρ r
  have hn := natEnc_mem' (M := M) (L := L) E.enc ρ
  have hxm := (encM_mem (M := M) (L := L) E.enc ρ (.w x)).1
  have hym := (encM_mem (M := M) (L := L) E.enc ρ (.w y)).1
  have hlhs := ite_mem L E.iteE (ρ := ρ) hRu (lt_mem L HL E.enc (ρ := ρ) hxm hym) (decLt_mem L HL (ρ := ρ) hxm hym) hXt hXe
  -- telescope R x y t e g1 g2 g3
  let ρ5 := push Xe (push Xt (push (natEnc M y.toNat) (push (natEnc M x.toNat) (push (tyS M r) ρ))))
  obtain ⟨G1, hG1, hp1⟩ := guard_mem (ρ := ρ5) (i := 3) L E.enc E.lit E.instN E.cmp hbl rfl x.toNat_lt_size
  obtain ⟨G2, hG2, hp2⟩ := guard_mem (ρ := push O.pt ρ5) (i := 3) L E.enc E.lit E.instN E.cmp hbl rfl y.toNat_lt_size
  have hBu := univ1 (M := M) (L := L) E.enc E.cmp.bool ρ
  have hblt := blt_set (M := M) L E.enc E.cmp ρ x.toNat y.toNat
  have hbltm : O.mem (O.app (O.app (M.cval "Nat.blt" []) (natEnc M x.toNat)) (natEnc M y.toNat)) (M.cval "Bool" []) := by
    rw [hblt]; exact bool_mem L E.cmp ρ _
  simp only [cmpV, show (2 : Nat) ≠ 1 by decide, ↓reduceIte]
  have hlt : decide (x < y) = decide (x.toNat < y.toNat) := by simp [UInt64.lt_iff_toNat_lt]
  cases hxy : decide (x < y)
  · rw [hxy] at hlt
    have hg3 : O.mem O.pt (O.app (O.app (O.app (M.cval "Eq" [1]) (M.cval "Bool" []))
        (O.app (O.app (M.cval "Nat.blt" []) (natEnc M x.toNat)) (natEnc M y.toNat))) (M.cval "Bool.false" [])) := by
      rw [M.eq_equality 1 ρ _ _ _ _ .const hBu hbltm (mem_ty M L E.cmp.bfalse (ρ := ρ) .const)]
      exact L.pt_mem_eqv (by rw [hblt, ← hlt]; rfl)
    obtain ⟨ty, hc, hty⟩ := HL.iteLtF
    exact transferN L M hc (ls := []) hty ρ
      (.cons .sort hRu (.cons .const (hn _) (.cons .const (hn _) (.cons .bvar hXt (.cons .bvar hXe
        (.cons hG1 hp1 (.cons hG2 hp2 (.cons (.app (.app (.app .const .const) (.app (.app .const .bvar) .bvar)) .const) hg3
          .nil)))))))) .bvar
      (.app (.app (.app (.app (.app .const .bvar) (.app (.app (.app (.app .const .const) .const) (.app .const .bvar))
        (.app .const .bvar))) (.app (.app .const (.app .const .bvar)) (.app .const .bvar))) .bvar) .bvar) .bvar
      hRu hlhs hXe
  · rw [hxy] at hlt
    have hg3 : O.mem O.pt (O.app (O.app (O.app (M.cval "Eq" [1]) (M.cval "Bool" []))
        (O.app (O.app (M.cval "Nat.blt" []) (natEnc M x.toNat)) (natEnc M y.toNat))) (M.cval "Bool.true" [])) := by
      rw [M.eq_equality 1 ρ _ _ _ _ .const hBu hbltm (mem_ty M L E.cmp.btrue (ρ := ρ) .const)]
      exact L.pt_mem_eqv (by rw [hblt, ← hlt]; rfl)
    obtain ⟨ty, hc, hty⟩ := HL.iteLtT
    exact transferN L M hc (ls := []) hty ρ
      (.cons .sort hRu (.cons .const (hn _) (.cons .const (hn _) (.cons .bvar hXt (.cons .bvar hXe
        (.cons hG1 hp1 (.cons hG2 hp2 (.cons (.app (.app (.app .const .const) (.app (.app .const .bvar) .bvar)) .const) hg3
          .nil)))))))) .bvar
      (.app (.app (.app (.app (.app .const .bvar) (.app (.app (.app (.app .const .const) .const) (.app .const .bvar))
        (.app .const .bvar))) (.app (.app .const (.app .const .bvar)) (.app .const .bvar))) .bvar) .bvar) .bvar
      hRu hlhs hXt

end Bridge.IteLt
