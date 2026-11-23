/- Bridge.Bits: `.bin` for `&&&` (op 4) and `|||` (op 5), DISCHARGED.  Stored theorems (all proved true in core Lean,
see the §11 notes): `land_z : Nat.land 0 b = 0`, `lor_z : Nat.lor 0 b = b`,
`land_r : Nat.land a b = 2 * Nat.land (a/2) (b/2) + a%2 * (b%2)`,
`lor_r : Nat.lor a b = 2 * Nat.lor (a/2) (b/2) + (a%2 + b%2 + a%2 * (b%2)) % 2`,
`br_and : ofNat a &&& ofNat b = ofNat (Nat.land a b)`, `br_or : ofNat a ||| ofNat b = ofNat (Nat.lor a b)`.

STATUS: proved, no sorry. -/
import Bridge.Final7

namespace Bridge.Bits
open ExprSpec ParSpec Bridge.Typed Bridge.Mini Bridge.EvM Bridge.TT Bridge.HT Bridge.Asm Bridge.Add Bridge.Final
  Bridge.Call Bridge.Len Bridge.Cmp Bridge.Final5 Bridge.Arith Bridge.Bytes Bridge.Final6 Bridge.Shift

variable {S : Type} {O : SetOps S} {env : List Const} {M : Model O env}

def andU (a b : E) : E := opE "HAnd.hAnd" "instHAndOfAndOp" tU "instAndOpUInt64" a b
def orU (a b : E) : E := opE "HOr.hOr" "instHOrOfOrOp" tU "instOrOpUInt64" a b
def two : E := litNat 2
def recTy (f : String) (low : E → E → E) : E := piN [(tNat, true), (tNat, true)]
  (eqE 1 tNat (bin2 f (.bvar 1) (.bvar 0))
    (addN (mulN two (bin2 f (divN (.bvar 1) two) (divN (.bvar 0) two))) (low (modN (.bvar 1) two) (modN (.bvar 0) two))))

structure BitsEnv (env : List Const) : Prop where
  andC : OpCore env "HAnd.hAnd" "HAnd" "instHAndOfAndOp" "AndOp"
  andI : HasTy env "instAndOpUInt64" [] (.app (.const "AndOp" [0]) tU)
  orC : OpCore env "HOr.hOr" "HOr" "instHOrOfOrOp" "OrOp"
  orI : HasTy env "instOrOpUInt64" [] (.app (.const "OrOp" [0]) tU)
  landH : HasTy env "Nat.land" [] (.forallE tNat (.forallE tNat tNat false) false)
  lorH : HasTy env "Nat.lor" [] (.forallE tNat (.forallE tNat tNat false) false)
  landZ : HasTy env "land_z" [] (piN [(tNat, true)] (eqE 1 tNat (bin2 "Nat.land" nz (.bvar 0)) nz))
  lorZ : HasTy env "lor_z" [] (piN [(tNat, true)] (eqE 1 tNat (bin2 "Nat.lor" nz (.bvar 0)) (.bvar 0)))
  landR : HasTy env "land_r" [] (recTy "Nat.land" mulN)
  lorR : HasTy env "lor_r" [] (recTy "Nat.lor" fun x y => modN (addN (addN x y) (mulN x y)) two)
  brAnd : HasTy env "br_and" [] (piN [(tNat, true), (tNat, true)]
    (eqE 1 tU (andU (ofN (.bvar 1)) (ofN (.bvar 0))) (ofN (bin2 "Nat.land" (.bvar 1) (.bvar 0)))))
  brOr : HasTy env "br_or" [] (piN [(tNat, true), (tNat, true)]
    (eqE 1 tU (orU (ofN (.bvar 1)) (ofN (.bvar 0))) (ofN (bin2 "Nat.lor" (.bvar 1) (.bvar 0)))))

variable (L : SetLaws O)
include L

theorem bin2_mem {f : String} (hf : HasTy env f [] (.forallE tNat (.forallE tNat tNat false) false)) (ρ : Nat → S)
    {a b : S} (ha : O.mem a (M.cval "Nat" [])) (hb : O.mem b (M.cval "Nat" [])) :
    O.mem (O.app (O.app (M.cval f []) a) b) (M.cval "Nat" []) := by
  have dP : D O M.cval ρ (.forallE tNat (.forallE tNat tNat false) false) _ :=
    .pi .const (fun _ _ => .pi .const (fun _ _ => .const) (np rfl)) (np rfl)
  exact L.app_mem_piR (L.app_mem_piR (mem_ty M L hf dP) ha (np rfl)) hb (np rfl)

omit L in
theorem land_rec (a b : Nat) : Nat.land a b = 2 * Nat.land (a / 2) (b / 2) + a % 2 * (b % 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [show Nat.land a b = a &&& b from rfl, show Nat.land (a/2) (b/2) = (a/2) &&& (b/2) from rfl]
  have hr : a % 2 * (b % 2) < 2 := by
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> rcases Nat.mod_two_eq_zero_or_one b with h' | h' <;> simp [h, h']
  cases i with
  | zero =>
    rw [Nat.testBit_and]
    simp only [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> rcases Nat.mod_two_eq_zero_or_one b with h' | h' <;>
      simp [h, h', Nat.add_mod, Nat.mul_mod_right]
  | succ i =>
    rw [Nat.testBit_succ, Nat.testBit_succ, show (2 * (a / 2 &&& b / 2) + a % 2 * (b % 2)) / 2 = (a / 2 &&& b / 2) by omega,
      Nat.testBit_and, ← Nat.testBit_succ, Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ]

omit L in
theorem lor_rec (a b : Nat) :
    Nat.lor a b = 2 * Nat.lor (a / 2) (b / 2) + (a % 2 + b % 2 + a % 2 * (b % 2)) % 2 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [show Nat.lor a b = a ||| b from rfl, show Nat.lor (a/2) (b/2) = (a/2) ||| (b/2) from rfl]
  cases i with
  | zero =>
    rw [Nat.testBit_or]
    simp only [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> rcases Nat.mod_two_eq_zero_or_one b with h' | h' <;>
      simp [h, h', Nat.add_mod, Nat.mul_mod_right]
  | succ i =>
    rw [Nat.testBit_succ, Nat.testBit_succ,
      show (2 * (a / 2 ||| b / 2) + (a % 2 + b % 2 + a % 2 * (b % 2)) % 2) / 2 = (a / 2 ||| b / 2) by omega,
      Nat.testBit_or, ← Nat.testBit_succ, Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ]

theorem land_set (E : Final7.Env7 env sig P) (HB : BitsEnv env) (hbl : HasTy env "br_litN" [] brLitNTy)
    (ρ : Nat → S) : ∀ a b, O.app (O.app (M.cval "Nat.land" []) (natEnc M a)) (natEnc M b) = natEnc M (Nat.land a b) := by
  have H := E.enc
  have HA := E.add
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have l2 := litNat_D (M := M) L E.toEnv hbl
  have md : ∀ x, O.app (O.app (opS M "HMod.hMod" "instHMod" (M.cval "Nat" []) "Nat.instMod") (natEnc M x)) (natEnc M 2)
      = natEnc M (x % 2) := fun x => (modDiv_set L H HA E.mul E.shift E.cmp ρ x 2 (by decide)).1
  have dv : ∀ x, O.app (O.app (opS M "HDiv.hDiv" "instHDiv" (M.cval "Nat" []) "Nat.instDiv") (natEnc M x)) (natEnc M 2)
      = natEnc M (x / 2) := fun x => (modDiv_set L H HA E.mul E.shift E.cmp ρ x 2 (by decide)).2
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
  intro b
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain ⟨ty, hc, hty⟩ := HB.landZ
    have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn b) .nil) .const
      (.app (.app .const .const) .bvar) .const hNu (bin2_mem L HB.landH ρ (hn 0) (hn b)) (hn 0)
    simp only [push] at key
    rw [show Nat.land 0 b = 0 from Nat.zero_and b]; exact key
  · obtain ⟨ty, hc, hty⟩ := HB.landR
    have hR : O.app (O.app (opS M "HAdd.hAdd" "instHAdd" (M.cval "Nat" []) "instAddNat")
        (O.app (O.app (opS M "HMul.hMul" "instHMul" (M.cval "Nat" []) "instMulNat") (natEnc M 2))
          (O.app (O.app (M.cval "Nat.land" [])
            (O.app (O.app (opS M "HDiv.hDiv" "instHDiv" (M.cval "Nat" []) "Nat.instDiv") (natEnc M a)) (natEnc M 2)))
            (O.app (O.app (opS M "HDiv.hDiv" "instHDiv" (M.cval "Nat" []) "Nat.instDiv") (natEnc M b)) (natEnc M 2)))))
        (O.app (O.app (opS M "HMul.hMul" "instHMul" (M.cval "Nat" []) "instMulNat")
          (O.app (O.app (opS M "HMod.hMod" "instHMod" (M.cval "Nat" []) "Nat.instMod") (natEnc M a)) (natEnc M 2)))
          (O.app (O.app (opS M "HMod.hMod" "instHMod" (M.cval "Nat" []) "Nat.instMod") (natEnc M b)) (natEnc M 2)))
        = natEnc M (Nat.land a b) := by
      rw [dv, dv, md, md, ih (a / 2) (by omega), mul_set L H E.add E.mul ρ, mul_set L H E.add E.mul ρ,
        add_set L H E.add ρ, ← land_rec]
    have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn a) (.cons .const (hn b) .nil)) .const
      (.app (.app .const .bvar) .bvar)
      (.app (.app (opS_D _ _) (.app (.app (opS_D _ _) (l2 _ 2)) (.app (.app .const
          (.app (.app (opS_D _ _) .bvar) (l2 _ 2))) (.app (.app (opS_D _ _) .bvar) (l2 _ 2)))))
        (.app (.app (opS_D _ _) (.app (.app (opS_D _ _) .bvar) (l2 _ 2))) (.app (.app (opS_D _ _) .bvar) (l2 _ 2))))
      hNu (bin2_mem L HB.landH ρ (hn a) (hn b)) (by simp only [push]; rw [hR]; exact hn _)
    simp only [push] at key
    rw [key, hR]

theorem lor_set (E : Final7.Env7 env sig P) (HB : BitsEnv env) (hbl : HasTy env "br_litN" [] brLitNTy)
    (ρ : Nat → S) : ∀ a b, O.app (O.app (M.cval "Nat.lor" []) (natEnc M a)) (natEnc M b) = natEnc M (Nat.lor a b) := by
  have H := E.enc
  have hNu := univ1 (M := M) (L := L) H H.nat ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have l2 := litNat_D (M := M) L E.toEnv hbl
  have md : ∀ x, O.app (O.app (opS M "HMod.hMod" "instHMod" (M.cval "Nat" []) "Nat.instMod") (natEnc M x)) (natEnc M 2)
      = natEnc M (x % 2) := fun x => (modDiv_set L H E.add E.mul E.shift E.cmp ρ x 2 (by decide)).1
  have dv : ∀ x, O.app (O.app (opS M "HDiv.hDiv" "instHDiv" (M.cval "Nat" []) "Nat.instDiv") (natEnc M x)) (natEnc M 2)
      = natEnc M (x / 2) := fun x => (modDiv_set L H E.add E.mul E.shift E.cmp ρ x 2 (by decide)).2
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
  intro b
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain ⟨ty, hc, hty⟩ := HB.lorZ
    have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn b) .nil) .const
      (.app (.app .const .const) .bvar) .bvar hNu (bin2_mem L HB.lorH ρ (hn 0) (hn b)) (hn b)
    simp only [push] at key
    rw [show Nat.lor 0 b = b from Nat.zero_or b]; exact key
  · obtain ⟨ty, hc, hty⟩ := HB.lorR
    have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn a) (.cons .const (hn b) .nil)) .const
      (.app (.app .const .bvar) .bvar)
      (.app (.app (opS_D _ _) (.app (.app (opS_D _ _) (l2 _ 2)) (.app (.app .const
          (.app (.app (opS_D _ _) .bvar) (l2 _ 2))) (.app (.app (opS_D _ _) .bvar) (l2 _ 2)))))
        (.app (.app (opS_D _ _) (.app (.app (opS_D _ _)
          (.app (.app (opS_D _ _) (.app (.app (opS_D _ _) .bvar) (l2 _ 2))) (.app (.app (opS_D _ _) .bvar) (l2 _ 2))))
          (.app (.app (opS_D _ _) (.app (.app (opS_D _ _) .bvar) (l2 _ 2))) (.app (.app (opS_D _ _) .bvar) (l2 _ 2)))))
          (l2 _ 2)))
      hNu (bin2_mem L HB.lorH ρ (hn a) (hn b)) (by simp only [push]; rw [dv, dv, md, md, ih (a / 2) (by omega), mul_set L H E.add E.mul ρ, mul_set L H E.add E.mul ρ, add_set L H E.add ρ, add_set L H E.add ρ, md, add_set L H E.add ρ, ← lor_rec]; exact hn _)
    simp only [push] at key
    rw [key, dv, dv, md, md, ih (a / 2) (by omega), mul_set L H E.add E.mul ρ, mul_set L H E.add E.mul ρ, add_set L H E.add ρ, add_set L H E.add ρ, md, add_set L H E.add ρ, ← lor_rec]

theorem and_field (E : Final7.Env7 env sig P) (HB : BitsEnv env) (hbl : HasTy env "br_litN" [] brLitNTy)
    (ρ : Nat → S) (x y : UInt64) :
    O.app (O.app (opS M "HAnd.hAnd" "instHAndOfAndOp" (M.cval "UInt64" []) "instAndOpUInt64")
      (encM M (.w x))) (encM M (.w y)) = encM M (.w (x &&& y)) := by
  have H := E.enc
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have dOF : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have ofMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app (M.cval "UInt64.ofNat" []) a) (M.cval "UInt64" []) :=
    fun a ha => mem_app' L dOF (mem_ty M L H.ofNat dOF) .const ha .const
  have hIU := mem_ty M L HB.andI (ρ := ρ) (.app .const .const)
  obtain ⟨ty, hc, hty⟩ := HB.brAnd
  have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn x.toNat) (.cons .const (hn y.toNat) .nil)) .const
    (.app (.app (opS_D _ _) (.app .const .bvar)) (.app .const .bvar)) (.app .const (.app (.app .const .bvar) .bvar)) hUu
    (core_mem L E.add HB.andC (ρ := ρ) hUu hIU (ofMem _ (hn _)) (ofMem _ (hn _)))
    (ofMem _ (bin2_mem L HB.landH ρ (hn _) (hn _)))
  simp only [push] at key
  show O.app (O.app _ (O.app (M.cval "UInt64.ofNat" []) (natEnc M x.toNat)))
    (O.app (M.cval "UInt64.ofNat" []) (natEnc M y.toNat)) = O.app (M.cval "UInt64.ofNat" []) (natEnc M (x &&& y).toNat)
  rw [key, land_set L E HB hbl ρ, UInt64.toNat_and]; rfl

theorem or_field (E : Final7.Env7 env sig P) (HB : BitsEnv env) (hbl : HasTy env "br_litN" [] brLitNTy)
    (ρ : Nat → S) (x y : UInt64) :
    O.app (O.app (opS M "HOr.hOr" "instHOrOfOrOp" (M.cval "UInt64" []) "instOrOpUInt64")
      (encM M (.w x))) (encM M (.w y)) = encM M (.w (x ||| y)) := by
  have H := E.enc
  have hUu := univ1 (M := M) (L := L) H H.u64 ρ
  have hn := natEnc_mem' (M := M) (L := L) H ρ
  have dOF : D O M.cval ρ (.forallE tNat tU false) _ := .pi .const (fun _ _ => .const) (np rfl)
  have ofMem : ∀ a, O.mem a (M.cval "Nat" []) → O.mem (O.app (M.cval "UInt64.ofNat" []) a) (M.cval "UInt64" []) :=
    fun a ha => mem_app' L dOF (mem_ty M L H.ofNat dOF) .const ha .const
  have hIU := mem_ty M L HB.orI (ρ := ρ) (.app .const .const)
  obtain ⟨ty, hc, hty⟩ := HB.brOr
  have key := transferN L M hc (ls := []) hty ρ (.cons .const (hn x.toNat) (.cons .const (hn y.toNat) .nil)) .const
    (.app (.app (opS_D _ _) (.app .const .bvar)) (.app .const .bvar)) (.app .const (.app (.app .const .bvar) .bvar)) hUu
    (core_mem L E.add HB.orC (ρ := ρ) hUu hIU (ofMem _ (hn _)) (ofMem _ (hn _)))
    (ofMem _ (bin2_mem L HB.lorH ρ (hn _) (hn _)))
  simp only [push] at key
  show O.app (O.app _ (O.app (M.cval "UInt64.ofNat" []) (natEnc M x.toNat)))
    (O.app (M.cval "UInt64.ofNat" []) (natEnc M y.toNat)) = O.app (M.cval "UInt64.ofNat" []) (natEnc M (x ||| y).toNat)
  rw [key, lor_set L E HB hbl ρ, UInt64.toNat_or]; rfl

end Bridge.Bits
