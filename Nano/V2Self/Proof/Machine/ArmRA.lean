/- rv2arm (`RA`, CertArm/Src.lean) on Gen's words: for a `GoodX` J instruction `j` that `armOK` accepts,
`RA.t0` appends exactly the little-endian bytes of `ArmEnc.blockJ j`, and `RA.c0` accepts only `armOK` instructions.
Method: every word is read through `toNat`; fields are `/ 2^k % 2^m` of a sum, closed by omega. -/
import Nano.V2Self.Proof.CertArm.Src
import Nano.V2Self.Proof.Machine.ArmEnc
import Nano.V2Self.Proof.Machine.SimXB
namespace ArmRA
open CallProbe ArmEnc

/-! ## toolkit -/

theorem orA {a b : Nat} (k : Nat) (ha : a % 2 ^ k = 0) (hb : b < 2 ^ k) : a ||| b = a + b := by
  have e : a = 2 ^ k * (a / 2 ^ k) := by have := Nat.div_add_mod a (2 ^ k); omega
  rw [e, Nat.two_pow_add_eq_or_of_lt hb]

theorem u64 {a b : UInt64} (h : a.toNat = b.toNat) : a = b := UInt64.toNat_inj.1 h

def le4 (v : UInt64) : List UInt8 := [v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]

theorem q_eq (x o : List UInt8) (v : UInt64) : RA.q x o v = o ++ le4 v := by simp [RA.q, put, le4]

/-- the bytes of a block (as numbers), after `o` -/
def emit (o : List UInt8) (ws : List Nat) : List UInt8 := o ++ (pad4 ws).flatMap fun W => le4 W.toUInt64

theorem k0_pad : RA.k0 = PAD.toUInt64 := rfl

theorem e0_eq (x o) : RA.e0 x o = emit o [] := by
  simp [RA.e0, q_eq, emit, pad4, k0_pad]
theorem e1_eq (x o) (a : Nat) : RA.e1 x o a.toUInt64 = emit o [a] := by
  simp [RA.e1, q_eq, emit, pad4, k0_pad]
theorem e2_eq (x o) (a b : Nat) : RA.e2 x o a.toUInt64 b.toUInt64 = emit o [a, b] := by
  simp [RA.e2, q_eq, emit, pad4, k0_pad]
theorem e3_eq (x o) (a b c : Nat) : RA.e3 x o a.toUInt64 b.toUInt64 c.toUInt64 = emit o [a, b, c] := by
  simp [RA.e3, q_eq, emit, pad4, k0_pad]
theorem e4_eq (x o) (a b c d : Nat) : RA.e4 x o a.toUInt64 b.toUInt64 c.toUInt64 d.toUInt64 = emit o [a, b, c, d] := by
  simp [RA.e4, q_eq, emit, pad4]

theorem and3 (n : Nat) : n &&& 3 = n % 4 := Bridge.mask n 2
theorem and7 (n : Nat) : n &&& 7 = n % 8 := Bridge.mask n 3
theorem and31 (n : Nat) : n &&& 31 = n % 32 := Bridge.mask n 5
theorem and127 (n : Nat) : n &&& 127 = n % 128 := Bridge.mask n 7
theorem and524287 (n : Nat) : n &&& 524287 = n % 524288 := Bridge.mask n 19
theorem and67108863 (n : Nat) : n &&& 67108863 = n % 67108864 := Bridge.mask n 26

/-- `toNat` normal form of a word built with `|||`, `<<<`, `>>>`, `&&&` and constants -/
macro "wnorm" : tactic => `(tactic| simp only [UInt64.toNat_or, UInt64.toNat_mul, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
  UInt64.toNat_and, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.reducePow, UInt64.reduceToNat, Nat.reduceMod,
  Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Bridge.and4095, Bridge.mask, Bridge.land1, Bridge.land15,
  Bridge.land63, Bridge.land255, Bridge.land1023, and3, and7, and31, and127, and524287, and67108863])

/-- an OR of disjoint bit ranges is a sum (simp lemmas, side goals by omega) -/
macro "orsum" : tactic => `(tactic| simp (disch := omega) only [orA 2, orA 3, orA 4, orA 5, orA 6, orA 7, orA 8, orA 9, orA 10, orA 11, orA 12, orA 13, orA 14, orA 15, orA 16, orA 17, orA 18, orA 19, orA 20, orA 21, orA 22, orA 23, orA 24, orA 25, orA 26, orA 27, orA 28, orA 29, orA 30, orA 31, orA 32])

/-! ## the field extractors of RA on a word `v` -/

theorem toU_toNat {r : Nat} (h : r < 2 ^ 64) : r.toUInt64.toNat = r := by simp [Nat.toUInt64_eq]; omega

theorem o0_eq {v : UInt64} {r : Nat} (h : v.toNat % 128 = r) : RA.o0 v = r.toUInt64 :=
  u64 (by unfold RA.o0; wnorm; omega)
theorem o1_eq {v : UInt64} {r : Nat} (h : v.toNat / 128 % 32 = r) : RA.o1 v = r.toUInt64 :=
  u64 (by unfold RA.o1; wnorm; omega)
theorem o2_eq {v : UInt64} {r : Nat} (h : v.toNat / 4096 % 8 = r) : RA.o2 v = r.toUInt64 :=
  u64 (by unfold RA.o2; wnorm; omega)
theorem o3_eq {v : UInt64} {r : Nat} (h : v.toNat / 32768 % 32 = r) : RA.o3 v = r.toUInt64 :=
  u64 (by unfold RA.o3; wnorm; omega)
theorem o4_eq {v : UInt64} {r : Nat} (h : v.toNat / 1048576 % 32 = r) : RA.o4 v = r.toUInt64 :=
  u64 (by unfold RA.o4; wnorm; omega)
theorem shr_eq {v : UInt64} {k r : Nat} (hk : k < 64) (h : v.toNat / 2 ^ k = r) : v >>> k.toUInt64 = r.toUInt64 :=
  u64 (by
    subst h; have := v.toNat_lt; wnorm; rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) this)).symm)

theorem u4_eq {y : UInt64} {z : Int} (h1 : -2048 ≤ z) (h2 : z < 2048) (h : y.toNat = (z % 4096).toNat) :
    RA.u4 y = CallProbe.iu z := by
  apply u64; rw [CallProbe.iu_toNat]; unfold RA.u4
  split
  · rename_i hl; rw [UInt64.lt_iff_toNat_lt] at hl; simp at hl; omega
  · rename_i hl; rw [UInt64.lt_iff_toNat_lt] at hl; simp at hl
    rw [UInt64.toNat_sub]; simp; omega

theorem o5_eq {v : UInt64} {z : Int} (h1 : -2048 ≤ z) (h2 : z < 2048)
    (h : v.toNat / 2 ^ 20 = (z % 4096).toNat) : RA.o5 v = CallProbe.iu z := by
  unfold RA.o5; exact u4_eq h1 h2 (by wnorm; omega)

/-! ## Gen's words and RA's builders as sums -/

theorem g2_sum (p f3 d a v : UInt64) (hp : p.toNat < 128) (hf : f3.toNat < 8) (hd : d.toNat < 32) (ha : a.toNat < 32) :
    (C.g2 p f3 d a v).toNat = v.toNat % 4096 * 2 ^ 20 + a.toNat * 2 ^ 15 + f3.toNat * 2 ^ 12 + d.toNat * 2 ^ 7 + p.toNat := by
  unfold C.g2; wnorm
  simp only [show C.g_4095.toNat = 4095 from rfl, Bridge.and4095]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  orsum

theorem mapped_cases {r : Nat} (hm : mapped r = true) : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨
    r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 28 ∨ r = 29 ∨ r = 30 ∨ r = 31 := by
  simp [mapped] at hm; omega

theorem u0_eq {r : Nat} (hm : mapped r = true) : RA.u0 r.toUInt64 = (armReg r).toUInt64 := by
  rcases mapped_cases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem addi_V (rd rs : Nat) (imm : Int) (hd : rd < 32) (hs : rs < 32) (h1 : -2048 ≤ imm) (h2 : imm < 2048) :
    (encG (.addi rd rs imm)).toNat = (imm % 4096).toNat * 2 ^ 20 + rs * 2 ^ 15 + rd * 2 ^ 7 + 19 := by
  simp only [encG, C.g10]
  rw [g2_sum _ _ _ _ _ (by decide) (by decide) (by rw [CallProbe.toU_toNat _ (by omega)]; omega) (by rw [CallProbe.toU_toNat _ (by omega)]; omega),
    CallProbe.iu_toNat, CallProbe.toU_toNat _ (by omega), CallProbe.toU_toNat _ (by omega)]
  rw [show C.g_19.toNat = 19 from rfl, show UInt64.toNat 0 = 0 from rfl]; omega

theorem armReg_lt (r : Nat) : armReg r < 32 := by unfold armReg; split <;> omega

theorem beq_u {r : Nat} (c : Nat) (h : r < 2 ^ 64) (hc : c < 2 ^ 64) : (r.toUInt64 == c.toUInt64) = decide (r = c) := by
  by_cases e : r = c
  · subst e; simp
  · simp only [e, decide_false]; apply beq_false_of_ne; intro h'
    have := congrArg UInt64.toNat h'; rw [CallProbe.toU_toNat _ h, CallProbe.toU_toNat _ hc] at this; exact e this

theorem u7_iu {z : Int} (h1 : -2 ^ 62 ≤ z) (h2 : z < 2 ^ 62) : RA.u7 (iu z) = if z < 0 then 1 else 0 := by
  unfold RA.u7
  have e := CallProbe.iu_toNat z
  by_cases hz : z < 0
  · rw [if_pos hz, if_pos (by rw [UInt64.lt_iff_toNat_lt, e]; simp; omega)]
  · rw [if_neg hz, if_neg (by rw [UInt64.lt_iff_toNat_lt, e]; simp; omega)]

theorem u8_iu {z : Int} (h1 : -2 ^ 62 ≤ z) (h2 : z < 2 ^ 62) : RA.u8 (iu z) = z.natAbs.toUInt64 := by
  rw [RA.u8, u7_iu h1 h2]; apply u64
  split
  · simp only [beq_self_eq_true, if_true]; rw [UInt64.toNat_sub, CallProbe.iu_toNat, CallProbe.toU_toNat _ (by omega)]
    simp; omega
  · simp only [show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false]; rw [CallProbe.iu_toNat, CallProbe.toU_toNat _ (by omega)]; omega

theorem a0_eq (d i : UInt64) (hd : d.toNat < 32) (hi : i.toNat < 65536) : RA.a0 d i = (movz d.toNat i.toNat).toUInt64 :=
  u64 (by unfold RA.a0 movz; rw [CallProbe.toU_toNat _ (by omega)]; wnorm; simp only [show RA.k1.toNat = 3531603968 from rfl]
          simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum)

macro "bld" : tactic => `(tactic| (apply u64; rw [CallProbe.toU_toNat _ (by omega)]; wnorm; (try simp (disch := omega) only [Nat.mod_eq_of_lt]); orsum))

theorem a1_eq (d n i : UInt64) (hd : d.toNat < 32) (hn : n.toNat < 32) (hi : i.toNat < 4096) :
    RA.a1 d n i = (addi d.toNat n.toNat i.toNat).toUInt64 := by
  unfold RA.a1 addi; simp only [show RA.k2 = 0x91000000 from rfl]; bld
theorem a2_eq (d n i : UInt64) (hd : d.toNat < 32) (hn : n.toNat < 32) (hi : i.toNat < 4096) :
    RA.a2 d n i = (subi d.toNat n.toNat i.toNat).toUInt64 := by
  unfold RA.a2 subi; simp only [show RA.k3 = 0xD1000000 from rfl]; bld
theorem a4_eq (n b : UInt64) (hn : n.toNat < 32) (hb : b.toNat < 32) :
    RA.a4 n b = (subsR n.toNat b.toNat).toUInt64 := by
  unfold RA.a4 subsR; simp only [show RA.k4 = 0xEB000000 from rfl]; bld
theorem a5_eq (c t n f : UInt64) (C0 : Nat) (hc : c.toNat = C0 * 2 ^ 22) (hC : C0 < 1024) (ht : t.toNat < 32)
    (hn : n.toNat < 32) (hf : f.toNat < 32768) :
    RA.a5 c t n f = (C0 * 2 ^ 22 + (f.toNat / 8) * 2 ^ 10 + n.toNat * 2 ^ 5 + t.toNat).toUInt64 := by
  unfold RA.a5; rw [← hc]; bld
theorem a7_eq (c t n f : UInt64) (C0 : Nat) (hc : c.toNat = C0 * 2 ^ 22) (hC : C0 < 1024) (ht : t.toNat < 32)
    (hn : n.toNat < 32) (hf : f.toNat < 4096) :
    RA.a7 c t n f = (C0 * 2 ^ 22 + f.toNat * 2 ^ 10 + n.toNat * 2 ^ 5 + t.toNat).toUInt64 := by
  unfold RA.a7; rw [← hc]; bld
theorem b0_eq (n : UInt64) (hn : n.toNat < 32) : RA.b0 n = (brR n.toNat).toUInt64 := by
  unfold RA.b0 brR; simp only [show RA.k6 = 0xD61F0000 from rfl]; bld
theorem b4_eq (d i h : UInt64) (hd : d.toNat < 32) (hi : i.toNat < 65536) (hh : h.toNat < 4) :
    RA.b4 d i h = (movk d.toNat i.toNat h.toNat).toUInt64 := by
  unfold RA.b4 movk; simp only [show RA.k15 = 0xF2800000 from rfl, show RA.k17 = 2097152 from rfl]
  bld

theorem a3_eq (c d n b : UInt64) (H M : Nat) (hc : c.toNat = H * 2 ^ 21 + M * 2 ^ 10) (hH : H < 2048) (hM : M < 64)
    (hd : d.toNat < 32) (hn : n.toNat < 32) (hb : b.toNat < 32) :
    RA.a3 c d n b = (rr c.toNat d.toNat n.toNat b.toNat).toUInt64 := by
  unfold RA.a3 rr; apply u64; rw [CallProbe.toU_toNat _ (by omega)]; wnorm
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  rw [hc, ← orA (a := H * 2 ^ 21) 21 (by omega) (by omega), Nat.or_assoc (H * 2 ^ 21), Nat.or_comm (M * 2 ^ 10),
    ← Nat.or_assoc]
  orsum; omega

theorem iu_mod26 (z : Int) : (iu z).toNat % 67108864 = mo z 26 := by
  rw [CallProbe.iu_toNat]; unfold mo; omega
theorem iu_mod19 (z : Int) : (iu z).toNat % 524288 = mo z 19 := by
  rw [CallProbe.iu_toNat]; unfold mo; omega

theorem a8_eq (c : UInt64) (z : Int) (hc : c.toNat % 2 ^ 26 = 0) (hc2 : c.toNat < 2 ^ 32) :
    RA.a8 c (iu z) = (c.toNat + mo z 26).toUInt64 := by
  unfold RA.a8; apply u64
  have : mo z 26 < 2 ^ 26 := by unfold mo; omega
  rw [CallProbe.toU_toNat _ (by omega)]; wnorm; rw [iu_mod26]; orsum

theorem a9_eq (c : UInt64) (z : Int) (hc : c.toNat < 16) : RA.a9 c (iu z) = (bc c.toNat z).toUInt64 := by
  unfold RA.a9 bc; simp only [show RA.k5 = 0x54000000 from rfl]; apply u64
  have : mo z 19 < 2 ^ 19 := by unfold mo; omega
  rw [CallProbe.toU_toNat _ (by omega)]; wnorm; rw [iu_mod19]
  simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum
theorem b5_eq (t : UInt64) (z : Int) (ht : t.toNat < 32) : RA.b5 t (iu z) = (cbz t.toNat z).toUInt64 := by
  unfold RA.b5 cbz; simp only [show RA.k16 = 0xB4000000 from rfl]; apply u64
  have : mo z 19 < 2 ^ 19 := by unfold mo; omega
  rw [CallProbe.toU_toNat _ (by omega)]; wnorm; rw [iu_mod19]
  simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum

end ArmRA
