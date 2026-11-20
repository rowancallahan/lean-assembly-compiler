/- rv2arm (`RA`, CertArm/Src.lean) on Gen's words: for a `GoodX` J instruction `j` that `armOK` accepts,
`RA.t0` appends exactly the little-endian bytes of `ArmEnc.blockJ j`, and `RA.c0` accepts only `armOK` instructions.
Method: every word is read through `toNat`; fields are `/ 2^k % 2^m` of a sum, closed by omega. -/
import Nano.V2Self.Proof.CertArm.Src
import Nano.V2Self.Proof.Machine.ArmEnc
import Nano.V2Self.Proof.Machine.SimXB
set_option linter.unusedSimpArgs false
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

theorem m64 {a : Nat} (h : a < 2 ^ 64) : a % 18446744073709551616 = a := Nat.mod_eq_of_lt h

theorem u5_eq {y : UInt64} {z : Int} (h1 : -4096 ≤ z) (h2 : z < 4096) (h : y.toNat = (z % 8192).toNat) :
    RA.u5 y = iu z := by
  apply u64; rw [CallProbe.iu_toNat]; unfold RA.u5
  split
  · rename_i hl; rw [UInt64.lt_iff_toNat_lt] at hl; simp at hl; omega
  · rename_i hl; rw [UInt64.lt_iff_toNat_lt] at hl; simp at hl; rw [UInt64.toNat_sub]; simp; omega
theorem u6_eq {y : UInt64} {z : Int} (h1 : -1048576 ≤ z) (h2 : z < 1048576) (h : y.toNat = (z % 2097152).toNat) :
    RA.u6 y = iu z := by
  apply u64; rw [CallProbe.iu_toNat]; unfold RA.u6
  split
  · rename_i hl; rw [UInt64.lt_iff_toNat_lt] at hl; simp at hl; omega
  · rename_i hl; rw [UInt64.lt_iff_toNat_lt] at hl; simp at hl; rw [UInt64.toNat_sub]; simp; omega

theorem o6_eq {v : UInt64} {z : Int} (h1 : -2048 ≤ z) (h2 : z < 2048) (hv : v.toNat < 2 ^ 32)
    (h : v.toNat / 2 ^ 25 * 32 + v.toNat / 128 % 32 = (z % 4096).toNat) : RA.o6 v = iu z := by
  unfold RA.o6; refine u4_eq h1 h2 ?_; wnorm
  simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum; omega
theorem o7_eq {v : UInt64} {z : Int} (h1 : -4096 ≤ z) (h2 : z < 4096) (hv : v.toNat < 2 ^ 32)
    (h : v.toNat / 2 ^ 31 % 2 * 4096 + v.toNat / 128 % 2 * 2048 + v.toNat / 2 ^ 25 % 64 * 32 + v.toNat / 256 % 16 * 2
      = (z % 8192).toNat) : RA.o7 v = iu z := by
  unfold RA.o7; refine u5_eq h1 h2 ?_; wnorm
  simp (disch := omega) only [m64]; orsum; rw [← h]
theorem o8_eq {v : UInt64} {z : Int} (h1 : -1048576 ≤ z) (h2 : z < 1048576) (hv : v.toNat < 2 ^ 32)
    (h : v.toNat / 2 ^ 31 % 2 * 2 ^ 20 + v.toNat / 4096 % 256 * 4096 + v.toNat / 2 ^ 20 % 2 * 2048 +
      v.toNat / 2 ^ 21 % 1024 * 2 = (z % 2097152).toNat) : RA.o8 v = iu z := by
  unfold RA.o8; refine u6_eq h1 h2 ?_; wnorm
  simp (disch := omega) only [m64]; orsum; rw [← h]

theorem g1_sum (f7 f3 d a b : UInt64) (h7 : f7.toNat < 128) (hf : f3.toNat < 8) (hd : d.toNat < 32) (ha : a.toNat < 32)
    (hb : b.toNat < 32) : (C.g1 f7 f3 d a b).toNat =
      f7.toNat * 2 ^ 25 + b.toNat * 2 ^ 20 + a.toNat * 2 ^ 15 + f3.toNat * 2 ^ 12 + d.toNat * 2 ^ 7 + 51 := by
  unfold C.g1; wnorm; simp only [show C.g_51.toNat = 51 from rfl]
  simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum
theorem g3_sum (f3 b a v : UInt64) (hf : f3.toNat < 8) (hb : b.toNat < 32) (ha : a.toNat < 32) :
    (C.g3 f3 b a v).toNat = v.toNat / 32 % 128 * 2 ^ 25 + b.toNat * 2 ^ 20 + a.toNat * 2 ^ 15 + f3.toNat * 2 ^ 12 +
      v.toNat % 32 * 2 ^ 7 + 35 := by
  unfold C.g3; wnorm
  simp only [show C.g_127.toNat = 127 from rfl, show C.g_31.toNat = 31 from rfl, show C.g_35.toNat = 35 from rfl,
    and127, and31]
  simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum
theorem g4_sum (f3 a b v : UInt64) (hf : f3.toNat < 8) (ha : a.toNat < 32) (hb : b.toNat < 32) :
    (C.g4 f3 a b v).toNat = v.toNat / 4096 % 2 * 2 ^ 31 + v.toNat / 32 % 64 * 2 ^ 25 + b.toNat * 2 ^ 20 +
      a.toNat * 2 ^ 15 + f3.toNat * 2 ^ 12 + v.toNat / 2 % 16 * 2 ^ 8 + v.toNat / 2048 % 2 * 2 ^ 7 + 99 := by
  unfold C.g4; wnorm
  simp only [show C.g_1.toNat = 1 from rfl, show C.g_63.toNat = 63 from rfl, show C.g_15.toNat = 15 from rfl,
    show C.g_99.toNat = 99 from rfl, Bridge.land1, Bridge.land15, Bridge.land63]
  simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum
theorem g5_sum (d v : UInt64) (hd : d.toNat < 32) :
    (C.g5 d v).toNat = v.toNat / 2 ^ 20 % 2 * 2 ^ 31 + v.toNat / 2 % 1024 * 2 ^ 21 + v.toNat / 2048 % 2 * 2 ^ 20 +
      v.toNat / 4096 % 256 * 2 ^ 12 + d.toNat * 2 ^ 7 + 111 := by
  unfold C.g5; wnorm
  simp only [show C.g_1.toNat = 1 from rfl, show C.g_1023.toNat = 1023 from rfl, show C.g_255.toNat = 255 from rfl,
    show C.g_111.toNat = 111 from rfl, Bridge.land1, Bridge.land1023, Bridge.land255]
  simp (disch := omega) only [Nat.mod_eq_of_lt]; orsum

/-! ## RA's sub-emitters -/

theorem beq0 {r : Nat} (h : r < 2 ^ 64) : (r.toUInt64 == 0) = decide (r = 0) := beq_u 0 h (by omega)
theorem tU {r : Nat} (h : r < 2 ^ 64) : r.toUInt64.toNat = r := CallProbe.toU_toNat _ h
theorem iu_nn {z : Int} (h0 : 0 ≤ z) (h : z < 2 ^ 63) : iu z = z.toNat.toUInt64 :=
  u64 (by rw [CallProbe.iu_toNat, tU (by omega)]; omega)

theorem t0_addi (x o : List UInt8) (rd rs : Nat) (imm : Int) (hd : rd < 32) (hs : rs < 32) (h1 : -2048 ≤ imm)
    (h2 : imm < 2048) (md : mapped rd = true) (ms : mapped rs = true) :
    RA.t0 x o (encG (.addi rd rs imm)) = emit o (body (.addi rd rs imm)) := by
  have hV := addi_V rd rs imm hd hs h1 h2
  generalize encG (.addi rd rs imm) = v at hV
  simp only [RA.t0]
  rw [o0_eq (r := 19) (by omega), o2_eq (r := 0) (by omega)]
  simp only [show ((19:Nat).toUInt64 == 19) = true from rfl, show ((0:Nat).toUInt64 == 0) = true from rfl, if_true]
  simp only [RA.d0]
  rw [o1_eq (r := rd) (by omega), o3_eq (r := rs) (by omega), o5_eq h1 h2 (by omega), beq0 (by omega),
    beq0 (by omega), u7_iu (by omega) (by omega)]
  have ar := armReg_lt rd; have as := armReg_lt rs
  by_cases hrd : rd = 0
  · simp [hrd, body, e0_eq]
  by_cases hrs : rs = 0
  · by_cases hn : imm < 0
    · simp only [hrd, hrs, hn, decide_false, decide_true, Bool.false_eq_true, if_false, if_true,
        show ((1 : UInt64) == 1) = true from rfl, u8_iu (z := imm) (by omega) (by omega), u0_eq md]
      rw [show (65536 : UInt64) - imm.natAbs.toUInt64 = (65536 - imm.natAbs).toUInt64 from
          u64 (by rw [UInt64.toNat_sub, tU (by omega), tU (by omega)]; simp; omega),
        a0_eq _ _ (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega),
        show (65535 : UInt64) = (65535 : Nat).toUInt64 from rfl,
        b4_eq _ _ 1 (by rw [tU (by omega)]; omega) (by decide) (by decide),
        b4_eq _ _ 2 (by rw [tU (by omega)]; omega) (by decide) (by decide),
        b4_eq _ _ 3 (by rw [tU (by omega)]; omega) (by decide) (by decide), e4_eq]
      simp only [tU (show armReg rd < 2 ^ 64 by omega), tU (show 65536 - imm.natAbs < 2 ^ 64 by omega), body, hrd, hrs, hn,
        if_false, if_true]
      rfl
    · simp only [hrd, hrs, hn, decide_false, decide_true, Bool.false_eq_true, if_false, if_true,
        show ((0 : UInt64) == 1) = false from rfl, u0_eq md, iu_nn (z := imm) (by omega) (by omega)]
      rw [a0_eq _ _ (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega), e1_eq]
      simp only [tU (show armReg rd < 2 ^ 64 by omega), tU (show imm.toNat < 2 ^ 64 by omega), body, hrd, hn,
        if_false, if_true]
  · by_cases hn : imm < 0
    · simp only [hrd, hrs, hn, decide_false, decide_true, Bool.false_eq_true, if_false, if_true,
        show ((1 : UInt64) == 1) = true from rfl, u8_iu (z := imm) (by omega) (by omega), u0_eq md, u0_eq ms]
      rw [a2_eq _ _ _ (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega), e1_eq]
      simp only [tU (show armReg rd < 2 ^ 64 by omega), tU (show armReg rs < 2 ^ 64 by omega),
        tU (show imm.natAbs < 2 ^ 64 by omega), body, hrd, hrs, hn, if_false, if_true]
    · simp only [hrd, hrs, hn, decide_false, decide_true, Bool.false_eq_true, if_false, if_true,
        show ((0 : UInt64) == 1) = false from rfl, u0_eq md, u0_eq ms, iu_nn (z := imm) (by omega) (by omega)]
      rw [a1_eq _ _ _ (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega), e1_eq]
      simp only [tU (show armReg rd < 2 ^ 64 by omega), tU (show armReg rs < 2 ^ 64 by omega),
        tU (show imm.toNat < 2 ^ 64 by omega), body, hrd, hrs, hn, if_false, if_true]

theorem opR_lt (r : Nat) : opR r < 32 := by unfold opR; have := armReg_lt r; split <;> omega
theorem y0_eq {t : Nat} (hm : mapped t = true) : RA.y0 t.toUInt64 = (opR t).toUInt64 := by
  unfold RA.y0 opR; rw [beq0 (by have := mapped_cases hm; omega)]
  by_cases h : t = 0 <;> simp [h, u0_eq hm]
theorem z1_eq {t : Nat} (hm : mapped t = true) : RA.z1 t.toUInt64 = (opR t).toUInt64 := y0_eq hm
theorem movz17 : RA.a0 17 0 = (movz 17 0).toUInt64 := rfl
theorem y1_eq (x o : List UInt8) {t : Nat} (ht : t < 2 ^ 64) (W : Nat) :
    RA.y1 x o t.toUInt64 W.toUInt64 = emit o (zpre t ++ [W]) := by
  unfold RA.y1 zpre; rw [beq0 ht]; by_cases h : t = 0 <;> simp [h, movz17, e1_eq, e2_eq]
theorem y2_eq (x o : List UInt8) {t : Nat} (ht : t < 2 ^ 64) (W1 W2 : Nat) :
    RA.y2 x o t.toUInt64 W1.toUInt64 W2.toUInt64 = emit o (zpre t ++ [W1, W2]) := by
  unfold RA.y2 zpre; rw [beq0 ht]; by_cases h : t = 0 <;> simp [h, movz17, e2_eq, e3_eq]

theorem d1_eq {s : Nat} {z : Int} (hm : mapped s = true) (h1 : -2048 ≤ z) (h2 : z < 2048) :
    RA.d1 s.toUInt64 (iu z) = (addr16 s z).toUInt64 := by
  have := armReg_lt s
  unfold RA.d1 addr16; rw [u7_iu (by omega) (by omega), u0_eq hm]
  by_cases hn : z < 0
  · simp only [hn, if_true, show ((1 : UInt64) == 1) = true from rfl, u8_iu (z := z) (by omega) (by omega)]
    rw [show (16 : UInt64) = (16 : Nat).toUInt64 from rfl,
      a2_eq _ _ _ (by decide) (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega),
      tU (show z.natAbs < 2 ^ 64 by omega), tU (show armReg s < 2 ^ 64 by omega)]; rfl
  · simp only [hn, if_false, show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, iu_nn (z := z) (by omega) (by omega)]
    rw [show (16 : UInt64) = (16 : Nat).toUInt64 from rfl,
      a1_eq _ _ _ (by decide) (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega),
      tU (show z.toNat < 2 ^ 64 by omega), tU (show armReg s < 2 ^ 64 by omega)]; rfl

theorem iu_and7 {z : Int} (h1 : -2048 ≤ z) (h2 : z < 2048) : (iu z &&& 7 == 0) = decide (z % 8 = 0) := by
  have e : (iu z &&& 7).toNat = (z % 8).toNat := by wnorm; rw [CallProbe.iu_toNat]; omega
  by_cases h : z % 8 = 0
  · simp only [h, decide_true]; apply beq_iff_eq.2; apply u64; rw [e, h]; rfl
  · simp only [h, decide_false]; apply beq_false_of_ne; intro h'; rw [h'] at e; simp at e; omega
theorem iu_lt {z : Int} (k : Nat) (hk : k < 2 ^ 62) (h1 : -2048 ≤ z) (h2 : z < 2048) :
    (iu z < k.toUInt64) = (0 ≤ z ∧ z < k) := by
  rw [UInt64.lt_iff_toNat_lt, CallProbe.iu_toNat, tU (by omega)]; apply propext; omega
theorem iu_lt32768 {z : Int} (h1 : -2048 ≤ z) (h2 : z < 2048) : (iu z < (32768 : Nat).toUInt64) = (0 ≤ z ∧ z < 32768) :=
  iu_lt 32768 (by omega) h1 h2
theorem iu_lt4096 {z : Int} (h1 : -2048 ≤ z) (h2 : z < 2048) : (iu z < (4096 : Nat).toUInt64) = (0 ≤ z ∧ z < 4096) :=
  iu_lt 4096 (by omega) h1 h2

theorem d2_eq (x o : List UInt8) (c : Nat) (hc : c = 0 ∨ c = 1) {t s : Nat} {z : Int} (mt : mapped t = true)
    (ms : mapped s = true) (h1 : -2048 ≤ z) (h2 : z < 2048) (W : Nat → Nat → Nat → Nat)
    (hW : ∀ t n f, W t n f = (if c = 1 then 997 else 996) * 2 ^ 22 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + t) :
    RA.d2 x o c.toUInt64 t.toUInt64 s.toUInt64 (iu z) = emit o (zpre t ++
      if z % 8 = 0 ∧ 0 ≤ z ∧ z < 32768 then [W (opR t) (armReg s) z.toNat] else [addr16 s z, W (opR t) 16 0]) := by
  have ht := mapped_cases mt; have hs := mapped_cases ms
  have := armReg_lt s; have := opR_lt t
  have hk : ((if c.toUInt64 == 1 then RA.k7 else RA.k8).toNat = (if c = 1 then 997 else 996) * 2 ^ 22) := by
    rcases hc with rfl | rfl <;> rfl
  unfold RA.d2; simp only []
  generalize (if c.toUInt64 == 1 then RA.k7 else RA.k8) = g at hk ⊢
  rw [iu_and7 h1 h2, y0_eq mt, u0_eq ms, show (32768 : UInt64) = (32768 : Nat).toUInt64 from rfl, d1_eq ms h1 h2, show (16 : UInt64) = (16 : Nat).toUInt64 from rfl,
    show (0 : UInt64) = (0 : Nat).toUInt64 from rfl]
  simp only [iu_lt32768 h1 h2]
  have hC : (if c = 1 then 997 else 996) < 1024 := by split <;> omega
  by_cases h8 : z % 8 = 0
  · by_cases hr : 0 ≤ z ∧ z < 32768
    · simp only [h8, hr, decide_true, and_self, if_true]
      rw [iu_nn hr.1 (by omega),
        a5_eq _ _ _ _ _ hk hC (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega),
        y1_eq x o (by omega), hW]; simp only [tU (show opR t < 2 ^ 64 by omega), tU (show armReg s < 2 ^ 64 by omega), tU (show z.toNat < 2 ^ 64 by omega), show (Nat.toUInt64 16).toNat = 16 from rfl, show (Nat.toUInt64 0).toNat = 0 from rfl]
    · simp only [h8, hr, decide_true, and_false, if_true, if_false]
      rw [
        a5_eq _ _ _ _ _ hk hC (by rw [tU (by omega)]; omega) (by decide) (by decide),
        y2_eq x o (by omega), hW]; simp only [tU (show opR t < 2 ^ 64 by omega), tU (show armReg s < 2 ^ 64 by omega), tU (show z.toNat < 2 ^ 64 by omega), show (Nat.toUInt64 16).toNat = 16 from rfl, show (Nat.toUInt64 0).toNat = 0 from rfl]
  · simp only [h8, decide_false, false_and, Bool.false_eq_true, if_false]
    rw [a5_eq _ _ _ _ _ hk hC (by rw [tU (by omega)]; omega) (by decide) (by decide),
      y2_eq x o (by omega), hW]; simp only [tU (show opR t < 2 ^ 64 by omega), tU (show armReg s < 2 ^ 64 by omega), tU (show z.toNat < 2 ^ 64 by omega), show (Nat.toUInt64 16).toNat = 16 from rfl, show (Nat.toUInt64 0).toNat = 0 from rfl]

theorem d3_eq (x o : List UInt8) (c : Nat) (hc : c = 0 ∨ c = 1) {t s : Nat} {z : Int} (mt : mapped t = true)
    (ms : mapped s = true) (h1 : -2048 ≤ z) (h2 : z < 2048) (W : Nat → Nat → Nat → Nat)
    (hW : ∀ t n f, W t n f = (if c = 1 then 229 else 228) * 2 ^ 22 + f * 2 ^ 10 + n * 2 ^ 5 + t) :
    RA.d3 x o c.toUInt64 t.toUInt64 s.toUInt64 (iu z) = emit o (zpre t ++
      if 0 ≤ z ∧ z < 4096 then [W (opR t) (armReg s) z.toNat] else [addr16 s z, W (opR t) 16 0]) := by
  have ht := mapped_cases mt; have hs := mapped_cases ms
  have := armReg_lt s; have := opR_lt t
  have hk : ((if c.toUInt64 == 1 then RA.k11 else RA.k12).toNat = (if c = 1 then 229 else 228) * 2 ^ 22) := by
    rcases hc with rfl | rfl <;> rfl
  unfold RA.d3; simp only []
  generalize (if c.toUInt64 == 1 then RA.k11 else RA.k12) = g at hk ⊢
  rw [y0_eq mt, u0_eq ms, show (4096 : UInt64) = (4096 : Nat).toUInt64 from rfl, d1_eq ms h1 h2, show (16 : UInt64) = (16 : Nat).toUInt64 from rfl,
    show (0 : UInt64) = (0 : Nat).toUInt64 from rfl]
  simp only [iu_lt4096 h1 h2]
  have hC : (if c = 1 then 229 else 228) < 1024 := by split <;> omega
  by_cases hr : 0 ≤ z ∧ z < 4096
  · simp only [hr, and_self, if_true]
    rw [iu_nn hr.1 (by omega), a7_eq _ _ _ _ _ hk hC (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega),
      y1_eq x o (by omega), hW]; simp only [tU (show opR t < 2 ^ 64 by omega), tU (show armReg s < 2 ^ 64 by omega), tU (show z.toNat < 2 ^ 64 by omega), show (Nat.toUInt64 16).toNat = 16 from rfl, show (Nat.toUInt64 0).toNat = 0 from rfl]
  · simp only [hr, if_false]
    rw [a7_eq _ _ _ _ _ hk hC (by rw [tU (by omega)]; omega) (by decide) (by decide),
      y2_eq x o (by omega), hW]; simp only [tU (show opR t < 2 ^ 64 by omega), tU (show armReg s < 2 ^ 64 by omega), tU (show z.toNat < 2 ^ 64 by omega), show (Nat.toUInt64 16).toNat = 16 from rfl, show (Nat.toUInt64 0).toNat = 0 from rfl]

/-! ## t0 per J kind: memory, ALU, shifts -/

theorem I_V (p f3 rd rs : Nat) (imm : Int) (hp : p < 128) (hf : f3 < 8) (hd : rd < 32) (hs : rs < 32) :
    (C.g2 p.toUInt64 f3.toUInt64 rd.toUInt64 rs.toUInt64 (iu imm)).toNat =
      (imm % 4096).toNat * 2 ^ 20 + rs * 2 ^ 15 + f3 * 2 ^ 12 + rd * 2 ^ 7 + p := by
  rw [g2_sum _ _ _ _ _ (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega)
    (by rw [tU (by omega)]; omega), CallProbe.iu_toNat, tU (by omega), tU (by omega), tU (by omega), tU (by omega)]
  omega
theorem S_V (f3 r2 r1 : Nat) (imm : Int) (hf : f3 < 8) (h2 : r2 < 32) (h1 : r1 < 32) :
    (C.g3 f3.toUInt64 r2.toUInt64 r1.toUInt64 (iu imm)).toNat =
      (imm % 4096).toNat / 32 * 2 ^ 25 + r2 * 2 ^ 20 + r1 * 2 ^ 15 + f3 * 2 ^ 12 + (imm % 4096).toNat % 32 * 2 ^ 7 + 35 := by
  rw [g3_sum _ _ _ _ (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega),
    CallProbe.iu_toNat, tU (by omega), tU (by omega), tU (by omega)]
  omega

theorem t0_ld (x o : List UInt8) (rd rs : Nat) (f : Int) (hd : rd < 32) (hs : rs < 32) (h1 : -2048 ≤ f)
    (h2 : f < 2048) (md : mapped rd = true) (ms : mapped rs = true) :
    RA.t0 x o (encG (.ld rd rs f)) = emit o (body (.ld rd rs f)) := by
  have hV := I_V 3 3 rd rs f (by omega) (by omega) hd hs
  simp only [encG, C.g11, show C.g_3 = (3 : Nat).toUInt64 from rfl, show (3 : UInt64) = (3 : Nat).toUInt64 from rfl]
  generalize C.g2 _ _ _ _ _ = v at hV ⊢
  simp only [RA.t0]
  rw [o0_eq (r := 3) (by omega), o2_eq (r := 3) (by omega), o1_eq (r := rd) (by omega), o3_eq (r := rs) (by omega),
    o5_eq h1 h2 (by omega), beq0 (by omega)]
  simp only [show ((3:Nat).toUInt64 == 19) = false from rfl, show ((3:Nat).toUInt64 == 3) = true from rfl,
    Bool.false_eq_true, if_false, if_true]
  by_cases hrd : rd = 0
  · simp [hrd, body, e0_eq]
  · rw [beq0 (r := rd) (by omega)]
    simp only [hrd, decide_false, Bool.false_eq_true, if_false]
    rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, d2_eq x o 1 (by omega) md ms h1 h2 ldr (fun _ _ _ => by simp [ldr])]
    simp [body, hrd, zpre, opR]

theorem t0_lbu (x o : List UInt8) (rd rs : Nat) (f : Int) (hd : rd < 32) (hs : rs < 32) (h1 : -2048 ≤ f)
    (h2 : f < 2048) (md : mapped rd = true) (ms : mapped rs = true) :
    RA.t0 x o (encG (.lbu rd rs f)) = emit o (body (.lbu rd rs f)) := by
  have hV := I_V 3 4 rd rs f (by omega) (by omega) hd hs
  simp only [encG, show C.g_3 = (3 : Nat).toUInt64 from rfl, show (4 : UInt64) = (4 : Nat).toUInt64 from rfl]
  generalize C.g2 _ _ _ _ _ = v at hV ⊢
  simp only [RA.t0]
  rw [o0_eq (r := 3) (by omega), o2_eq (r := 4) (by omega), o1_eq (r := rd) (by omega), o3_eq (r := rs) (by omega),
    o5_eq h1 h2 (by omega)]
  simp only [show ((3:Nat).toUInt64 == 19) = false from rfl, show ((3:Nat).toUInt64 == 3) = true from rfl,
    show ((4:Nat).toUInt64 == 3) = false from rfl, Bool.false_eq_true, if_false, if_true]
  by_cases hrd : rd = 0
  · simp [hrd, body, e0_eq]
  · rw [beq0 (r := rd) (by omega)]
    simp only [hrd, decide_false, Bool.false_eq_true, if_false]
    rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, d3_eq x o 1 (by omega) md ms h1 h2 ldrb (fun _ _ _ => by simp [ldrb])]
    simp [body, hrd, zpre, opR]

theorem t0_sd (x o : List UInt8) (r2 r1 : Nat) (f : Int) (hd : r2 < 32) (hs : r1 < 32) (h1 : -2048 ≤ f)
    (h2 : f < 2048) (md : mapped r2 = true) (ms : mapped r1 = true) :
    RA.t0 x o (encG (.sd r2 r1 f)) = emit o (body (.sd r2 r1 f)) := by
  have hV := S_V 3 r2 r1 f (by omega) hd hs
  simp only [encG, C.g12, show (3 : UInt64) = (3 : Nat).toUInt64 from rfl]
  generalize C.g3 _ _ _ _ = v at hV ⊢
  simp only [RA.t0]
  rw [o0_eq (r := 35) (by omega), o2_eq (r := 3) (by omega), o4_eq (r := r2) (by omega), o3_eq (r := r1) (by omega),
    o6_eq h1 h2 (by omega) (by omega)]
  simp only [show ((35:Nat).toUInt64 == 19) = false from rfl, show ((35:Nat).toUInt64 == 3) = false from rfl,
    show ((35:Nat).toUInt64 == 35) = true from rfl, show ((3:Nat).toUInt64 == 3) = true from rfl,
    Bool.false_eq_true, if_false, if_true]
  rw [show (0 : UInt64) = (0 : Nat).toUInt64 from rfl, d2_eq x o 0 (by omega) md ms h1 h2 str (fun _ _ _ => by simp [str])]
  simp [body]

theorem t0_sb (x o : List UInt8) (r2 r1 : Nat) (f : Int) (hd : r2 < 32) (hs : r1 < 32) (h1 : -2048 ≤ f)
    (h2 : f < 2048) (md : mapped r2 = true) (ms : mapped r1 = true) :
    RA.t0 x o (encG (.sb r2 r1 f)) = emit o (body (.sb r2 r1 f)) := by
  have hV := S_V 0 r2 r1 f (by omega) hd hs
  simp only [encG, show (0 : UInt64) = (0 : Nat).toUInt64 from rfl]
  generalize C.g3 _ _ _ _ = v at hV ⊢
  simp only [RA.t0]
  rw [o0_eq (r := 35) (by omega), o2_eq (r := 0) (by omega), o4_eq (r := r2) (by omega), o3_eq (r := r1) (by omega),
    o6_eq h1 h2 (by omega) (by omega)]
  simp only [show ((35:Nat).toUInt64 == 19) = false from rfl, show ((35:Nat).toUInt64 == 3) = false from rfl,
    show ((35:Nat).toUInt64 == 35) = true from rfl, show ((0:Nat).toUInt64 == 3) = false from rfl,
    Bool.false_eq_true, if_false, if_true]
  rw [show (0 : UInt64) = (0 : Nat).toUInt64 from rfl, d3_eq x o 0 (by omega) md ms h1 h2 strb (fun _ _ _ => by simp [strb])]
  simp [body]

theorem alu_facts (op : Nat) (h1 : 1 ≤ op) (h2 : op ≤ 8) :
    RA.b1 (aluF op).2 (aluF op).1 = op.toUInt64 ∧ RA.b2 op.toUInt64 = (aluC op).toUInt64 ∧ aluC op % 1024 = 0 ∧
    aluC op < 2 ^ 32 ∧ (aluF op).1.toNat < 128 ∧ (aluF op).2.toNat < 8 ∧ aluC op % 2 ^ 21 < 65536 := by
  have : op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem t0_alu (x o : List UInt8) (op rd a b : Nat) (ho1 : 1 ≤ op) (ho2 : op ≤ 8) (hd : rd < 32) (ha : a < 32)
    (hb : b < 32) (md : mapped rd = true) (ma : mapped a = true) (mb : mapped b = true) :
    RA.t0 x o (encG (.alu op rd a b)) = emit o (body (.alu op rd a b)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := alu_facts op ho1 ho2
  have hV := g1_sum (aluF op).1 (aluF op).2 rd.toUInt64 a.toUInt64 b.toUInt64 f5 f6 (by rw [tU (by omega)]; omega)
    (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega)
  rw [tU (by omega), tU (by omega), tU (by omega)] at hV
  simp only [encG]
  generalize C.g1 _ _ _ _ _ = v at hV ⊢
  simp only [RA.t0, RA.d6]
  rw [o0_eq (r := 51) (by omega), o2_eq (r := (aluF op).2.toNat) (by omega), o1_eq (r := rd) (by omega),
    o3_eq (r := a) (by omega), o4_eq (r := b) (by omega),
    show (25 : UInt64) = (25 : Nat).toUInt64 from rfl, shr_eq (r := (aluF op).1.toNat) (by omega) (by omega)]
  simp only [show ((51:Nat).toUInt64 == 19) = false from rfl, show ((51:Nat).toUInt64 == 3) = false from rfl,
    show ((51:Nat).toUInt64 == 35) = false from rfl, show ((51:Nat).toUInt64 == 51) = true from rfl,
    Bool.false_eq_true, if_false, if_true]
  rw [show (aluF op).2.toNat.toUInt64 = (aluF op).2 from u64 (tU (by omega)),
    show (aluF op).1.toNat.toUInt64 = (aluF op).1 from u64 (tU (by omega)), f1, f2, u0_eq md, z1_eq ma, z1_eq mb,
    a3_eq _ _ _ _ (aluC op / 2 ^ 21) (aluC op % 2 ^ 21 / 2 ^ 10) (by rw [tU (by omega)]; omega) (by omega) (by omega)
      (by rw [tU (by have := armReg_lt rd; omega)]; have := armReg_lt rd; omega)
      (by rw [tU (by have := opR_lt a; omega)]; have := opR_lt a; omega)
      (by rw [tU (by have := opR_lt b; omega)]; have := opR_lt b; omega),
    beq0 (r := rd) (by omega), beq0 (r := a) (by omega), beq0 (r := b) (by omega), show (3 : UInt64) = (3 : Nat).toUInt64 from rfl, beq_u 3 (by omega) (by omega)]
  have := armReg_lt rd; have := opR_lt a; have := opR_lt b
  simp only [tU (show aluC op < 2 ^ 64 by omega), tU (show armReg rd < 2 ^ 64 by omega),
    tU (show opR a < 2 ^ 64 by omega), tU (show opR b < 2 ^ 64 by omega)]
  by_cases hrd : rd = 0
  · simp [hrd, body, e0_eq]
  simp only [hrd, decide_false, Bool.false_eq_true, if_false, body, zpre, movz17]
  by_cases h0 : a = 0
  · simp [h0, e2_eq]
  by_cases h1 : b = 0
  · simp [h0, h1, e2_eq]
  by_cases h3 : op = 3
  · simp [h0, h1, h3, e2_eq]
  · simp [h0, h1, h3, e1_eq]

theorem a3N (c : UInt64) (d n b : Nat) (H M : Nat) (hc : c.toNat = H * 2 ^ 21 + M * 2 ^ 10) (hH : H < 2048)
    (hM : M < 64) (hd : d < 32) (hn : n < 32) (hb : b < 32) :
    RA.a3 c d.toUInt64 n.toUInt64 b.toUInt64 = (rr c.toNat d n b).toUInt64 := by
  rw [a3_eq c _ _ _ H M hc hH hM (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega)
    (by rw [tU (by omega)]; omega), tU (by omega), tU (by omega), tU (by omega)]
theorem a0_16 {sh : Nat} (hh : sh < 64) : RA.a0 16 sh.toUInt64 = (movz 16 sh).toUInt64 := by
  rw [show (16 : UInt64) = (16 : Nat).toUInt64 from rfl, a0_eq _ _ (by decide) (by rw [tU (by omega)]; omega),
    tU (show sh < 2 ^ 64 by omega)]; rfl

theorem d7_eq (x o : List UInt8) (v : UInt64) (c : Nat) (hc : c = 0 ∨ c = 1) (rd rs sh : Nat) (hd : rd < 32) (hs : rs < 32)
    (hh : sh < 64) (md : mapped rd = true) (ms : mapped rs = true)
    (h1 : v.toNat / 128 % 32 = rd) (h2 : v.toNat / 32768 % 32 = rs) (h3 : v.toNat / 2 ^ 20 % 64 = sh) :
    RA.d7 x o v c.toUInt64 = emit o (if rd = 0 then [] else
      zpre rs ++ [movz 16 sh, rr (if c = 1 then 0x9AC02000 else 0x9AC02400) (armReg rd) (opR rs) 16]) := by
  have hk : (if c.toUInt64 == 1 then RA.k13 else RA.k14).toNat =
      (if c = 1 then 0x9AC02000 else 0x9AC02400 : Nat) := by
    rcases hc with rfl | rfl <;> rfl
  have hK : (if c = 1 then 0x9AC02000 else 0x9AC02400 : Nat) = 1238 * 2 ^ 21 + (8 + (if c = 1 then 0 else 1)) * 2 ^ 10 := by
    split <;> decide
  have hm : 8 + (if c = 1 then 0 else 1) < 64 := by split <;> omega
  have := armReg_lt rd; have := opR_lt rs; have := armReg_lt rs
  unfold RA.d7; simp only []
  generalize (if c.toUInt64 == 1 then RA.k13 else RA.k14) = g at hk ⊢
  have hsh : (v >>> 20) &&& 63 = sh.toUInt64 := u64 (by wnorm; omega)
  rw [o1_eq h1, o3_eq h2, hsh, beq0 (r := rd) (by omega), beq0 (r := rs) (by omega)]
  by_cases hrd : rd = 0
  · simp [hrd, e0_eq]
  simp only [hrd, decide_false, Bool.false_eq_true, if_false]
  rw [u0_eq md, a0_16 hh, show (16 : UInt64) = (16 : Nat).toUInt64 from rfl]
  by_cases hrs : rs = 0
  · simp only [hrs, decide_true, if_true, movz17]
    rw [show (17 : UInt64) = (17 : Nat).toUInt64 from rfl,
      a3N g _ _ _ 1238 (8 + (if c = 1 then 0 else 1)) (by rw [hk]; omega) (by omega) hm (by omega) (by omega) (by omega),
      e3_eq, hk]
    simp [zpre, opR]
  · simp only [hrs, decide_false, Bool.false_eq_true, if_false]
    rw [u0_eq ms,
      a3N g _ _ _ 1238 (8 + (if c = 1 then 0 else 1)) (by rw [hk]; omega) (by omega) hm (by omega) (by omega) (by omega),
      e2_eq, hk]
    simp [zpre, opR, hrs]

theorem sh_V (f3 rd rs sh : Nat) (hf : f3 < 8) (hd : rd < 32) (hs : rs < 32) (hh : sh < 64) :
    (C.g2 C.g_19 f3.toUInt64 rd.toUInt64 rs.toUInt64 sh.toUInt64).toNat =
      sh * 2 ^ 20 + rs * 2 ^ 15 + f3 * 2 ^ 12 + rd * 2 ^ 7 + 19 := by
  rw [g2_sum _ _ _ _ _ (by decide) (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega)
    (by rw [tU (by omega)]; omega), tU (show sh < 2 ^ 64 by omega), tU (show rs < 2 ^ 64 by omega),
    tU (show f3 < 2 ^ 64 by omega), tU (show rd < 2 ^ 64 by omega)]
  rw [show C.g_19.toNat = 19 from rfl]; omega

theorem t0_slli (x o : List UInt8) (rd rs sh : Nat) (hd : rd < 32) (hs : rs < 32) (hh : sh < 64)
    (md : mapped rd = true) (ms : mapped rs = true) :
    RA.t0 x o (encG (.slli rd rs sh)) = emit o (body (.slli rd rs sh)) := by
  have hV := sh_V 1 rd rs sh (by omega) hd hs hh
  simp only [encG, show (1 : UInt64) = (1 : Nat).toUInt64 from rfl]
  generalize C.g2 _ _ _ _ _ = v at hV ⊢
  simp only [RA.t0]
  rw [o0_eq (r := 19) (by omega), o2_eq (r := 1) (by omega)]
  simp only [show ((19:Nat).toUInt64 == 19) = true from rfl, show ((1:Nat).toUInt64 == 0) = false from rfl,
    show ((1:Nat).toUInt64 == 1) = true from rfl, Bool.false_eq_true, if_false, if_true]
  rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl,
    d7_eq x o v 1 (by omega) rd rs sh hd hs hh md ms (by omega) (by omega) (by omega)]
  simp [body]

theorem t0_srli (x o : List UInt8) (rd rs sh : Nat) (hd : rd < 32) (hs : rs < 32) (hh : sh < 64)
    (md : mapped rd = true) (ms : mapped rs = true) :
    RA.t0 x o (encG (.srli rd rs sh)) = emit o (body (.srli rd rs sh)) := by
  have hV := sh_V 5 rd rs sh (by omega) hd hs hh
  simp only [encG, show (5 : UInt64) = (5 : Nat).toUInt64 from rfl]
  generalize C.g2 _ _ _ _ _ = v at hV ⊢
  simp only [RA.t0]
  rw [o0_eq (r := 19) (by omega), o2_eq (r := 5) (by omega)]
  simp only [show ((19:Nat).toUInt64 == 19) = true from rfl, show ((5:Nat).toUInt64 == 0) = false from rfl,
    show ((5:Nat).toUInt64 == 1) = false from rfl, Bool.false_eq_true, if_false, if_true]
  rw [show (0 : UInt64) = (0 : Nat).toUInt64 from rfl,
    d7_eq x o v 0 (by omega) rd rs sh hd hs hh md ms (by omega) (by omega) (by omega)]
  simp [body]

/-! ## t0 per J kind: branches, jal, jalr -/

theorem B_V (f3 a b : Nat) (o : Int) (hf : f3 < 8) (ha : a < 32) (hb : b < 32) :
    (C.g4 f3.toUInt64 a.toUInt64 b.toUInt64 (iu (4 * o))).toNat =
      ((4 * o) % 8192).toNat / 4096 % 2 * 2 ^ 31 + ((4 * o) % 8192).toNat / 32 % 64 * 2 ^ 25 + b * 2 ^ 20 +
      a * 2 ^ 15 + f3 * 2 ^ 12 + ((4 * o) % 8192).toNat / 2 % 16 * 2 ^ 8 + ((4 * o) % 8192).toNat / 2048 % 2 * 2 ^ 7 + 99 := by
  rw [g4_sum _ _ _ _ (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega),
    CallProbe.iu_toNat, tU (show f3 < 2 ^ 64 by omega), tU (show a < 2 ^ 64 by omega), tU (show b < 2 ^ 64 by omega)]
  omega

theorem extractB (p1 p2 p3 p4 a b f3 V : Nat) (h1 : p1 < 2) (h2 : p2 < 64) (h3 : p3 < 16) (h4 : p4 < 2) (ha : a < 32)
    (hb : b < 32) (hf : f3 < 8)
    (hV : V = p1 * 2 ^ 31 + p2 * 2 ^ 25 + b * 2 ^ 20 + a * 2 ^ 15 + f3 * 2 ^ 12 + p3 * 2 ^ 8 + p4 * 2 ^ 7 + 99) :
    V / 2 ^ 31 % 2 * 4096 + V / 128 % 2 * 2048 + V / 2 ^ 25 % 64 * 32 + V / 256 % 16 * 2 =
      p1 * 4096 + p4 * 2048 + p2 * 32 + p3 * 2 := by
  subst hV
  have e1 : (p1 * 2 ^ 31 + p2 * 2 ^ 25 + b * 2 ^ 20 + a * 2 ^ 15 + f3 * 2 ^ 12 + p3 * 2 ^ 8 + p4 * 2 ^ 7 + 99) / 2 ^ 31 % 2 = p1 := by omega
  have e2 : (p1 * 2 ^ 31 + p2 * 2 ^ 25 + b * 2 ^ 20 + a * 2 ^ 15 + f3 * 2 ^ 12 + p3 * 2 ^ 8 + p4 * 2 ^ 7 + 99) / 128 % 2 = p4 := by omega
  have e3 : (p1 * 2 ^ 31 + p2 * 2 ^ 25 + b * 2 ^ 20 + a * 2 ^ 15 + f3 * 2 ^ 12 + p3 * 2 ^ 8 + p4 * 2 ^ 7 + 99) / 2 ^ 25 % 64 = p2 := by omega
  have e4 : (p1 * 2 ^ 31 + p2 * 2 ^ 25 + b * 2 ^ 20 + a * 2 ^ 15 + f3 * 2 ^ 12 + p3 * 2 ^ 8 + p4 * 2 ^ 7 + 99) / 256 % 16 = p3 := by omega
  rw [e1, e2, e3, e4]

theorem br_o7 {v : UInt64} {o : Int} (h1 : -1000 ≤ o) (h2 : o ≤ 1000) {a b f3 : Nat} (hf : f3 < 8) (ha : a < 32) (hb : b < 32)
    (hV : v.toNat = ((4 * o) % 8192).toNat / 4096 % 2 * 2 ^ 31 + ((4 * o) % 8192).toNat / 32 % 64 * 2 ^ 25 + b * 2 ^ 20 +
      a * 2 ^ 15 + f3 * 2 ^ 12 + ((4 * o) % 8192).toNat / 2 % 16 * 2 ^ 8 + ((4 * o) % 8192).toNat / 2048 % 2 * 2 ^ 7 + 99) :
    RA.o7 v = iu (4 * o) := by
  have hu2 : ((4 * o) % 8192).toNat % 2 = 0 := by omega
  have hu3 : ((4 * o) % 8192).toNat < 8192 := by omega
  refine o7_eq (by omega) (by omega) (by omega) ?_
  rw [extractB _ _ _ _ a b f3 _ (by omega) (by omega) (by omega) (by omega) ha hb hf hV]
  generalize ((4 * o) % 8192).toNat = u at hu2 hu3 ⊢
  omega

theorem iu_sub (z : Int) (k : Nat) (hk : k < 2 ^ 32) : iu z - k.toUInt64 = iu (z - k) :=
  u64 (by rw [UInt64.toNat_sub, CallProbe.iu_toNat, CallProbe.iu_toNat, tU (by omega)]; omega)

theorem d9_eq (x o : List UInt8) {a b : Nat} (c : Nat) (hc : c < 16) (ma : mapped a = true) (mb : mapped b = true)
    (w : Int) (hw1 : -2 ^ 40 ≤ w) (hw2 : w < 2 ^ 40) :
    RA.d9 x o a.toUInt64 b.toUInt64 c.toUInt64 (iu w) = emit o (if a = 0 ∨ b = 0 then
      [movz 17 0, subsR (opR a) (opR b), bc c (w - 2)] else [subsR (armReg a) (armReg b), bc c (w - 1)]) := by
  have := mapped_cases ma; have := mapped_cases mb
  have := opR_lt a; have := opR_lt b; have := armReg_lt a; have := armReg_lt b
  unfold RA.d9
  rw [beq0 (r := a) (by omega), beq0 (r := b) (by omega), show (2 : UInt64) = (2 : Nat).toUInt64 from rfl,
    show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, iu_sub _ 2 (by omega), iu_sub _ 1 (by omega),
    a9_eq _ _ (by rw [tU (by omega)]; omega), a9_eq _ _ (by rw [tU (by omega)]; omega), z1_eq ma, z1_eq mb,
    u0_eq ma, u0_eq mb, a4_eq _ _ (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega),
    a4_eq _ _ (by rw [tU (by omega)]; omega) (by rw [tU (by omega)]; omega), movz17]
  simp only [tU (show opR a < 2 ^ 64 by omega), tU (show opR b < 2 ^ 64 by omega),
    tU (show armReg a < 2 ^ 64 by omega), tU (show armReg b < 2 ^ 64 by omega), tU (show c < 2 ^ 64 by omega)]
  by_cases h0 : a = 0
  · simp [h0, e3_eq]
  by_cases h1 : b = 0
  · simp [h0, h1, e3_eq]
  · simp [h0, h1, e2_eq, opR]

theorem B_fields {V a b f3 : Nat} {o : Int} (ha : a < 32) (hb : b < 32) (hf : f3 < 8)
    (hV : V = ((4 * o) % 8192).toNat / 4096 % 2 * 2 ^ 31 + ((4 * o) % 8192).toNat / 32 % 64 * 2 ^ 25 + b * 2 ^ 20 +
      a * 2 ^ 15 + f3 * 2 ^ 12 + ((4 * o) % 8192).toNat / 2 % 16 * 2 ^ 8 + ((4 * o) % 8192).toNat / 2048 % 2 * 2 ^ 7 + 99) :
    V % 128 = 99 ∧ V / 4096 % 8 = f3 ∧ V / 32768 % 32 = a ∧ V / 1048576 % 32 = b := by
  have b1 : ((4 * o) % 8192).toNat / 4096 % 2 < 2 := Nat.mod_lt _ (by decide)
  have b2 : ((4 * o) % 8192).toNat / 32 % 64 < 64 := Nat.mod_lt _ (by decide)
  have b3 : ((4 * o) % 8192).toNat / 2 % 16 < 16 := Nat.mod_lt _ (by decide)
  have b4 : ((4 * o) % 8192).toNat / 2048 % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize ((4 * o) % 8192).toNat / 4096 % 2 = p1 at hV b1
  generalize ((4 * o) % 8192).toNat / 32 % 64 = p2 at hV b2
  generalize ((4 * o) % 8192).toNat / 2 % 16 = p3 at hV b3
  generalize ((4 * o) % 8192).toNat / 2048 % 2 = p4 at hV b4
  subst hV; omega

theorem p99 : ((99:Nat).toUInt64 == 19) = false ∧ ((99:Nat).toUInt64 == 3) = false ∧ ((99:Nat).toUInt64 == 35) = false ∧
    ((99:Nat).toUInt64 == 51) = false ∧ ((99:Nat).toUInt64 == 99) = true := by decide

theorem t0_beq (x o : List UInt8) (a b : Nat) (off : Int) (ha : a < 32) (hb : b < 32) (h1 : -1000 ≤ off)
    (h2 : off ≤ 1000) (ma : mapped a = true) (mb : mapped b = true) :
    RA.t0 x o (encG (.beq a b off)) = emit o (body (.beq a b off)) := by
  have hV := B_V 0 a b off (by omega) ha hb
  simp only [encG, show (0 : UInt64) = (0 : Nat).toUInt64 from rfl]
  generalize C.g4 _ _ _ _ = v at hV ⊢
  have := armReg_lt a; have := armReg_lt b
  simp only [RA.t0, RA.d8]
  obtain ⟨q0, q2, q3, q4⟩ := B_fields ha hb (by omega) hV
  rw [o0_eq q0, o2_eq q2, o3_eq q3, o4_eq q4, br_o7 h1 h2 (by omega) ha hb hV]
  simp only [p99, show ((0:Nat).toUInt64 == 0) = true from rfl, Bool.false_eq_true, if_false, if_true]
  rw [beq0 (r := a) (by omega), beq0 (r := b) (by omega), u0_eq ma, u0_eq mb,
    b5_eq _ _ (by rw [tU (by omega)]; omega), b5_eq _ _ (by rw [tU (by omega)]; omega),
    a8_eq _ _ (by decide) (by decide), show (0 : UInt64) = (0 : Nat).toUInt64 from rfl,
    d9_eq x o 0 (by omega) ma mb _ (by omega) (by omega)]
  simp only [tU (show armReg a < 2 ^ 64 by omega), tU (show armReg b < 2 ^ 64 by omega)]
  by_cases h0 : a = 0
  · by_cases h0' : b = 0
    · simp only [h0, h0', decide_true, if_true]; rw [e1_eq]; simp [body, bB]
    · simp [h0, h0', body, e1_eq]
  · by_cases h0' : b = 0
    · simp [h0, h0', body, e1_eq]
    · simp [h0, h0', body, compBr]

theorem t0_cbr (x o : List UInt8) (f3 c : Nat) (hfc : (f3 = 1 ∧ c = 1) ∨ (f3 = 6 ∧ c = 3) ∨ (f3 = 7 ∧ c = 2))
    (a b : Nat) (off : Int) (ha : a < 32) (hb : b < 32) (h1 : -1000 ≤ off)
    (h2 : off ≤ 1000) (ma : mapped a = true) (mb : mapped b = true) :
    RA.t0 x o (C.g4 f3.toUInt64 a.toUInt64 b.toUInt64 (iu (4 * off))) = emit o (compBr c a b off) := by
  have hV := B_V f3 a b off (by omega) ha hb
  generalize C.g4 _ _ _ _ = v at hV ⊢
  simp only [RA.t0, RA.d8]
  have hb3 : RA.b3 f3.toUInt64 = c.toUInt64 := by rcases hfc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  obtain ⟨q0, q2, q3, q4⟩ := B_fields ha hb (by omega) hV
  rw [o0_eq q0, o2_eq q2, o3_eq q3, o4_eq q4, br_o7 h1 h2 (by omega) ha hb hV, hb3, beq0 (r := f3) (by omega)]
  simp only [p99, show f3 ≠ 0 by omega, decide_false, Bool.false_eq_true, if_false, if_true]
  rw [d9_eq x o c (by omega) ma mb _ (by omega) (by omega)]
  simp only [compBr]

theorem u_split (u : Nat) (hu : u < 2097152) (hu2 : u % 2 = 0) :
    u = u / 2 ^ 20 % 2 * 2 ^ 20 + u / 4096 % 256 * 4096 + u / 2048 % 2 * 2048 + u / 2 % 1024 * 2 := by omega

theorem J_fields {V rd : Nat} {z : Int} (hd : rd < 32) (h1 : -1048576 ≤ z) (h2 : z < 1048576) (he : z % 2 = 0)
    (hV : V = (z % 2097152).toNat / 2 ^ 20 % 2 * 2 ^ 31 + (z % 2097152).toNat / 2 % 1024 * 2 ^ 21 +
      (z % 2097152).toNat / 2048 % 2 * 2 ^ 20 + (z % 2097152).toNat / 4096 % 256 * 2 ^ 12 + rd * 2 ^ 7 + 111) :
    V % 128 = 111 ∧ V / 128 % 32 = rd ∧ V < 2 ^ 32 ∧
    V / 2 ^ 31 % 2 * 2 ^ 20 + V / 4096 % 256 * 4096 + V / 2 ^ 20 % 2 * 2048 + V / 2 ^ 21 % 1024 * 2 =
      (z % 2097152).toNat := by
  have hu : (z % 2097152).toNat < 2097152 := by omega
  have hu2 : (z % 2097152).toNat % 2 = 0 := by omega
  have b1 : (z % 2097152).toNat / 2 ^ 20 % 2 < 2 := Nat.mod_lt _ (by decide)
  have b2 : (z % 2097152).toNat / 2 % 1024 < 1024 := Nat.mod_lt _ (by decide)
  have b3 : (z % 2097152).toNat / 2048 % 2 < 2 := Nat.mod_lt _ (by decide)
  have b4 : (z % 2097152).toNat / 4096 % 256 < 256 := Nat.mod_lt _ (by decide)
  generalize (z % 2097152).toNat = u at hu hu2 b1 b2 b3 b4 hV ⊢
  have hr := u_split u hu hu2
  rw [hr]
  generalize u / 2 ^ 20 % 2 = p1 at hV b1 ⊢
  generalize u / 2 % 1024 = p2 at hV b2 ⊢
  generalize u / 2048 % 2 = p3 at hV b3 ⊢
  generalize u / 4096 % 256 = p4 at hV b4 ⊢
  subst hV; omega

theorem p111 : ((111:Nat).toUInt64 == 19) = false ∧ ((111:Nat).toUInt64 == 3) = false ∧
    ((111:Nat).toUInt64 == 35) = false ∧ ((111:Nat).toUInt64 == 51) = false ∧ ((111:Nat).toUInt64 == 99) = false ∧
    ((111:Nat).toUInt64 == 111) = true := by decide

theorem jal_V (rd : Nat) (off : Int) (hd : rd < 32) :
    (C.g5 rd.toUInt64 (iu (4 * off))).toNat = ((4 * off) % 2097152).toNat / 2 ^ 20 % 2 * 2 ^ 31 +
      ((4 * off) % 2097152).toNat / 2 % 1024 * 2 ^ 21 + ((4 * off) % 2097152).toNat / 2048 % 2 * 2 ^ 20 +
      ((4 * off) % 2097152).toNat / 4096 % 256 * 2 ^ 12 + rd * 2 ^ 7 + 111 := by
  rw [g5_sum _ _ (by rw [tU (by omega)]; omega), CallProbe.iu_toNat, tU (show rd < 2 ^ 64 by omega)]
  omega

theorem t0_jal (x o : List UInt8) (rd : Nat) (off : Int) (hd : rd < 32) (h1 : -2 ^ 18 < off) (h2 : off < 2 ^ 18) :
    RA.t0 x o (encG (.jal rd off)) = emit o (body (.jal rd off)) := by
  have hV := jal_V rd off hd
  obtain ⟨q0, q1, q2, q3⟩ := J_fields hd (by omega) (by omega) (by omega) hV
  simp only [encG]
  generalize C.g5 _ _ = v at hV q0 q1 q2 q3 ⊢
  simp only [RA.t0]
  rw [o0_eq q0, o1_eq q1, o8_eq (by omega) (by omega) q2 q3, beq0 (r := rd) (by omega)]
  simp only [p111, Bool.false_eq_true, if_false, if_true]
  rw [show (3 : UInt64) = (3 : Nat).toUInt64 from rfl, iu_sub _ 3 (by omega),
    a8_eq _ _ (by decide) (by decide), a8_eq _ _ (by decide) (by decide)]
  by_cases h0 : rd = 0
  · simp only [h0, decide_true, if_true]; rw [e1_eq]; simp [body, bB]
  · simp only [h0, decide_false, Bool.false_eq_true, if_false, k0_pad]; rw [e4_eq]; simp [body, h0, blB]

theorem t0_jalr (x o : List UInt8) (rd rs : Nat) (hd : rd < 32) (hs : rs < 32) (ms : mapped rs = true) :
    RA.t0 x o (encG (.jalr rd rs)) = emit o (body (.jalr rd rs)) := by
  have hV := g2_sum C.g_103 0 rd.toUInt64 rs.toUInt64 0 (by decide) (by decide) (by rw [tU (by omega)]; omega)
    (by rw [tU (by omega)]; omega)
  rw [tU (show rd < 2 ^ 64 by omega), tU (show rs < 2 ^ 64 by omega), show C.g_103.toNat = 103 from rfl,
    show (0 : UInt64).toNat = 0 from rfl] at hV
  simp only [encG]
  generalize C.g2 _ _ _ _ _ = v at hV ⊢
  have := armReg_lt rs
  simp only [RA.t0]
  rw [o0_eq (r := 103) (by omega), o3_eq (r := rs) (by omega)]
  simp only [show ((103:Nat).toUInt64 == 19) = false from rfl, show ((103:Nat).toUInt64 == 3) = false from rfl,
    show ((103:Nat).toUInt64 == 35) = false from rfl, show ((103:Nat).toUInt64 == 51) = false from rfl,
    show ((103:Nat).toUInt64 == 99) = false from rfl, show ((103:Nat).toUInt64 == 111) = false from rfl,
    Bool.false_eq_true, if_false]
  rw [u0_eq ms, b0_eq _ (by rw [tU (by omega)]; omega), tU (by omega), e1_eq]
  rfl

end ArmRA
