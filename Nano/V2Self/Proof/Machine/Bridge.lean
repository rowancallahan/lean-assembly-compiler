/- Bridge (Astra-11): C's word encoders (Nano/V2Self/C/Gen.lean g1–g5, g10–g13) produce exactly nano-v2's
`I.enc` words (Nano/V2/Gen.lean), which Nano/V2/Enc.lean + Sim.lean already tie to the Sail step lemmas.  Sail-free (the one Sail-word lemma
`g5_wJ` lives in SimW).
Immediates: C passes a UInt64 two's-complement value `v`; the instruction's signed immediate is `sI v`. -/
import Nano.V2.Gen
import Nano.V2Self.C.Gen

namespace Bridge
open Nano.V2B

/-- the signed reading of a UInt64 -/
def sI (v : UInt64) : Int := if v.toNat < 2 ^ 63 then v.toNat else (v.toNat : Int) - 2 ^ 64

theorem bits_sI12 (v : UInt64) : bits (sI v) 12 = v.toNat % 4096 := by
  have := v.toNat_lt; unfold bits sI; split <;> simp <;> omega
theorem bits_sI13 (v : UInt64) : bits (sI v) 13 = v.toNat % 8192 := by
  have := v.toNat_lt; unfold bits sI; split <;> simp <;> omega
theorem bits_sI21 (v : UInt64) : bits (sI v) 21 = v.toNat % 2097152 := by
  have := v.toNat_lt; unfold bits sI; split <;> simp <;> omega

theorem and4095 (n : Nat) : n &&& 4095 = n % 4096 := by
  rw [show (4095 : Nat) = 2 ^ 12 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem shl_lt (x k : Nat) (h : x < 2 ^ (64 - k)) (hk : k < 64) : (x <<< k) % 2 ^ 64 = x <<< k := by
  rw [Nat.shiftLeft_eq]; apply Nat.mod_eq_of_lt
  calc x * 2 ^ k < 2 ^ (64 - k) * 2 ^ k := Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos k)
    _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega

/-- I-type: `g2 p f3 d a v` is `encIt` with the signed immediate `sI v` -/
theorem g2_enc (p f3 d a v : UInt64) (hp : p.toNat < 128) (hf : f3.toNat < 8) (hd : d.toNat < 32) (ha : a.toNat < 32) :
    (C.g2 p f3 d a v).toNat = encIt p.toNat f3.toNat d.toNat a.toNat (sI v) := by
  unfold C.g2 encIt
  rw [bits_sI12]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_and, show C.g_4095.toNat = 4095 from rfl,
    and4095, show (20 : UInt64).toNat % 64 = 20 from rfl, show (15 : UInt64).toNat % 64 = 15 from rfl,
    show (12 : UInt64).toNat % 64 = 12 from rfl, show (7 : UInt64).toNat % 64 = 7 from rfl]
  rw [shl_lt _ 20 (by omega) (by omega), shl_lt _ 15 (by omega) (by omega), shl_lt _ 12 (by omega) (by omega),
    shl_lt _ 7 (by omega) (by omega)]

theorem mask (n k : Nat) : n &&& (2 ^ k - 1) = n % 2 ^ k := Nat.and_two_pow_sub_one_eq_mod n k
theorem land1 (n : Nat) : n &&& 1 = n % 2 := mask n 1
theorem land15 (n : Nat) : n &&& 15 = n % 16 := mask n 4
theorem land63 (n : Nat) : n &&& 63 = n % 64 := mask n 6
theorem land255 (n : Nat) : n &&& 255 = n % 256 := mask n 8
theorem land1023 (n : Nat) : n &&& 1023 = n % 1024 := mask n 10
theorem shr (n k : Nat) : n >>> k = n / 2 ^ k := Nat.shiftRight_eq_div_pow n k

/-- S-type (`g3` = sd/sb) is `encSt` -/
theorem g3_enc (f3 b a v : UInt64) (hf : f3.toNat < 8) (hb : b.toNat < 32) (ha : a.toNat < 32) :
    (C.g3 f3 b a v).toNat = encSt f3.toNat b.toNat a.toNat (sI v) := by
  unfold C.g3 encSt
  simp only [bits_sI12]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.toNat_and,
    show C.g_127.toNat = 2 ^ 7 - 1 from rfl, show C.g_31.toNat = 2 ^ 5 - 1 from rfl, show C.g_35.toNat = 0x23 from rfl,
    mask, show (25 : UInt64).toNat % 64 = 25 from rfl, show (20 : UInt64).toNat % 64 = 20 from rfl,
    show (15 : UInt64).toNat % 64 = 15 from rfl, show (12 : UInt64).toNat % 64 = 12 from rfl,
    show (7 : UInt64).toNat % 64 = 7 from rfl, show (5 : UInt64).toNat % 64 = 5 from rfl]
  rw [shl_lt _ 25 (by rw [Nat.shiftRight_eq_div_pow]; omega) (by omega), shl_lt _ 20 (by omega) (by omega),
    shl_lt _ 15 (by omega) (by omega), shl_lt _ 12 (by omega) (by omega), shl_lt _ 7 (by omega) (by omega)]
  have e1 : (v.toNat >>> 5) % 2 ^ 7 = (v.toNat % 4096) >>> 5 := by simp only [Nat.shiftRight_eq_div_pow]; omega
  have e2 : v.toNat % 2 ^ 5 = (v.toNat % 4096) &&& 31 := by
    rw [show (31 : Nat) = 2 ^ 5 - 1 by rfl, mask]; omega
  rw [e1, e2]

/-- B-type (`g4` = beq/bne/bltu/bgeu) is `encBt` -/
theorem g4_enc (f3 a b v : UInt64) (hf : f3.toNat < 8) (ha : a.toNat < 32) (hb : b.toNat < 32) :
    (C.g4 f3 a b v).toNat = encBt f3.toNat a.toNat b.toNat (sI v) := by
  unfold C.g4 encBt
  simp only [bits_sI13]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.toNat_and,
    show C.g_1.toNat = 1 from rfl, show C.g_63.toNat = 63 from rfl, show C.g_15.toNat = 15 from rfl,
    show C.g_99.toNat = 0x63 from rfl,
    show (31 : UInt64).toNat = 31 from rfl, show (25 : UInt64).toNat = 25 from rfl,
    show (21 : UInt64).toNat = 21 from rfl, show (20 : UInt64).toNat = 20 from rfl,
    show (15 : UInt64).toNat = 15 from rfl, show (12 : UInt64).toNat = 12 from rfl,
    show (11 : UInt64).toNat = 11 from rfl, show (8 : UInt64).toNat = 8 from rfl,
    show (7 : UInt64).toNat = 7 from rfl, show (5 : UInt64).toNat = 5 from rfl,
    show (1 : UInt64).toNat = 1 from rfl, land1, land15, land63, land255, land1023, shr]
  rw [shl_lt _ 31 (by omega) (by omega), shl_lt _ 25 (by omega) (by omega), shl_lt _ 20 (by omega) (by omega),
    shl_lt _ 15 (by omega) (by omega), shl_lt _ 12 (by omega) (by omega), shl_lt _ 8 (by omega) (by omega),
    shl_lt _ 7 (by omega) (by omega)]
  rw [show v.toNat / 2 ^ 12 % 2 = v.toNat % 8192 / 2 ^ 12 % 2 by omega,
    show v.toNat / 2 ^ 5 % 64 = v.toNat % 8192 / 2 ^ 5 % 64 by omega,
    show v.toNat / 2 ^ 1 % 16 = v.toNat % 8192 / 2 ^ 1 % 16 by omega,
    show v.toNat / 2 ^ 11 % 2 = v.toNat % 8192 / 2 ^ 11 % 2 by omega]

/-- J-type (`g5` = jal rd) : `encJt` for rd = 0, plus `rd <<< 7` -/
theorem g5_enc (d v : UInt64) (hd : d.toNat < 32) :
    (C.g5 d v).toNat = encJt (sI v) ||| d.toNat <<< 7 := by
  unfold C.g5 encJt
  simp only [bits_sI21]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.toNat_and,
    show C.g_1.toNat = 1 from rfl, show C.g_1023.toNat = 1023 from rfl,
    show C.g_255.toNat = 255 from rfl, show C.g_111.toNat = 0x6f from rfl,
    show (31 : UInt64).toNat = 31 from rfl, show (25 : UInt64).toNat = 25 from rfl,
    show (21 : UInt64).toNat = 21 from rfl, show (20 : UInt64).toNat = 20 from rfl,
    show (15 : UInt64).toNat = 15 from rfl, show (12 : UInt64).toNat = 12 from rfl,
    show (11 : UInt64).toNat = 11 from rfl, show (8 : UInt64).toNat = 8 from rfl,
    show (7 : UInt64).toNat = 7 from rfl, show (5 : UInt64).toNat = 5 from rfl,
    show (1 : UInt64).toNat = 1 from rfl, land1, land15, land63, land255, land1023, shr]
  rw [shl_lt _ 31 (by omega) (by omega), shl_lt _ 21 (by omega) (by omega), shl_lt _ 20 (by omega) (by omega),
    shl_lt _ 12 (by omega) (by omega), shl_lt _ 7 (by omega) (by omega)]
  rw [show v.toNat / 2 ^ 20 % 2 = v.toNat % 2097152 / 2 ^ 20 % 2 by omega,
    show v.toNat / 2 ^ 1 % 1024 = v.toNat % 2097152 / 2 ^ 1 % 1024 by omega,
    show v.toNat / 2 ^ 11 % 2 = v.toNat % 2097152 / 2 ^ 11 % 2 by omega,
    show v.toNat / 2 ^ 12 % 256 = v.toNat % 2097152 / 2 ^ 12 % 256 by omega]
  rw [Nat.or_assoc, Nat.or_comm (d.toNat <<< 7) 111, ← Nat.or_assoc]

/-- R-type (`g1`) is `encR` -/
theorem g1_enc (f7 f3 d a b : UInt64) (h7 : f7.toNat < 128) (hf : f3.toNat < 8) (hd : d.toNat < 32) (ha : a.toNat < 32)
    (hb : b.toNat < 32) : (C.g1 f7 f3 d a b).toNat = encR f7.toNat f3.toNat d.toNat a.toNat b.toNat := by
  unfold C.g1 encR
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, show C.g_51.toNat = 0x33 from rfl,
    show (25 : UInt64).toNat = 25 from rfl, show (20 : UInt64).toNat = 20 from rfl, show (15 : UInt64).toNat = 15 from rfl,
    show (12 : UInt64).toNat = 12 from rfl, show (7 : UInt64).toNat = 7 from rfl]
  rw [shl_lt _ 25 (by omega) (by omega), shl_lt _ 20 (by omega) (by omega), shl_lt _ 15 (by omega) (by omega),
    shl_lt _ 12 (by omega) (by omega), shl_lt _ 7 (by omega) (by omega)]

/-! ## per instruction: C's emitters produce nano-v2's `I.enc` words (registers as Nats < 32) -/
theorem g10_I (d a v : UInt64) (hd : d.toNat < 32) (ha : a.toNat < 32) :
    (C.g10 d a v).toNat = (I.i .addi d.toNat a.toNat (sI v)).enc := by
  unfold C.g10; rw [g2_enc _ _ _ _ _ (by decide) (by decide) hd ha]; rfl
theorem g11_I (d a v : UInt64) (hd : d.toNat < 32) (ha : a.toNat < 32) :
    (C.g11 d a v).toNat = (I.ld d.toNat a.toNat (sI v)).enc := by
  unfold C.g11; rw [g2_enc _ _ _ _ _ (by decide) (by decide) hd ha]; rfl
theorem g12_I (b a v : UInt64) (hb : b.toNat < 32) (ha : a.toNat < 32) :
    (C.g12 b a v).toNat = (I.sd b.toNat a.toNat (sI v)).enc := by
  unfold C.g12; rw [g3_enc _ _ _ _ (by decide) hb ha]; rfl
theorem g4_bgeu (a b v : UInt64) (ha : a.toNat < 32) (hb : b.toNat < 32) :
    (C.g4 7 a b v).toNat = (I.br .bgeu a.toNat b.toNat (sI v)).enc := by
  rw [g4_enc _ _ _ _ (by decide) ha hb]; rfl
theorem g4_beq (a b v : UInt64) (ha : a.toNat < 32) (hb : b.toNat < 32) :
    (C.g4 0 a b v).toNat = (I.br .beq a.toNat b.toNat (sI v)).enc := by
  rw [g4_enc _ _ _ _ (by decide) ha hb]; rfl
theorem g4_bne (a b v : UInt64) (ha : a.toNat < 32) (hb : b.toNat < 32) :
    (C.g4 1 a b v).toNat = (I.br .bne a.toNat b.toNat (sI v)).enc := by
  rw [g4_enc _ _ _ _ (by decide) ha hb]; rfl
theorem g4_bltu (a b v : UInt64) (ha : a.toNat < 32) (hb : b.toNat < 32) :
    (C.g4 6 a b v).toNat = (I.br .bltu a.toNat b.toNat (sI v)).enc := by
  rw [g4_enc _ _ _ _ (by decide) ha hb]; rfl
/-- `jal x0` (C's long jumps) is nano-v2's `jal` -/
theorem g5_jal0 (v : UInt64) : (C.g5 0 v).toNat = (I.jal (sI v)).enc := by
  rw [g5_enc _ _ (by decide)]; simp [I.enc]

/-! ## calls and returns: the Sail words of `jal rd` and `jalr x0, rs` -/
/-- C's return `jalr x0, 0(rs)` (`g2 103 0 0 a 0`) is the word of Sail's `step_jalr` with imm 0, rd 0 -/
theorem g2_jalr (a : UInt64) (ha : a.toNat < 32) :
    BitVec.ofNat 32 (C.g2 C.g_103 0 0 a 0).toNat =
      BitVec.ofNat 32 ((0 : BitVec 12).toNat <<< 20 ||| a.toNat <<< 15 ||| (0 : Nat) <<< 7 ||| 0x67) := by
  rw [g2_enc _ _ _ _ _ (by decide) (by decide) (by decide) ha]
  unfold encIt; rw [bits_sI12]; simp [show C.g_103.toNat = 0x67 from rfl]

end Bridge
