/- The RISC-V adapter's machine words (Sail-free): `encJ`/`encJX` = the RV64 word of each J instruction (via
nano-v2's `I.enc` and C's encoders g2–g5), `ropOf`/`aluf_eval` (J's BIN numbering as `ROp`).  Split out of
SimW/SimX; names stay in namespace `SimW`. -/
import Nano.V2Self.Proof.Machine.Call
import Nano.V2Self.Proof.Machine.Bridge
import Nano.Base.V2.Sem

namespace SimW
open Nano.V2B

/-- J's ALU numbering (Gen's BIN: add 1 sub 2 mul 3 and 4 or 5 sll 6 srl 7 xor 8) as nano-v2's `ROp` -/
def ropOf (op : Nat) : ROp :=
  if op = 1 then .add else if op = 2 then .sub else if op = 3 then .mul else if op = 4 then .and
  else if op = 5 then .or else if op = 6 then .sll else if op = 7 then .srl else .xor

theorem shl_mod (a b : UInt64) : a <<< b = a <<< (b % 64) := by
  apply UInt64.toBitVec_inj.1; rw [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftLeft]; simp [BitVec.shiftLeft_eq', UInt64.toBitVec_mod]
theorem shr_mod (a b : UInt64) : a >>> b = a >>> (b % 64) := by
  apply UInt64.toBitVec_inj.1; rw [UInt64.toBitVec_shiftRight, UInt64.toBitVec_shiftRight]; simp [BitVec.ushiftRight_eq', UInt64.toBitVec_mod]

theorem aluf_eval (op : Nat) (x y : UInt64) (h : 1 ≤ op ∧ op ≤ 8) : CallProbe.aluf op x y = (ropOf op).eval x y := by
  obtain ⟨h1, h2⟩ := h
  rcases (by omega : op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CallProbe.aluf, ropOf, ROp.eval]
  · exact shl_mod x y
  · exact shr_mod x y

theorem ofInt_bv' (x : Int) : (UInt64.ofInt x).toBitVec = BitVec.ofInt 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, UInt64.toNat_toBitVec]
  unfold UInt64.ofInt; rw [UInt64.toNat_ofNat']
  have h1 : (0 : Int) ≤ x % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h2 : x % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by decide)
  omega

theorem ofInt_toNat64 (x : Int) : (UInt64.ofInt x).toNat = (x % 2 ^ 64).toNat := by
  unfold UInt64.ofInt; rw [UInt64.toNat_ofNat']
  have h1 : (0 : Int) ≤ x % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h2 : x % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by decide)
  omega

/-- the word C emits for a J instruction (branches only as `bgeu a b +2 instructions`, returns only `jalr x0`) -/
def encJ : CallProbe.J → Nat
  | .addi rd rs imm => (I.i .addi rd rs imm).enc
  | .ld rd rs off => (I.ld rd rs off).enc
  | .sd b a off => (I.sd b a off).enc
  | .bgeu a b o => (I.br .bgeu a b (4 * o)).enc
  | .beq a b _ => (I.br .beq a b 8).enc
  | .bltu a b _ => (I.br .bltu a b 8).enc
  | .jal rd off => (C.g5 (UInt64.ofNat rd) (UInt64.ofInt (4 * off))).toNat
  | .jalr _ rs => (C.g2 C.g_103 0 0 (UInt64.ofNat rs) 0).toNat
  | .alu op rd a b => (I.r (ropOf op) rd a b).enc
  | .slli rd rs sh => (I.i .slli rd rs (sh : Int)).enc
  | .lbu rd rs off => (I.lbu rd rs off).enc
  | .srli rd rs sh => (C.g2 C.g_19 5 (UInt64.ofNat rd) (UInt64.ofNat rs) (UInt64.ofNat sh)).toNat
  | .bne a b off => (C.g4 1 (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofInt (4 * off))).toNat
  | .sb r2 r1 off => (C.g3 0 (UInt64.ofNat r2) (UInt64.ofNat r1) (UInt64.ofInt off)).toNat

theorem sI_ofNat (n : Nat) (h : n < 2 ^ 63) : Bridge.sI (UInt64.ofNat n) = n := by
  unfold Bridge.sI; simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega), h]

theorem sI_ofInt (z : Int) (h1 : -2 ^ 63 ≤ z) (h2 : z < 2 ^ 63) : Bridge.sI (UInt64.ofInt z) = z := by
  unfold Bridge.sI
  have : ((UInt64.ofInt z).toNat : Int) = z % 2 ^ 64 := by
    rw [ofInt_toNat64]; omega
  split <;> omega

theorem encJ_srli (rd rs sh : Nat) (hd : rd < 32) (hs : rs < 32) (hh : sh < 64) :
    encJ (.srli rd rs sh) = (I.i .srli rd rs (sh : Int)).enc := by
  simp only [encJ]
  rw [Bridge.g2_enc _ _ _ _ _ (by decide) (by decide) (by simp; omega) (by simp; omega), sI_ofNat _ (by omega)]
  simp [I.enc, UInt64.toNat_ofNat, Nat.mod_eq_of_lt (show rd < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show rs < 2 ^ 64 by omega)]; rfl

theorem encJ_bne (a b : Nat) (ha : a < 32) (hb : b < 32) :
    encJ (.bne a b 4) = (I.br .bne a b 16).enc := by
  simp only [encJ]
  rw [Bridge.g4_bne _ _ _ (by simp; omega) (by simp; omega), sI_ofInt _ (by omega) (by omega)]
  simp [UInt64.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]

theorem encJ_sb (b a : Nat) (off : Int) (hb : b < 32) (ha : a < 32) (h1 : -2048 ≤ off) (h2 : off < 2048) :
    encJ (.sb b a off) = (I.sb b a off).enc := by
  simp only [encJ]
  rw [Bridge.g3_enc _ _ _ _ (by decide) (by simp; omega) (by simp; omega), sI_ofInt _ (by omega) (by omega)]
  simp [I.enc, UInt64.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]

def encJX : CallProbe.J → Nat
  | .beq a b o => (I.br .beq a b (4 * o)).enc
  | i => encJ i

end SimW
