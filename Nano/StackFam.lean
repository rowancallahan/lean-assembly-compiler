/- Route (a): the records `genR` emits belong to a fixed list of (opcode, register) FAMILIES (`Fam`), and each family's
`asm` bytes are one RISC-V word of a known encoder (`w_*`, checked by `decide` over the 8-bit field).  This is what the
Sail refinement (`Nano/StackSail.lean`) needs to run any record of `genR p` on the Sail model. -/
import Nano.StackRun
import Riscv.Steps.GenMem
import Riscv.Steps.GenMul

namespace Nano.F
open Proven Proven.G Nano

/-- the record families of `genR` (opcode, registers; `c` bounded where the encoding needs it) -/
def Fam (op a b c : UInt8) : Bool :=
  (op == 0 && ((a == 31 && b == 31) || (a == 10 && b == 0) || (a == 5 && b == 0) || (a == 28 && b == 10))) ||
  (op == 1 && ((a == 5 && b == 5) || (a == 31 && b == 31)) && c < 64) ||
  (op == 3 && (a == 5 || a == 6) && b == 31) ||
  (op == 4 && (a == 5 || a == 6) && b == 28) ||
  (op == 5 && ((a == 6 && b == 5) || (a == 31 && b == 2)) && c < 64) ||
  (op == 6 && a == 5 && b == 5) ||
  (op == 7 && a == 0 && b == 31 && c == 12) ||
  (op == 8 && ((a == 31 && b == 31) || (a == 28 && b == 28))) ||
  (op == 11 && a == 5 && b == 31) ||
  ((op == 14 || op == 24 || op == 32 || op == 40) && a == 5 && b == 5 && c == 6) ||
  (op == 16 && a == 6 && b == 13 && c < 32) ||
  (op == 48 && a == 0 && b == 1 && c == 0)

/-- every record of the list is in a family -/
def allFam : List UInt8 → Bool
  | op :: a :: b :: c :: rest => Fam op a b c && allFam rest
  | [] => true
  | _ => false

theorem allFam_append : ∀ (l₁ l₂ : List UInt8), l₁.length % 4 = 0 → allFam (l₁ ++ l₂) = (allFam l₁ && allFam l₂)
  | [], _, _ => by simp [allFam]
  | op :: a :: b :: c :: rest, l₂, h => by
    simp only [List.cons_append, allFam]
    rw [allFam_append rest l₂ (by simp at h; omega), Bool.and_assoc]
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h
  | [_, _, _], _, h => by simp at h

theorem allFam_get : ∀ (P : List UInt8) (i : Nat) {op a b c : UInt8} {rest : List UInt8}, allFam P = true →
    P.drop (4 * i) = op :: a :: b :: c :: rest → Fam op a b c = true
  | op' :: a' :: b' :: c' :: P', 0, op, a, b, c, rest, h, e => by
    simp only [Nat.mul_zero, List.drop_zero, List.cons.injEq] at e
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := e
    simp only [allFam, Bool.and_eq_true] at h; exact h.1
  | op' :: a' :: b' :: c' :: P', i + 1, op, a, b, c, rest, h, e => by
    simp only [allFam, Bool.and_eq_true] at h
    exact allFam_get P' i h.2 (by rw [show 4 * (i + 1) = 4 * i + 4 by omega] at e; simpa using e)
  | [], _, _, _, _, _, _, _, e => by simp at e
  | [_], i, _, _, _, _, _, _, e => by have := congrArg List.length e; simp at this; omega
  | [_, _], i, _, _, _, _, _, _, e => by have := congrArg List.length e; simp at this; omega
  | [_, _, _], i, _, _, _, _, _, _, e => by have := congrArg List.length e; simp at this; omega

/-! ## the blocks of `genR` -/

theorem fam_ori (x : UInt8) : Fam 6 5 5 x = true := rfl
theorem fam_ld (x : UInt8) : Fam 3 5 31 x = true := rfl
theorem fam_addsp (x : UInt8) : Fam 8 31 31 x = true := rfl

theorem af_li (n : UInt64) : allFam (li n) = true := by simp [li, r, allFam, fam_ori]; decide
theorem af_push : allFam push = true := by decide
theorem af_ld (k : Nat) : allFam (ld 5 31 k) = true := by simp [ld, r, allFam, fam_ld]
theorem af_addSp (k : Nat) : allFam (addSp k) = true := by simp [addSp, r, allFam, fam_addsp]
theorem af_sd : allFam (sd 5 31 0) = true := by decide
theorem af_binop (k : UInt8) (hk : k = 24 ∨ k = 32 ∨ k = 40) : allFam (binop k) = true := by
  rcases hk with rfl | rfl | rfl <;> decide
theorem af_rd8 : allFam rd8 = true := by decide
theorem af_wr8 : allFam wr8 = true := by decide

theorem len_li (n : UInt64) : (li n).length % 4 = 0 := by simp [li, r]
theorem len_push : push.length % 4 = 0 := by decide
theorem len_ld (k : Nat) : (ld 5 31 k).length % 4 = 0 := by simp [ld, r]
theorem len_addSp (k : Nat) : (addSp k).length % 4 = 0 := by simp [addSp, r]
theorem len_binop (k : UInt8) : (binop k).length % 4 = 0 := by simp [binop, ld, addSp, sd, r]

mutual
theorem len_genE : ∀ (sc : List Nat) (d : Nat) (e : Ex), (genE sc d e).length % 4 = 0
  | _, _, .num n => by simp only [genE, List.length_append]; have := len_li n; have := len_push; omega
  | _, _, .var _ => by simp only [genE, List.length_append]; have := len_push; simp [ld, r]; omega
  | sc, d, .add a b => by
    simp only [genE, List.length_append]; have := len_genE sc d a; have := len_genE sc (d + 1) b
    have := len_binop 24; omega
  | sc, d, .sub a b => by
    simp only [genE, List.length_append]; have := len_genE sc d a; have := len_genE sc (d + 1) b
    have := len_binop 32; omega
  | sc, d, .mul a b => by
    simp only [genE, List.length_append]; have := len_genE sc d a; have := len_genE sc (d + 1) b
    have := len_binop 40; omega
  | sc, d, .let_ v b => by
    simp only [genE, List.length_append]; have := len_genE sc d v; have := len_genE (d :: sc) (d + 1) b
    simp [ld, addSp, sd, r]; omega
  | sc, d, .call b as => by
    simp only [genE, List.length_append]; have := len_genA sc d as
    have := len_genE (mkSc (cnt as) d) (d + cnt as) b
    simp [ld, addSp, sd, r]; omega
  | _, _, .anil => by simp [genE]
  | _, _, .acons _ _ => by simp [genE]
theorem len_genA : ∀ (sc : List Nat) (d : Nat) (e : Ex), (genA sc d e).length % 4 = 0
  | sc, d, .acons e r => by
    simp only [genA, List.length_append]; have := len_genE sc d e; have := len_genA sc (d + 1) r; omega
  | _, _, .num _ => by simp [genA] | _, _, .var _ => by simp [genA] | _, _, .add _ _ => by simp [genA]
  | _, _, .sub _ _ => by simp [genA] | _, _, .mul _ _ => by simp [genA] | _, _, .let_ _ _ => by simp [genA]
  | _, _, .call _ _ => by simp [genA] | _, _, .anil => by simp [genA]
end

mutual
theorem af_genE : ∀ (sc : List Nat) (d : Nat) (e : Ex), allFam (genE sc d e) = true
  | _, _, .num n => by simp only [genE]; rw [allFam_append _ _ (len_li n), af_li, af_push]; rfl
  | _, _, .var _ => by simp only [genE]; rw [allFam_append _ _ (len_ld _), af_ld, af_push]; rfl
  | sc, d, .add a b => by
    simp only [genE]
    rw [allFam_append _ _ (by have := len_genE sc d a; have := len_genE sc (d + 1) b; simp; omega),
      allFam_append _ _ (len_genE sc d a), af_genE sc d a, af_genE sc (d + 1) b, af_binop 24 (by decide)]; rfl
  | sc, d, .sub a b => by
    simp only [genE]
    rw [allFam_append _ _ (by have := len_genE sc d a; have := len_genE sc (d + 1) b; simp; omega),
      allFam_append _ _ (len_genE sc d a), af_genE sc d a, af_genE sc (d + 1) b, af_binop 32 (by decide)]; rfl
  | sc, d, .mul a b => by
    simp only [genE]
    rw [allFam_append _ _ (by have := len_genE sc d a; have := len_genE sc (d + 1) b; simp; omega),
      allFam_append _ _ (len_genE sc d a), af_genE sc d a, af_genE sc (d + 1) b, af_binop 40 (by decide)]; rfl
  | sc, d, .let_ v b => by
    simp only [genE, List.append_assoc]
    rw [allFam_append _ _ (len_genE sc d v), allFam_append _ _ (len_genE (d :: sc) (d + 1) b),
      allFam_append _ _ (len_ld 0), allFam_append _ _ (len_addSp 1), af_genE sc d v, af_genE (d :: sc) (d + 1) b,
      af_ld, af_addSp, af_sd]; rfl
  | sc, d, .call b as => by
    simp only [genE, List.append_assoc]
    rw [allFam_append _ _ (len_genA sc d as), allFam_append _ _ (len_genE (mkSc (cnt as) d) (d + cnt as) b),
      allFam_append _ _ (len_ld 0), allFam_append _ _ (len_addSp _), af_genA sc d as,
      af_genE (mkSc (cnt as) d) (d + cnt as) b, af_ld, af_addSp, af_sd]; rfl
  | _, _, .anil => by simp [genE, allFam]
  | _, _, .acons _ _ => by simp [genE, allFam]
theorem af_genA : ∀ (sc : List Nat) (d : Nat) (e : Ex), allFam (genA sc d e) = true
  | sc, d, .acons e r => by
    simp only [genA]; rw [allFam_append _ _ (len_genE sc d e), af_genE sc d e, af_genA sc (d + 1) r]; rfl
  | _, _, .num _ => by simp [genA, allFam] | _, _, .var _ => by simp [genA, allFam]
  | _, _, .add _ _ => by simp [genA, allFam] | _, _, .sub _ _ => by simp [genA, allFam]
  | _, _, .mul _ _ => by simp [genA, allFam] | _, _, .let_ _ _ => by simp [genA, allFam]
  | _, _, .call _ _ => by simp [genA, allFam] | _, _, .anil => by simp [genA, allFam]
end

theorem af_pro : ∀ k, allFam (pro k) = true ∧ (pro k).length % 4 = 0
  | 0 => by simp [pro, allFam]
  | k + 1 => by
    obtain ⟨h1, h2⟩ := af_pro k
    have l1 : rd8.length % 4 = 0 := by decide
    simp only [pro, List.append_assoc]
    refine ⟨?_, by simp only [List.length_append]; have := len_push; simp [r]; omega⟩
    rw [allFam_append _ _ l1, allFam_append _ _ len_push, allFam_append _ _ (by decide), af_rd8, af_push, h1]; rfl

/-- **every record of `genR p` is in a family** -/
theorem af_genR (p : Prog) : allFam (genR p) = true := by
  simp only [genR, List.append_assoc]
  obtain ⟨h1, h2⟩ := af_pro p.1
  rw [allFam_append _ _ (by decide), allFam_append _ _ (by decide), allFam_append _ _ (by decide),
    allFam_append _ _ h2, allFam_append _ _ (len_genE _ _ _), allFam_append _ _ (len_ld 0),
    allFam_append _ _ (by decide), h1, af_genE, af_ld, af_wr8]; rfl

/-! ## the words: `asm` of a record of each family -/

/-- the 4 little-endian bytes of a word -/
def wb (w : BitVec 32) : List UInt8 :=
  [UInt8.ofBitVec (w.extractLsb' 0 8), UInt8.ofBitVec (w.extractLsb' 8 8), UInt8.ofBitVec (w.extractLsb' 16 8),
    UInt8.ofBitVec (w.extractLsb' 24 8)]

/-- the 12-bit immediate of an `addi` record: `c` sign-extended -/
def sx12 (c : UInt8) : BitVec 12 := c.toBitVec.signExtend 12

set_option maxRecDepth 100000

theorem w_addi_31_31 : ∀ c, c < 256 → asm [0, 31, 31, c.toUInt8] = wb (encI 0 (sx12 c.toUInt8).toNat 31 31) := by decide +kernel
theorem w_addi_10_0 : ∀ c, c < 256 → asm [0, 10, 0, c.toUInt8] = wb (encI 0 (sx12 c.toUInt8).toNat 10 0) := by decide +kernel
theorem w_addi_5_0 : ∀ c, c < 256 → asm [0, 5, 0, c.toUInt8] = wb (encI 0 (sx12 c.toUInt8).toNat 5 0) := by decide +kernel
theorem w_addi_28_10 : ∀ c, c < 256 → asm [0, 28, 10, c.toUInt8] = wb (encI 0 (sx12 c.toUInt8).toNat 28 10) := by decide +kernel
theorem w_slli_5_5 : ∀ c, c < 64 → asm [1, 5, 5, c.toUInt8] = wb (encI 1 (0 <<< 6 ||| (BitVec.ofNat 6 c).toNat) 5 5) := by decide +kernel
theorem w_slli_31_31 : ∀ c, c < 64 → asm [1, 31, 31, c.toUInt8] = wb (encI 1 (0 <<< 6 ||| (BitVec.ofNat 6 c).toNat) 31 31) := by decide +kernel
theorem w_ld_5 : ∀ c, c < 256 → asm [3, 5, 31, c.toUInt8] = wb (encL 3 (BitVec.ofNat 12 (8 * c)) 5 31) := by decide +kernel
theorem w_ld_6 : ∀ c, c < 256 → asm [3, 6, 31, c.toUInt8] = wb (encL 3 (BitVec.ofNat 12 (8 * c)) 6 31) := by decide +kernel
theorem w_lbu_5 : ∀ c, c < 256 → asm [4, 5, 28, c.toUInt8] = wb (encL 4 (BitVec.ofNat 12 c) 5 28) := by decide +kernel
theorem w_lbu_6 : ∀ c, c < 256 → asm [4, 6, 28, c.toUInt8] = wb (encL 4 (BitVec.ofNat 12 c) 6 28) := by decide +kernel
theorem w_srli_6_5 : ∀ c, c < 64 → asm [5, 6, 5, c.toUInt8] = wb (encI 5 (0 <<< 6 ||| (BitVec.ofNat 6 c).toNat) 6 5) := by decide +kernel
theorem w_srli_31_2 : ∀ c, c < 64 → asm [5, 31, 2, c.toUInt8] = wb (encI 5 (0 <<< 6 ||| (BitVec.ofNat 6 c).toNat) 31 2) := by decide +kernel
theorem w_ori : ∀ c, c < 256 → asm [6, 5, 5, c.toUInt8] = wb (encI 6 (BitVec.ofNat 12 c).toNat 5 5) := by decide +kernel
theorem w_bgeu : asm [7, 0, 31, 12] = wb (wB 7 (BitVec.ofFin (31 : Fin 32)) (BitVec.ofFin (12 : Fin 32)) 6#12) := by decide +kernel
theorem w_addi8_31 : ∀ c, c < 256 → asm [8, 31, 31, c.toUInt8] = wb (encI 0 (BitVec.ofNat 12 (8 * c)).toNat 31 31) := by decide +kernel
theorem w_addi8_28 : ∀ c, c < 256 → asm [8, 28, 28, c.toUInt8] = wb (encI 0 (BitVec.ofNat 12 (8 * c)).toNat 28 28) := by decide +kernel
theorem w_sd : ∀ c, c < 256 → asm [11, 5, 31, c.toUInt8] = wb (encS 3 (BitVec.ofNat 12 (8 * c)) 5 31) := by decide +kernel
theorem w_or : asm [14, 5, 5, 6] = wb (encR 0 6 5 5 6) := by decide +kernel
theorem w_add : asm [24, 5, 5, 6] = wb (encR 0 0 5 5 6) := by decide +kernel
theorem w_sub : asm [32, 5, 5, 6] = wb (encR 0x20 0 5 5 6) := by decide +kernel
theorem w_mul : asm [40, 5, 5, 6] = wb (encR 1 0 5 5 6) := by decide +kernel
theorem w_sb : ∀ c, c < 32 → asm [16, 6, 13, c.toUInt8] = wb (encS 0 (BitVec.ofNat 12 c) 6 13) := by decide +kernel
theorem w_ret : asm [48, 0, 1, 0] = wb (BitVec.ofNat 32 ((0 : BitVec 12).toNat <<< 20 ||| (1 : Fin 32).val <<< 15 |||
    (0 : Fin 32).val <<< 7 ||| 0x67)) := by decide +kernel

end Nano.F
