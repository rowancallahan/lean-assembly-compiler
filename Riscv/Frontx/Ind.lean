/- User inductive types with payload (cells in the work block, `Compiler/Ind.lean`) in `Implements1` form, and
the command `frontx_ind` that compiles a structural recursive Lean function over a user inductive.

`implements1_ind` (once): `indProg` + `ind_ok` (source level) + `implements1_of_cexecW` (word block at the bottom of
the work block, stack above) give `Implements1With encA encB (callsCode1W …) f space` for any `f` whose meaning is
the program's (`hout`), with `space n = 8 wn n + need n + 24`, `wn n = 8 + 4 (M + 1) n` words of cells. -/
import Compiler.IndMain
import Riscv.Back.CallsImpl1W

set_option linter.unusedVariables false

namespace Proven.Frontx.Ind
open Proven Proven.Mach Proven.Mach.Ind Proven.Mach.Riscv

/-- cells of the word block for `n` input bytes -/
def wn (M n : Nat) : Nat := 8 + 4 * (M + 1) * n

/-- the work space: cells, then the stack -/
def space (M n : Nat) : Nat := 8 * wn M n + (56 + 136 * (1 + n + wn M n)) + 24

theorem wr_take (O : List (BitVec 8)) (L : List UInt8) (h : L.length ≤ O.length) :
    (wr O 0 L).take L.length = L.map (·.toBitVec) := by simp [wr]
theorem wr_drop (O : List (BitVec 8)) (L : List UInt8) (h : L.length ≤ O.length) :
    (wr O 0 L).drop L.length = O.drop L.length := by simp [wr]

/-- **User inductives ⇒ `Implements1`.** -/
theorem implements1_ind {rk : Kd} {γ β : Type} (sh : Shape) (pg : Pg rk) (bi : BIn) (a0 : BitVec 64) (nb : Nat)
    (encA : γ → List UInt8) (encB : β → List UInt8) (f : γ → β) (v₁ v₂ : γ → C)
    (henc : ∀ g, encA g = inBytes sh bi (v₁ g) (v₂ g)) (hw1 : ∀ g, (v₁ g).wf sh)
    (hw2 : bi = .inp → ∀ g, (v₂ g).wf sh)
    (hout : ∀ g, encB (f g) = Kd.out sh nb rk (pg.sem (v₁ g) a0 (bi.val (v₂ g))))
    (hsh : sh.length < 255) (hn : pg.arms.length ≤ 255) (htg : ∀ e ∈ pg.arms, e.tags < 256) (hlin : pg.lin)
    (hbi : ∀ t, bi = .ctor t → t < 256) (hnb : nb ≤ 8) (hM : pg.M < 2 ^ 20)
    (hwf : WfProg1W (indProg sh pg bi a0 nb) (if rk = .t then 1 else 7) 0) :
    Implements1With encA encB (callsCode1W (indProg sh pg bi a0 nb) (if rk = .t then 1 else 7) 0) f
      (space pg.M) (2 ^ 20) (decide (rk = .t)) := by
  have := implements1_of_cexecW encA encB f (indProg sh pg bi a0 nb) (if rk = .t then 1 else 7) 0 hwf
    (by split <;> omega) (fun n => 56 + 136 * (1 + n + wn pg.M n)) (wn pg.M) (2 ^ 20) (decide (rk = .t))
    (fun g out W₀ env h1 hmax h32 hol hout32 hW => by
      rw [henc] at hmax h32 hW ⊢
      rw [hout] at hol ⊢
      obtain ⟨σ', hx, hh, hr⟩ := ind_ok sh pg bi a0 nb hsh hn htg hlin hbi hnb (v₁ g) (v₂ g) (hw1 g)
        (fun h => hw2 h g) out W₀ env (if rk = .t then 1 else 7) (by split <;> omega) (by omega) (by
          rw [hW]; unfold wn
          have : (pg.M + 1) * (inBytes sh bi (v₁ g) (v₂ g)).length ≤ 2 ^ 20 * 2 ^ 20 :=
            Nat.mul_le_mul (by omega) (by omega)
          rw [Nat.mul_assoc]; omega)
        (by rw [hW]; unfold wn; omega) (by omega) hol
      refine ⟨σ', _, by rw [hW] at hx; exact hx, hh, wr_take _ _ hol, wr_drop _ _ hol, fun ht => ?_⟩
      have ht' : rk = .t := by simpa using ht
      have := hr ht'
      simp only [ht', if_true] at this
      exact this)
  simpa [space] using this

/-! ## results and `Bool`s as words -/

theorem leN_mod : ∀ (k n : Nat), leN k (n % 256 ^ k) = leN k n
  | 0, _ => rfl
  | k + 1, n => by
    simp only [leN]
    rw [Nat.pow_succ, show 256 ^ k * 256 = 256 * 256 ^ k from Nat.mul_comm _ _,
      Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 256 _), Nat.mod_mul_right_div_self, leN_mod k]

/-- a `Nat` result: 8 bytes, little-endian, mod `2^64` -/
theorem outNat (n : Nat) : leN 8 n = (leN 8 (BitVec.ofNat 64 n).toNat).take 8 := by
  rw [List.take_of_length_le (by simp [leN_length]), BitVec.toNat_ofNat, show 2 ^ 64 = 256 ^ 8 from rfl, leN_mod]

def bw (b : Bool) : BitVec 64 := if b = true then 1 else 0

/-- a `Bool` result: one byte -/
theorem outBool (b : Bool) : [if b then (1 : UInt8) else 0] = (leN 8 (bw b).toNat).take 1 := by
  cases b <;> rfl

@[simp] theorem bw_or (a b : Bool) : Op.eval .or (bw a) (bw b) = bw (a || b) := by cases a <;> cases b <;> rfl
@[simp] theorem bw_and (a b : Bool) : Op.eval .and (bw a) (bw b) = bw (a && b) := by cases a <;> cases b <;> rfl
@[simp] theorem bw_not (a : Bool) : Op.eval .xor (bw a) 1 = bw (!a) := by cases a <;> rfl
@[simp] theorem bw_true : bw true = 1 := rfl
@[simp] theorem bw_false : bw false = 0 := rfl
@[simp] theorem nat_add (a b : Nat) : Op.eval .add (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a + b) := by
  simp [Op.eval, BitVec.ofNat_add]

/-! ## comparisons (`frontx_ind` with `ite`): `Nat`s below `2^64`, `UInt64`, `Bool` -/

theorem nat_ult {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Op.eval .ult (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = bw (decide (x < y)) := by
  simp only [Op.eval, bw, BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  by_cases h : x < y <;> simp [h]
theorem nat_eq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Op.eval .eq (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = bw (decide (x = y)) := by
  have e : BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x = y := by
    constructor
    · intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this; exact this
    · intro h; rw [h]
  simp only [Op.eval, bw]
  by_cases h : x = y <;> simp [h, e]
theorem u64_ult (x y : UInt64) : Op.eval .ult x.toBitVec y.toBitVec = bw (decide (x < y)) := by
  have e : (x.toBitVec < y.toBitVec) ↔ x < y := Iff.rfl
  simp only [Op.eval, bw]; by_cases h : x < y <;> simp [e, h]
theorem u64_eq (x y : UInt64) : Op.eval .eq x.toBitVec y.toBitVec = bw (decide (x = y)) := by
  simp only [Op.eval, bw]; by_cases h : x = y <;> simp [h, UInt64.toBitVec_inj]
theorem bool_eq (x y : Bool) : Op.eval .eq (bw x) (bw y) = bw (decide (x = y)) := by
  cases x <;> cases y <;> rfl
@[simp] theorem bw_eq0 (c : Bool) : (bw c = 0) = (c = false) := by cases c <;> decide
@[simp] theorem bw_eq0' (c : Bool) : (bw c = 0#64) = (c = false) := by cases c <;> decide

end Proven.Frontx.Ind
