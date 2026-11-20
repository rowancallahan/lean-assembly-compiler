/- User inductive types with payload (cells in the work block, `Compiler/Ind.lean`) in `Implements1` form, and
the command `frontx_ind` that compiles a structural recursive Lean function over a user inductive.

`implements1_ind` (once): `indProg` + `ind_ok` (source level) + `implements1_of_cexecW` (word block at the bottom of
the work block, stack above) give `Implements1With encA encB (callsCode1W …) f space` for any `f` whose meaning is
the program's (`hout`), with `space n = 8 wn n + need n + 24`, `wn n = 8 + 4 (M + 1) n` words of cells. -/
import Compiler.IndSup
import Riscv.Back.CallsImpl1W

set_option linter.unusedVariables false

namespace Proven.Frontx.Ind
open Proven Proven.Mach Proven.Mach.Ind Proven.Mach.Riscv

/-- cells of the word block for `n` input bytes -/
def wn (M n : Nat) : Nat := 8 + 4 * (M + 1) * n

/-- the work space: cells, then the stack -/
def space (M n : Nat) : Nat := 8 * wn M n + (56 + 136 * (1 + n + wn M n)) + 24

/-- words of the word block for `n` input bytes when the program allocates at most `A n` cells -/
def wnA (A : Nat → Nat) (n : Nat) : Nat := 8 + 4 * n + 4 * A n

/-- the work space of a program of `m` functions with `nl` locals each, allocating at most `A n` cells for `n`
input bytes: the word block, then the stack (`8 (nl + 1)` bytes per activation, at most `n + m (1 + words)` deep) -/
def spaceA (m nl : Nat) (A : Nat → Nat) (n : Nat) : Nat :=
  8 * wnA A n + (56 + 8 * (nl + 1) * (n + m * (1 + wnA A n))) + 24

theorem wr_take (O : List (BitVec 8)) (L : List UInt8) (h : L.length ≤ O.length) :
    (wr O 0 L).take L.length = L.map (·.toBitVec) := by simp [wr]
theorem wr_drop (O : List (BitVec 8)) (L : List UInt8) (h : L.length ≤ O.length) :
    (wr O 0 L).drop L.length = O.drop L.length := by simp [wr]

/-- **User inductives, several functions ⇒ `Implements1`**, for any bound `A` on the cells allocated -/
theorem implements1_indM {rk : Kd} {γ β : Type} (sh shO : Shape) (pg : Pg rk) (hs : List (Σ k : Kd, Pg k))
    (bi : BIn) (ain : Bool) (a0 : BitVec 64) (nb nl : Nat)
    (encA : γ → List UInt8) (encB : β → List UInt8) (f : γ → β) (v₁ v₂ : γ → C) (av : γ → BitVec 64) (A : Nat → Nat)
    (henc : ∀ g, encA g = inBytesA sh bi ain (v₁ g) (v₂ g) (av g)) (hw1 : ∀ g, (v₁ g).wf sh)
    (hw2 : bi = .inp → ∀ g, (v₂ g).wf sh)
    (hout : ∀ g, encB (f g) = Kd.out shO nb rk (pg.sem (v₁ g) (if ain then av g else a0) (bi.val (v₂ g))))
    (hA : ∀ g, (encA g).length < 2 ^ 32 → pg.al (v₁ g) (if ain then av g else a0) (bi.val (v₂ g)) ≤ A (encA g).length)
    (hsh : sh.length < 255) (hshO : shO.length < 255) (hnl : 16 ≤ nl) (hch : Chain (⟨rk, pg⟩ :: hs))
    (hok : okL (⟨rk, pg⟩ :: hs) = true) (hbi : ∀ t, bi = .ctor t → t < 256) (hnb : nb ≤ 8)
    (hwf : WfProg1W (indProgM sh shO pg hs bi ain a0 nb nl) (if rk = .t then 1 else 7) 0) :
    Implements1With encA encB (callsCode1W (indProgM sh shO pg hs bi ain a0 nb nl) (if rk = .t then 1 else 7) 0) f
      (spaceA (1 + hs.length) nl A) (2 ^ 20) (decide (rk = .t)) := by
  have := implements1_of_cexecW encA encB f (indProgM sh shO pg hs bi ain a0 nb nl) (if rk = .t then 1 else 7) 0 hwf
    (by split <;> omega) (fun n => 56 + 8 * (nl + 1) * (n + (1 + hs.length) * (1 + wnA A n))) (wnA A) (2 ^ 20)
    (decide (rk = .t))
    (fun g out W₀ env h1 hmax h32 hol hout32 hW hW32 => by
      have hA' := hA g h32
      rw [henc] at hmax h32 hW hW32 hA' ⊢
      rw [hout] at hol ⊢
      obtain ⟨σ', hx, hh, hr⟩ := ind_okM sh shO pg hs bi ain a0 nb nl hsh hshO hnl hch hok hbi hnb (v₁ g) (v₂ g) (av g)
        (hw1 g) (fun h => hw2 h g) out W₀ env (if rk = .t then 1 else 7) (by split <;> omega) (by omega)
        (by rw [hW]; unfold wnA at hW32 ⊢; omega)
        (by rw [hW]; unfold wnA; omega) (by omega) hol
      refine ⟨σ', _, by rw [hW] at hx; exact hx, hh, wr_take _ _ hol, wr_drop _ _ hol, fun ht => ?_⟩
      have ht' : rk = .t := by simpa using ht
      have := hr ht'
      simp only [ht', if_true] at this
      exact this)
  simp [spaceA] at this ⊢; exact this

/-- **User inductives ⇒ `Implements1`** (one function: at most `M` cells per input node). -/
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
  have hIA : ∀ v₁ v₂ : C, inBytesA sh bi false v₁ v₂ 0 = inBytes sh bi v₁ v₂ := fun _ _ => by simp [inBytesA]
  have := implements1_indM sh sh pg [] bi false a0 nb 16 encA encB f v₁ v₂ (fun _ => 0) (fun n => pg.M * n)
    (fun g => by rw [hIA]; exact henc g) hw1 hw2 (fun g => by simpa using hout g)
    (fun g _ => by
      have h1 := al_le pg hlin (v₁ g) a0 (bi.val (v₂ g))
      have h2 := nodes_le sh (v₁ g) (hw1 g)
      have h3 : (v₁ g).nodes ≤ (encA g).length := by rw [henc]; cases bi <;> simp [inBytes] <;> omega
      simp only [Bool.false_eq_true, if_false]
      exact Nat.le_trans h1 (Nat.mul_le_mul_left _ h3))
    hsh hsh (by omega) ⟨fun j hj => absurd hj (by simp), trivial⟩
    (by simp only [okL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        exact ⟨⟨hn, fun e he => ⟨htg e he, by simpa using (hlin e he).2.2.2⟩⟩, trivial⟩) hbi hnb hwf
  have hsp : spaceA (1 + ([] : List (Σ k : Kd, Pg k)).length) 16 (fun n => pg.M * n) = space pg.M := by
    funext n
    simp only [spaceA, space, wnA, wn, List.length_nil, Nat.add_zero, Nat.one_mul]
    rw [show 4 * (pg.M + 1) * n = 4 * n + 4 * (pg.M * n) by rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_add]; omega]
    omega
  rw [hsp] at this
  exact this

/-- **User inductives, several functions ⇒ `Implements1`**, the space from the worst-case cell count over all
inputs of each length (`cellsSup`, `Compiler/IndSup.lean`) -/
theorem implements1_indS {rk : Kd} {γ β : Type} (sh shO : Shape) (pg : Pg rk) (hs : List (Σ k : Kd, Pg k))
    (bi : BIn) (ain : Bool) (a0 : BitVec 64) (nb nl : Nat)
    (encA : γ → List UInt8) (encB : β → List UInt8) (f : γ → β) (v₁ v₂ : γ → C) (av : γ → BitVec 64)
    (henc : ∀ g, encA g = inBytesA sh bi ain (v₁ g) (v₂ g) (av g)) (hw1 : ∀ g, (v₁ g).wf sh)
    (hw2 : bi = .inp → ∀ g, (v₂ g).wf sh)
    (hout : ∀ g, encB (f g) = Kd.out shO nb rk (pg.sem (v₁ g) (if ain then av g else a0) (bi.val (v₂ g))))
    (hsh : sh.length < 255) (hshO : shO.length < 255) (hnl : 16 ≤ nl) (hch : Chain (⟨rk, pg⟩ :: hs))
    (hok : okL (⟨rk, pg⟩ :: hs) = true) (hbi : ∀ t, bi = .ctor t → t < 256) (hnb : nb ≤ 8)
    (hwf : WfProg1W (indProgM sh shO pg hs bi ain a0 nb nl) (if rk = .t then 1 else 7) 0) :
    Implements1With encA encB (callsCode1W (indProgM sh shO pg hs bi ain a0 nb nl) (if rk = .t then 1 else 7) 0) f
      (spaceA (1 + hs.length) nl (cellsSup sh pg bi ain a0)) (2 ^ 20) (decide (rk = .t)) :=
  implements1_indM sh shO pg hs bi ain a0 nb nl encA encB f v₁ v₂ av _ henc hw1 hw2 hout
    (fun g hg => by
      rw [henc] at hg ⊢
      exact al_le_cellsSup sh hsh pg bi ain a0 (v₁ g) (v₂ g) (av g) (hw1 g) (fun h => hw2 h g) (by omega))
    hsh hshO hnl hch hok hbi hnb hwf

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
theorem u64_ops (x y : UInt64) : Op.eval .add x.toBitVec y.toBitVec = (x + y).toBitVec ∧
    Op.eval .sub x.toBitVec y.toBitVec = (x - y).toBitVec ∧ Op.eval .and x.toBitVec y.toBitVec = (x &&& y).toBitVec ∧
    Op.eval .or x.toBitVec y.toBitVec = (x ||| y).toBitVec ∧ Op.eval .xor x.toBitVec y.toBitVec = (x ^^^ y).toBitVec := by
  simp [Op.eval]
@[simp] theorem bw_eq0 (c : Bool) : (bw c = 0) = (c = false) := by cases c <;> decide
@[simp] theorem bw_eq0' (c : Bool) : (bw c = 0#64) = (c = false) := by cases c <;> decide

end Proven.Frontx.Ind

namespace Proven.Frontx.Ind
open Proven Proven.Mach Proven.Mach.Ind Proven.Mach.Riscv

/-- **User inductives ⇒ `Implements1`**, one function at most `M` cells per input node (`lin`), with the input
word and the output shape of `implements1_indM` -/
theorem implements1_indL {rk : Kd} {γ β : Type} (sh shO : Shape) (pg : Pg rk) (bi : BIn) (ain : Bool)
    (a0 : BitVec 64) (nb : Nat)
    (encA : γ → List UInt8) (encB : β → List UInt8) (f : γ → β) (v₁ v₂ : γ → C) (av : γ → BitVec 64)
    (henc : ∀ g, encA g = inBytesA sh bi ain (v₁ g) (v₂ g) (av g)) (hw1 : ∀ g, (v₁ g).wf sh)
    (hw2 : bi = .inp → ∀ g, (v₂ g).wf sh)
    (hout : ∀ g, encB (f g) = Kd.out shO nb rk (pg.sem (v₁ g) (if ain then av g else a0) (bi.val (v₂ g))))
    (hsh : sh.length < 255) (hshO : shO.length < 255) (hn : pg.arms.length ≤ 255)
    (htg : ∀ e ∈ pg.arms, e.tags < 256) (hlin : pg.lin) (hbi : ∀ t, bi = .ctor t → t < 256) (hnb : nb ≤ 8)
    (hwf : WfProg1W (indProgM sh shO pg [] bi ain a0 nb 16) (if rk = .t then 1 else 7) 0) :
    Implements1With encA encB (callsCode1W (indProgM sh shO pg [] bi ain a0 nb 16) (if rk = .t then 1 else 7) 0) f
      (spaceA 1 16 (fun n => pg.M * n)) (2 ^ 20) (decide (rk = .t)) :=
  implements1_indM sh shO pg [] bi ain a0 nb 16 encA encB f v₁ v₂ av (fun n => pg.M * n) henc hw1 hw2 hout
    (fun g _ => by
      have h1 := al_le pg hlin (v₁ g) (if ain then av g else a0) (bi.val (v₂ g))
      have h2 := nodes_le sh (v₁ g) (hw1 g)
      have h3 : (v₁ g).nodes ≤ (encA g).length := by
        rw [henc]; simp only [inBytesA, List.length_append]; cases bi <;> simp [inBytes] <;> omega
      exact Nat.le_trans h1 (Nat.mul_le_mul_left _ h3))
    hsh hshO (by omega) ⟨fun j hj => absurd hj (by simp), trivial⟩
    (by simp only [okL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        exact ⟨⟨hn, fun e he => ⟨htg e he, by simpa using (hlin e he).2.2.2⟩⟩, trivial⟩) hbi hnb hwf

/-- an 8-byte word argument of the input -/
theorem leN8_ofNat (n : Nat) : leN 8 (BitVec.ofNat 64 n).toNat = leN 8 n := by
  rw [BitVec.toNat_ofNat, show 2 ^ 64 = 256 ^ 8 from rfl, leN_mod]

end Proven.Frontx.Ind

namespace Proven.Frontx.Ind

theorem beq_dec {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (a b : α) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

end Proven.Frontx.Ind

namespace Proven.Frontx.Ind

theorem leN8_mod (n : Nat) : leN 8 (n % 18446744073709551616) = leN 8 n := by
  rw [show 18446744073709551616 = 256 ^ 8 from rfl, leN_mod]

end Proven.Frontx.Ind

namespace Proven.Frontx.Ind
open Proven Proven.Mach Proven.Mach.Ind

/-! ## `Nat` subtraction (truncated at `0`): `if a < b then 0 else a - b` on words below `2^64` -/

def natSub {rk : Kd} (a b : E rk .w) : E rk .w := .ite (.bin .ult a b) (.k 0) (.bin .sub a b)

def natSubW (u v : BitVec 64) : BitVec 64 := if u < v then 0 else u - v

theorem ev_natSub {rk : Kd} (self : Cn rk) (x : BitVec 64) (l r : C) (a : BitVec 64) (b : C) (e₁ e₂ : E rk .w) :
    ev self x l r a b (natSub e₁ e₂) = natSubW (ev self x l r a b e₁) (ev self x l r a b e₂) := by
  simp only [natSub, ev, natSubW, Op.eval]; split <;> simp_all

theorem natSubW_ofNat {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    natSubW (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = BitVec.ofNat 64 (x - y) := by
  simp only [natSubW, BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  split
  · rename_i h; rw [Nat.sub_eq_zero_of_le (by omega)]; rfl
  · rename_i h; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]; omega

end Proven.Frontx.Ind
