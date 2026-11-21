/- T01 (M3): GenArm's `li d, v` (`a6`/`a7`/`a8`): `movz` / `movn` / first word (`movz` or `movn` with `lsl 16j`) + `movk`
chain over the 16-bit chunks.  Result `wr st d v` for every `v < 2^64`.  CONST = `n_li` into x5, then `n_push`.
Statement `n_li`; the word list is `liL` (GenArm's order), `LiWords A h t v n` says `A` has it at `h`. -/
import Nano.Run.NatT.Base
import Nano.Run.NatT.LiDef

namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop} {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St} {q : Nat}

/-! ## the value: bits -/

theorem shl_lt {c j : Nat} (hc : c < 2 ^ 16) (hj : j < 4) : c <<< (16 * j) < 2 ^ 64 := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp [Nat.shiftLeft_eq] <;> omega

/-- `c <<< 16j` as a machine word -/
theorem shl_toNat {c j : Nat} (hc : c < 2 ^ 16) (hj : j < 4) :
    ((UInt64.ofNat c) <<< (16 * j).toUInt64).toNat = c <<< (16 * j) := by
  rw [UInt64.toNat_shiftLeft]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp [Nat.shiftLeft_eq] <;> omega

theorem movnV_toNat {c j : Nat} (hc : c < 2 ^ 16) (hj : j < 4) : (movnV c j).toNat = 2 ^ 64 - 1 - (c <<< (16 * j)) := by
  have h := shl_toNat hc hj
  unfold movnV
  rw [UInt64.toNat_not, h]

theorem testBit_shl {c j i : Nat} : (c <<< (16 * j)).testBit i = (decide (16 * j ≤ i) && c.testBit (i - 16 * j)) := by
  rw [Nat.testBit_shiftLeft]

theorem ge16 {c b : Nat} (hc : c < 2 ^ 16) (hb : 16 ≤ b) : c.testBit b = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by omega) hb))

theorem tb65535 (b : Nat) : Nat.testBit 65535 b = decide (b < 16) := by
  rw [show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.testBit_two_pow_sub_one]

theorem comp_bit {c b : Nat} (hc : c < 2 ^ 16) (hb : b < 16) : (65535 - c).testBit b = !(c.testBit b) := by
  rw [show 65535 - c = 2 ^ 16 - (c + 1) by omega, Nat.testBit_two_pow_sub_succ hc]
  simp [hb]

theorem movn_bit {c j i : Nat} (hc : c < 2 ^ 16) (hj : j < 4) (hi : i < 64) :
    (movnV c j).toNat.testBit i = !(decide (16 * j ≤ i) && c.testBit (i - 16 * j)) := by
  rw [movnV_toNat hc hj, show 2 ^ 64 - 1 - c <<< (16 * j) = 2 ^ 64 - (c <<< (16 * j) + 1) by omega,
    Nat.testBit_two_pow_sub_succ (shl_lt hc hj), testBit_shl]
  simp [hi]

/-- `movk` rewrites exactly the bits of its chunk -/
theorem movk_bit (r : UInt64) {c j i : Nat} (hc : c < 2 ^ 16) (hj : j < 4) (hi : i < 64) :
    (movkV r c j).toNat.testBit i = if 16 * j ≤ i ∧ i < 16 * j + 16 then c.testBit (i - 16 * j) else r.toNat.testBit i := by
  have hs := shl_toNat hc hj
  have hm : (~~~((0xFFFF : UInt64) <<< (16 * j).toUInt64)).toNat = 2 ^ 64 - 1 - (65535 <<< (16 * j)) := by
    have := movnV_toNat (c := 65535) (j := j) (by omega) hj
    unfold movnV at this
    exact this
  have hlt : 65535 <<< (16 * j) < 2 ^ 64 := shl_lt (by omega) hj
  unfold movkV
  rw [UInt64.toNat_or, UInt64.toNat_and, hm, hs, Nat.testBit_or, Nat.testBit_and,
    show 2 ^ 64 - 1 - 65535 <<< (16 * j) = 2 ^ 64 - (65535 <<< (16 * j) + 1) by omega,
    Nat.testBit_two_pow_sub_succ hlt, testBit_shl, testBit_shl, tb65535]
  by_cases h : 16 * j ≤ i ∧ i < 16 * j + 16
  · simp [h, hi, show i - 16 * j < 16 by omega]
  · by_cases h1 : 16 * j ≤ i
    · simp [h, h1, hi, show ¬ i - 16 * j < 16 by omega, ge16 hc (show 16 ≤ i - 16 * j by omega)]
      intro _; omega
    · simp [h, h1, hi]

/-- `movz #c, lsl 16j` : the bits -/
theorem movzH_bit {c j i : Nat} (hc : c < 2 ^ 16) (hj : j < 4) :
    ((UInt64.ofNat c) <<< (16 * j).toUInt64).toNat.testBit i = (decide (16 * j ≤ i) && c.testBit (i - 16 * j)) := by
  rw [shl_toNat hc hj]; exact testBit_shl

/-! ## the chunk walk (GenArm `a7`) and the whole `li` -/

theorem chk_bit {V j b : Nat} (hb : b < 16) : (chk V j).testBit b = V.testBit (16 * j + b) := by
  unfold chk
  rw [show (65536 : Nat) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hb, Nat.add_comm]

theorem chk_lt (V j : Nat) : chk V j < 2 ^ 16 := Nat.mod_lt _ (by decide)

/-- words `h ..` of `A` are GenArm's `li` of `v` into the raw register `t`, `n` words -/
def LiWords (A : List Nat) (h t : Nat) (v : UInt64) (n : Nat) : Prop :=
  n = (liL t v.toNat).length ∧ ∀ i < n, A[h + i]? = (liL t v.toNat)[i]?

/-! ### invariants: bits below `16j` are `V`'s, bits above are the fill -/

/-- fill bit of `e` -/
def fb (e : Nat) : Bool := decide (e ≠ 0)

def Inv (V : Nat) (e : Nat) (r : UInt64) (j : Nat) : Prop :=
  ∀ i < 64, r.toNat.testBit i = if i < 16 * j then V.testBit i else fb e

/-- bits of `V` below `16j` are the fill -/
def Sk (V e j : Nat) : Prop := ∀ i < 16 * j, V.testBit i = fb e

theorem chunk_fill {V e j : Nat} (he : e = 0 ∨ e = 65535) (hc : chk V j = e) {i : Nat} (h1 : 16 * j ≤ i) (h2 : i < 16 * j + 16) :
    V.testBit i = fb e := by
  have := chk_bit (V := V) (j := j) (b := i - 16 * j) (by omega)
  rw [show 16 * j + (i - 16 * j) = i by omega, hc] at this
  rw [← this]
  rcases he with rfl | rfl
  · simp [fb]
  · simp [fb, tb65535]; omega

theorem inv_skip {V e j : Nat} {r : UInt64} (he : e = 0 ∨ e = 65535) (hc : chk V j = e) (hj : j < 4) (hI : Inv V e r j) :
    Inv V e r (j + 1) := by
  intro i hi
  rw [hI i hi]
  by_cases h1 : i < 16 * j
  · simp [h1, show i < 16 * (j + 1) by omega]
  · by_cases h2 : i < 16 * (j + 1)
    · simp [h1, h2]; exact (chunk_fill he hc (by omega) (by omega)).symm
    · simp [h1, h2]

theorem inv_movk {V e j : Nat} {r : UInt64} (hc : chk V j ≠ e) (hj : j < 4) (hI : Inv V e r j) :
    Inv V e (movkV r (chk V j) j) (j + 1) := by
  intro i hi
  rw [movk_bit r (chk_lt V j) hj hi]
  by_cases h1 : 16 * j ≤ i ∧ i < 16 * j + 16
  · rw [if_pos h1, if_pos (by omega)]
    have := chk_bit (V := V) (j := j) (b := i - 16 * j) (by omega)
    rw [show 16 * j + (i - 16 * j) = i by omega] at this
    exact this
  · rw [if_neg h1, hI i hi]
    by_cases h3 : i < 16 * j
    · simp [h3, show i < 16 * (j + 1) by omega]
    · simp [h3, show ¬ i < 16 * (j + 1) by omega]

theorem inv_eq {V r : UInt64} {e : Nat} (hI : Inv V.toNat e r 4) : r = V := by
  apply UInt64.toNat_inj.1
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · have := hI i hi; rw [if_pos (by omega)] at this; exact this
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le r.toNat_lt (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le V.toNat_lt (Nat.pow_le_pow_right (by omega) (by omega)))]

/-! ### runs -/

theorem wr_x_d (st0 : CallProbe.St) {d : Nat} (h0 : d ≠ 0) (r : UInt64) : (CallProbe.wr st0 d r).x d = r := wr_same st0 h0 r

/-- the `movk` chain -/
theorem chain_run (S : A64SemN M X W) (hB : K.base + 4 * A.length ≤ 2 ^ 32) {d : Nat} (hd : mapped d = true) (h0 : d ≠ 0)
    (V e : Nat) (he : e = 0 ∨ e = 65535) (st0 : CallProbe.St) :
    ∀ n j h (r : UInt64) (s : M.State), j + n = 4 → NMid X W K A s0 (CallProbe.wr st0 d r) h s →
      (∀ i < (chain (armReg d) V e n j).length, A[h + i]? = (chain (armReg d) V e n j)[i]?) → Inv V e r j →
      ∃ s' r', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st0 d r') (h + (chain (armReg d) V e n j).length) s' ∧
        Inv V e r' 4 := by
  intro n
  induction n with
  | zero =>
    intro j h r s hj hM _ hI
    have : j = 4 := by omega
    subst this
    exact ⟨s, r, Runs.stop, by simpa [chain] using hM, hI⟩
  | succ n ih =>
    intro j h r s hj hM hA hI
    by_cases hc : chk V j = e
    · have hch : chain (armReg d) V e (n + 1) j = chain (armReg d) V e n (j + 1) := by simp [chain, hc]
      rw [hch] at hA ⊢
      exact ih (j + 1) h r s (by omega) hM hA (inv_skip he hc (by omega) hI)
    · have hch : chain (armReg d) V e (n + 1) j =
          ArmEnc.movk (armReg d) (chk V j) j :: chain (armReg d) V e n (j + 1) := by simp [chain, hc]
      rw [hch] at hA ⊢
      have a0 : A[h]? = some (ArmEnc.movk (armReg d) (chk V j) j) := by simpa using hA 0 (by simp)
      obtain ⟨s1, r1, N1⟩ := n_movk S hM hB a0 hd h0 (chk_lt V j) (by omega)
      rw [wr_x_d st0 h0, wr_wr] at N1
      obtain ⟨s', r', R, N, I⟩ := ih (j + 1) (h + 1) _ s1 (by omega) N1
        (fun i hi => by
          have := hA (i + 1) (by simp; omega)
          rw [show h + (i + 1) = h + 1 + i by omega] at this
          simpa using this) (inv_movk hc (by omega) hI)
      refine ⟨s', r', Runs.trans r1 R, ?_, I⟩
      rw [show h + (ArmEnc.movk (armReg d) (chk V j) j :: chain (armReg d) V e n (j + 1)).length
        = h + 1 + (chain (armReg d) V e n (j + 1)).length by simp; omega]
      exact N

/-- the first word, skipping equal chunks; some chunk differs from `e` -/
theorem walk_run (S : A64SemN M X W) (hB : K.base + 4 * A.length ≤ 2 ^ 32) {d : Nat}
    (hd : mapped d = true) (h0 : d ≠ 0) (V e : Nat) (hV : V < 2 ^ 64) (he : e = 0 ∨ e = 65535) (st0 : CallProbe.St) :
    ∀ n j h (r : UInt64) (s : M.State), j + n = 4 → NMid X W K A s0 (CallProbe.wr st0 d r) h s →
      (∀ i < (walk0 (armReg d) V e n j).length, A[h + i]? = (walk0 (armReg d) V e n j)[i]?) → Sk V e j →
      (∃ k, j ≤ k ∧ k < 4 ∧ chk V k ≠ e) →
      ∃ s' r', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st0 d r') (h + (walk0 (armReg d) V e n j).length) s' ∧
        Inv V e r' 4 := by
  intro n
  induction n with
  | zero => intro j h r s hj _ _ _ hk; obtain ⟨k, h1, h2, _⟩ := hk; omega
  | succ n ih =>
    intro j h r s hj hM hA hSk hk
    by_cases hc : chk V j = e
    · have hch : walk0 (armReg d) V e (n + 1) j = walk0 (armReg d) V e n (j + 1) := by simp [walk0, hc]
      rw [hch] at hA ⊢
      refine ih (j + 1) h r s (by omega) hM hA (fun i hi => ?_) ?_
      · by_cases h1 : i < 16 * j
        · exact hSk i h1
        · exact chunk_fill he hc (by omega) (by omega)
      · obtain ⟨k, h1, h2, h3⟩ := hk
        exact ⟨k, by rcases Nat.lt_or_ge j k with h | h; omega; (have : k = j := by omega); subst this; exact absurd hc h3, h2, h3⟩
    · have hch : walk0 (armReg d) V e (n + 1) j = (if e = 0 then ArmEnc.movzH (armReg d) (chk V j) j
          else ArmEnc.movn (armReg d) (65535 - chk V j) j) :: chain (armReg d) V e n (j + 1) := by simp [walk0, hc]
      rw [hch] at hA ⊢
      have hj4 : j < 4 := by omega
      have hA' : ∀ i < (chain (armReg d) V e n (j + 1)).length, A[h + 1 + i]? = (chain (armReg d) V e n (j + 1))[i]? :=
        fun i hi => by
          have := hA (i + 1) (by simp; omega)
          rw [show h + (i + 1) = h + 1 + i by omega] at this
          simpa using this
      have a0 := hA 0 (by simp)
      simp only [Nat.add_zero, List.getElem?_cons_zero] at a0
      -- the first word, then the chain
      have key : ∃ s1 r1, Runs M s s1 ∧ NMid X W K A s0 (CallProbe.wr st0 d r1) (h + 1) s1 ∧ Inv V e r1 (j + 1) := by
        by_cases he0 : e = 0
        · subst he0
          rw [if_pos rfl] at a0
          obtain ⟨s1, r1, N1⟩ := n_movzH S hM hB a0 hd h0 (chk_lt V j) hj4
          rw [wr_wr] at N1
          refine ⟨s1, _, r1, N1, ?_⟩
          intro i hi
          rw [movzH_bit (chk_lt V j) hj4]
          by_cases h1 : i < 16 * j
          · simp [h1, show i < 16 * (j + 1) by omega, show ¬ 16 * j ≤ i by omega]; simpa [fb] using hSk i h1
          · by_cases h2 : i < 16 * (j + 1)
            · simp [h1, h2, show 16 * j ≤ i by omega]
              have := chk_bit (V := V) (j := j) (b := i - 16 * j) (by omega)
              rw [show 16 * j + (i - 16 * j) = i by omega] at this
              exact this
            · simp [h1, h2, fb, show 16 * j ≤ i by omega]
              exact ge16 (chk_lt V j) (by omega)
        · rw [if_neg he0] at a0
          have he65 : e = 65535 := by omega
          subst he65
          obtain ⟨s1, r1, N1⟩ := n_movn S hM hB a0 hd h0 (by omega) hj4
          rw [wr_wr] at N1
          refine ⟨s1, _, r1, N1, ?_⟩
          intro i hi
          rw [movn_bit (by omega) hj4 hi]
          by_cases h1 : i < 16 * j
          · simp [h1, show i < 16 * (j + 1) by omega, show ¬ 16 * j ≤ i by omega, hSk i h1, fb]
          · by_cases h2 : i < 16 * (j + 1)
            · simp [h1, h2, show 16 * j ≤ i by omega]
              rw [comp_bit (chk_lt V j) (by omega)]
              have := chk_bit (V := V) (j := j) (b := i - 16 * j) (by omega)
              rw [show 16 * j + (i - 16 * j) = i by omega] at this
              simp [this]
            · simp [h1, h2, fb, show 16 * j ≤ i by omega]
              exact ge16 (by omega) (by omega)
      obtain ⟨s1, r1, R1, N1, I1⟩ := key
      obtain ⟨s', r', R, N, I⟩ := chain_run S hB hd h0 V e he st0 n (j + 1) (h + 1) r1 s1 (by omega) N1 hA' I1
      refine ⟨s', r', Runs.trans R1 R, ?_, I⟩
      rw [show h + ((if e = 0 then ArmEnc.movzH (armReg d) (chk V j) j else ArmEnc.movn (armReg d) (65535 - chk V j) j) ::
        chain (armReg d) V e n (j + 1)).length = h + 1 + (chain (armReg d) V e n (j + 1)).length by simp; omega]
      exact N


theorem wr_self (st : CallProbe.St) (d : Nat) : CallProbe.wr st d (st.x d) = st := by
  unfold CallProbe.wr; split
  · rfl
  · cases st; simp only [CallProbe.upd]; congr; funext i; unfold CallProbe.upd; split <;> simp_all

/-- some chunk differs from the fill, for the two fills `li` uses -/
theorem exists_ne {V : Nat} (hV : V < 2 ^ 64) {e : Nat} (he : e = 0 ∨ e = 65535) (h1 : 65536 ≤ V)
    (h2 : 65536 ≤ 2 ^ 64 - 1 - V) : ∃ k, 0 ≤ k ∧ k < 4 ∧ chk V k ≠ e := by
  apply Classical.byContradiction
  intro hn
  have a0 : chk V 0 = e := Classical.byContradiction fun h => hn ⟨0, by omega, by omega, h⟩
  have a1 : chk V 1 = e := Classical.byContradiction fun h => hn ⟨1, by omega, by omega, h⟩
  have a2 : chk V 2 = e := Classical.byContradiction fun h => hn ⟨2, by omega, by omega, h⟩
  have a3 : chk V 3 = e := Classical.byContradiction fun h => hn ⟨3, by omega, by omega, h⟩
  simp only [chk, Nat.reduceMul, Nat.reducePow] at a0 a1 a2 a3
  rcases he with rfl | rfl <;> omega

theorem walk_all (S : A64SemN M X W) (hB : K.base + 4 * A.length ≤ 2 ^ 32) {d h : Nat}
    (hd : mapped d = true) (h0 : d ≠ 0) (v : UInt64) {e : Nat} (he : e = 0 ∨ e = 65535) (h1 : 65536 ≤ v.toNat)
    (h2 : 65536 ≤ 2 ^ 64 - 1 - v.toNat) (hM : NMid X W K A s0 st h s)
    (hA : ∀ i < (walk0 (armReg d) v.toNat e 4 0).length, A[h + i]? = (walk0 (armReg d) v.toNat e 4 0)[i]?) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d v) (h + (walk0 (armReg d) v.toNat e 4 0).length) s' := by
  have hV := v.toNat_lt
  obtain ⟨s', r', R, N, I⟩ := walk_run S hB hd h0 v.toNat e hV he st 4 0 h (st.x d) s (by omega)
    (by rw [wr_self]; exact hM) hA (fun i hi => by omega) (exists_ne hV he h1 h2)
  have hr : r' = v := inv_eq I
  rw [hr] at N
  exact ⟨s', R, N⟩

/-- **`li t, v`** (`a6`): the register gets `v` -/
theorem n_li (S : A64SemN M X W) {h d n : Nat} {v : UInt64} (hM : NMid X W K A s0 st h s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hW : LiWords A h (armReg d) v n) (hd : mapped d = true) (hd0 : d ≠ 0) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d v) (h + n) s' := by
  obtain ⟨hn, hA⟩ := hW
  have hV := v.toNat_lt
  subst hn
  by_cases c1 : v.toNat < 65536
  · have e : liL (armReg d) v.toNat = [ArmEnc.movz (armReg d) v.toNat] := by simp [liL, c1]
    rw [e] at hA ⊢
    obtain ⟨s', R, N⟩ := n_movz S hM hB (by simpa using hA 0 (by simp)) hd hd0 (by omega)
    rw [UInt64.ofNat_toNat] at N
    exact ⟨s', R, by simpa using N⟩
  by_cases c2 : 2 ^ 64 - 1 - v.toNat < 65536
  · have e : liL (armReg d) v.toNat = [ArmEnc.movn (armReg d) (2 ^ 64 - 1 - v.toNat) 0] := by simp [liL, c1, c2]
    rw [e] at hA ⊢
    obtain ⟨s', R, N⟩ := n_movn S hM hB (by simpa using hA 0 (by simp)) hd hd0 c2 (by omega)
    have : movnV (2 ^ 64 - 1 - v.toNat) 0 = v := by
      apply UInt64.toNat_inj.1
      rw [movnV_toNat c2 (by omega)]; simp; omega
    rw [this] at N
    exact ⟨s', R, by simpa using N⟩
  · have hl : liL (armReg d) v.toNat =
        if cnt v.toNat 0 < cnt v.toNat 65535 then walk0 (armReg d) v.toNat 65535 4 0 else walk0 (armReg d) v.toNat 0 4 0 := by
      simp [liL, c1, c2]
    by_cases c3 : cnt v.toNat 0 < cnt v.toNat 65535
    · rw [hl, if_pos c3] at hA ⊢
      exact walk_all S hB hd hd0 v (Or.inr rfl) (by omega) (by omega) hM hA
    · rw [hl, if_neg c3] at hA ⊢
      exact walk_all S hB hd hd0 v (Or.inl rfl) (by omega) (by omega) hM hA

/-- `n_li` with the constant as a natural number and the words given directly -/
theorem n_liN (S : A64SemN M X W) {h d v : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hv : v < 2 ^ 64) (hd : mapped d = true) (hd0 : d ≠ 0)
    (hA : ∀ i, i < (liL (armReg d) v).length → A[h + i]? = (liL (armReg d) v)[i]?) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (UInt64.ofNat v)) (h + (liL (armReg d) v).length) s' := by
  have e : (UInt64.ofNat v).toNat = v := by
    first | exact UInt64.toNat_ofNat_of_lt' hv | (rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hv)
  exact n_li S hM hB ⟨by rw [e], by rw [e]; exact hA⟩ hd hd0

/-! ### length -/

theorem chain_len (t V e : Nat) : ∀ n j, (chain t V e n j).length ≤ n := by
  intro n
  induction n with
  | zero => intro j; simp [chain]
  | succ n ih =>
    intro j
    have := ih (j + 1)
    simp only [chain]
    split <;> simp <;> omega

theorem walk_len (t V e : Nat) : ∀ n j, (walk0 t V e n j).length ≤ n ∧
    ((∃ k, j ≤ k ∧ k < j + n ∧ chk V k ≠ e) → 1 ≤ (walk0 t V e n j).length) := by
  intro n
  induction n with
  | zero => intro j; refine ⟨by simp [walk0], fun ⟨k, h1, h2, _⟩ => by omega⟩
  | succ n ih =>
    intro j
    have h1 := ih (j + 1)
    have h2 := chain_len t V e n (j + 1)
    simp only [walk0]
    by_cases hc : chk V j = e
    · rw [if_pos hc]
      refine ⟨by omega, fun ⟨k, a, b, c⟩ => h1.2 ⟨k, ?_, by omega, c⟩⟩
      rcases Nat.lt_or_ge j k with h | h
      · omega
      · have : k = j := by omega
        subst this; exact absurd hc c
    · rw [if_neg hc]
      exact ⟨by simp; omega, fun _ => by simp⟩

/-- `li` is 1 to 4 words -/
theorem liL_length (t : Nat) {v : Nat} (hv : v < 2 ^ 64) : 1 ≤ (liL t v).length ∧ (liL t v).length ≤ 4 := by
  unfold liL
  by_cases c1 : v < 65536
  · simp [c1]
  by_cases c2 : 2 ^ 64 - 1 - v < 65536
  · simp [c1, c2]
  rw [if_neg c1, if_neg c2]
  split
  · have := walk_len t v 65535 4 0
    obtain ⟨k, a, b, c⟩ := exists_ne hv (Or.inr rfl) (by omega) (by omega)
    exact ⟨this.2 ⟨k, a, by omega, c⟩, this.1⟩
  · have := walk_len t v 0 4 0
    obtain ⟨k, a, b, c⟩ := exists_ne hv (Or.inl rfl) (by omega) (by omega)
    exact ⟨this.2 ⟨k, a, by omega, c⟩, this.1⟩

end JT
