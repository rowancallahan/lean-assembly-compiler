/- T02 (M3): slot access `a9` (8-byte load / store at [x8 + off], three reachable forms) and the signed add `a5`
(add / sub immediate forms).  Testing/notes/NATIVE_ARM_TEMPLATES.md section 3. -/
import Nano.Run.NatT.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop} {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St}

/-! ## for ArmNat -/

/-- `sub x16, x8, #n` (scratch base of the far slot forms) -/
theorem n_subi16 (S : A64SemN M X W) {h n : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hA : A[h]? = some (ArmEnc.subi 16 (armReg 8) n)) (hn : n < 4096) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (h + 1) s' ∧ (M.observe s').register 16 = st.x 8 - UInt64.ofNat n := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.subi s 16 (armReg 8) n hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (by decide) (by decide) hn (nmid_word hM hA hB)
  rw [hM.x 8 (by omega) (by omega)] at this
  obtain ⟨s', r, N, o⟩ := nmid_scr hM (Or.inl rfl) this
  exact ⟨s', r, N, by rw [o]; simp [setReg]⟩

/-! ## slot access -/

/-- the words of `a9 … 0 t 8 off` (load into raw register `t`), `n` words from `h` -/
def SlotLd (A : List Nat) (h t : Nat) (off : Int) (n : Nat) : Prop :=
  (off % 8 = 0 ∧ 0 ≤ off ∧ off < 32768 ∧ n = 1 ∧ A[h]? = some (ArmEnc.ldr t (armReg 8) off.toNat)) ∨
  (-256 ≤ off ∧ off < 0 ∧ n = 1 ∧ A[h]? = some (ArmEnc.ldur t (armReg 8) off)) ∨
  (-4096 < off ∧ off < -256 ∧ n = 2 ∧ A[h]? = some (ArmEnc.subi 16 (armReg 8) (-off).toNat) ∧
    A[h + 1]? = some (ArmEnc.ldr t 16 0))

/-- the words of `a9 … 1 t 8 off` (store of raw register `t`) -/
def SlotSt (A : List Nat) (h t : Nat) (off : Int) (n : Nat) : Prop :=
  (off % 8 = 0 ∧ 0 ≤ off ∧ off < 32768 ∧ n = 1 ∧ A[h]? = some (ArmEnc.str t (armReg 8) off.toNat)) ∨
  (-256 ≤ off ∧ off < 0 ∧ n = 1 ∧ A[h]? = some (ArmEnc.stur t (armReg 8) off)) ∨
  (-4096 < off ∧ off < -256 ∧ n = 2 ∧ A[h]? = some (ArmEnc.subi 16 (armReg 8) (-off).toNat) ∧
    A[h + 1]? = some (ArmEnc.str t 16 0))

theorem n_slotLd (S : A64SemN M X W) {h d n a : Nat} {off : Int} (hM : NMid X W K A s0 st h s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hW : SlotLd A h (armReg d) off n) (hd : mapped d = true) (hd0 : d ≠ 0)
    (ha : (a : Int) = (st.x 8).toNat + off) (hw : wok K a) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (st.m a)) (h + n) s' := by
  have h8 := hM.x 8 (by omega) (by omega)
  rcases hW with ⟨h1, h2, h3, rfl, hA⟩ | ⟨h1, h2, rfl, hA⟩ | ⟨h1, h2, rfl, hA, hA1⟩
  · exact n_ldr S hM hB hA hd hd0 (by decide) h8 (by omega) (by omega) (by omega) hw
  · exact n_ldur S hM hB hA hd hd0 (by decide) h8 h1 (by omega) ha hw
  · obtain ⟨s1, r1, N1, o1⟩ := n_subi16 S hM hB hA (by omega)
    have e : (st.x 8 - UInt64.ofNat (-off).toNat).toNat = (st.x 8).toNat - (-off).toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_ofNat_lt (by omega)]; omega),
        toNat_ofNat_lt (by omega)]
    obtain ⟨s2, r2, N2⟩ := n_ldr S N1 hB hA1 hd hd0 (by decide) o1 (by decide) (by decide)
      (by rw [e]; omega) hw
    exact ⟨s2, Runs.trans r1 r2, N2⟩

theorem n_slotSt (S : A64SemN M X W) {h r n a : Nat} {off : Int} (hM : NMid X W K A s0 st h s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hW : SlotSt A h (armReg r) off n) (hr : mapped r = true) (hr0 : r ≠ 0)
    (ha : (a : Int) = (st.x 8).toNat + off) (hw : wok K a) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 { st with m := CallProbe.upd st.m a (st.x r) } (h + n) s' := by
  have h8 := hM.x 8 (by omega) (by omega)
  have hx := hM.x r (by omega) (mapped_lt hr)
  rcases hW with ⟨h1, h2, h3, rfl, hA⟩ | ⟨h1, h2, rfl, hA⟩ | ⟨h1, h2, rfl, hA, hA1⟩
  · exact n_str S hM hB hA (armReg_lt hr hr0) hx (by decide) h8 (by omega) (by omega) (by omega) hw
  · exact n_stur S hM hB hA (armReg_lt hr hr0) hx (by decide) h8 h1 (by omega) ha hw
  · obtain ⟨s1, r1, N1, o1⟩ := n_subi16 S hM hB hA (by omega)
    have e : (st.x 8 - UInt64.ofNat (-off).toNat).toNat = (st.x 8).toNat - (-off).toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_ofNat_lt (by omega)]; omega),
        toNat_ofNat_lt (by omega)]
    obtain ⟨s2, r2, N2⟩ := n_str S N1 hB hA1 (armReg_lt hr hr0) (N1.x r (by omega) (mapped_lt hr)) (by decide) o1
      (by decide) (by decide) (by rw [e]; omega) hw
    exact ⟨s2, Runs.trans r1 r2, N2⟩

/-! ## signed add `a5` (one-word forms; the `li x16` + `add` form is `n_movz`.. + `n_alu`) -/

/-- `add xd, xn, #v`, `0 ≤ v < 4096` -/
theorem n_addS (S : A64SemN M X W) {h d n : Nat} {v : Int} (hM : NMid X W K A s0 st h s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hA : A[h]? = some (ArmEnc.addi (armReg d) (armReg n) v.toNat))
    (hd : mapped d = true) (hd0 : d ≠ 0) (hn : mapped n = true) (hn0 : n ≠ 0) (h1 : 0 ≤ v) (h2 : v < 4096) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (st.x n + UInt64.ofInt v)) (h + 1) s' := by
  obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le h1
  exact n_addi S hM hB hA hd hd0 hn hn0 (by omega)

/-- `sub xd, xn, #(-v)`, `-4096 < v < 0` -/
theorem n_subS (S : A64SemN M X W) {h d n : Nat} {v : Int} (hM : NMid X W K A s0 st h s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hA : A[h]? = some (ArmEnc.subi (armReg d) (armReg n) (-v).toNat))
    (hd : mapped d = true) (hd0 : d ≠ 0) (hn : mapped n = true) (hn0 : n ≠ 0) (h1 : -4096 < v) (h2 : v < 0) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (st.x n + UInt64.ofInt v)) (h + 1) s' := by
  obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -v by omega)
  have : v = -(i : Int) := by omega
  subst this
  have := n_subi S hM hB hA hd hd0 hn hn0 (by omega)
  simpa [UInt64.ofInt, sub_eq_add_neg] using this

end JT
