/- T03: LOCAL s w (`a20`): per word `slot load into x5 ; push x5`, then the w-word induction (NATIVE_ARM_TEMPLATES.md §4).
The slot load is T02's `n_slotLd`, here the hypothesis `T : SlotLdStmt M X W`. -/
import Nano.Run.NatT.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

section T02_interface
/-- the words of a slot load `a9` into register `t`: `n` words at `h` -/
def SlotLd (A : List Nat) (h t : Nat) (off : Int) (n : Nat) : Prop :=
  (off % 8 = 0 ∧ 0 ≤ off ∧ off < 32768 ∧ n = 1 ∧ A[h]? = some (ArmEnc.ldr t (armReg 8) off.toNat)) ∨
  (-256 ≤ off ∧ off < 0 ∧ n = 1 ∧ A[h]? = some (ArmEnc.ldur t (armReg 8) off)) ∨
  (-4096 < off ∧ off < -256 ∧ n = 2 ∧ A[h]? = some (ArmEnc.subi 16 (armReg 8) (-off).toNat) ∧
    A[h + 1]? = some (ArmEnc.ldr t 16 0))

/-- T02's `n_slotLd`, as a hypothesis -/
def SlotLdStmt (M : Machine) (X W : M.State → Nat → Prop) : Prop :=
  ∀ (S : A64SemN M X W) {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St} {h d n a : Nat} {off : Int},
    NMid X W K A s0 st h s → K.base + 4 * A.length ≤ 2 ^ 32 → SlotLd A h (armReg d) off n → mapped d = true →
    d ≠ 0 → (a : Int) = (st.x 8).toNat + off → wok K a →
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (st.m a)) (h + n) s'
end T02_interface

variable {M : Machine} {X W : M.State → Nat → Prop} {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St}

/-- the view after the load of cell `a` into x5 and the pointer decrement -/
def lw (st : CallProbe.St) (a : Nat) : CallProbe.St :=
  let st0 := CallProbe.wr st 5 (st.m a); CallProbe.wr st0 31 (st0.x 31 - 8)
/-- ... and the push store -/
def lstep (st : CallProbe.St) (a : Nat) : CallProbe.St :=
  let t := lw st a; { t with m := CallProbe.upd t.m (t.x 31).toNat (t.x 5) }
/-- the push is out of room -/
def lroom (st : CallProbe.St) (a : Nat) : Prop := ((lw st a).x 31).toNat < ((lw st a).x 30).toNat

instance (st : CallProbe.St) (a : Nat) : Decidable (lroom st a) := by unfold lroom; infer_instance

@[simp] theorem lw_x31 (st : CallProbe.St) (a : Nat) : (lw st a).x 31 = st.x 31 - 8 := by
  simp [lw, CallProbe.wr, CallProbe.upd]
@[simp] theorem lw_x30 (st : CallProbe.St) (a : Nat) : (lw st a).x 30 = st.x 30 := by
  simp [lw, CallProbe.wr, CallProbe.upd]
@[simp] theorem lw_x8 (st : CallProbe.St) (a : Nat) : (lw st a).x 8 = st.x 8 := by
  simp [lw, CallProbe.wr, CallProbe.upd]
@[simp] theorem lstep_x31 (st : CallProbe.St) (a : Nat) : (lstep st a).x 31 = st.x 31 - 8 := by simp [lstep]
@[simp] theorem lstep_x30 (st : CallProbe.St) (a : Nat) : (lstep st a).x 30 = st.x 30 := by simp [lstep]
@[simp] theorem lstep_x8 (st : CallProbe.St) (a : Nat) : (lstep st a).x 8 = st.x 8 := by simp [lstep]

/-- **one LOCAL word**: slot load into x5 (`n` words), then push x5 (`a10`) -/
theorem n_localWord (S : A64SemN M X W) (T : SlotLdStmt M X W) {h n a : Nat} {off : Int}
    (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hL : A.length < 2 ^ 18) (h1 : 1 ≤ A.length) (hW : SlotLd A h (armReg 5) off n)
    (a0 : A[h + n]? = some (ArmEnc.subi (armReg 31) (armReg 31) 8))
    (a1 : A[h + n + 1]? = some (ArmEnc.subsR (armReg 31) (armReg 30)))
    (a2 : A[h + n + 2]? = some (ArmEnc.bc 3 ((1 : Int) - (((h + n : Nat) : Int) + 2))))
    (a3 : A[h + n + 3]? = some (ArmEnc.str (armReg 5) (armReg 31) 0))
    (ha : (a : Int) = (st.x 8).toNat + off) (hwa : wok K a)
    (hw : ¬ lroom st a → wok K ((lw st a).x 31).toNat) :
    ∃ s', Runs M s s' ∧
      if lroom st a then NMid X W K A s0 (lw st a) 1 s' else NMid X W K A s0 (lstep st a) (h + n + 4) s' := by
  obtain ⟨s1, r1, N1⟩ := T S hM hB hW (by decide) (by decide) ha hwa
  obtain ⟨s2, r2, N2⟩ := n_push S N1 hB hL h1 a0 a1 (by simpa using a2) a3 (by decide) (by decide) hw
  exact ⟨s2, Runs.trans r1 r2, N2⟩

/-- the words of the LOCAL template, word by word: `(offset, length of the load)` -/
def LocalWords (A : List Nat) : Nat → List (Int × Nat) → Prop
  | _, [] => True
  | h, (off, n) :: r =>
    SlotLd A h (armReg 5) off n ∧ A[h + n]? = some (ArmEnc.subi (armReg 31) (armReg 31) 8) ∧
    A[h + n + 1]? = some (ArmEnc.subsR (armReg 31) (armReg 30)) ∧
    A[h + n + 2]? = some (ArmEnc.bc 3 ((1 : Int) - (((h + n : Nat) : Int) + 2))) ∧
    A[h + n + 3]? = some (ArmEnc.str (armReg 5) (armReg 31) 0) ∧ LocalWords A (h + n + 4) r

/-- the cell of the slot at offset `off` from x8 -/
def laddr (st : CallProbe.St) (off : Int) : Nat := ((st.x 8).toNat + off).toNat
/-- the view after all the words -/
def localV (st : CallProbe.St) : List (Int × Nat) → CallProbe.St
  | [] => st
  | (off, _) :: r => localV (lstep st (laddr st off)) r
/-- the length in words -/
def localLen (ps : List (Int × Nat)) : Nat := (ps.map fun p => p.2 + 4).sum

theorem sp8 {x : UInt64} (h : 8 ≤ x.toNat) : (x - 8).toNat = x.toNat - 8 := by
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simpa using h)]; rfl

/-- **LOCAL**: all the words.  Either the template is passed (view `localV st ps`, word `h + localLen ps`), or some
word's push was out of room (word 1, view `lw` there). -/
theorem n_local (S : A64SemN M X W) (T : SlotLdStmt M X W) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hL : A.length < 2 ^ 18) (h1 : 1 ≤ A.length) :
    ∀ (ps : List (Int × Nat)) {h : Nat} {st : CallProbe.St} {s : M.State}, NMid X W K A s0 st h s →
    LocalWords A h ps → (∀ p ∈ ps, wok K (laddr st p.1) ∧ 0 ≤ (st.x 8).toNat + p.1) →
    (∀ u : UInt64, (st.x 30).toNat ≤ u.toNat → u.toNat < (st.x 31).toNat → wok K u.toNat) →
    8 ≤ (st.x 30).toNat → (st.x 30).toNat ≤ (st.x 31).toNat →
    ∃ s', Runs M s s' ∧
      (NMid X W K A s0 (localV st ps) (h + localLen ps) s' ∨
       ∃ pre off n post, ps = pre ++ (off, n) :: post ∧ lroom (localV st pre) (laddr (localV st pre) off) ∧
         NMid X W K A s0 (lw (localV st pre) (laddr (localV st pre) off)) 1 s') := by
  intro ps
  induction ps with
  | nil => intro h st s hM _ _ _ _ _; exact ⟨s, Runs.stop, Or.inl (by simpa [localV, localLen] using hM)⟩
  | cons p r ih =>
    obtain ⟨off, n⟩ := p
    intro h st s hM hW hs hstk h8 hsp
    obtain ⟨hS, a0, a1, a2, a3, hr⟩ := hW
    obtain ⟨hwa, hnn⟩ := hs (off, n) (by simp)
    have hsp8 : (st.x 31 - 8).toNat = (st.x 31).toNat - 8 := sp8 (by omega)
    obtain ⟨s', r1, N⟩ := n_localWord S T hM hB hL h1 hS a0 a1 a2 a3 (a := laddr st off)
      (by unfold laddr; omega) hwa
      (fun hn => by
        unfold lroom at hn; simp only [lw_x31, lw_x30] at hn
        exact hstk _ (by simp only [lw_x31]; omega) (by simp only [lw_x31]; omega))
    by_cases hlr : lroom st (laddr st off)
    · rw [if_pos hlr] at N
      exact ⟨s', r1, Or.inr ⟨[], off, n, r, rfl, hlr, N⟩⟩
    · rw [if_neg hlr] at N
      have hlr' : ¬ ((st.x 31).toNat - 8 < (st.x 30).toNat) := by
        unfold lroom at hlr; simpa [hsp8] using hlr
      obtain ⟨s'', r2, R⟩ := ih N hr
        (fun q hq => by
          obtain ⟨h1', h2'⟩ := hs q (by simp [hq])
          exact ⟨by simpa [laddr] using h1', by simpa using h2'⟩)
        (fun u hu1 hu2 => hstk u (by simpa using hu1) (by simp at hu2; omega))
        (by simpa using h8) (by simp; omega)
      refine ⟨s'', Runs.trans r1 r2, ?_⟩
      rcases R with R | ⟨pre, off', n', post, e, hroom, N'⟩
      · left
        have : h + n + 4 + localLen r = h + localLen ((off, n) :: r) := by simp [localLen]; omega
        rw [← this]; exact R
      · right
        exact ⟨(off, n) :: pre, off', n', post, by simp [e], by simpa [localV] using hroom,
          by simpa [localV] using N'⟩

end JT
