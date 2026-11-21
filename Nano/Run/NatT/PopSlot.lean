/- T04: pop into slots (LET, CONTINUE; `a21`): per word `ldr x5,[x11]; add x11,x11,#8;` slot store of x5 (T02's `n_slotSt`),
then the w-word induction over a per-word list of (slot offset, store length). -/
import Nano.Run.NatT.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

section T02_interface
def SlotSt (A : List Nat) (h t : Nat) (off : Int) (n : Nat) : Prop :=
  (off % 8 = 0 ∧ 0 ≤ off ∧ off < 32768 ∧ n = 1 ∧ A[h]? = some (ArmEnc.str t (armReg 8) off.toNat)) ∨
  (-256 ≤ off ∧ off < 0 ∧ n = 1 ∧ A[h]? = some (ArmEnc.stur t (armReg 8) off)) ∨
  (-4096 < off ∧ off < -256 ∧ n = 2 ∧ A[h]? = some (ArmEnc.subi 16 (armReg 8) (-off).toNat) ∧
    A[h + 1]? = some (ArmEnc.str t 16 0))

/-- T02's `n_slotSt` as a hypothesis -/
def SlotStHyp (M : Machine) (X W : M.State → Nat → Prop) : Prop :=
  ∀ (S : A64SemN M X W) {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St} {h r n a : Nat} {off : Int}
    (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hW : SlotSt A h (armReg r) off n) (hr : mapped r = true) (hr0 : r ≠ 0)
    (ha : (a : Int) = (st.x 8).toNat + off) (hw : wok K a),
    ∃ s', Runs M s s' ∧ NMid X W K A s0 { st with m := CallProbe.upd st.m a (st.x r) } (h + n) s'
end T02_interface

variable {M : Machine} {X W : M.State → Nat → Prop} {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St}

/-- one word: `ldr x5, [x11]; add x11, x11, #8;` store x5 to `x8 + off` -/
theorem n_popOne (S : A64SemN M X W) (slotSt : SlotStHyp M X W) {h n a : Nat} {off : Int}
    (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (a0 : A[h]? = some (ArmEnc.ldr (armReg 5) (armReg 31) 0))
    (a1 : A[h + 1]? = some (ArmEnc.addi (armReg 31) (armReg 31) 8))
    (hW : SlotSt A (h + 2) (armReg 5) off n) (ha : (a : Int) = (st.x 8).toNat + off)
    (hw : wok K (st.x 31).toNat) (hwa : wok K a) :
    let st1 := CallProbe.wr st 5 (st.m (st.x 31).toNat)
    let st2 := CallProbe.wr st1 31 (st1.x 31 + UInt64.ofNat 8)
    ∃ s', Runs M s s' ∧ NMid X W K A s0 { st2 with m := CallProbe.upd st2.m a (st2.x 5) } (h + 2 + n) s' := by
  intro st1 st2
  obtain ⟨s1, r1, N1⟩ := n_ldr (a := (st.x 31).toNat) S hM hB a0 (by decide) (by decide) (by decide)
    (hM.x 31 (by omega) (by omega)) (by decide) (by decide) (by omega) hw
  obtain ⟨s2, r2, N2⟩ := n_addi S N1 hB a1 (by decide) (by decide) (by decide) (by decide) (by decide)
  change NMid X W K A s0 st2 _ s2 at N2
  have e8 : st2.x 8 = st.x 8 := by simp [st2, st1, CallProbe.wr, CallProbe.upd]
  obtain ⟨s3, r3, N3⟩ := slotSt S (r := 5) N2 hB hW (by decide) (by decide) (by rw [e8]; exact ha) hwa
  exact ⟨s3, Runs.trans (Runs.trans r1 r2) r3, N3⟩

/-- the view after one popped word stored at `x8 + off` -/
def popStep (st : CallProbe.St) (off : Int) : CallProbe.St :=
  let st1 := CallProbe.wr st 5 (st.m (st.x 31).toNat)
  let st2 := CallProbe.wr st1 31 (st1.x 31 + UInt64.ofNat 8)
  { st2 with m := CallProbe.upd st2.m ((st.x 8).toNat + off).toNat (st2.x 5) }

/-- the view after popping the words of `L` (code order: first entry = top word) -/
def popSt : CallProbe.St → List (Int × Nat) → CallProbe.St
  | st, [] => st
  | st, (off, _) :: L => popSt (popStep st off) L

/-- code words of the pops `L` (per word: `ldr`, `add`, then `n` store words) -/
def PopCode (A : List Nat) : Nat → List (Int × Nat) → Prop
  | _, [] => True
  | h, (off, n) :: L => A[h]? = some (ArmEnc.ldr (armReg 5) (armReg 31) 0) ∧
      A[h + 1]? = some (ArmEnc.addi (armReg 31) (armReg 31) 8) ∧ SlotSt A (h + 2) (armReg 5) off n ∧
      PopCode A (h + 2 + n) L

/-- memory side conditions, per word -/
def PopOK (K : LayW) : CallProbe.St → List (Int × Nat) → Prop
  | _, [] => True
  | st, (off, _) :: L => 0 ≤ ((st.x 8).toNat : Int) + off ∧ wok K (st.x 31).toNat ∧
      wok K ((st.x 8).toNat + off).toNat ∧ PopOK K (popStep st off) L

/-- number of A64 words -/
def popLen : List (Int × Nat) → Nat
  | [] => 0
  | (_, n) :: L => 2 + n + popLen L

theorem popStep_x8 (st : CallProbe.St) (off : Int) : (popStep st off).x 8 = st.x 8 := by
  simp [popStep, CallProbe.wr, CallProbe.upd]

/-- **pop `L.length` words into slots** (`a21`) -/
theorem n_popN (S : A64SemN M X W) (slotSt : SlotStHyp M X W) :
    ∀ (L : List (Int × Nat)) {h : Nat} {st : CallProbe.St} {s : M.State} (hM : NMid X W K A s0 st h s)
      (hB : K.base + 4 * A.length ≤ 2 ^ 32), PopCode A h L → PopOK K st L →
      ∃ s', Runs M s s' ∧ NMid X W K A s0 (popSt st L) (h + popLen L) s'
  | [], h, st, s, hM, _, _, _ => ⟨s, Runs.stop, hM⟩
  | (off, n) :: L, h, st, s, hM, hB, ⟨a0, a1, hW, hC⟩, ⟨hn, hw, hwa, hO⟩ => by
    obtain ⟨s1, r1, N1⟩ := n_popOne S slotSt (a := ((st.x 8).toNat + off).toNat) hM hB a0 a1 hW
      (by omega) hw hwa
    obtain ⟨s2, r2, N2⟩ := n_popN S slotSt L N1 hB hC hO
    rw [popLen, show h + (2 + n + popLen L) = h + 2 + n + popLen L by omega]
    exact ⟨s2, Runs.trans r1 r2, N2⟩

end JT
