/- Two helpers for LOCAL kept from the former plain leaf layer: `slotAddr_eq` and `local1_run` (one slot push as a
plain `run`), used by EVSLeaf.lean. -/
import Nano.V2Self.Proof.Machine.Templates
import Nano.V2Self.Proof.Machine.Expr
namespace Templates
open CallProbe

/-- the two slot-address definitions agree on a valid frame -/
theorem slotAddr_eq {p nl S0 k : Nat} (h : 8 * (nl - p) ≤ S0) (hp : p ≤ nl) (hk : k < nl) :
    CallProbe.slotAddr p k S0 = slotAddr p S0 k := by
  unfold CallProbe.slotAddr slotAddr slotOff; split <;> omega

/-- LOCAL of width 1: `ld t0, off(s0)`, then the checked push -/
theorem local1_run {C : List J} {pc tgt p k : Nat} (s : St) (hC : At C pc (localT tgt p k pc 1)) (hs0 : (s.x 8).toNat < 2 ^ 62)
    (hp : p < 2 ^ 20) (hk : k < p ∨ 8 * (k - p + 1) ≤ (s.x 8).toNat) (hh : (s.x 30).toNat + 8 ≤ (s.x 31).toNat) :
    ∃ s', run C 4 (pc, s) = some (pc + 5, s') ∧
      s'.x = upd (upd s.x 5 (s.m (CallProbe.slotAddr p k (s.x 8).toNat))) 31 (UInt64.ofNat ((s.x 31).toNat - 8)) ∧
      s'.m = upd s.m ((s.x 31).toNat - 8) (s.m (CallProbe.slotAddr p k (s.x 8).toNat)) := by
  have hA : At C pc ([.ld 5 8 (offOf p k)] ++ pushA tgt (pc + 1) 5 ++ localT tgt p (k + 1) (pc + 5) 0) := hC
  have hL : At C pc [.ld 5 8 (offOf p k)] := hA.left.left
  have hP : At C (pc + 1) (pushA tgt (pc + 1) 5) := by simpa using hA.left.right
  have l0 := hL.at 0 (by simp); simp at l0
  have ea0 : ea (s.x 8) (offOf p k) = CallProbe.slotAddr p k (s.x 8).toNat := ea_slot p k _ hs0 hp hk _ rfl
  let v := s.m (CallProbe.slotAddr p k (s.x 8).toNat)
  let s1 : St := ⟨upd s.x 5 v, s.m, s.b, s.ly⟩
  have r1 : run C 1 (pc, s) = some (pc + 1, s1) := by simp [run, step, l0, wr, ea0, v, s1]
  have x31 : s1.x 31 = s.x 31 := by simp [s1, upd_ne]
  have x30 : s1.x 30 = s.x 30 := by simp [s1, upd_ne]
  have hh1 : (s1.x 30).toNat + 8 ≤ (s1.x 31).toNat := by rw [x31, x30]; exact hh
  have r2 := push_run (s := s1) (by simpa [pushA] using hP) (by decide) (by decide) hh1
  refine ⟨⟨upd (upd s.x 5 v) 31 (UInt64.ofNat ((s.x 31).toNat - 8)), upd s.m ((s.x 31).toNat - 8) v, s.b, s.ly⟩, ?_, rfl, rfl⟩
  rw [show 4 = 1 + 3 from rfl, run_add r1, r2]
  have e5 : s1.x 5 = v := by simp [s1, upd_same]
  rw [e5, x31]

end Templates
