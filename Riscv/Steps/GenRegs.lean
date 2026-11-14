/- Register-generic reads and writes of the Sail RV64 model: `rX_bits` / `wX_bits` at a SYMBOLIC
register index, as one lemma each (the 32-way case split happens once, here).  Used by the
register-generic step lemmas (`Riscv/Steps/Gen*.lean`), which freeze `rX_bits` / `wX_bits` and
rewrite them with `rX_bits_ok` / `wX_bits_ok`. -/
import Riscv.Steps.Step
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Proven

/-- all of `x1 .. x31` are present (reads of them do not fail) -/
def xpresent (m : Regs) : Prop := ∀ r ∈ xregs, m.contains r = true

theorem Cfg.xpresent {s : St} (h : Cfg s) : xpresent s.regs := by
  intro r hr; apply h.present; simp only [xregs, List.mem_cons] at hr ⊢; simp [hr]
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h <;> simp_all

@[simp] theorem xpresent_insert {m : Regs} (h : xpresent m) {r : Register} {v} : xpresent (m.insert r v) := by
  intro r' hr'; simp [Std.ExtDHashMap.contains_insert, h r' hr']

theorem xpresent_get {m : Regs} (h : xpresent m) {r : Register} (hr : r ∈ xregs) : ∃ v, m.get? r = some v := by
  have := h r hr
  rw [Std.ExtDHashMap.contains_eq_isSome_get?] at this
  exact Option.isSome_iff_exists.mp this

theorem bv5_cases : ∀ i : BitVec 5, i = 0#5 ∨ i = 1#5 ∨ i = 2#5 ∨ i = 3#5 ∨ i = 4#5 ∨ i = 5#5 ∨ i = 6#5 ∨ i = 7#5 ∨
    i = 8#5 ∨ i = 9#5 ∨ i = 10#5 ∨ i = 11#5 ∨ i = 12#5 ∨ i = 13#5 ∨ i = 14#5 ∨ i = 15#5 ∨ i = 16#5 ∨ i = 17#5 ∨
    i = 18#5 ∨ i = 19#5 ∨ i = 20#5 ∨ i = 21#5 ∨ i = 22#5 ∨ i = 23#5 ∨ i = 24#5 ∨ i = 25#5 ∨ i = 26#5 ∨ i = 27#5 ∨
    i = 28#5 ∨ i = 29#5 ∨ i = 30#5 ∨ i = 31#5 := by decide

/-- the one 32-way split for reads -/
theorem rX_bits_ok (s : St) (hp : xpresent s.regs) (i : BitVec 5) :
    rX_bits (.Regidx i) s = .ok (xval s.regs i.toFin) s := by
  rcases bv5_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sail_eval [rX_bits, rX, zero_reg, zeros]; all_goals rfl
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x1) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x2) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x3) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x4) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x5) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x6) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x7) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x8) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x9) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x10) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x11) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x12) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x13) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x14) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x15) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x16) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x17) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x18) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x19) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x20) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x21) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x22) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x23) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x24) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x25) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x26) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x27) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x28) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x29) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x30) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]
  · obtain ⟨v, hv⟩ := xpresent_get hp (r := .x31) (by decide)
    sail_eval [rX_bits, rX, hv]; all_goals simp [xval, hv]

/-- the one 32-way split for writes (`x0` writes are dropped) -/
theorem wX_bits_ok (s : St) (i : BitVec 5) (v : BitVec 64) :
    wX_bits (.Regidx i) v s = .ok () { s with regs := xset s.regs i.toFin v } := by
  rcases bv5_cases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    sail_eval [wX_bits, wX]
    all_goals first | rfl | simp [xset]

end Proven
