/- The ARM adapter `armTarget M` over ANY machine `M` with the abstract A64 steps `A64Sem M` (Machine/A64Sem.lean).
Words: O's `ArmEnc.blk` (rv2arm's blocks, 4 words per J instruction); registers `armReg` (π); scratch x16, x17;
link width 16 (`Rel.ww`: wk = 3).  `lay` = the generic layout ∧ rv2arm's validation `progOK`.

PROOF NOTES (per J kind: block, relation, lemmas) — Testing/nano/v2self/arm/PROOF_NOTES.md; here:
* `Mid K C s0 p k s`: `Rel` with the pc at word `k` of block `p.1` (base + 16·p.1 + 4·k).  `Rel ↔ Mid _ 0`.
* `mid_regs`: an instruction that keeps memory, writes registers only in π's image of the J registers it changes
  and in the scratch registers, and moves the pc, keeps `Mid` (for the new J state).
* per block: the words from `Mid.word`, the A64Sem fields in sequence, `mid_regs` after each. -/
import Nano.V2Self.Proof.Machine.A64Sem
import Nano.V2Self.Proof.Machine.HostOn
namespace JT
open Proven.Top SimW CallProbe ArmEnc

/-- **the ARM target** over a machine `M` -/
def armTarget (M : Machine) : JTarget where
  M := M
  blockLen := 4
  enc := blk
  reg := armReg
  scratch := armScratch
  lay K C := JTarget.LayOK M (16 * C.length) K ∧ progOK C = true
  m0 s a := ((M.observe s).memory (UInt64.ofNat a)).map UInt8.toBitVec
  inv _ _ := True
  words _ := []
  valid C := progOK C = true

variable {M : Machine}

/-! ## registers -/

theorem mapped_iff {r : Nat} : mapped r = true ↔ r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 10 ∨
    r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 28 ∨ r = 29 ∨ r = 30 ∨ r = 31 := by
  simp [mapped]

theorem armReg_lt {r : Nat} (h : mapped r = true) (h0 : r ≠ 0) : armReg r < 31 := by
  rcases mapped_iff.1 h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> first | decide | exact absurd rfl h0

/-- π is injective on the mapped registers -/
theorem armReg_inj {r j : Nat} (hr : mapped r = true) (hj : j < 32) (h : armReg j = armReg r) : j = r := by
  rcases mapped_iff.1 hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> revert h <;> revert hj <;> revert j <;> decide

theorem body_len (j : J) : (body j).length ≤ 4 := by
  cases j <;> simp only [body, zpre, compBr] <;> (repeat' split) <;> simp

theorem blockJ_len (j : J) : (blockJ j).length = 4 := by
  have := body_len j; simp [blockJ, pad4]; omega

theorem blk_len (j : J) : (blk j).length = 4 := by simp [blk, blockJ_len]

/-! ## the mid-block relation -/

/-- `Rel` with the pc at word `k` of block `p.1` -/
structure Mid (K : LayW) (C : List J) (s0 : M.State) (p : Nat × CallProbe.St) (k : Nat) (s : M.State) : Prop where
  cfg : M.configured s
  pc : (M.observe s).programCounter = UInt64.ofNat (K.base + 16 * p.1 + 4 * k)
  code : ∀ i (h : i < C.length) k' (hk : k' < (blk C[i]).length) b, b < 4 →
    (M.observe s).memory (UInt64.ofNat (K.base + 4 * 4 * i + 4 * k' + b)) = some (wbyte (blk C[i])[k'] b)
  x0 : p.2.x 0 = 0
  bb : p.2.b = K.base
  ww : p.2.wk = 3
  x : ∀ j, 0 < j → j < 32 → (M.observe s).register (armReg j) = p.2.x j
  keep : ∀ r, (∀ j, 0 < j → j < 32 → armReg j ≠ r) → r ∉ armScratch →
    (M.observe s).register r = (M.observe s0).register r
  w : ∀ a, wok K a → ∀ k < 8, (M.observe s).memory (UInt64.ofNat (a + k)) = some (cbyte (p.2.m a) k)
  bw : ∀ a, io K a → (M.observe s).memory (UInt64.ofNat a) = some (cbyte (p.2.m (a - a % 8)) (a % 8))
  fr : ∀ a, a < 2 ^ 64 → ¬ wok K (a - a % 8) → ¬ outB K a →
    (M.observe s).memory (UInt64.ofNat a) = (K.m0 a).map UInt8.ofBitVec

theorem mid_of_rel {K : LayW} {C : List J} {s0 s : M.State} {p : Nat × CallProbe.St}
    (h : (armTarget M).Rel K C s0 p s) : Mid K C s0 p 0 s :=
  ⟨h.cfg, by have := h.pc; simp only [JTarget.addr, armTarget] at this; rw [this]; congr 1, h.code, h.x0, h.bb, h.ww, h.x, h.keep, h.w, h.bw, h.fr⟩

theorem rel_of_mid {K : LayW} {C : List J} {s0 s : M.State} {p : Nat × CallProbe.St}
    (h : Mid K C s0 p 0 s) : (armTarget M).Rel K C s0 p s :=
  ⟨h.cfg, by show (M.observe s).programCounter = _; rw [h.pc]; simp only [JTarget.addr, armTarget]; congr 1, h.code, h.x0, h.bb, h.ww, h.x, h.keep, h.w, h.bw, h.fr,
    trivial⟩

end JT
