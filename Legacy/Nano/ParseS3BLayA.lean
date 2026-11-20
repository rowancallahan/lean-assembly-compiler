/- Stage 2b, kernel checks part 3 (Nano/ParseS3BStage.lean): the allocated program `stage2B_Q`, its allocation
`stage2B_hQ`, the first two layout rounds `stage2B_h1`, `stage2B_h2`. -/
import Legacy.Nano.ParseS3BAllocB

set_option Elab.async false

namespace Nano.PS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem stage2B_small : smallB Stage2B.P.S = true := by decide +kernel

theorem stage2B_main : (Stage2B.P.S.fn Stage2B.P.main).1.length = 1 := by decide

/-- the allocated program -/
def stage2B_Q : Ir.Prog Nat := ⟨[stage2B_F0, stage2B_F1, stage2B_F2, stage2B_F3, stage2B_F4, stage2B_F5, stage2B_F6, stage2B_F7, stage2B_F8, stage2B_F9, stage2B_F10, stage2B_F11, stage2B_F12, stage2B_F13, stage2B_F14, stage2B_F15, stage2B_F16, stage2B_F17, stage2B_F18, stage2B_F19, stage2B_F20, stage2B_F21, stage2B_F22, stage2B_F23, stage2B_F24, stage2B_F25, stage2B_F26, stage2B_F27, stage2B_F28, stage2B_F29, stage2B_F30, stage2B_F31, stage2B_F32, stage2B_F33, stage2B_F34, stage2B_F35, stage2B_F36, stage2B_F37, stage2B_F38, stage2B_F39, stage2B_F40, stage2B_F41], (lowerP Stage2B.P).main⟩

set_option maxRecDepth 100000 in
theorem stage2B_funcs : (lowerP Stage2B.P).funcs = [lowFn Stage2B.P ⟨0, by decide⟩, lowFn Stage2B.P ⟨1, by decide⟩, lowFn Stage2B.P ⟨2, by decide⟩, lowFn Stage2B.P ⟨3, by decide⟩, lowFn Stage2B.P ⟨4, by decide⟩, lowFn Stage2B.P ⟨5, by decide⟩, lowFn Stage2B.P ⟨6, by decide⟩, lowFn Stage2B.P ⟨7, by decide⟩, lowFn Stage2B.P ⟨8, by decide⟩, lowFn Stage2B.P ⟨9, by decide⟩, lowFn Stage2B.P ⟨10, by decide⟩, lowFn Stage2B.P ⟨11, by decide⟩, lowFn Stage2B.P ⟨12, by decide⟩, lowFn Stage2B.P ⟨13, by decide⟩, lowFn Stage2B.P ⟨14, by decide⟩, lowFn Stage2B.P ⟨15, by decide⟩, lowFn Stage2B.P ⟨16, by decide⟩, lowFn Stage2B.P ⟨17, by decide⟩, lowFn Stage2B.P ⟨18, by decide⟩, lowFn Stage2B.P ⟨19, by decide⟩, lowFn Stage2B.P ⟨20, by decide⟩, lowFn Stage2B.P ⟨21, by decide⟩, lowFn Stage2B.P ⟨22, by decide⟩, lowFn Stage2B.P ⟨23, by decide⟩, lowFn Stage2B.P ⟨24, by decide⟩, lowFn Stage2B.P ⟨25, by decide⟩, lowFn Stage2B.P ⟨26, by decide⟩, lowFn Stage2B.P ⟨27, by decide⟩, lowFn Stage2B.P ⟨28, by decide⟩, lowFn Stage2B.P ⟨29, by decide⟩, lowFn Stage2B.P ⟨30, by decide⟩, lowFn Stage2B.P ⟨31, by decide⟩, lowFn Stage2B.P ⟨32, by decide⟩, lowFn Stage2B.P ⟨33, by decide⟩, lowFn Stage2B.P ⟨34, by decide⟩, lowFn Stage2B.P ⟨35, by decide⟩, lowFn Stage2B.P ⟨36, by decide⟩, lowFn Stage2B.P ⟨37, by decide⟩, lowFn Stage2B.P ⟨38, by decide⟩, lowFn Stage2B.P ⟨39, by decide⟩, lowFn Stage2B.P ⟨40, by decide⟩, mainF Stage2B.P.main.val] := rfl

set_option maxRecDepth 100000 in
theorem stage2B_hQ : Ir.alloc (lowerP Stage2B.P) = some stage2B_Q := by
  unfold Ir.alloc
  rw [stage2B_funcs]
  simp only [List.mapM_cons, List.mapM_nil, stage2B_a0, stage2B_a1, stage2B_a2, stage2B_a3, stage2B_a4, stage2B_a5, stage2B_a6, stage2B_a7, stage2B_a8, stage2B_a9, stage2B_a10, stage2B_a11, stage2B_a12, stage2B_a13, stage2B_a14, stage2B_a15, stage2B_a16, stage2B_a17, stage2B_a18, stage2B_a19, stage2B_a20, stage2B_a21, stage2B_a22, stage2B_a23, stage2B_a24, stage2B_a25, stage2B_a26, stage2B_a27, stage2B_a28, stage2B_a29, stage2B_a30, stage2B_a31, stage2B_a32, stage2B_a33, stage2B_a34, stage2B_a35, stage2B_a36, stage2B_a37, stage2B_a38, stage2B_a39, stage2B_a40, stage2B_a41]
  rfl

set_option maxRecDepth 100000 in
def stage2B_L1 : Lay := layLit% (rvT.layStep stage2B_Q ⟨[], [], 0⟩)
set_option maxRecDepth 100000 in
def stage2B_L2 : Lay := layLit% (rvT.layStep stage2B_Q stage2B_L1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_h1 : rvT.layStep stage2B_Q ⟨[], [], 0⟩ = stage2B_L1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_h2 : rvT.layStep stage2B_Q stage2B_L1 = stage2B_L2 := by decide +kernel
end Nano.PS
