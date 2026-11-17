/- Stage 2b, kernel checks part 1: the allocation of every function except function 18 (Nano/ParseS3BStage.lean). -/
import Nano.ParseS3BSelf
import Nano.S3Stage

namespace Nano.PS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
/-- function 0, allocated (literal) -/
def stage2B_F0 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨0, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a0 : Func.alloc1 (lowFn Stage2B.P ⟨0, by decide⟩) = some stage2B_F0 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 1, allocated (literal) -/
def stage2B_F1 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨1, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a1 : Func.alloc1 (lowFn Stage2B.P ⟨1, by decide⟩) = some stage2B_F1 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 2, allocated (literal) -/
def stage2B_F2 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨2, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a2 : Func.alloc1 (lowFn Stage2B.P ⟨2, by decide⟩) = some stage2B_F2 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 3, allocated (literal) -/
def stage2B_F3 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨3, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a3 : Func.alloc1 (lowFn Stage2B.P ⟨3, by decide⟩) = some stage2B_F3 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 4, allocated (literal) -/
def stage2B_F4 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨4, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a4 : Func.alloc1 (lowFn Stage2B.P ⟨4, by decide⟩) = some stage2B_F4 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 5, allocated (literal) -/
def stage2B_F5 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨5, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a5 : Func.alloc1 (lowFn Stage2B.P ⟨5, by decide⟩) = some stage2B_F5 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 6, allocated (literal) -/
def stage2B_F6 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨6, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a6 : Func.alloc1 (lowFn Stage2B.P ⟨6, by decide⟩) = some stage2B_F6 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 7, allocated (literal) -/
def stage2B_F7 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨7, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a7 : Func.alloc1 (lowFn Stage2B.P ⟨7, by decide⟩) = some stage2B_F7 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 8, allocated (literal) -/
def stage2B_F8 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨8, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a8 : Func.alloc1 (lowFn Stage2B.P ⟨8, by decide⟩) = some stage2B_F8 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 9, allocated (literal) -/
def stage2B_F9 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨9, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a9 : Func.alloc1 (lowFn Stage2B.P ⟨9, by decide⟩) = some stage2B_F9 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 10, allocated (literal) -/
def stage2B_F10 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨10, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a10 : Func.alloc1 (lowFn Stage2B.P ⟨10, by decide⟩) = some stage2B_F10 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 11, allocated (literal) -/
def stage2B_F11 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨11, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a11 : Func.alloc1 (lowFn Stage2B.P ⟨11, by decide⟩) = some stage2B_F11 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 12, allocated (literal) -/
def stage2B_F12 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨12, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a12 : Func.alloc1 (lowFn Stage2B.P ⟨12, by decide⟩) = some stage2B_F12 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 13, allocated (literal) -/
def stage2B_F13 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨13, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a13 : Func.alloc1 (lowFn Stage2B.P ⟨13, by decide⟩) = some stage2B_F13 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 14, allocated (literal) -/
def stage2B_F14 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨14, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a14 : Func.alloc1 (lowFn Stage2B.P ⟨14, by decide⟩) = some stage2B_F14 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 15, allocated (literal) -/
def stage2B_F15 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨15, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a15 : Func.alloc1 (lowFn Stage2B.P ⟨15, by decide⟩) = some stage2B_F15 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 16, allocated (literal) -/
def stage2B_F16 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨16, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a16 : Func.alloc1 (lowFn Stage2B.P ⟨16, by decide⟩) = some stage2B_F16 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 17, allocated (literal) -/
def stage2B_F17 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨17, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a17 : Func.alloc1 (lowFn Stage2B.P ⟨17, by decide⟩) = some stage2B_F17 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 19, allocated (literal) -/
def stage2B_F19 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨19, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a19 : Func.alloc1 (lowFn Stage2B.P ⟨19, by decide⟩) = some stage2B_F19 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 20, allocated (literal) -/
def stage2B_F20 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨20, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a20 : Func.alloc1 (lowFn Stage2B.P ⟨20, by decide⟩) = some stage2B_F20 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 21, allocated (literal) -/
def stage2B_F21 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨21, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a21 : Func.alloc1 (lowFn Stage2B.P ⟨21, by decide⟩) = some stage2B_F21 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 22, allocated (literal) -/
def stage2B_F22 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨22, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a22 : Func.alloc1 (lowFn Stage2B.P ⟨22, by decide⟩) = some stage2B_F22 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 23, allocated (literal) -/
def stage2B_F23 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨23, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a23 : Func.alloc1 (lowFn Stage2B.P ⟨23, by decide⟩) = some stage2B_F23 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 24, allocated (literal) -/
def stage2B_F24 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨24, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a24 : Func.alloc1 (lowFn Stage2B.P ⟨24, by decide⟩) = some stage2B_F24 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 25, allocated (literal) -/
def stage2B_F25 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨25, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a25 : Func.alloc1 (lowFn Stage2B.P ⟨25, by decide⟩) = some stage2B_F25 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 26, allocated (literal) -/
def stage2B_F26 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨26, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a26 : Func.alloc1 (lowFn Stage2B.P ⟨26, by decide⟩) = some stage2B_F26 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 27, allocated (literal) -/
def stage2B_F27 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨27, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a27 : Func.alloc1 (lowFn Stage2B.P ⟨27, by decide⟩) = some stage2B_F27 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 28, allocated (literal) -/
def stage2B_F28 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨28, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a28 : Func.alloc1 (lowFn Stage2B.P ⟨28, by decide⟩) = some stage2B_F28 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 29, allocated (literal) -/
def stage2B_F29 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨29, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a29 : Func.alloc1 (lowFn Stage2B.P ⟨29, by decide⟩) = some stage2B_F29 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 30, allocated (literal) -/
def stage2B_F30 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨30, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a30 : Func.alloc1 (lowFn Stage2B.P ⟨30, by decide⟩) = some stage2B_F30 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 31, allocated (literal) -/
def stage2B_F31 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨31, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a31 : Func.alloc1 (lowFn Stage2B.P ⟨31, by decide⟩) = some stage2B_F31 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 32, allocated (literal) -/
def stage2B_F32 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨32, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a32 : Func.alloc1 (lowFn Stage2B.P ⟨32, by decide⟩) = some stage2B_F32 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 33, allocated (literal) -/
def stage2B_F33 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨33, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a33 : Func.alloc1 (lowFn Stage2B.P ⟨33, by decide⟩) = some stage2B_F33 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 34, allocated (literal) -/
def stage2B_F34 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨34, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a34 : Func.alloc1 (lowFn Stage2B.P ⟨34, by decide⟩) = some stage2B_F34 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 35, allocated (literal) -/
def stage2B_F35 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨35, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a35 : Func.alloc1 (lowFn Stage2B.P ⟨35, by decide⟩) = some stage2B_F35 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 36, allocated (literal) -/
def stage2B_F36 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨36, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a36 : Func.alloc1 (lowFn Stage2B.P ⟨36, by decide⟩) = some stage2B_F36 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 37, allocated (literal) -/
def stage2B_F37 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨37, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a37 : Func.alloc1 (lowFn Stage2B.P ⟨37, by decide⟩) = some stage2B_F37 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 38, allocated (literal) -/
def stage2B_F38 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨38, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a38 : Func.alloc1 (lowFn Stage2B.P ⟨38, by decide⟩) = some stage2B_F38 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 39, allocated (literal) -/
def stage2B_F39 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨39, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a39 : Func.alloc1 (lowFn Stage2B.P ⟨39, by decide⟩) = some stage2B_F39 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 40, allocated (literal) -/
def stage2B_F40 : Ir.Func Nat := funcLit% ((Func.alloc1 (lowFn Stage2B.P ⟨40, by decide⟩)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a40 : Func.alloc1 (lowFn Stage2B.P ⟨40, by decide⟩) = some stage2B_F40 := by decide +kernel

set_option maxRecDepth 100000 in
/-- function 41, allocated (literal) -/
def stage2B_F41 : Ir.Func Nat := funcLit% ((Func.alloc1 (mainF Stage2B.P.main.val)).getD ⟨[], 0, [], 0⟩)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stage2B_a41 : Func.alloc1 (mainF Stage2B.P.main.val) = some stage2B_F41 := by decide +kernel

end Nano.PS
