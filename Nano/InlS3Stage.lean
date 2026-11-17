/- The inliner through S3: the machine theorem, from the S3 program `InlS3` (`Nano/InlS3Self.lean`, the S3 compile with its
certificates) through the adapter (`Nano.S3Stage.stage`). The IR compiler's acceptance and the code length are
kernel-checked on literals (`irLit%`, `layLit%`: the allocated program and the layout, elaborated by evaluation and
checked by the kernel; see Nano/S3Stage.lean). -/
import Nano.InlS3Self

namespace Nano.IS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem inlS3_small : smallB InlS3.P.S = true := by decide +kernel

theorem inlS3_main : (InlS3.P.S.fn InlS3.P.main).1.length = 1 := by decide

/-- the allocated program (literal) -/
def inlS3_Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP InlS3.P)).getD ⟨[], 0⟩)
/-- the layout after one and two rounds (literals) -/
def inlS3_L1 : Lay := layLit% (rvT.layStep inlS3_Q ⟨[], [], 0⟩)
def inlS3_L2 : Lay := layLit% (rvT.layStep inlS3_Q inlS3_L1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlS3_hQ : Ir.alloc (lowerP InlS3.P) = some inlS3_Q := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlS3_h1 : rvT.layStep inlS3_Q ⟨[], [], 0⟩ = inlS3_L1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlS3_h2 : rvT.layStep inlS3_Q inlS3_L1 = inlS3_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlS3_fix : rvT.layStep inlS3_Q inlS3_L2 = inlS3_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlS3_hm : 2 ≤ Target.rounds inlS3_Q := by decide +kernel
theorem inlS3_hL : rvT.layout inlS3_Q 2 ⟨[], [], 0⟩ = inlS3_L2 := by
  simp only [Target.layout, inlS3_h1, inlS3_h2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlS3_hE : (rvT.emitP inlS3_Q inlS3_L2).isSome = true := by decide +kernel

/-- the IR compiler accepts the program -/
theorem inlS3_compiles : (Ir.compileW (lowerP InlS3.P)).isSome = true :=
  compileW_isSome 2 inlS3_hQ inlS3_hm inlS3_hL inlS3_fix inlS3_hE

/-- **the machine theorem of inlB, route S3** (Sail axioms only) -/
theorem inlS3_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words InlS3.P)
      (fun xs => inlBS xs.data.toList) (spaceP InlS3.P) (2 ^ 20) true :=
  stage InlS3.computes inlS3_small inlS3_main inlS3_compiles

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlS3_code_len' : (((rvT.emitP inlS3_Q inlS3_L2).map rvT.words).getD []).length < 2 ^ 17 := by
  decide +kernel

theorem inlS3_code_len : (S3.words InlS3.P).length < 2 ^ 17 := by
  rw [words_eq' 2 inlS3_hQ inlS3_hm inlS3_hL inlS3_fix]; exact inlS3_code_len'

/-- the compiled stage computes `inlB` on every input -/
theorem inlS3_f (x : List UInt8) : (fun xs : ByteArray => inlBS xs.data.toList) (Nano.Link.ofL x) = U.inlB x :=
  inlBS_eq x

end Nano.IS
