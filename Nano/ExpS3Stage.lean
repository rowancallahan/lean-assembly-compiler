/- The expander `mexp` through S3 (branch nano-s3-all): the machine theorem, from the S3 program `ExpS3` (`Nano/ExpS3Self.lean`, `mexp` verbatim, the S3 compile with its
certificates) through the adapter (`Nano.S3Stage.stage`). The IR compiler's acceptance and the code length are
kernel-checked on literals (`irLit%`, `layLit%`: the allocated program and the layout, elaborated by evaluation and
checked by the kernel; see Nano/S3Stage.lean). -/
import Nano.ExpS3Self

namespace Nano.XS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem expS3_small : smallB ExpS3.P.S = true := by decide +kernel

theorem expS3_main : (ExpS3.P.S.fn ExpS3.P.main).1.length = 1 := by decide

/-- the allocated program (literal) -/
def expS3_Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP ExpS3.P)).getD ⟨[], 0⟩)
/-- the layout after one and two rounds (literals) -/
def expS3_L1 : Lay := layLit% (rvT.layStep expS3_Q ⟨[], [], 0⟩)
def expS3_L2 : Lay := layLit% (rvT.layStep expS3_Q expS3_L1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expS3_hQ : Ir.alloc (lowerP ExpS3.P) = some expS3_Q := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expS3_h1 : rvT.layStep expS3_Q ⟨[], [], 0⟩ = expS3_L1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expS3_h2 : rvT.layStep expS3_Q expS3_L1 = expS3_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expS3_fix : rvT.layStep expS3_Q expS3_L2 = expS3_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expS3_hm : 2 ≤ Target.rounds expS3_Q := by decide +kernel
theorem expS3_hL : rvT.layout expS3_Q 2 ⟨[], [], 0⟩ = expS3_L2 := by
  simp only [Target.layout, expS3_h1, expS3_h2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expS3_hE : (rvT.emitP expS3_Q expS3_L2).isSome = true := by decide +kernel

/-- the IR compiler accepts the program -/
theorem expS3_compiles : (Ir.compileW (lowerP ExpS3.P)).isSome = true :=
  compileW_isSome 2 expS3_hQ expS3_hm expS3_hL expS3_fix expS3_hE

/-- **the machine theorem of the expander `mexp`, route S3** (Sail axioms only) -/
theorem expS3_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words ExpS3.P)
      (fun xs => Nano.mexp xs.data.toList) (spaceP ExpS3.P) (2 ^ 20) true :=
  stage ExpS3.computes expS3_small expS3_main expS3_compiles

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem expS3_code_len' : (((rvT.emitP expS3_Q expS3_L2).map rvT.words).getD []).length < 2 ^ 17 := by
  decide +kernel

theorem expS3_code_len : (S3.words ExpS3.P).length < 2 ^ 17 := by
  rw [words_eq' 2 expS3_hQ expS3_hm expS3_hL expS3_fix]; exact expS3_code_len'

/-- the compiled stage computes `Nano.mexp` on every input -/
theorem expS3_f (x : List UInt8) : (fun xs : ByteArray => Nano.mexp xs.data.toList) (Nano.Link.ofL x) = Nano.mexp x :=
  rfl

end Nano.XS
