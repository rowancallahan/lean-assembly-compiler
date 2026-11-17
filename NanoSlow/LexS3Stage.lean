/- The front stage (lexer + parser 2a) through S3: the machine theorem, from the S3 program `LexA` (`Nano/LexASelf.lean`, the S3 compile with its
certificates) through the adapter (`Nano.S3Stage.stage`). The IR compiler's acceptance and the code length are
kernel-checked on literals (`irLit%`, `layLit%`: the allocated program and the layout, elaborated by evaluation and
checked by the kernel; see Nano/S3Stage.lean). -/
import NanoSlow.LexS3Self
import Nano.S3Stage

namespace Nano.LS
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage

set_option maxRecDepth 100000 in
theorem lexA_small : smallB LexA.P.S = true := by decide +kernel

theorem lexA_main : (LexA.P.S.fn LexA.P.main).1.length = 1 := by decide

/-- the allocated program (literal) -/
def lexA_Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP LexA.P)).getD ⟨[], 0⟩)
/-- the layout after one and two rounds (literals) -/
def lexA_L1 : Lay := layLit% (rvT.layStep lexA_Q ⟨[], [], 0⟩)
def lexA_L2 : Lay := layLit% (rvT.layStep lexA_Q lexA_L1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexA_hQ : Ir.alloc (lowerP LexA.P) = some lexA_Q := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexA_h1 : rvT.layStep lexA_Q ⟨[], [], 0⟩ = lexA_L1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexA_h2 : rvT.layStep lexA_Q lexA_L1 = lexA_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexA_fix : rvT.layStep lexA_Q lexA_L2 = lexA_L2 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexA_hm : 2 ≤ Target.rounds lexA_Q := by decide +kernel
theorem lexA_hL : rvT.layout lexA_Q 2 ⟨[], [], 0⟩ = lexA_L2 := by
  simp only [Target.layout, lexA_h1, lexA_h2]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexA_hE : (rvT.emitP lexA_Q lexA_L2).isSome = true := by decide +kernel

/-- the IR compiler accepts the program -/
theorem lexA_compiles : (Ir.compileW (lowerP LexA.P)).isSome = true :=
  compileW_isSome 2 lexA_hQ lexA_hm lexA_hL lexA_fix lexA_hE

/-- **the machine theorem of inlB, route S3** (Sail axioms only) -/
theorem lexA_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words LexA.P)
      (fun xs => lexA xs.data.toList) (spaceP LexA.P) (2 ^ 20) true :=
  stage LexA.computes lexA_small lexA_main lexA_compiles

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lexA_code_len' : (((rvT.emitP lexA_Q lexA_L2).map rvT.words).getD []).length < 2 ^ 17 := by
  decide +kernel

theorem lexA_code_len : (S3.words LexA.P).length < 2 ^ 17 := by
  rw [words_eq' 2 lexA_hQ lexA_hm lexA_hL lexA_fix]; exact lexA_code_len'

/-- the compiled stage computes `stage2a ∘ lexB` on every input -/
theorem lexA_f (x : List UInt8) : (fun xs : ByteArray => lexA xs.data.toList) (Nano.Link.ofL x) = Nano.PS.stage2a (Nano.B.lexB x) :=
  lexA_eq x

end Nano.LS
