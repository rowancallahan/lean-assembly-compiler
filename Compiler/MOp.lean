/- Multiply / divide for the middle layer and the optimiser (NOTES section 22).  `Spec/Code.lean`'s `Op` is the
owner's held-out spec and stays as it is; these operations live on the compiler side only: `BStmt.mop`
(`Compiler/BLang.lean`), `IR.Ins.mop`, `WOp.mop` (with the law `Wide.w_mop`), and per target the M-extension
words (`Riscv/Back/Wide.lean`, `Riscv/Steps/GenMul.lean`).  Pure Lean (core only). -/

namespace Proven.Mach

/-- multiply / divide (the RISC-V M extension; compiler side only: `Spec`'s `Op` is unchanged).  The meaning is the
hardware's: `divu` by zero gives all ones (Lean's `/` gives `0`, so front ends guard it), `remu` by zero gives the
dividend (= Lean's `%`).  `div` / `rem` are the signed ones (NOTES section 26): quotient rounded toward zero
(`Int.tdiv`, by zero all ones, `-2^63 / -1` wraps to `-2^63`), remainder with the sign of the dividend
(`Int.tmod`, by zero the dividend); Lean's `Int` `/` and `%` (`Int.ediv` / `Int.emod`) are built from them by
the front ends. -/
inductive MOp where | mul | divu | remu | div | rem
  deriving DecidableEq, Repr

def MOp.eval : MOp → BitVec 64 → BitVec 64 → BitVec 64
  | .mul, a, b => a * b
  | .divu, a, b => if b = 0 then BitVec.allOnes 64 else a / b
  | .remu, a, b => a % b
  | .div, a, b => if b = 0 then BitVec.allOnes 64 else BitVec.ofInt 64 (a.toInt.tdiv b.toInt)
  | .rem, a, b => BitVec.ofInt 64 (a.toInt.tmod b.toInt)

end Proven.Mach
