/- Multiply, divide, remainder and shifts by a variable in the list front end (`frontx_compile`, NOTES section 22):
`*`, `/`, `%` on `Nat`, `UInt64`, `UInt32` by variables go through `BStmt.mop` (`mopS`, the RISC-V M extension;
`/` guarded: the machine's quotient by zero is all ones, Lean's is `0`), with `Implements1` theorems through the
checked words `compBFC` (`frontx_implementsC`, `Checked.lean`). -/
import Legacy.Riscv.Frontx.ScalarExamples
import Legacy.Riscv.Frontx.Checked

namespace Proven.Frontx.Mul
open Proven.Frontx.Scal Proven.Frontx.Book

/-! ## every variable operation, on the two 64-bit words at bytes `i` and `i + 8` -/

def ops64At (xs : ByteArray) (i : Nat) : UInt64 :=
  let a := u64At xs i
  let b := u64At xs (i + 8)
  (a * b) ^^^ (a / b) ^^^ (a % b) ^^^ (a <<< b) ^^^ (a >>> b)
frontx_compile ops64At requires fun _ i => i + 32 < 2 ^ 64

def ops64E (xs : ByteArray) : UInt64 := ops64At xs 0
frontx_entry ops64E
frontx_implementsC ops64E

/-- the same on `UInt32` (the low halves of the words; the products masked to 32 bits) -/
def ops32At (xs : ByteArray) (i : Nat) : UInt32 :=
  let a := (u64At xs i).toUInt32
  let b := (u64At xs (i + 8)).toUInt32
  (a * b) ^^^ (a / b) ^^^ (a % b) ^^^ (a <<< b) ^^^ (a >>> b)
frontx_compile ops32At requires fun _ i => i + 32 < 2 ^ 64

def ops32E (xs : ByteArray) : UInt32 := ops32At xs 0
frontx_entry ops32E
frontx_implementsC ops32E

/-- the same on `Nat` (the words' values; the shift amount reduced below 64) -/
def opsNAt (xs : ByteArray) (i : Nat) : Nat :=
  let a := (u64At xs i).toNat
  let b := (u64At xs (i + 8)).toNat
  (a * b) ^^^ (a / b) ^^^ (a % b) ^^^ (a <<< (b % 64)) ^^^ (a >>> b)
frontx_compile opsNAt requires fun _ i => i + 32 < 2 ^ 64

def opsNE (xs : ByteArray) : Nat := opsNAt xs 0
frontx_entry opsNE
frontx_implementsC opsNE

/-! ## Lean 4 v4.29.0 core `Nat.gcd` (`Init/Data/Nat/Gcd.lean:35`, used directly: `if m = 0 then n else gcd (n % m) m`) -/

end Proven.Frontx.Mul

frontx_compile Nat.gcd requires fun m n => m < 2 ^ 64 ∧ n < 2 ^ 64

namespace Proven.Frontx.Mul
open Proven.Frontx.Scal

/-- `gcd` of the two 64-bit words at bytes `i` and `i + 8` -/
def gcdAt (xs : ByteArray) (i : Nat) : Nat := Nat.gcd (u64At xs i).toNat (u64At xs (i + 8)).toNat
frontx_compile gcdAt requires fun _ i => i + 32 < 2 ^ 64

def gcdE (xs : ByteArray) : Nat := gcdAt xs 0
frontx_entry gcdE
frontx_implementsC gcdE

end Proven.Frontx.Mul
