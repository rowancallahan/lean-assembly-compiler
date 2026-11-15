/- Calling conventions as register numbers. -/

namespace Proven.Top

/-- Which register carries what. -/
structure RegisterMapping where
  returnAddress : Nat
  inputAddress : Nat
  inputLength : Nat
  workAddress : Nat
  workTop : Nat
  outputAddress : Nat
  status : Nat
  outputLength : Nat
  kept : List Nat

/-- RISC-V: ra, a0–a3, sp. -/
def riscvMapping : RegisterMapping where
  returnAddress := 1
  inputAddress := 10
  inputLength := 11
  workAddress := 12
  workTop := 2
  outputAddress := 13
  status := 10
  outputLength := 11
  kept := [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- AArch64: x30, x0–x3, sp. -/
def armMapping : RegisterMapping where
  returnAddress := 30
  inputAddress := 0
  inputLength := 1
  workAddress := 2
  workTop := 31
  outputAddress := 3
  status := 0
  outputLength := 1
  kept := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 31]

end Proven.Top
