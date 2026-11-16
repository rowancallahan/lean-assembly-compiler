/- IR back-end tests (`Compiler/Ir/`, `Riscv/Back/IrTop.lean`): for each hand-written RTL program the words of
`Ir.compile` (`compileW`), and per case the input, the IR interpreter's output and `memoryNeeded` (8 bytes times the peak of the
run's events and the frame).  Run: `lake env lean --tstack=4000000 Testing/asm/emit_ir.lean`, then
`python3 Testing/asm/ir_test.py check 60 <name>` (QEMU + Sail at `memoryNeeded` and `memoryNeeded - 1`). -/
import Riscv.Back.IrTop
import Compiler.Ir.Examples
open Proven.Ir Proven.Mach.Riscv Proven.Top.Alloc
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64

def emit (name : String) (P : Prog VReg) (inputs : List (List UInt8)) : IO Unit := do
  match compileW P with
  | none => IO.println s!"{name}: compile failed"
  | some (ws, nS) =>
    IO.FS.writeFile s!"Testing/asm/ir-words/{name}.words" (String.intercalate "\n" (s!"{name} 0" :: ws.map hex8) ++ "\n")
    let mut lines : List String := []
    for x in inputs do
      match interp P 10000000 x with
      | some (o, ev) => lines := lines ++ [s!"{hx x} {hx o} {8 * peak (ev ++ [.alloc (nS + 1)])}"]
      | none => IO.println s!"{name}: interpreter failed on {hx x}"
    IO.FS.writeFile s!"Testing/asm/ir-words/{name}.cases" (String.intercalate "\n" lines ++ "\n")
    IO.println s!"{name}: {ws.length} words, {nS} slots, {lines.length} cases"

def inputs (n : Nat) (seed : Nat) : List (List UInt8) :=
  (List.range n).map fun i => (List.range (i % 37 + i / 3)).map fun j => UInt8.ofNat (rnd (i + seed) j)

#eval emit "reverse" Examples.reverse (inputs 60 1)
#eval emit "mix" Examples.mix (inputs 60 2)
