import Legacy.Nano.ParseS3BSelf
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage Nano.PS
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Q : Ir.Prog Nat := irLit% ((Ir.alloc (lowerP Stage2B.P)).getD ⟨[], 0⟩)
def L1 : Lay := layLit% (rvT.layStep Q ⟨[], [], 0⟩)
def L2 : Lay := layLit% (rvT.layStep Q L1)
theorem h1 : rvT.layStep Q ⟨[], [], 0⟩ = L1 := by decide +kernel
theorem h2 : rvT.layStep Q L1 = L2 := by decide +kernel
theorem hfix : rvT.layStep Q L2 = L2 := by decide +kernel
theorem hE : (rvT.emitP Q L2).isSome = true := by decide +kernel
