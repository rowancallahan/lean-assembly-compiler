import Legacy.Nano.ParseS3BSelf
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage Nano.PS
def Q0 : Ir.Prog Nat := (Ir.alloc (lowerP Stage2B.P)).getD ⟨[], 0⟩
def L2 : Ir.Lay := rvT.layout Q0 2 ⟨[], [], 0⟩
#eval decide (rvT.layStep Q0 L2 = L2)
#eval ((rvT.emitP Q0 L2).map (fun c => (rvT.words c).length))
