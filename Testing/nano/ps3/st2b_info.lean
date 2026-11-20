import Legacy.Nano.ParseS3BSelf
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage Nano.PS
def Q0 : Ir.Prog Nat := (Ir.alloc (lowerP Stage2B.P)).getD ⟨[], 0⟩
#eval Q0.funcs.length
#eval (Q0.funcs.map (fun F => F.blocks.length)).foldl (· + ·) 0
#eval (Q0.funcs.map (fun F => (F.blocks.map (fun B => B.2.body.length)).foldl (· + ·) 0)).foldl (· + ·) 0
def L0 : Ir.Lay := rvT.layout Q0 3 ⟨[], [], 0⟩
#eval (Q0.funcs.map (fun F => (F.slots, F.params.length)))
#eval (List.range Q0.funcs.length).map fun f =>
  match Q0.funcs[f]? with
  | some F => (rvT.emitF (Q0.env L0) F (L0.posF f) L0.ex (L0.fq.getD f 0) (L0.fq.getD (f + 1) L0.ex)).isSome
  | none => false
#eval rvT.maxSlots
