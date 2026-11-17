import Nano.ParseS3BSelf
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage Nano.PS
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t : ((lowerP Stage2B.P).funcs.map (fun F => F.blocks.length)).foldl (· + ·) 0 = 1071 := by decide +kernel
