import Legacy.Nano.ParseS3BSelf
import Legacy.Nano.S3Stage
open Proven Proven.S3 Proven.Ir Proven.Mach.Riscv Nano.S3Stage Nano.PS
#eval ((lowerP Stage2B.P).funcs.map (fun F => (F.blocks.map (fun B => B.2.body.length)).foldl (· + ·) 0)).foldl (· + ·) 0
#eval ((lowerP Stage2B.P).funcs.map (fun F => (F.blocks.map (fun B => B.2.body.length)).foldl (· + ·) 0))
