import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Frontx.Ind2Examples
import Legacy.Riscv.Frontx.IndCmpExamples
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.DataExamples
import Legacy.Riscv.Frontx.PairExamples
import Legacy.Riscv.Frontx.MonadExamples
namespace Proven.S3.Ex
open Proven.Frontx.IndEx
def eqTreeMain (bs : List UInt8) : List UInt8 :=
  match decTGo bs [] with
  | t2 :: t1 :: _ => boolB (eqBinTree t1 t2)
  | _ => []
s3_compile S3EqTree := eqTreeMain
end Proven.S3.Ex
