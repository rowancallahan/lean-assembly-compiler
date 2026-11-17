import Riscv.Frontx.S3IO
import Riscv.Frontx.Ind2Examples
import Riscv.Frontx.IndCmpExamples
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.DataExamples
import Riscv.Frontx.PairExamples
import Riscv.Frontx.MonadExamples
namespace Proven.S3.Ex
open Proven.Frontx.IndEx
def graftMain (bs : List UInt8) : List UInt8 :=
  match decTGo bs [] with
  | t2 :: t1 :: _ => encT (BinTree.graftLeft t1 t2)
  | _ => []
s3_compile S3Graft := graftMain
end Proven.S3.Ex
