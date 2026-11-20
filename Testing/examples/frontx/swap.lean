import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Frontx.Ind2Examples
import Legacy.Riscv.Frontx.IndCmpExamples
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.DataExamples
import Legacy.Riscv.Frontx.PairExamples
import Legacy.Riscv.Frontx.MonadExamples
namespace Proven.S3.Ex
open Proven.Frontx.IndEx
def swapMain (bs : List UInt8) : List UInt8 :=
  match decW bs with
  | a :: b :: _ => match Proven.Frontx.Data.swap (a, b) with
    | (c, d) => enc8 c ++ enc8 d
  | _ => []
s3_compile S3Swap := swapMain
end Proven.S3.Ex
