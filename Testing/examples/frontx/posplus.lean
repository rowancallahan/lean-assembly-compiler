import Riscv.Frontx.S3IO
import Riscv.Frontx.Ind2Examples
import Riscv.Frontx.IndCmpExamples
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.DataExamples
import Riscv.Frontx.PairExamples
import Riscv.Frontx.MonadExamples
namespace Proven.S3.Ex
open Proven.Frontx.IndEx
def posPlusMain (bs : List UInt8) : List UInt8 :=
  match decP bs with
  | (a, r) => match decP r with
    | (b, _) => encP (a.plus b)
s3_compile S3PosPlus := posPlusMain
end Proven.S3.Ex
