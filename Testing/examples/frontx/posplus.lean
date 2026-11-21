import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Frontx.Ind2Examples
import Legacy.Riscv.Frontx.IndCmpExamples
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.DataExamples
import Legacy.Riscv.Frontx.PairExamples
import Legacy.Riscv.Frontx.MonadExamples
namespace Proven.S3.Ex
open Proven.Frontx.IndEx
def posPlusMain (bs : List UInt8) : List UInt8 :=
  match decP bs with
  | (a, r) => match decP r with
    | (b, _) => encP (a.plus b)
s3_compile S3PosPlus := posPlusMain
end Proven.S3.Ex
