import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Frontx.Ind2Examples
import Legacy.Riscv.Frontx.IndCmpExamples
import Legacy.Riscv.Frontx.ListOutExamples
import Legacy.Riscv.Frontx.DataExamples
import Legacy.Riscv.Frontx.PairExamples
import Legacy.Riscv.Frontx.MonadExamples
namespace Proven.S3.Ex
open Proven.Frontx.IndEx
def nonTailRevMain (bs : List UInt8) : List UInt8 := encW (NonTail.reverse (decW bs))
s3_compile S3NonTailRev := nonTailRevMain
end Proven.S3.Ex
