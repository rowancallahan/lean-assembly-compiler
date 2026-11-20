import Riscv.Frontx.S3IO
import Riscv.Frontx.Ind2Examples
import Riscv.Frontx.IndCmpExamples
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.DataExamples
import Riscv.Frontx.PairExamples
import Riscv.Frontx.MonadExamples
namespace Proven.S3.Ex
open Proven.Frontx.IndEx
def tailRevMain (bs : List UInt8) : List UInt8 := encW (Tail.reverse (decW bs))
s3_compile S3TailRev := tailRevMain
end Proven.S3.Ex
