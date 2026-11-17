import Riscv.Frontx.S3IO
import Riscv.Frontx.Ind2Examples
import Riscv.Frontx.IndCmpExamples
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.DataExamples
import Riscv.Frontx.PairExamples
import Riscv.Frontx.MonadExamples
namespace Proven.S3.Ex
open Proven.Frontx.IndEx
s3_compile S3Filter := Proven.Frontx.BookOut.filterGt3
end Proven.S3.Ex
