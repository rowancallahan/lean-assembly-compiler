import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseBGas
namespace P
def moM (bs : List UInt8) : List UInt8 := match bs with | a :: _ => Nano.mo a a | [] => []
s3_compile Q := moM
end P
