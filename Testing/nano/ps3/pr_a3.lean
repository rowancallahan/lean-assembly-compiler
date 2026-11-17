import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseBGas
namespace P
def a3 (bs : List UInt8) : List UInt8 := match bs with | a :: _ => Nano.mo 6 ((a.toUInt64 >>> 8).toUInt8) | [] => []
s3_compile Q := a3
end P
