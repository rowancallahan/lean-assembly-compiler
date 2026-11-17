import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseBGas
namespace P
def sLiM (bs : List UInt8) : List UInt8 := match bs with | a :: _ => Nano.sLi a.toUInt64 | [] => []
set_option maxRecDepth 20000 in
s3_compile Q := sLiM
end P
