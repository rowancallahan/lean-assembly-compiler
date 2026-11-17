import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseBGas
namespace P
def a1 (bs : List UInt8) : List UInt8 := bs ++ bs
s3_compile Q := a1
end P
