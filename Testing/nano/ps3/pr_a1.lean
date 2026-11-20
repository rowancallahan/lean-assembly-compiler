import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseBGas
namespace P
def a1 (bs : List UInt8) : List UInt8 := bs ++ bs
s3_compile Q := a1
end P
