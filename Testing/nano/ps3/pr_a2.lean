import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseBGas
namespace P
def a2 (bs : List UInt8) : List UInt8 := match bs with | a :: _ => [a, 0] ++ [a, 1] | [] => []
s3_compile Q := a2
end P
