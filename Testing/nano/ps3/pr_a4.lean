import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseBGas
namespace P
def a4 (bs : List UInt8) : List UInt8 := match bs with | a :: _ => [5, 0] ++ Nano.mo 6 a | [] => []
s3_compile Q := a4
end P
