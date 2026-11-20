import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseBGas
namespace P
def moM (bs : List UInt8) : List UInt8 := match bs with | a :: _ => Nano.mo a a | [] => []
s3_compile Q := moM
end P
