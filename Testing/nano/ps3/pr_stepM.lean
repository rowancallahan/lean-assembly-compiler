import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseBGas
namespace P
def stepM (bs : List UInt8) : List UInt8 := match Nano.PB.step .ret (Nano.PB.st0 []) with | .done o => o | _ => bs
s3_compile Q := stepM
end P
