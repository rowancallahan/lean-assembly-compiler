import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseBGas
namespace P
def stepM (bs : List UInt8) : List UInt8 := match Nano.PB.step .ret (Nano.PB.st0 []) with | .done o => o | _ => bs
s3_compile Q := stepM
end P
