import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseBGas
namespace P
def decLm (bs : List UInt8) : List UInt8 := match Nano.decL bs with | some (_, ts) => [ts.length.toUInt8] | none => []
s3_compile Q := decLm
end P
