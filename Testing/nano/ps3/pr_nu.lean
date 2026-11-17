import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseBGas
namespace P
open Nano Nano.PB
def nu (bs : List UInt8) : List UInt8 := [bs.length.toUInt8]
set_option maxRecDepth 20000 in
s3_compile Q := nu
end P
