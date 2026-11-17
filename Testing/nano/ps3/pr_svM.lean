import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseBGas
namespace P
open Nano Nano.PB
def svM (bs : List UInt8) : List UInt8 := sVar bs.length 1
set_option maxRecDepth 20000 in
s3_compile Q := svM
end P
