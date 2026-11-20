import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseBGas
namespace P
open Nano Nano.PB
def scM (bs : List UInt8) : List UInt8 := sCall bs.length 2
set_option maxRecDepth 20000 in
s3_compile Q := scM
end P
