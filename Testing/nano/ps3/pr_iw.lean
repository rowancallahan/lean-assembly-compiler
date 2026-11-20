import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseS3
namespace P
open Nano Nano.PB Nano.PS
def iw (bs : List UInt8) : List UInt8 := bs.filter isW
set_option maxRecDepth 20000 in
s3_compile Q := iw
end P
