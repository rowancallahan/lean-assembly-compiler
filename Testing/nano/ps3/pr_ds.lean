import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseS3
namespace P
open Nano Nano.PB Nano.PS
def ds (bs : List UInt8) : List UInt8 := match decS bs [] none with | some ts => [u8N ts.length] | none => []
set_option maxRecDepth 20000 in
s3_compile Q := ds
end P
