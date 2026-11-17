import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseS3
namespace P
open Nano Nano.PB Nano.PS
def sv (bs : List UInt8) : List UInt8 := sVarS bs.length 1 ++ sCallS bs.length 3
set_option maxRecDepth 20000 in
s3_compile Q := sv
end P
