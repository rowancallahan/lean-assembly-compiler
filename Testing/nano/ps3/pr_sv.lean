import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseS3
namespace P
open Nano Nano.PB Nano.PS
def sv (bs : List UInt8) : List UInt8 := sVarS bs.length 1 ++ sCallS bs.length 3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileB Q := sv
end P
