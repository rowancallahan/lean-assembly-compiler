import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseS3
s3_enc Nano.Tok
s3_enc Nano.PB.Fr
s3_enc Nano.PB.Ctl
s3_enc Nano.PB.St
s3_enc Nano.PB.Res
namespace P
open Nano Nano.PB Nano.PS
def st (bs : List UInt8) : List UInt8 := match stepS .ret (st0 []) with | .done o => o | _ => bs
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compile Q := st
end P
