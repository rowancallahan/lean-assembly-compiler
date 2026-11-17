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
def rf (bs : List UInt8) : List UInt8 := match retFS (st0 []) .letB [] with | .go _ s => s.out | _ => bs
set_option maxRecDepth 20000 in
s3_compile Q := rf
end P
