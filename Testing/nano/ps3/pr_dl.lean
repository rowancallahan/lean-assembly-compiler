import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseS3
namespace P
open Nano Nano.PB Nano.PS
def dl (bs : List UInt8) : List UInt8 := match decLS bs with | some (_, ts) => [u8N ts.length] | none => []
set_option maxRecDepth 20000 in
s3_compile Q := dl
end P
