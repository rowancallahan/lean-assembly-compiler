import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseBGas
namespace P
open Nano Nano.PB
def edM (bs : List UInt8) : List UInt8 := match endDef (st0 []) with | .done o => o | _ => bs
set_option maxRecDepth 20000 in
s3_compile Q := edM
end P
