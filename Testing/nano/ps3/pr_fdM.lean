import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseBGas
namespace P
open Nano Nano.PB
def fdM (bs : List UInt8) : List UInt8 := match findD bs [([1],2,3)] with | some (a, b) => [a.toUInt8, b.toUInt8] | none => []
set_option maxRecDepth 20000 in
s3_compile Q := fdM
end P
