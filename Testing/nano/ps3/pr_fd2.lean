import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Nano.ParseBGas
namespace P
open Nano Nano.PB
def fd2 (bs : List UInt8) : List UInt8 := match findD bs [([1],2,3)] with | some (_, _) => [1] | none => []
set_option maxRecDepth 20000 in
s3_compile Q := fd2
end P
