import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseBGas
namespace P
def lookM (bs : List UInt8) : List UInt8 := match Nano.PB.lookS bs [([1],2)] with | some _ => [1] | none => []
set_option maxHeartbeats 0 in
s3_compileB Q := lookM
end P
