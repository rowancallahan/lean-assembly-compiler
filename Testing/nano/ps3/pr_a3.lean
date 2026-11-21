import Legacy.Riscv.Frontx.S3IO
import Legacy.Riscv.Back.S3Top
import Legacy.Nano.ParseBGas
namespace P
def a3 (bs : List UInt8) : List UInt8 := match bs with | a :: _ => Nano.mo 6 ((a.toUInt64 >>> 8).toUInt8) | [] => []
set_option maxHeartbeats 0 in
s3_compileB Q := a3
end P
