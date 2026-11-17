import Compiler.S3.Front
import Riscv.Back.S3Top
import Nano.ParseS3B
import Compiler.S3.CertBytes
namespace P
open Proven.S3
def lm (bs : List UInt8) : List UInt8 := match bs with | a :: _ => Nano.PS.le8 (a.toUInt64 * 77777) | [] => []
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option s3.depth 4 in
s3_compileF Q := lm
end P
