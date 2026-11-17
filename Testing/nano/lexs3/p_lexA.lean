import Compiler.S3.Front
import Nano.LexS3
import Nano.S3Stage

s3_enc Nano.Tok
namespace Nano.LS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF LexA := Nano.LS.lexA
#print axioms LexA.computes
end Nano.LS
