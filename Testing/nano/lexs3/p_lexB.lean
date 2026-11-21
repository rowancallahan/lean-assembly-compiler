import Legacy.Compiler.S3.Front
import Legacy.Nano.ElabB
import Legacy.Nano.S3Stage
namespace Nano.LS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF LexS3 := Nano.B.lexB
#print axioms LexS3.computes
end Nano.LS
