import Compiler.S3.Front
import Nano.Expand
namespace Nano.XS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF ExpS3 := Nano.mexp
#print axioms ExpS3.computes
end Nano.XS
