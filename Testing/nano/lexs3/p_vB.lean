import Compiler.S3.Front
import Nano.ElabBSplit
import Nano.S3Stage
namespace Nano.LS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF Lex_vB := Nano.B.vB
#print axioms Lex_vB.computes
end Nano.LS
