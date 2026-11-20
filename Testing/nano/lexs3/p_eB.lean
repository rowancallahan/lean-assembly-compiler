import Legacy.Compiler.S3.Front
import Legacy.Nano.ElabBSplitE
import Legacy.Nano.S3Stage
namespace Nano.LS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF Lex_eB := Nano.B.eB
#print axioms Lex_eB.computes
end Nano.LS
