import Compiler.S3.Front
import Nano.Asm
namespace Nano.AS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF AsmS3 := Nano.asm
#print axioms AsmS3.computes
end Nano.AS
