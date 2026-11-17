import Compiler.S3.Front
import Nano.AsmS3
namespace Nano.AS
#print axioms asmS_eq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option s3.depth 24 in
s3_compileF AsmS3 := asmS
#print axioms AsmS3.computes
end Nano.AS
