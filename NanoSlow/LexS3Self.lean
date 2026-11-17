/- **The front stage (lexer + parser 2a) compiled through S3**: `lexA` (Nano/LexS3.lean, box nano-final;
`lexA_eq : lexA xs = stage2a (lexB xs)` on every input) compiled by `s3_compileF` (program, kernel-checked
certificates, `computes`). The stage theorem: Nano/LexS3Stage.lean. -/
import Compiler.S3.Front
import Nano.LexS3

s3_enc Nano.Tok

namespace Nano.LS
open Proven Proven.S3

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF LexA := lexA

end Nano.LS
