/- **Stage 1 + parser 2a compiled through S3** (branch nano-final): `lexA` (Nano/LexS3.lean; `lexA xs = stage2a (lexB xs)`
on every input) compiled by `s3_compileF` (program, kernel-checked certificates, `computes`). One certificate needs the
byte normal form `le8_byte` (local `s3_norm`). The stage theorem: Nano/LexS3Stage.lean. -/
import Compiler.S3.Front
import Nano.LexS3
import Nano.S3Stage
import Nano.TokS3Enc

namespace Nano.LS
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
attribute [local s3_norm] le8_byte in
s3_compileF LexA := lexA

end Nano.LS
