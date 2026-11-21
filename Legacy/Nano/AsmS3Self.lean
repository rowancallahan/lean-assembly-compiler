/- **The assembler compiled through S3** (branch nano-s3-all): `asmS` (Nano/AsmS3.lean; `asmS xs = asm xs` on every
input) compiled by `s3_compileF` (program, kernel-checked certificates, `computes`). The op case split is 12 deep, so
the certificate search depth is raised (`s3.depth 24`). The stage theorem: Nano/AsmS3Stage.lean. -/
import Legacy.Compiler.S3.Front
import Legacy.Nano.AsmS3
import Legacy.Nano.S3Stage

namespace Nano.AS
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option s3.depth 24 in
s3_compileF AsmS3 := asmS

end Nano.AS
