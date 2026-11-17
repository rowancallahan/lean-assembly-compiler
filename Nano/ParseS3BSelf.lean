/- **Stage 2b (the parser machine on the tag format) compiled through S3** (`Testing/notes/NANO_PARSE_S3.md`):
`stage2b` (Nano/ParseS3B.lean; `stage2b (stage2a bs) = stage2 bs` on every input) compiled by `s3_compileF`
(program, kernel-checked certificates, `computes`), split in four files (Nano/ParseS3BSelfA.lean, B, C and this one:
commands [172, 215), `main_good`, `wf`, `computes`) to keep each build ≤ 5 min. The stage theorem:
Nano/ParseS3BStage.lean. -/
import Nano.ParseS3BSelfC

namespace Nano.PS
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF Stage2B := stage2b s3_part 172 215

end Nano.PS
