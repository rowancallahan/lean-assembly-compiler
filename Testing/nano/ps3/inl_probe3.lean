/- **The inliner compiled through S3** (`Testing/notes/NANO_PARSE_S3.md`): `inlBS` (= `inlB` on every input,
`Nano.IS.inlBS_eq`) compiled by the S3 front end (`s3_compileB`), then the ONE S3 compiler theorem through the
adapter (`Nano.S3Stage.stage`): the machine theorem in the linker's form, `inlS3_implements`. -/
import Compiler.S3.Front
import Nano.InlS3
import Nano.S3Stage

namespace Nano.IS
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option s3.depth 4 in
s3_compileB InlS3 := inlBS

set_option maxRecDepth 100000 in
theorem inlS3_small : smallB InlS3.P.S = true := by decide +kernel

theorem inlS3_main : (InlS3.P.S.fn InlS3.P.main).1.length = 1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem t0 : (Ir.alloc (lowerP InlS3.P)).isSome = true := by decide +kernel
end Nano.IS
