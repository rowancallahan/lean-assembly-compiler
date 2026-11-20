/- **The inliner compiled through S3** (`Testing/notes/NANO_PARSE_S3.md`): `inlBS` (= `inlB` on every input,
`Nano.IS.inlBS_eq`) compiled by the S3 front end (`s3_compileB`), then the ONE S3 compiler theorem through the
adapter (`Nano.S3Stage.stage`): the machine theorem in the linker's form, `inlS3_implements`. -/
import Legacy.Compiler.S3.Front
import Legacy.Nano.InlS3
import Legacy.Nano.S3Stage

namespace Nano.IS
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileB InlS3 := inlBS

end Nano.IS
