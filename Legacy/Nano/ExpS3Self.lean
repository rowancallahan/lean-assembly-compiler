/- **The expander compiled through S3** (branch nano-s3-all): `Nano.mexp` (Nano/Expand.lean) compiled VERBATIM by the S3
front end (`s3_compileF`: program, kernel-checked certificates, `computes`). The bridge is `rfl`; the stage theorem:
Nano/ExpS3Stage.lean. -/
import Legacy.Compiler.S3.Front
import Legacy.Nano.Expand
import Legacy.Nano.S3Stage

namespace Nano.XS
open Proven Proven.S3 Nano.S3Stage

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
s3_compileF ExpS3 := Nano.mexp

end Nano.XS
