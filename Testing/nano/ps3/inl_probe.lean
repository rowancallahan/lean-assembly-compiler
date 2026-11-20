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
set_option s3.depth 4 in
s3_compileB InlS3 := inlBS

set_option maxRecDepth 100000 in
theorem inlS3_small : smallB InlS3.P.S = true := by decide +kernel

theorem inlS3_main : (InlS3.P.S.fn InlS3.P.main).1.length = 1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- the IR compiler accepts the program (kernel evaluation of the compiler) -/
theorem inlS3_compiles : (Ir.compileW (lowerP InlS3.P)).isSome = true := by decide +kernel

/-- **the machine theorem of the inliner, route S3** (Sail axioms only) -/
theorem inlS3_implements :
    Implements1With (fun xs : ByteArray => xs.data.toList) (fun l => l) (S3.words InlS3.P)
      (fun xs => inlBS xs.data.toList) (spaceP InlS3.P) (2 ^ 20) true :=
  stage InlS3.computes inlS3_small inlS3_main inlS3_compiles

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem inlS3_code_len : (S3.words InlS3.P).length < 2 ^ 17 := by decide +kernel

/-- the compiled stage computes `inlB` on every input -/
theorem inlS3_f (x : List UInt8) : (fun xs : ByteArray => inlBS xs.data.toList) (Nano.Link.ofL x) = U.inlB x :=
  inlBS_eq x

end Nano.IS
