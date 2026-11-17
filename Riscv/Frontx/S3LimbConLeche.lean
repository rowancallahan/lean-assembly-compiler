/- **con-leche over limb `Nat`s through S3** (`Testing/notes/S3_REC.md` §7; entries as in `S3LimbExamples.lean`).

| entry | function under test | what it exercises |
|---|---|---|
| `S3LDropVars` | con-leche `Expr.dropVars` (+ `Expr.instantiate1`, verbatim), the harness of `S3DropVars` | `s3_encL` on con-leche's `Name`, `Level`, `Literal`, `Expr` (their `Nat` fields as limbs); structural recursion on `Nat` (`Nat.brecOn`) over limbs; `Expr.data`'s `Nat` hashing (`UInt64.ofNat`) |
-/
import Riscv.Frontx.S3RecExamples

s3_encL ConLeche.Name
s3_encL ConLeche.Level
s3_encL ConLeche.Literal
s3_encL ConLeche.Expr

namespace Proven.S3.Limb
open Proven.S3 Proven.S3.Ex Proven.S3.Rec

s3_compileL S3LDropVars := dropMain

end Proven.S3.Limb
