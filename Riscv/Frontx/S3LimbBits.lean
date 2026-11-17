/- **Bitwise operations on limb `Nat`s through S3** (`Testing/notes/S3_REC.md` §7; entries as in
`S3LimbExamples.lean`).

| entry | function under test | what it exercises |
|---|---|---|
| `S3LBits` | `bits` (ours) | `&&& ||| ^^^` (primitives); `<<<`, `>>>`, `Nat.gcd`, `^` compiled verbatim from their equations over the primitives |
-/
import Riscv.Frontx.S3LimbExamples

namespace Proven.S3.Limb
open Proven.S3 Proven.S3.Ex

/-- the bitwise operations, the shifts, `gcd` and a power on numbers of up to four limbs -/
def bits (x y k : Nat) : List Nat :=
  [x &&& y, x ||| y, x ^^^ y, x >>> k, y <<< (k % 40), Nat.gcd x y, (k % 9) ^ (k % 7)]

def bitsMain (bs : List UInt8) : List UInt8 :=
  match decW bs with
  | a :: b :: c :: _ => (bits (a.toNat * b.toNat + c.toNat) (b.toNat * c.toNat) (a.toNat % 100)).flatMap natB
  | _ => []
s3_compileL S3LBits := bitsMain

end Proven.S3.Limb
