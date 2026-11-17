/- **Recursion on limb `Nat`s through S3** (`Testing/notes/S3_REC.md` §7; entries as in `S3LimbExamples.lean`).

| entry | function under test | what it exercises |
|---|---|---|
| `S3LFact` | `fact`, `digits` (ours) | structural recursion on `Nat` (`n + 1` patterns), numbers of many limbs, well-founded recursion on `Nat` (`termination_by n`) |
| `S3LNatSize` | con-leche's `natSizeBytes` and `maxNatSizeDefault` (verbatim) | `Nat.log2` (a primitive), the size refusal test of con-leche's `Nat` operations |

Bitwise operations: `S3LimbBits.lean`.
-/
import Riscv.Frontx.S3LimbExamples

namespace Proven.S3.Limb
open Proven.S3 Proven.S3.Ex

/-! ## structural and well-founded recursion on `Nat`, many limbs -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- the base-`2^64` digits, least significant first -/
def digits (n : Nat) : List UInt64 :=
  if h : n = 0 then [] else UInt64.ofNat (n % 18446744073709551616) :: digits (n / 18446744073709551616)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

def factMain (bs : List UInt8) : List UInt8 :=
  match bs with
  | b :: _ => encW (digits (fact (b.toUInt64 &&& 63).toNat))
  | [] => []
s3_compileL S3LFact := factMain

end Proven.S3.Limb
-- con-leche `ConLeche/Cached/StateC.lean` (`F2.lean.txt` lines 17205-17208 on `origin/conleche-depth`;
-- con-leche @6810492c1), verbatim
namespace ConLeche.Cached
/-- The official kernel's size of a numeral in bytes
(`lean_nat_size_in_bytes`): one machine word for a scalar, the limbs
for a GMP number — 8 bytes per started 64 bits, and at least 8. -/
def natSizeBytes (n : Nat) : Nat := 8 * (n.log2 / 64 + 1)
end ConLeche.Cached
namespace Proven.S3.Limb
open Proven.S3 Proven.S3.Ex

/-- per input word `w`: the sizes of `w`, `w^2`, `w^4`, `w^8` and whether `w^8` would be refused at a maximum size
of `w % 64` bytes or at the default -/
def natSizeMain (bs : List UInt8) : List UInt8 :=
  (decW bs).flatMap fun w =>
    let n := w.toNat
    let n2 := n * n
    let n4 := n2 * n2
    let n8 := n4 * n4
    natB (ConLeche.Cached.natSizeBytes n) ++ natB (ConLeche.Cached.natSizeBytes n2) ++
      natB (ConLeche.Cached.natSizeBytes n4) ++ natB (ConLeche.Cached.natSizeBytes n8) ++
      [if ConLeche.Cached.natSizeBytes n8 > n % 64 then 1 else 0,
       if ConLeche.Cached.natSizeBytes n8 > ConLeche.Cached.maxNatSizeDefault then 1 else 0]
s3_compileL S3LNatSize := natSizeMain

end Proven.S3.Limb
