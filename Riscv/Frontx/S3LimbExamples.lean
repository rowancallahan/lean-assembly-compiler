/- **`Nat` as limbs through S3** (`Testing/notes/S3_REC.md` §7, `Compiler/S3/Limbs.lean`): `s3_compileL` compiles
`Nat` as base-`2^32` digits (a limb list), the `Nat` operations as limb primitives proved once, literals as limb
chains, `Nat.casesOn`/`Nat.rec` as a test against `0` and the predecessor.  Each entry: `main = encodeOut ∘ f ∘
decodeIn` (byte formats `S3IO.lean`), the S3 program, certificates, `computes`, `correct` (exactly the Sail axioms),
`wf`.  Tests: `Testing/asm/emit_s3limb.lean`, `python3 Testing/asm/ir_test.py check 50 s3l_<name>`.

| entry | function under test | what it exercises |
|---|---|---|
| `S3LArith` | `arith` (ours) | `+ - * / %`, `< ≤ ==` on 64-bit and 128-bit `Nat`s, `UInt64.toNat`/`UInt64.ofNat` |
| `S3LFuel` | con-leche's `whnfLoopFuel` (`2^62`) and `maxNatSizeDefault` (`2^27`), verbatim; `walkFuel` (ours) | large `Nat` constants as data; a fuel parameter decremented per step |

More entries (recursion on `Nat`, `Nat.log2`): `S3LimbRec.lean`.
-/
import Riscv.Frontx.S3IO
import Riscv.Back.S3Top

namespace Proven.S3.Limb
open Proven.S3 Proven.S3.Ex

/-! ## arithmetic on 64- and 128-bit numbers -/

/-- every operation on `x`, `y` and their product -/
def arith (x y : Nat) : List Nat :=
  let p := x * y
  [x + y, x - y, y - x, p, p / (y + 1), p % (x + 7), p / 4294967296 / 4294967296, x / y, x % y,
   if x < y then 1 else 0, if x ≤ y then 1 else 0, if x == y then 1 else 0, if p == y * x then 1 else 0]

/-- a `Nat` below `2^128` as two words -/
def natB (n : Nat) : List UInt8 := enc8 (UInt64.ofNat n) ++ enc8 (UInt64.ofNat (n / 18446744073709551616))

def arithMain (bs : List UInt8) : List UInt8 :=
  match decW bs with
  | a :: b :: _ => (arith a.toNat b.toNat).flatMap natB
  | _ => []
s3_compileL S3LArith := arithMain

/-! ## con-leche's large constants as data, a fuel parameter -/

end Proven.S3.Limb
-- con-leche `ConLeche/Kernel/Core.lean` / `ConLeche/Cached/StateC.lean` (`F2.lean.txt` lines 7540 and 17203 on
-- `origin/conleche-depth`; con-leche @6810492c1), verbatim
namespace ConLeche
@[irreducible, noinline] def whnfLoopFuel : Nat := 4611686018427387904  -- 2^62
end ConLeche
namespace ConLeche.Cached
/-- The official kernel's default maximum `Nat` size, 128 MiB. -/
def maxNatSizeDefault : Nat := 134217728
end ConLeche.Cached
namespace Proven.S3.Limb
open Proven.S3 Proven.S3.Ex

/-- one step per word while fuel lasts (the fuel is a value, kept exactly) -/
def walkFuel (fuel : Nat) : List UInt64 → Nat × UInt64
  | [] => (fuel, 0)
  | x :: r => if fuel = 0 then (0, 0) else
    match walkFuel (fuel - 1) r with
    | (f, s) => (f, s + x)

def fuelMain (bs : List UInt8) : List UInt8 :=
  let ws := decW bs
  let fuel := match ws with
    | f :: _ => if f == 0 then ConLeche.whnfLoopFuel else f.toNat % 5
    | [] => ConLeche.whnfLoopFuel
  match walkFuel fuel ws with
  | (f, s) => natB f ++ enc8 s ++ natB (ConLeche.whnfLoopFuel / ConLeche.Cached.maxNatSizeDefault) ++
      natB (ConLeche.Cached.maxNatSizeDefault * 8)
s3_compileL S3LFuel := fuelMain

end Proven.S3.Limb
