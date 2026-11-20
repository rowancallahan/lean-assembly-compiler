/- Fixed-width scalars and conditionals in the list front end (`frontx_compile`, NOTES section 19): con-leche's packed
`Expr` data word, copied verbatim (`UInt64` arithmetic with wraparound; `/`, `%`, `*` by powers of two as shifts and
masks, `==` and `if` on `UInt64`, `min` on `Nat`), each with an `Implements1` theorem for an entry point that reads
the arguments as 64-bit little-endian words from the input bytes. -/
import Legacy.Riscv.Frontx.Machine

/-! ## con-leche @6810492 `ConLeche/Kernel/Expr.lean` -/

namespace ConLeche

-- Kernel/Expr.lean:241
def satRange : Nat := 32767

-- Kernel/Expr.lean:247-248
@[inline] def packData (h b f : UInt64) (lp : Bool) : UInt64 :=
  h * 4294967296 + b * 65536 + f * 2 + (if lp then 1 else 0)

-- Kernel/Expr.lean:251
@[inline] def hashOfData (w : UInt64) : UInt64 := w / 4294967296

-- Kernel/Expr.lean:254
@[inline] def bvarOfData (w : UInt64) : UInt64 := w / 65536 % 32768

-- Kernel/Expr.lean:257
@[inline] def fvarOfData (w : UInt64) : UInt64 := w / 2 % 32768

-- Kernel/Expr.lean:260
@[inline] def lpOfData (w : UInt64) : Bool := w % 2 == 1

-- Kernel/Expr.lean:263
@[inline] def hash32 (w : UInt64) : UInt64 := w % 4294967296

-- Kernel/Expr.lean:266
@[inline] def satSucc (n : Nat) : UInt64 := UInt64.ofNat (min (n + 1) satRange)

-- Kernel/Expr.lean:271-272
@[inline] def satPred (x : UInt64) : UInt64 :=
  if x == 32767 then 32767 else if x == 0 then 0 else x - 1

end ConLeche

/-! ## entry points: arguments as 64-bit little-endian words (`u64At`), `Bool`s as a byte `≠ 0` -/

namespace Proven.Frontx.Scal
open Proven.Frontx.Book

/-- the `k` bytes at `i, …, i + k - 1` as a little-endian word below `acc` (a loop: called as a sub-program) -/
def rdLE (xs : ByteArray) (i : Nat) (k : Nat) (acc : UInt64) : UInt64 :=
  match k with
  | 0 => acc
  | k + 1 => rdLE xs i k (acc <<< 8 ||| (byteAt xs (i + k)).toUInt64)
frontx_compile rdLE requires fun _ i k _ => i + k < 2 ^ 64

/-- the 64-bit little-endian word at byte `i` (`0` past the end) -/
def u64At (xs : ByteArray) (i : Nat) : UInt64 := rdLE xs i 8 0

def hashOfDataAt (xs : ByteArray) (i : Nat) : UInt64 := ConLeche.hashOfData (u64At xs i)
def bvarOfDataAt (xs : ByteArray) (i : Nat) : UInt64 := ConLeche.bvarOfData (u64At xs i)
def fvarOfDataAt (xs : ByteArray) (i : Nat) : UInt64 := ConLeche.fvarOfData (u64At xs i)
def lpOfDataAt (xs : ByteArray) (i : Nat) : Bool := ConLeche.lpOfData (u64At xs i)
def hash32At (xs : ByteArray) (i : Nat) : UInt64 := ConLeche.hash32 (u64At xs i)
def satPredAt (xs : ByteArray) (i : Nat) : UInt64 := ConLeche.satPred (u64At xs i)
def satSuccAt (xs : ByteArray) (i : Nat) : UInt64 := ConLeche.satSucc (u16 xs i)
/-- `h`, `b`, `f`, `lp` the bytes at `i`, …, `i + 3` (`lp`: `≠ 0`); the full words are exercised by the field readers -/
def packDataAt (xs : ByteArray) (i : Nat) : UInt64 :=
  ConLeche.packData (byteAt xs i).toUInt64 (byteAt xs (i + 1)).toUInt64 (byteAt xs (i + 2)).toUInt64 (byteAt xs (i + 3) != 0)

frontx_compile hashOfDataAt requires fun _ i => i + 32 < 2 ^ 64
frontx_compile bvarOfDataAt requires fun _ i => i + 32 < 2 ^ 64
frontx_compile fvarOfDataAt requires fun _ i => i + 32 < 2 ^ 64
frontx_compile lpOfDataAt requires fun _ i => i + 32 < 2 ^ 64
frontx_compile hash32At requires fun _ i => i + 32 < 2 ^ 64
frontx_compile satPredAt requires fun _ i => i + 32 < 2 ^ 64
frontx_compile satSuccAt requires fun _ i => i + 32 < 2 ^ 64
frontx_compile packDataAt requires fun _ i => i + 32 < 2 ^ 64

def hashOfDataE (xs : ByteArray) := hashOfDataAt xs 0
def bvarOfDataE (xs : ByteArray) := bvarOfDataAt xs 0
def fvarOfDataE (xs : ByteArray) := fvarOfDataAt xs 0
def lpOfDataE (xs : ByteArray) := lpOfDataAt xs 0
def hash32E (xs : ByteArray) := hash32At xs 0
def satPredE (xs : ByteArray) := satPredAt xs 0
def satSuccE (xs : ByteArray) := satSuccAt xs 0
def packDataE (xs : ByteArray) := packDataAt xs 0
frontx_entry hashOfDataE
frontx_implements hashOfDataE
frontx_entry bvarOfDataE
frontx_implements bvarOfDataE
frontx_entry fvarOfDataE
frontx_implements fvarOfDataE
frontx_entry lpOfDataE
frontx_implements lpOfDataE
frontx_entry hash32E
frontx_implements hash32E
frontx_entry satPredE
frontx_implements satPredE
frontx_entry satSuccE
frontx_implements satSuccE
frontx_entry packDataE
frontx_implements packDataE

end Proven.Frontx.Scal
