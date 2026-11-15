/- Restatements of pure kernels of lean-zip (https://github.com/rowancallahan/lean-zip, Lean 4.34) for `frontx`.
Survey and the exact differences to the originals: `Testing/notes/LEANZIP_SURVEY.md`. Nothing is proved by hand. -/
import Riscv.Frontx.Machine

namespace Proven.Frontx.LZ
open Proven Proven.Frontx Proven.Frontx.Ex

/-! ## K1 Adler-32 (`Zip/Spec/Adler32.lean` `updateByte`, `Zip/Native/Adler32.lean` `adler32 1`)
Original: `Nat` state, `% 65521`.  Here: `UInt32` state; both operands of each `%` are `< 2 * 65521`, so the
reduction is one conditional subtraction.  Result packed as `b * 65536 + a` in a `Nat` (= `Spec.pack`; `UInt32` `<<<` has no `Rep` lemma). -/

def adlerGo (xs : ByteArray) (i : Nat) (a b : UInt32) : Nat :=
  if h : i < xs.size then
    let a1 := a + xs[i].toUInt32
    let a2 := if a1 < 65521 then a1 else a1 - 65521
    let b1 := b + a2
    let b2 := if b1 < 65521 then b1 else b1 - 65521
    adlerGo xs (i + 1) a2 b2
  else b.toNat * 65536 + a.toNat
termination_by xs.size - i

-- the translation takes 18 s (default heartbeat limit: timeout) and logs one spurious `No goals to be solved` at the
-- end; `adlerGo.exec` is added (checked: only propext, Classical.choice, Quot.sound)
set_option maxHeartbeats 0
/-- error: No goals to be solved -/
#guard_msgs (error, drop info) in
frontx_compile adlerGo
set_option maxHeartbeats 200000

/-- `Adler32.Native.adler32 1 xs` -/
def lzAdler (xs : ByteArray) : Nat := adlerGo xs 0 1 0
frontx_entry lzAdler
frontx_implements lzAdler

/-! ## K3 bit reader, `readBits n` value (`ZipCommon/BitReader.lean`, `Zip/Native/Inflate.lean` `readBitsFast.go`)
Original: `BitReader` structure, `acc ||| (bit <<< shift)` (no `UInt32` `<<<` lemma: here `acc + w`, `w` doubled), `Except String (UInt32 × BitReader)`, error at end of input.  Here: the cursor is
two `Nat` parameters, the result is the value only, a read past the end gives bit 0 (`at'`).  Same value whenever the
original succeeds. -/

def rbGo (xs : ByteArray) (pos bitOff : Nat) (acc w : UInt32) (fuel : Nat) : UInt32 :=
  match fuel with
  | 0 => acc
  | k + 1 =>
    let bit : UInt32 := ((at' xs pos).toUInt32 >>> bitOff.toUInt32) &&& 1
    let acc' := if bit = 1 then acc + w else acc
    if bitOff + 1 ≥ 8 then rbGo xs (pos + 1) 0 acc' (w + w) k
    else rbGo xs pos (bitOff + 1) acc' (w + w) k

frontx_compile rbGo with fun _ pos bitOff _ _ fuel => pos + fuel < 2 ^ 32 ∧ bitOff < 8

/-- 13 bits starting at bit 3 of byte 0 -/
def lzReadBits (xs : ByteArray) : UInt32 := rbGo xs 0 3 0 1 13
frontx_entry lzReadBits
frontx_implements lzReadBits

/-! ## K4 Huffman: one symbol through the packed table (`Inflate.lean` `decodeSym`, `HuffTree.DecodeTable`)
Original: `Array UInt32` table, `bitBuf : UInt64`, fallback `walkTree`.  Here: the input block is the 8 byte buffer
followed by the 2048 table words (4 bytes each, little endian; only the low 11 bits of the buffer are used, here read
from its first two bytes, because `Nat` `&&&` has no bound lemma); result `sym <<< 8 ||| len` of the table hit
(`= the packed entry`), `0xFFFFFFFF` where the original falls back to the tree walk (`len = 0`). -/

def huffAt (xs : ByteArray) (p : Nat) : Nat :=
  let idx : Nat := (at' xs p).toNat + 256 * (at' xs (p + 1) &&& 7).toNat
  let q := p + 8 + 4 * idx
  if at' xs q = 0 then 0xFFFFFFFF
  else (at' xs q).toNat ||| ((at' xs (q + 1)).toNat <<< 8) ||| ((at' xs (q + 2)).toNat <<< 16)
frontx_compile huffAt with fun _ p => p < 2 ^ 32

def huffSym (xs : ByteArray) : Nat := huffAt xs 0
frontx_entry huffSym
frontx_implements huffSym

/-! ## K5 LZ77 match length (`Zip/Native/Deflate.lean` `lz77Greedy.countMatch.go`)
Original: hypotheses `h1 : p1 + maxLen ≤ data.size`, `h2 : p2 + maxLen ≤ data.size` as parameters.  Here: the
bounds are tested at run time (same value when `h1`, `h2` hold) and the index `p1 + i` is kept as a running position
`a` (a load at `xs[p1 + i]` fails in the translator, see the survey); the result is `a`, i.e. `p1 + i`. -/

def cmGo (xs : ByteArray) (a b e : Nat) : Nat :=
  if h : a < e ∧ a < xs.size ∧ b < xs.size then
    if xs[a] == xs[b] then cmGo xs (a + 1) (b + 1) e else a
  else a
termination_by e - a

frontx_compile cmGo with fun _ a b e => a ≤ e ∧ e < 2 ^ 32 ∧ b + (e - a) < 2 ^ 40

/-- match length between position 0 and position 4 (`p1 = 0`, so the result position `a` is the length) -/
def lzMatch04 (xs : ByteArray) : Nat := cmGo xs 0 4 xs.size
frontx_entry lzMatch04
frontx_implements lzMatch04

end Proven.Frontx.LZ
