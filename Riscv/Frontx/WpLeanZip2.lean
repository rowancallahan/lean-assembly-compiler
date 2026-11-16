/- Paged front end (NOTES section 35): lean-zip code compiled VERBATIM by `wp_compile` (`WpCmd.lean`).

Source: github.com/rowancallahan/lean-zip @ 7e10583, definitions copied VERBATIM with `file:line` per block; doc
comments and proofs are not copied.  `ByteArray.copyWithin`'s `@[extern "lean_zip_byte_array_copy_within"]`
attribute line is left out (its body, the reference definition, is copied; the rules here forbid `extern`).  The
entry points (`…E : ByteArray → ByteArray`) fix the other arguments; they are not library code. -/
import Riscv.Frontx.WpCmd

namespace Zip.Native.InflateBuf
-- Zip/Native/InflateFast.lean:596@7e10583
def storedCopyLoop (output bytes : ByteArray) (outPos start len : Nat) : ByteArray :=
  if start < len then
    storedCopyLoop (output.set! (outPos + start) (bytes.get! start)) bytes outPos (start + 1) len
  else output
termination_by len - start
decreasing_by omega
end Zip.Native.InflateBuf

namespace ByteArray
-- Zip/Native/CopyWithin.lean:37@7e10583
def copyWithin (a : ByteArray) (srcOff len : Nat) : ByteArray :=
  a ++ a.extract srcOff (srcOff + len)
end ByteArray

namespace Zip.Native.Inflate
-- Zip/Native/Inflate.lean:710@7e10583
def copyLoopGo (buf : ByteArray) (start distance : Nat)
    (k length : Nat)
    (hd_pos : distance > 0 := by omega) (hsd : start + distance ≤ buf.size := by omega) : ByteArray :=
  if k < length then
    have hidx : start + (k % distance) < buf.size := by
      have := Nat.mod_lt k hd_pos; omega
    copyLoopGo (buf.push buf[start + (k % distance)]) start distance (k + 1) length
      hd_pos (by simp [ByteArray.size_push]; omega)
  else buf
termination_by length - k
end Zip.Native.Inflate

namespace Proven.WA.LeanZip2
open Proven.WA

/-- the input's bytes written again from its middle on (`storedCopyLoop xs xs (n / 2) 0 n`; writes past the end are
dropped by `set!`) -/
def storedCopyE (xs : ByteArray) : ByteArray :=
  Zip.Native.InflateBuf.storedCopyLoop xs xs (xs.size >>> 1) 0 xs.size
wp_compile storedCopyE max 1048576
  invariant fun (_output bytes : ByteArray) (outPos start len : Nat) =>
    start ≤ len ∧ len < 2 ^ 32 ∧ outPos < 2 ^ 32
  measure fun (_output _bytes : ByteArray) (_outPos start len : Nat) => len - start

/-- `xs.copyWithin (n / 4) (n / 2)`: `xs ++ xs.extract (n / 4) (n / 4 + n / 2)` -/
def copyWithinE (xs : ByteArray) : ByteArray := xs.copyWithin (xs.size >>> 2) (xs.size >>> 1)
wp_compile copyWithinE max 524288

/-- an LZ77 back-reference: `n` bytes copied from distance `n % 7 + 1` behind the end of `xs ++ [0]` -/
def copyLoopGoE (xs : ByteArray) : ByteArray :=
  Zip.Native.Inflate.copyLoopGo (xs.push 0) (xs.size + 1 - (xs.size % 7 + 1)) (xs.size % 7 + 1) 0 xs.size
    (by omega) (by simp [ByteArray.size_push]; omega)
wp_compile copyLoopGoE max 524287
  invariant fun (buf : ByteArray) (start distance k length : Nat) =>
    0 < distance ∧ start + distance ≤ buf.size ∧ k ≤ length ∧ buf.size + (length - k) ≤ 1048576 ∧
      length < 2 ^ 32 ∧ start < 2 ^ 32 ∧ distance < 2 ^ 32
  measure fun (_buf : ByteArray) (_start _distance k length : Nat) => length - k

end Proven.WA.LeanZip2
