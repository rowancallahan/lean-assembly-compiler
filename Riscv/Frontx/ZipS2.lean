/- lean-zip Adler-32 (INV row of `Testing/notes/LEANZIP_TARGETS.md` @ origin/leanzip-targets), list front end.
Source: github.com/kim-em/lean-zip @ 7e10583, copied VERBATIM (doc comments dropped, nothing else changed), `file:line`
per block.  The `requires` / `with` clauses are the human input of `PairExamples.lean` (same lines, same bounds).
The entry `adlerE` fixes the other argument (zlib's `adler32(1, xs)`) and is glue. -/
import Riscv.Frontx.Impl1
import Riscv.Frontx.DataExamples
import Riscv.Frontx.BookExamples

namespace Adler32.Spec
-- Zip/Spec/Adler32.lean:20@7e10583
def MOD_ADLER : Nat := 65521
-- Zip/Spec/Adler32.lean:23@7e10583
abbrev State := Nat × Nat
-- Zip/Spec/Adler32.lean:29@7e10583
def updateByte (s : State) (byte : UInt8) : State :=
  let a := (s.1 + byte.toNat) % MOD_ADLER
  let b := (s.2 + a) % MOD_ADLER
  (a, b)
-- Zip/Spec/Adler32.lean:39@7e10583
def pack (s : State) : UInt32 :=
  (UInt32.ofNat s.2 <<< 16) ||| UInt32.ofNat s.1
-- Zip/Spec/Adler32.lean:47@7e10583
def unpack (v : UInt32) : State :=
  (v.toNat % 65536, v.toNat / 65536)
end Adler32.Spec

namespace Adler32.Native
-- Zip/Native/Adler32.lean:13@7e10583
def updateBytes (s : Spec.State) (data : ByteArray) : Spec.State :=
  data.data.foldl Spec.updateByte s
-- Zip/Native/Adler32.lean:17@7e10583
def adler32 (init : UInt32 := 1) (data : ByteArray) : UInt32 :=
  let s := Spec.unpack init
  let s' := updateBytes s data
  Spec.pack s'
end Adler32.Native

namespace Proven.Frontx.ZipS2
open Proven Proven.Frontx

frontx_compile Adler32.Spec.pack
frontx_compile Adler32.Spec.unpack
frontx_compile Adler32.Spec.updateByte requires fun s _ => s.1 < 65521 ∧ s.2 < 65521
frontx_compile Adler32.Native.updateBytes requires fun s _ => s.1 < 65521 ∧ s.2 < 65521
  with fun _ _ _ a b => a < 65521 ∧ b < 65521
frontx_compile Adler32.Native.adler32 requires fun init _ => init.toNat % 65536 < 65521 ∧ init.toNat / 65536 < 65521
  with fun _ _ _ a b => a < 65521 ∧ b < 65521

/-- zlib's `adler32(1, xs)` -/
def adlerE (xs : ByteArray) : UInt32 := Adler32.Native.adler32 1 xs
frontx_entry adlerE
frontx_implements adlerE

end Proven.Frontx.ZipS2
