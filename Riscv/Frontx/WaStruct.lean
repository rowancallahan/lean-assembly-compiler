/- User structures on the word-array path (NOTES section 32): lean-zip's `DecodeTable` (a structure whose field is
an `Array UInt32`) as the parameter of its readers `entryAt`, `lenAt`, `symAt` (rows STR 1-3 of LEANZIP_TARGETS.md).
`wa_compile` splits `let t : S := S.mk a…` into one `let` per field and reduces the projections of the constructor.

Source: github.com/rowancallahan/lean-zip @ 7e10583, copied VERBATIM with `file:line` per block; doc comments are
dropped, nothing else is changed.  `WaStructGlue.tbl` (a 256-slot table packed with lean-zip's own `packEntry`) and
the entry points `…E` are glue, not library code. -/
import Riscv.Frontx.WaCmd
-- Lean 4.34.1: instance arguments are compared at restricted transparency; the generated proofs need the old check
set_option backward.isDefEq.respectTransparency false

namespace Zip.Native
namespace HuffTree
-- Zip/Native/Inflate.lean:190@7e10583
@[inline] def packEntry (sym : UInt16) (len : UInt8) : UInt32 :=
  len.toUInt32 ||| (sym.toUInt32 <<< 8)
-- Zip/Native/Inflate.lean:194@7e10583
@[inline] def unpackSym (e : UInt32) : UInt16 := (e >>> 8).toUInt16
-- Zip/Native/Inflate.lean:198@7e10583
@[inline] def unpackLen (e : UInt32) : UInt8 := e.toUInt8
-- Zip/Native/Inflate.lean:221@7e10583
structure DecodeTable where
  packed : Array UInt32
-- Zip/Native/Inflate.lean:228@7e10583
@[inline] def DecodeTable.lenAt (t : DecodeTable) (idx : Nat) : UInt8 :=
  if h : idx < t.packed.size then unpackLen (t.packed[idx]'h) else 0
-- Zip/Native/Inflate.lean:234@7e10583
@[inline] def DecodeTable.symAt (t : DecodeTable) (idx : Nat) : UInt16 :=
  if h : idx < t.packed.size then unpackSym (t.packed[idx]'h) else 0
-- Zip/Native/Inflate.lean:260@7e10583
@[inline] def DecodeTable.entryAt (t : DecodeTable) (idx : Nat) : UInt32 :=
  if h : idx < t.packed.size then t.packed[idx]'h else 0
end HuffTree
end Zip.Native

namespace WaStructGlue
/-- glue: a 256-slot table, slot `i` = `packEntry (7 i mod 2^16) (i mod 16)` -/
def tbl : Zip.Native.HuffTree.DecodeTable :=
  ⟨Array.ofFn fun (i : Fin 256) => Zip.Native.HuffTree.packEntry (UInt16.ofNat (i.val * 7)) (UInt8.ofNat (i.val % 16))⟩
end WaStructGlue

namespace Proven.WA.Struct
open Proven.WA WaStructGlue

/-- the slot at `xs[0] + xs[1]` (in range up to 255, out of range from 256 on: `0`) -/
def entryAtE (xs : ByteArray) : UInt32 := tbl.entryAt (xs.data[0]!.toNat + xs.data[1]!.toNat)
wa_compile entryAtE
def lenAtE (xs : ByteArray) : UInt8 := tbl.lenAt (xs.data[0]!.toNat + xs.data[1]!.toNat)
wa_compile lenAtE
def symAtE (xs : ByteArray) : UInt16 := tbl.symAt (xs.data[0]!.toNat + xs.data[1]!.toNat)
wa_compile symAtE

end Proven.WA.Struct
