/- User structures (NOTES section 32): constructors, field projections and `{ s with f := v }` of lean-svg structures,
compiled by `frontx_compile` on the library definitions themselves (a constructor `S.mk` and a projection `S.f` are
functions of their own: `Rgba.mk` and `Rgba.r` are rows of LEANSVG_TARGETS.md).

Source: github.com/rowancallahan/lean-svg @ df8e663, copied VERBATIM with `file:line` per block; doc comments are
dropped, nothing else is changed.  The `…At` / `…E` functions are entry glue (they read the arguments from the input
bytes), not library code. -/
import Legacy.Riscv.Frontx.Impl1
import Legacy.Riscv.Frontx.PairExamples

namespace LeanSvg

-- LeanSvg/Canvas.lean:16@df8e663
structure Rgba where
  r : Nat
  g : Nat
  b : Nat
  a : Nat
deriving Repr, Inhabited, BEq

-- LeanSvg/Canvas.lean:23@df8e663
structure Canvas where
  w : Nat
  h : Nat
  px : Array Nat
deriving Inhabited

namespace PngDecode
-- LeanSvg/PngDecode.lean:43@df8e663
structure Hdr where
  w : Nat
  h : Nat
  depth : Nat
  ctype : Nat
  interlace : Bool
end PngDecode

namespace Css
-- LeanSvg/Css.lean:46@df8e663
inductive AttrOp where
  | exists_
  | eq (v : String)
  | contains (v : String)        -- `~=`: one of the space-separated words
  | startsWithDash (v : String)  -- `|=`: exactly `v`, or `v` followed by `-`
deriving Repr, BEq, Inhabited

-- LeanSvg/Css.lean:53@df8e663
structure Compound where
  hasType : Bool := false
  typeName : String := ""
  id : Option String := none
  classes : Array String := #[]
  attrs : Array (String × AttrOp) := #[]
  firstChild : Bool := false
  valid : Bool := true
deriving Repr, BEq, Inhabited
end Css

namespace Shape
-- LeanSvg/Shape.lean:64@df8e663
structure GInfo where
  cp : Nat := 0
  gid : Nat := 0
  cluster : Nat := 0
  mask : Nat := 0
  gc : Nat := 0
  ccc : Nat := 0
  uflags : Nat := 0
  gprops : Nat := 0
  lig : Nat := 0
  syl : Nat := 0
  cat : Nat := 0
  ipos : Nat := 0
  ngid : Nat := 0
deriving Inhabited, Repr

-- LeanSvg/Shape.lean:107@df8e663
namespace GInfo
def isIgnorable (g : GInfo) : Bool := g.uflags &&& 0x20 != 0 && g.gprops &&& 0x10 == 0
def isHidden (g : GInfo) : Bool := g.uflags &&& 0x40 != 0
def isContinuation (g : GInfo) : Bool := g.uflags &&& 0x80 != 0
def isZwj (g : GInfo) : Bool := g.gc == 1 && g.uflags &&& 0x100 != 0
def isZwnj (g : GInfo) : Bool := g.gc == 1 && g.uflags &&& 0x200 != 0
def isUnicodeMark (g : GInfo) : Bool := g.gc == 10 || g.gc == 11 || g.gc == 12
def ligId (g : GInfo) : Nat := g.lig >>> 5
def ligatedInternal (g : GInfo) : Bool := g.lig &&& 0x10 != 0
def ligComp (g : GInfo) : Nat := if g.ligatedInternal then 0 else g.lig &&& 0x0F
def ligNumComps (g : GInfo) : Nat :=
  if g.gprops &&& 4 != 0 && g.ligatedInternal then g.lig &&& 0x0F else 1
def isBase (g : GInfo) : Bool := g.gprops &&& 2 != 0
def isLigature (g : GInfo) : Bool := g.gprops &&& 4 != 0
def isMark (g : GInfo) : Bool := g.gprops &&& 8 != 0
def substituted (g : GInfo) : Bool := g.gprops &&& 0x10 != 0
def ligated (g : GInfo) : Bool := g.gprops &&& 0x20 != 0
def multiplied (g : GInfo) : Bool := g.gprops &&& 0x40 != 0
def ligatedAndDidntMultiply (g : GInfo) : Bool := g.ligated && !g.multiplied
def setLigForLigature (g : GInfo) (id n : Nat) : GInfo :=
  { g with lig := (id % 8) <<< 5 ||| 0x10 ||| (n &&& 0x0F) }
def setLigForMark (g : GInfo) (id comp : Nat) : GInfo :=
  { g with lig := (id % 8) <<< 5 ||| (comp &&& 0x0F) }
end GInfo
end Shape

end LeanSvg

namespace Proven.Frontx.Structs
open Proven Proven.Frontx Proven.Frontx.Book LeanSvg

/-! ## The library definitions themselves (source level: `f.exec`) -/

-- constructors (LEANSVG_TARGETS §1.1 `Rgba.mk`, `PngDecode.Hdr.mk`)
frontx_compile LeanSvg.Rgba.mk
frontx_compile LeanSvg.PngDecode.Hdr.mk
-- projections (§1.5 `Rgba.r` … `PngDecode.Hdr.interlace`, `Shape.GInfo.lig` …; §1.2 `Canvas.w`, `Canvas.h`;
-- §1.1 `Css.Compound.hasType` …: fields that are arrays / strings get no variable)
frontx_compile LeanSvg.Rgba.r
frontx_compile LeanSvg.Rgba.g
frontx_compile LeanSvg.Rgba.b
frontx_compile LeanSvg.Rgba.a
frontx_compile LeanSvg.PngDecode.Hdr.w
frontx_compile LeanSvg.PngDecode.Hdr.h
frontx_compile LeanSvg.PngDecode.Hdr.depth
frontx_compile LeanSvg.PngDecode.Hdr.ctype
frontx_compile LeanSvg.PngDecode.Hdr.interlace
frontx_compile LeanSvg.Canvas.w
frontx_compile LeanSvg.Canvas.h
frontx_compile LeanSvg.Css.Compound.hasType
frontx_compile LeanSvg.Css.Compound.firstChild
frontx_compile LeanSvg.Css.Compound.valid
frontx_compile LeanSvg.Shape.GInfo.cp
frontx_compile LeanSvg.Shape.GInfo.gc
frontx_compile LeanSvg.Shape.GInfo.lig
frontx_compile LeanSvg.Shape.GInfo.gprops
frontx_compile LeanSvg.Shape.GInfo.ngid
-- functions over a 13-field structure, and `{ g with lig := … }` (a 13-component result)
frontx_compile LeanSvg.Shape.GInfo.isIgnorable
frontx_compile LeanSvg.Shape.GInfo.ligNumComps
frontx_compile LeanSvg.Shape.GInfo.ligatedAndDidntMultiply
frontx_compile LeanSvg.Shape.GInfo.setLigForLigature
frontx_compile LeanSvg.Shape.GInfo.setLigForMark

/-! ## Entry points with machine theorems (glue: the arguments are bytes / 16-bit numbers of the input) -/

def rgbaAt (xs : ByteArray) (i : Nat) : Rgba :=
  Rgba.mk (byteAt xs i).toNat (byteAt xs (i + 1)).toNat (byteAt xs (i + 2)).toNat (byteAt xs (i + 3)).toNat
def hdrAt (xs : ByteArray) (i : Nat) : PngDecode.Hdr :=
  PngDecode.Hdr.mk (u16 xs i) (u16 xs (i + 2)) (byteAt xs (i + 4)).toNat (byteAt xs (i + 5)).toNat (byteAt xs (i + 6) == 1)
def rgbaGAt (xs : ByteArray) (i : Nat) : Nat :=
  Rgba.g ⟨(byteAt xs i).toNat, (byteAt xs (i + 1)).toNat, (byteAt xs (i + 2)).toNat, (byteAt xs (i + 3)).toNat⟩
def interlaceAt (xs : ByteArray) (i : Nat) : Bool :=
  PngDecode.Hdr.interlace ⟨u16 xs i, u16 xs (i + 2), 8, 6, byteAt xs (i + 4) == 1⟩
def canvasHAt (xs : ByteArray) (i : Nat) : Nat := Canvas.h ⟨u16 xs i, u16 xs (i + 2), #[1, 2, 3]⟩
def compoundValidAt (xs : ByteArray) (i : Nat) : Bool :=
  Css.Compound.valid
    { hasType := byteAt xs i == 1
      typeName := "rect"
      classes := #["a", "b"]
      firstChild := byteAt xs (i + 1) == 1
      valid := byteAt xs (i + 2) != 0 }
/-- a glyph record: five fields from the input, the others their defaults -/
def gAt (xs : ByteArray) (i : Nat) : Shape.GInfo :=
  { cp := (byteAt xs i).toNat, gc := (byteAt xs (i + 1)).toNat, uflags := u16 xs (i + 2), gprops := (byteAt xs (i + 4)).toNat,
    lig := (byteAt xs (i + 5)).toNat }
def setLigAt (xs : ByteArray) (i : Nat) : Shape.GInfo :=
  Shape.GInfo.setLigForLigature (gAt xs i) (byteAt xs (i + 6)).toNat (byteAt xs (i + 7)).toNat
def ligNumCompsAt (xs : ByteArray) (i : Nat) : Nat := Shape.GInfo.ligNumComps (gAt xs i)
def isIgnorableAt (xs : ByteArray) (i : Nat) : Bool := Shape.GInfo.isIgnorable (gAt xs i)
/-- a tuple of two structures -/
def rgbaHdrAt (xs : ByteArray) (i : Nat) : Rgba × PngDecode.Hdr := (rgbaAt xs i, hdrAt xs (i + 4))

frontx_compile rgbaAt requires fun _ i => i + 16 < 2 ^ 64
frontx_compile hdrAt requires fun _ i => i + 16 < 2 ^ 64
frontx_compile rgbaGAt requires fun _ i => i + 16 < 2 ^ 64
frontx_compile interlaceAt requires fun _ i => i + 16 < 2 ^ 64
frontx_compile canvasHAt requires fun _ i => i + 16 < 2 ^ 64
frontx_compile compoundValidAt requires fun _ i => i + 16 < 2 ^ 64
set_option maxHeartbeats 2000000 in
frontx_compile setLigAt requires fun _ i => i + 32 < 2 ^ 64
frontx_compile ligNumCompsAt requires fun _ i => i + 32 < 2 ^ 64
frontx_compile isIgnorableAt requires fun _ i => i + 32 < 2 ^ 64
set_option maxHeartbeats 2000000 in
frontx_compile rgbaHdrAt requires fun _ i => i + 32 < 2 ^ 64

def rgbaE (xs : ByteArray) : Rgba := rgbaAt xs 0
frontx_entry rgbaE
frontx_implements_bytes rgbaE
def hdrE (xs : ByteArray) : PngDecode.Hdr := hdrAt xs 0
frontx_entry hdrE
frontx_implements_bytes hdrE
def rgbaGE (xs : ByteArray) : Nat := rgbaGAt xs 0
frontx_entry rgbaGE
frontx_implements rgbaGE
def interlaceE (xs : ByteArray) : Bool := interlaceAt xs 0
frontx_entry interlaceE
frontx_implements interlaceE
def canvasHE (xs : ByteArray) : Nat := canvasHAt xs 0
frontx_entry canvasHE
frontx_implements canvasHE
def compoundValidE (xs : ByteArray) : Bool := compoundValidAt xs 0
frontx_entry compoundValidE
frontx_implements compoundValidE
def setLigE (xs : ByteArray) : Shape.GInfo := setLigAt xs 0
frontx_entry setLigE
frontx_implements_bytes setLigE
def ligNumCompsE (xs : ByteArray) : Nat := ligNumCompsAt xs 0
frontx_entry ligNumCompsE
frontx_implements ligNumCompsE
def isIgnorableE (xs : ByteArray) : Bool := isIgnorableAt xs 0
frontx_entry isIgnorableE
frontx_implements isIgnorableE
def rgbaHdrE (xs : ByteArray) : Rgba × PngDecode.Hdr := rgbaHdrAt xs 0
frontx_entry rgbaHdrE
frontx_implements_bytes rgbaHdrE

end Proven.Frontx.Structs
