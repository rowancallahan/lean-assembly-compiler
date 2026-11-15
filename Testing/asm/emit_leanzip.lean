import Riscv.Frontx.LeanZip
/- Words and cases for the lean-zip kernels of `Riscv/Frontx/LeanZip.lean`.  The expected results are computed by
the REFERENCE functions below, copied from lean-zip (Lean 4.34) with only the changes noted, not by the restatements.
Run: `lake env lean Testing/asm/emit_leanzip.lean`, then `python3 Testing/asm/frontx_test.py check 60 <name>`. -/
open Proven Proven.Frontx Proven.Frontx.LZ

def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64

/-! ### references -/
namespace Ref
-- Zip/Spec/Adler32.lean + Zip/Native/Adler32.lean (`adler32 1`), verbatim
def MOD_ADLER : Nat := 65521
def updateByte (s : Nat × Nat) (byte : UInt8) : Nat × Nat :=
  let a := (s.1 + byte.toNat) % MOD_ADLER
  let b := (s.2 + a) % MOD_ADLER
  (a, b)
def pack (s : Nat × Nat) : UInt32 := (UInt32.ofNat s.2 <<< 16) ||| UInt32.ofNat s.1
def adler32 (data : ByteArray) : Nat := (pack (data.data.foldl updateByte (1, 0))).toNat

-- ZipCommon/BitReader.lean structure and Zip/Native/Inflate.lean `readBitsFast`, verbatim
structure BitReader where
  data : ByteArray
  pos : Nat
  bitOff : Nat
def readBitsFast (br : BitReader) (n : Nat) : Except String (UInt32 × BitReader) :=
  go br.pos br.bitOff 0 0 n
where
  go (pos bitOff : Nat) (acc : UInt32) (shift : Nat) :
      Nat → Except String (UInt32 × BitReader)
    | 0 => .ok (acc, { br with pos := pos, bitOff := bitOff })
    | k + 1 =>
      if h : pos ≥ br.data.size then .error "BitReader: unexpected end of input"
      else
        let bit : UInt32 := (((br.data[pos]'(by omega)).toUInt32 >>> bitOff.toUInt32) &&& 1)
        if bitOff + 1 ≥ 8 then
          go (pos + 1) 0 (acc ||| (bit <<< shift.toUInt32)) (shift + 1) k
        else
          go pos (bitOff + 1) (acc ||| (bit <<< shift.toUInt32)) (shift + 1) k

-- Zip/Native/Inflate.lean: packEntry/unpackSym/unpackLen/DecodeTable.entryAt and the table-hit branch of `decodeSym`
def unpackSym (e : UInt32) : UInt16 := (e >>> 8).toUInt16
def unpackLen (e : UInt32) : UInt8 := e.toUInt8
def entryAt (t : Array UInt32) (idx : Nat) : UInt32 := if h : idx < t.size then t[idx] else 0
def huffSym (data : ByteArray) : Nat :=
  let le32 (i : Nat) : UInt32 := (data.get! i).toUInt32 ||| ((data.get! (i+1)).toUInt32 <<< 8) |||
    ((data.get! (i+2)).toUInt32 <<< 16) ||| ((data.get! (i+3)).toUInt32 <<< 24)
  let bitBuf : UInt64 := (le32 0).toUInt64
  let table : Array UInt32 := (Array.range 2048).map fun k => le32 (8 + 4 * k)
  let idx := (bitBuf &&& 0x7FF).toNat
  let e := entryAt table idx
  let r : UInt32 := if (unpackLen e).toNat == 0 then 0xFFFFFFFF else (unpackSym e).toUInt32 <<< 8 ||| (unpackLen e).toUInt32
  r.toNat

-- Zip/Native/Deflate.lean `lz77Greedy.countMatch.go`, verbatim (hypotheses as parameters)
def go (data : ByteArray) (p1 p2 i maxLen : Nat)
    (h1 : p1 + maxLen ≤ data.size) (h2 : p2 + maxLen ≤ data.size) : Nat :=
  if hi : i < maxLen then
    if (data[p1 + i]'(by omega)) == (data[p2 + i]'(by omega)) then
      go data p1 p2 (i + 1) maxLen h1 h2
    else i
  else i
termination_by maxLen - i
def match04 (xs : ByteArray) : Nat := if h : 4 ≤ xs.size then go xs 0 4 0 (xs.size - 4) (by omega) (by omega) else 0
end Ref

/-! ### inputs -/
def genIn (i : Nat) : List UInt8 :=
  let L := if i % 9 = 0 then rnd i 7 % 3000 else rnd i 99 % 70
  (List.range L).map fun j => UInt8.ofNat (match i % 4 with
    | 0 => rnd i j % 256 | 1 => rnd i j % 12 | 2 => (j * 37) % 256 | _ => 255 - rnd i j % 5)
def fixed : List (List UInt8) :=
  [[], [0], [255], [3, 3], [9, 200], [1, 2], [255, 255], [7, 1, 2, 3, 4], "123456789".toUTF8.data.toList,
   List.replicate 64 255, List.replicate 64 0]
def general : List (List UInt8) := fixed ++ (List.range 60).map genIn
/-- a periodic input with period 4 .. 11 and one broken byte: long matches at distance 4 for period 4 -/
def periodic : List (List UInt8) :=
  (List.range 40).map fun i =>
    let L := 4 + rnd i 5 % (if i % 7 = 0 then 900 else 40)
    let per := 1 + rnd i 3 % 8
    let br := rnd i 11 % (L + 1)
    (List.range L).map fun j => UInt8.ofNat (if j = br then 77 else (j % per) * 31 + 5)
/-- bit reader: at least 2 bytes (the original reports an error otherwise) -/
def rbInputs : List (List UInt8) := general.filter (·.length ≥ 2)
/-- Huffman: 8 bytes of bit buffer and 2048 table words (len 0..15, symbol 0..287, ~1/5 empty slots) -/
def huffInputs : List (List UInt8) :=
  (List.range 40).map fun i =>
    let w (k : Nat) : List UInt8 :=
      let r := rnd i (k + 1000)
      let len := if r % 5 = 0 then 0 else 1 + (r / 5) % 15
      let sym := (r / 97) % 288
      let e := sym * 256 + len
      [UInt8.ofNat e, UInt8.ofNat (e / 256), UInt8.ofNat (e / 65536), 0]
    (List.range 8).map (fun j => UInt8.ofNat (rnd i (j + 500) % 256)) ++ (List.range 2048).flatMap w

def emit (name : String) (slots : Nat) (code : List (BitVec 32)) (ins : List (List UInt8)) (f : ByteArray → List UInt8) : IO Unit := do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words" (String.intercalate "\n" (toString slots :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases" (String.join (ins.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
def enc {β : Type} [Res β] (f : ByteArray → β) : ByteArray → List UInt8 := fun xs => Res.enc (f xs)

#eval emit "lzadler" lzAdler.slots lzAdler.code general (enc Ref.adler32)
#eval emit "lzreadbits" lzReadBits.slots lzReadBits.code rbInputs
  (enc fun xs => match Ref.readBitsFast ⟨xs, 0, 3⟩ 13 with | .ok (v, _) => v | .error _ => 0)
#eval emit "lzhuffsym" huffSym.slots huffSym.code huffInputs (enc Ref.huffSym)
#eval emit "lzmatch04" lzMatch04.slots lzMatch04.code (general ++ periodic) (enc Ref.match04)
