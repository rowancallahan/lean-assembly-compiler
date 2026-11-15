import Orig
/- Executed-Lean test cases for the ORIGINAL lean-zip functions (`Orig.lean`), written to `Testing/leanzip/cases/<name>.cases`,
one case per line: `<input bytes hex, - = empty> <result bytes hex>` (format of `Testing/asm/frontx-words/*.cases`).
Entry conventions (what a future compiled entry point must compute from the single input block `xs`):
  adler      Adler32.Native.adler32 1 xs                                  UInt32, 4 bytes LE
  crc        Crc32.Native.crc32 0 xs                                      UInt32, 4 bytes LE
  readbits   ZipCommon.BitReader.readBits ⟨xs, 0, 3⟩ 13                   tag(1: ok, 0: error) val(u32) pos(u64) bitOff(u64), LE; error: all 0
  readbitsfast  Zip.Native.readBitsFast ⟨xs, 0, 3⟩ 13                    same encoding
  decodesym  xs = bitBuf(8 bytes LE) cnt(1 byte) table(2048 × u32 LE); decodeSym .empty ⟨table⟩ bitBuf cnt
             tag(1) sym(u16) bitBuf(u64) cnt(u64) used(u64); error: tag 0, rest 0   (tree = `.empty`: fallback = error)
  countmatch Zip.Native.countMatchGo xs 0 4 0 (xs.size - 4)               Nat, 8 bytes LE (inputs of size ≥ 4)
  copyloop   xs = d(1) len(1) buf(…), d ≥ 1, d ≤ |buf|: copyLoop buf (|buf| - d) d 0 len     the resulting ByteArray
  decodestored  decodeStored ⟨xs, 0, 3⟩ ByteArray.empty 2^30             tag(1) pos(u64) bitOff(u64) output bytes; error: tag 0 only
Run: `Testing/leanzip/run.sh cases`. -/
open Orig Zip.Native

def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
def le (n bytes : Nat) : List UInt8 := (List.range bytes).map fun k => UInt8.ofNat (n / 256 ^ k % 256)
def genIn (i : Nat) : List UInt8 :=
  let L := if i % 9 = 0 then rnd i 7 % 3000 else rnd i 99 % 70
  (List.range L).map fun j => UInt8.ofNat (match i % 4 with
    | 0 => rnd i j % 256 | 1 => rnd i j % 12 | 2 => (j * 37) % 256 | _ => 255 - rnd i j % 5)
def general : List (List UInt8) :=
  [[], [0], [255], [3, 3], [9, 200], [1, 2], [255, 255], [7, 1, 2, 3, 4], "123456789".toUTF8.data.toList,
   List.replicate 64 255, List.replicate 64 0] ++ (List.range 60).map genIn
def periodic : List (List UInt8) :=
  (List.range 40).map fun i =>
    let L := 4 + rnd i 5 % (if i % 7 = 0 then 900 else 40)
    let per := 1 + rnd i 3 % 8
    let br := rnd i 11 % (L + 1)
    (List.range L).map fun j => UInt8.ofNat (if j = br then 77 else (j % per) * 31 + 5)
def ba (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩

def encBR : Except String (UInt32 × ZipCommon.BitReader) → List UInt8
  | .ok (v, br) => 1 :: le v.toNat 4 ++ le br.pos 8 ++ le br.bitOff 8
  | .error _ => List.replicate 21 0
def huffIn : List (List UInt8) :=
  (List.range 40).map fun i =>
    let w (k : Nat) : List UInt8 :=
      let r := rnd i (k + 1000)
      let len := if r % 5 = 0 then 0 else 1 + (r / 5) % 15
      let e := ((r / 97) % 288) * 256 + len
      [UInt8.ofNat e, UInt8.ofNat (e / 256), UInt8.ofNat (e / 65536), 0]
    (List.range 8).map (fun j => UInt8.ofNat (rnd i (j + 500) % 256)) ++ [UInt8.ofNat (rnd i 77 % 65)] ++ (List.range 2048).flatMap w
def decSym (xs : List UInt8) : List UInt8 :=
  let bitBuf := (List.range 8).foldr (fun k a => a * 256 + (xs.getD k 0).toNat) 0
  let table : Array UInt32 := (Array.range 2048).map fun k =>
    UInt32.ofNat ((List.range 4).foldr (fun j a => a * 256 + (xs.getD (9 + 4 * k + j) 0).toNat) 0)
  match InflateBuf.decodeSym .empty ⟨table⟩ (UInt64.ofNat bitBuf) (xs.getD 8 0).toNat with
  | .ok (s, bb, c, u) => 1 :: le s.toNat 2 ++ le bb.toNat 8 ++ le c 8 ++ le u 8
  | .error _ => List.replicate 27 0
def copyIn : List (List UInt8) :=
  (List.range 60).map fun i =>
    let n := 1 + rnd i 3 % (if i % 5 = 0 then 300 else 20)
    let d := 1 + rnd i 5 % n
    [UInt8.ofNat d, UInt8.ofNat (rnd i 9 % 256)] ++ (List.range n).map fun j => UInt8.ofNat (rnd i (j + 40) % 256)
def copyRun (xs : List UInt8) : List UInt8 :=
  let d := (xs.getD 0 1).toNat; let len := (xs.getD 1 0).toNat; let buf := ba (xs.drop 2)
  if h : 1 ≤ d ∧ d ≤ buf.size then
    (Inflate.copyLoop buf (buf.size - d) d 0 len (by omega) (by omega)).data.toList else []
def storedIn : List (List UInt8) :=
  (List.range 40).map fun i =>
    let n := rnd i 3 % (if i % 6 = 0 then 3000 else 40)
    let nlen := if i % 7 = 3 then (n + 1) % 65536 else 65535 - n
    let cut := if i % 8 = 5 then n / 2 else 0
    ([UInt8.ofNat (rnd i 1 % 8 / 2 * 2)] ++ le n 2 ++ le nlen 2 ++ (List.range (n - cut)).map fun j => UInt8.ofNat (rnd i (j + 8) % 256))
def storedRun (xs : List UInt8) : List UInt8 :=
  -- the 3 header bits are skipped by aligning: the reader starts at bit 3 of byte 0, `decodeStored` aligns to byte 1
  match Inflate.decodeStored ⟨ba xs, 0, 3⟩ ByteArray.empty (2 ^ 30) with
  | .ok (out, br) => 1 :: le br.pos 8 ++ le br.bitOff 8 ++ out.data.toList
  | .error _ => [0]

def emit (name : String) (ins : List (List UInt8)) (f : List UInt8 → List UInt8) : IO Unit := do
  IO.FS.createDirAll "Testing/leanzip/cases"
  IO.FS.writeFile s!"Testing/leanzip/cases/{name}.cases" (String.join (ins.map fun xs => s!"{hx xs} {hx (f xs)}\n"))
#eval emit "adler" general fun xs => le (Adler32.Native.adler32 1 (ba xs)).toNat 4
#eval emit "crc" general fun xs => le (Crc32.Native.crc32 0 (ba xs)).toNat 4
#eval emit "readbits" (general.filter (·.length ≥ 1)) fun xs => encBR (ZipCommon.BitReader.readBits ⟨ba xs, 0, 3⟩ 13)
#eval emit "readbitsfast" (general.filter (·.length ≥ 1)) fun xs => encBR (readBitsFast ⟨ba xs, 0, 3⟩ 13)
#eval emit "decodesym" huffIn decSym
#eval emit "countmatch" ((general ++ periodic).filter (·.length ≥ 4)) fun xs =>
  if h : 4 ≤ (ba xs).size then le (countMatchGo (ba xs) 0 4 0 ((ba xs).size - 4) (by omega) (by omega)) 8 else []
#eval emit "copyloop" copyIn copyRun
#eval emit "decodestored" storedIn storedRun
