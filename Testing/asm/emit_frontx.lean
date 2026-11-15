import Riscv.Frontx.Machine
import Riscv.Frontx.RecExamples
import Riscv.Frontx.PairExamples
open Proven Proven.Frontx Proven.Frontx.Ex
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64
/-- the test inputs: fixed ones, then pseudo-random lengths and bytes (some up to 3000 bytes) -/
def inputs : List (List UInt8) :=
  [[], [0], [255], [3, 3], [9, 200], [10], [1, 2, 3, 4, 5, 6, 7], "123456789".toUTF8.data.toList,
   "The quick brown fox\njumps over the lazy dog".toUTF8.data.toList, List.replicate 64 255] ++
  (List.range 40).map fun i =>
    let L := if i % 9 = 0 then rnd i 7 % 3000 else rnd i 99 % 70
    (List.range L).map fun j => UInt8.ofNat (match i % 4 with
      | 0 => rnd i j % 256 | 1 => rnd i j % 12 | 2 => (j * 37) % 256 | _ => 255 - rnd i j % 5)
-- inputs of the `Nat` book functions: two 16-bit little-endian numbers (small: the book's recursions are slow in
-- the interpreter, e.g. `times` through `plus`), and some large ones (`large`)
def le16b (n : Nat) : List UInt8 := [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256 % 256)]
def natInputs (large : Bool) : List (List UInt8) :=
  ([(0, 0), (0, 1), (1, 0), (1, 1), (2, 3), (3, 2), (7, 7), (255, 1), (256, 255), (300, 299)] ++
    (List.range 30).map (fun i => (rnd i 3 % 301, rnd i 5 % 301)) ++
    (if large then [(65535, 65535), (65535, 0), (0, 65535), (40000, 50000), (65534, 65535)] else [])).map
    fun (a, b) => le16b a ++ le16b b
/-- `name.words`: first line the number of slots (work space = `8 * (slots + 1) + 7`), then the code words;
`name.cases`: per line the input bytes and the result bytes as computed by Lean (`#eval` of the function) -/
def emit (name : String) (slots : Nat) (code : List (BitVec 32)) (f : ByteArray → List UInt8)
    (inputs : List (List UInt8) := inputs) : IO Unit := do
  IO.FS.createDirAll "Testing/asm/frontx-words"
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words" (String.intercalate "\n" (toString slots :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases"
    (String.join (inputs.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
def enc {β : Type} [Res β] (f : ByteArray → β) : ByteArray → List UInt8 := fun xs => Res.enc (f xs)
#eval emit "crcraw" crcRaw.slots crcRaw.code (enc crcRaw)
#eval emit "b64all" b64All.slots b64All.code (enc b64All)
#eval emit "findnl" findNL.slots findNL.code (enc findNL)
#eval emit "be32at0" be32At0.slots be32At0.code (enc be32At0)
#eval emit "tailsum" Proven.Frontx.BookList.tailSum.slots tailSum.code (enc Proven.Frontx.BookList.tailSum)
#eval emit "nontailsum" Proven.Frontx.BookList.nonTailSum.slots nonTailSum.code (enc Proven.Frontx.BookList.nonTailSum)
#eval emit "taillength" Proven.Frontx.BookList.tailLength.slots tailLength.code (enc Proven.Frontx.BookList.tailLength)
#eval emit "booklength" Proven.Frontx.BookList.bookLength.slots bookLength.code (enc Proven.Frontx.BookList.bookLength)
open Proven.Frontx.BookOut in
#eval do
  emit "take5" take5.slots Proven.Frontx.Ex.take5.code take5
  emit "drop5" drop5.slots Proven.Frontx.Ex.drop5.code drop5
  emit "matchdrop3" matchDrop3.slots Proven.Frontx.Ex.matchDrop3.code matchDrop3
  emit "filterall" filterAll.slots Proven.Frontx.Ex.filterAll.code filterAll
  emit "inceach" incEach.slots Proven.Frontx.Ex.incEach.code incEach
  emit "twice" twice.slots Proven.Frontx.Ex.twice.code twice
  emit "headof" headOf.slots Proven.Frontx.Ex.headOf.code (enc headOf)
  emit "finalof" finalOf.slots Proven.Frontx.Ex.finalOf.code (enc finalOf)
  emit "findfirstgt3" findFirstGt3.slots Proven.Frontx.Ex.findFirstGt3.code (enc findFirstGt3)
open Proven.Frontx.Ex.BookNat in
#eval do
  emit "add1e" add1E.slots add1E.code (enc add1E) (natInputs true)
  emit "maximume" maximumE.slots maximumE.code (enc maximumE) (natInputs true)
  emit "iszeroe" isZeroE.slots isZeroE.code (enc isZeroE) (natInputs true)
  emit "prede" predE.slots predE.code (enc predE) (natInputs true)
  emit "evene" evenE.slots evenE.code (enc evenE) (natInputs false)
  emit "pluse" plusE.slots plusE.code (enc plusE) (natInputs false)
  emit "timese" timesE.slots timesE.code (enc timesE) (natInputs false)
  emit "minuse" minusE.slots minusE.code (enc minusE) (natInputs false)
  emit "doublee" doubleE.slots doubleE.code (enc doubleE) (natInputs false)
  emit "natdoublee" natDoubleE.slots natDoubleE.code (enc natDoubleE) (natInputs true)
  emit "triplee" tripleE.slots tripleE.code (enc tripleE) (natInputs true)
  emit "quadruplee" quadrupleE.slots quadrupleE.code (enc quadrupleE) (natInputs true)
  emit "timestwelvee" timesTwelveE.slots timesTwelveE.code (enc timesTwelveE) (natInputs true)
  emit "dive" divE.slots divE.code (enc divE) (natInputs false)
  emit "halvee" halveE.slots halveE.code (enc halveE) (natInputs false)

#eval emit "dupcount" Proven.Frontx.Calls.dupCount.slots dupCount.code (enc Proven.Frontx.Calls.dupCount)
#eval emit "samelen" Proven.Frontx.Calls.sameLen.slots sameLen.code (enc Proven.Frontx.Calls.sameLen)
#eval emit "nontaillength" Proven.Frontx.BookList.nonTailLength.slots nonTailLength.code (enc Proven.Frontx.BookList.nonTailLength)
open Proven.Frontx.Ex.BookNat in
#eval do
  emit "matchevene" matchEvenE.slots matchEvenE.code (enc matchEvenE) (natInputs false)
  emit "explicithalvee" explicitHalveE.slots explicitHalveE.code (enc explicitHalveE) (natInputs false)

-- real calls (`frontx_rec`, `RecExamples.lean`): first line `rec <frame bytes>`, work space `frame * (n + 1) + 32`
def emitRec (name : String) (frame : Nat) (code : List (BitVec 32)) (f : ByteArray → List UInt8)
    (inputs : List (List UInt8) := inputs) : IO Unit := do
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words" (String.intercalate "\n" (s!"rec {frame}" :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases"
    (String.join (inputs.map fun xs => s!"{hx xs} {hx (f ⟨xs.toArray⟩)}\n"))
#eval emitRec "nontailsumrec" 88 Proven.Frontx.BookList.nonTailSumRec.code (enc Proven.Frontx.BookList.nonTailSumRec)
#eval emitRec "nontaillengthrec" 80 Proven.Frontx.BookList.nonTailLengthRec.code (enc Proven.Frontx.BookList.nonTailLengthRec)
-- `fib` of the length: lengths 0 .. 16 (the Sail memory trace of the test grows with the number of calls)
#eval emitRec "fiblen" 96 Proven.Frontx.RecEx.fibLen.code (enc Proven.Frontx.RecEx.fibLen)
  ((List.range 50).map fun i => List.replicate (i % 17) (UInt8.ofNat i))
-- round 6: tuples / structures (results as the components' bytes, `g.enc`), lean-zip Adler-32 verbatim
open Proven.Frontx.Pairs in
#eval do
  emit "adlere" adlerE.slots adlerE.code (enc adlerE)
  emit "adlerstatee" adlerStateE.slots adlerStateE.code (fun xs => adlerStateE.enc (adlerStateE xs))
  emit "replacexe" replaceXE.slots replaceXE.code (fun xs => replaceXE.enc (replaceXE xs)) (natInputs true)
  emit "fromoptione" fromOptionE.slots fromOptionE.code (enc fromOptionE)
  emit "smalle" smallE.slots smallE.code (enc smallE)
  emit "swape" swapE.slots swapE.code (fun xs => swapE.enc (swapE xs))
  emit "addpointse" addPointsE.slots addPointsE.code (fun xs => addPointsE.enc (addPointsE xs))
  emit "zeroxe" zeroXE.slots zeroXE.code (fun xs => zeroXE.enc (zeroXE xs))
  emit "neste" nestE.slots nestE.code (fun xs => nestE.enc (nestE xs))
