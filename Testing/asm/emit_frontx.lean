import Riscv.Frontx.Machine
import Riscv.Frontx.RecExamples
import Riscv.Frontx.PairExamples
import Riscv.Frontx.ExceptExamples
import Riscv.Frontx.ExceptBook
import Riscv.Frontx.IndExamples
import Riscv.Frontx.Ind2Examples
import Riscv.Frontx.NameExamples
import Riscv.Frontx.ScalarExamples
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
-- round 7: `Except` / `Option` results with payloads (tag byte, payload; zeros when absent), lean-zip-common `BitReader`
open Proven.Frontx.Exc in
#eval do
  emit "readbite" readBitE.slots readBitE.code (fun xs => readBitE.enc (readBitE xs))
  emit "readbitse" readBitsE.slots readBitsE.code (fun xs => readBitsE.enc (readBitsE xs))
  emit "readbits2e" readBits2E.slots readBits2E.code (fun xs => readBits2E.enc (readBits2E xs))
  emit "readbitsfaste" readBitsFastE.slots readBitsFastE.code (fun xs => readBitsFastE.enc (readBitsFastE xs))
  emit "aligne" alignE.slots alignE.code (fun xs => alignE.enc (alignE xs))
  emit "readuint16lee" readUInt16LEE.slots readUInt16LEE.code (fun xs => readUInt16LEE.enc (readUInt16LEE xs))
  emit "readuint16le5e" readUInt16LE5E.slots readUInt16LE5E.code (fun xs => readUInt16LE5E.enc (readUInt16LE5E xs))
  emit "readalignede" readAlignedE.slots readAlignedE.code (fun xs => readAlignedE.enc (readAlignedE xs))
open Proven.Frontx.ExcBook in
#eval do
  emit "optfirstthirde" optFirstThirdE.slots optFirstThirdE.code (fun xs => optFirstThirdE.enc (optFirstThirdE xs))
  emit "optmfirstthirde" optMFirstThirdE.slots optMFirstThirdE.code (fun xs => optMFirstThirdE.enc (optMFirstThirdE xs))
  emit "optparensfirstthirde" optParensFirstThirdE.slots optParensFirstThirdE.code (fun xs => optParensFirstThirdE.enc (optParensFirstThirdE xs))
  emit "optinfixfirstthirde" optInfixFirstThirdE.slots optInfixFirstThirdE.code (fun xs => optInfixFirstThirdE.enc (optInfixFirstThirdE xs))
  emit "errfirste" errFirstE.slots errFirstE.code (fun xs => errFirstE.enc (errFirstE xs))
  emit "errfirstthirde" errFirstThirdE.slots errFirstThirdE.code (fun xs => errFirstThirdE.enc (errFirstThirdE xs))
  emit "errandthenfirstthirde" errAndThenFirstThirdE.slots errAndThenFirstThirdE.code (fun xs => errAndThenFirstThirdE.enc (errAndThenFirstThirdE xs))
  emit "errinfixfirstthirde" errInfixFirstThirdE.slots errInfixFirstThirdE.code (fun xs => errInfixFirstThirdE.enc (errInfixFirstThirdE xs))
-- user inductives as cells (`frontx_ind`, `IndExamples.lean`): first line `ind <A> <B> <L>`, work space `A + B n`
-- (`Proven.Frontx.Ind.space`), `L = 1` for tree results (length in `a1`); inputs: values of the type in its byte format
section
open Proven.Frontx.IndEx
def emitInd (name : String) (code : List (BitVec 32)) (M : Nat) (retLen : Bool) (cases : List (List UInt8 × List UInt8)) :
    IO Unit := do
  let A := Proven.Frontx.Ind.space M 0
  let B := Proven.Frontx.Ind.space M 1 - A
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words"
    (String.intercalate "\n" (s!"ind {A} {B} {if retLen then 1 else 0}" :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases" (String.join (cases.map fun (x, y) => s!"{hx x} {hx y}\n"))
/-- payloads: small, and some at and above `2^64` (the format keeps them mod `2^64`) -/
def payload (i : Nat) : Nat := match i % 7 with
  | 0 => rnd i 1 % 2 ^ 64 | 1 => 2 ^ 64 - 1 | 2 => 2 ^ 64 + 5 | _ => rnd i 2 % 1000
def genT : Nat → Nat → BinTree Nat
  | 0, _ => .leaf
  | d + 1, s => if rnd s d % 4 = 0 then .leaf else .branch (genT d (2 * s + 1)) (payload s) (genT d (2 * s + 2))
def trees : List (BinTree Nat) := [.leaf, .branch .leaf 7 .leaf] ++ (List.range 48).map fun i => genT (i % 6 + 1) (i + 3)
def genP : Nat → Pos | 0 => .one | n + 1 => .succ (genP n)
def poss : List Pos := (List.range 50).map fun i => genP (rnd i 5 % 60)
def lists : List (List Nat) := [[], [3], [2 ^ 64 - 1, 1]] ++ (List.range 47).map fun i =>
  (List.range (rnd i 9 % 25)).map fun j => payload (i * 31 + j)
def genL : Nat → Nat → ConLeche.Level
  | 0, s => if s % 2 = 0 then .zero else .param .anonymous
  | d + 1, s => match rnd s d % 8 with
    | 0 => .zero | 1 => .param .anonymous | 2 | 3 => .succ (genL d (s + 1))
    | 4 | 5 => .max (genL d (2 * s)) (genL d (2 * s + 1)) | _ => .imax (genL d (2 * s)) (genL d (2 * s + 1))
def levels : List ConLeche.Level := (List.range 50).map fun i => genL (i % 9) (i + 1)
def natB (n : Nat) : List UInt8 := leN 8 n
def boolB (b : Bool) : List UInt8 := [if b then 1 else 0]
#eval do
  emitInd "bt_count" BinTree.count.code BinTree.count.ind.pg.M false (trees.map fun t => (BTN.enc t, natB t.count))
  emitInd "bt_mirror" BinTree.mirror.code BinTree.mirror.ind.pg.M true (trees.map fun t => (BTN.enc t, BTN.enc t.mirror))
  emitInd "bt_graftleft" BinTree.graftLeft.code BinTree.graftLeft.ind.pg.M true
    ((List.range 50).map fun i => let p := (trees.getD i .leaf, trees.getD ((i * 7 + 3) % 50) .leaf); (BTN.enc2 p, BTN.enc (p.1.graftLeft p.2)))
  emitInd "pos_tonat" Pos.toNat.code Pos.toNat.ind.pg.M false (poss.map fun p => (PosT.enc p, natB p.toNat))
  emitInd "pos_plus" Pos.plus.code Pos.plus.ind.pg.M true
    ((List.range 50).map fun i => let p := (poss.getD i .one, poss.getD ((i * 7 + 3) % 50) .one); (PosT.enc2 p, PosT.enc (p.1.plus p.2)))
  emitInd "nontail_sum_ln" NonTail.sum.code NonTail.sum.ind.pg.M false (lists.map fun l => (LN.enc l, natB (NonTail.sum l)))
  emitInd "tail_sum_ln" Tail.sum.code Tail.sum.ind.pg.M false (lists.map fun l => (LN.enc l, natB (Tail.sum l)))
  emitInd "tail_reverse_ln" Tail.reverse.code Tail.reverse.ind.pg.M true (lists.map fun l => (LN.enc l, LN.enc (Tail.reverse l)))
  emitInd "list_append_ln" List.append.code List.append.ind.pg.M true
    ((List.range 50).map fun i => let p := (lists.getD i [], lists.getD ((i * 7 + 3) % 50) []); (LN.enc2 p, LN.enc (List.append p.1 p.2)))
  emitInd "level_hasparam" ConLeche.levelHasParam.code ConLeche.levelHasParam.ind.pg.M false
    (levels.map fun l => (LevelT.enc l, boolB (ConLeche.levelHasParam l)))
  emitInd "level_isneverzero" ConLeche.Level.isNeverZero.code ConLeche.Level.isNeverZero.ind.pg.M false
    (levels.map fun l => (LevelT.enc l, boolB (ConLeche.Level.isNeverZero l)))
end
-- conditionals and comparisons (`IndCmpExamples.lean`, NOTES section 19): inputs in the subtype (every `Nat` field
-- below `2^64`); keys small (the key `5` is often present) and some near `2^64` (unsigned comparisons)
section
open Proven.Frontx.IndCmp
def key (i : Nat) : Nat := match i % 9 with
  | 0 => 2 ^ 64 - 1 - rnd i 4 % 3 | 1 => rnd i 1 % 2 ^ 63 + 2 ^ 63 | _ => rnd i 2 % 12
/-- binary search trees built by the book's own `insert` -/
def bsts : List (Tree Unit) := [.leaf, Tree.leaf.insert 5 ()] ++ (List.range 48).map fun i =>
  (List.range (rnd i 8 % 40)).foldl (fun t j => t.insert (key (i * 53 + j)) ()) .leaf
def keyLists : List (List Nat) := [[], [5], [2 ^ 64 - 1, 5, 5]] ++ (List.range 47).map fun i =>
  (List.range (rnd i 9 % 30)).map fun j => key (i * 31 + j)
#eval do
  emitInd "tree_contains5" contains5.code contains5.ind.pg.M false (bsts.map fun t => (TU.enc t, boolB (contains5 t)))
  emitInd "tree_insert5" insert5.code insert5.ind.pg.M true (bsts.map fun t => (TU.enc t, TU.enc (insert5 t)))
  emitInd "list_elem5" elem5.code elem5.ind.pg.M false (keyLists.map fun l => (LN.enc l, boolB (elem5 l)))
  emitInd "list_erase5" erase5.code erase5.ind.pg.M true (keyLists.map fun l => (LN.enc l, LN.enc (erase5 l)))
-- enumerations: every value (every pair), repeated to 50 cases
def days : List Weekday := [.monday, .tuesday, .wednesday, .thursday, .friday, .saturday, .sunday]
def ords : List Ordering := [.lt, .eq, .gt]
def cyc {α : Type} (xs : List α) : List α := (List.range 50).flatMap fun i => (xs.drop (i % xs.length)).take 1
#eval do
  emitInd "weekday_isweekend_a" A.Weekday.isWeekend.code A.Weekday.isWeekend.ind.pg.M false
    ((cyc days).map fun d => (WD.enc d, boolB (A.Weekday.isWeekend d)))
  emitInd "weekday_isweekend_b" B.Weekday.isWeekend.code B.Weekday.isWeekend.ind.pg.M false
    ((cyc days).map fun d => (WD.enc d, boolB (B.Weekday.isWeekend d)))
  emitInd "ordering_swap" Ordering.swap.code Ordering.swap.ind.pg.M true ((cyc ords).map fun o => (OrdT.enc o, OrdT.enc o.swap))
  emitInd "ordering_then" Ordering.then.code Ordering.then.ind.pg.M true
    ((cyc (ords.flatMap fun a => ords.map fun b => (a, b))).map fun p => (OrdT.enc2 p, OrdT.enc (p.1.then p.2)))
  emitInd "ordering_isle" Ordering.isLE.code Ordering.isLE.ind.pg.M false ((cyc ords).map fun o => (OrdT.enc o, boolB o.isLE))
  emitInd "ordering_iseq" Ordering.isEq.code Ordering.isEq.ind.pg.M false ((cyc ords).map fun o => (OrdT.enc o, boolB o.isEq))
end
-- fixed-width scalars (`ScalarExamples.lean`): 64-bit words at byte 0, the saturation edges, then the random inputs
section
open Proven.Frontx.Scal
def le8b (n : Nat) : List UInt8 := (List.range 8).map fun j => UInt8.ofNat (n / 256 ^ j)
def wordInputs : List (List UInt8) :=
  ([0, 1, 2, 32766, 32767, 32768, 65535, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 63, 2 ^ 64 - 1].map le8b) ++ inputs
#eval do
  emit "hashofdatae" hashOfDataE.slots hashOfDataE.code (enc hashOfDataE) wordInputs
  emit "bvarofdatae" bvarOfDataE.slots bvarOfDataE.code (enc bvarOfDataE) wordInputs
  emit "fvarofdatae" fvarOfDataE.slots fvarOfDataE.code (enc fvarOfDataE) wordInputs
  emit "lpofdatae" lpOfDataE.slots lpOfDataE.code (enc lpOfDataE) wordInputs
  emit "hash32e" hash32E.slots hash32E.code (enc hash32E) wordInputs
  emit "satprede" satPredE.slots satPredE.code (enc satPredE) wordInputs
  emit "satsucce" satSuccE.slots satSuccE.code (enc satSuccE) wordInputs
  emit "packdatae" packDataE.slots packDataE.code (enc packDataE) wordInputs
end
-- over 16 slots (19 / 27 / 17; `NS` raised to 254)
open Proven.Frontx.ExcBook in
#eval do
  emit "optfirstthirdfifthe" optFirstThirdFifthE.slots optFirstThirdFifthE.code (fun xs => optFirstThirdFifthE.enc (optFirstThirdFifthE xs))
  emit "optfirstthirdfifthseventhe" optFirstThirdFifthSeventhE.slots optFirstThirdFifthSeventhE.code (fun xs => optFirstThirdFifthSeventhE.enc (optFirstThirdFifthSeventhE xs))
  emit "optmfirstthirdfifthseventhe" optMFirstThirdFifthSeventhE.slots optMFirstThirdFifthSeventhE.code (fun xs => optMFirstThirdFifthSeventhE.enc (optMFirstThirdFifthSeventhE xs))
  emit "errfirstthirdfifthe" errFirstThirdFifthE.slots errFirstThirdFifthE.code (fun xs => errFirstThirdFifthE.enc (errFirstThirdFifthE xs))
  emit "errfirstthirdfifthseventhe" errFirstThirdFifthSeventhE.slots errFirstThirdFifthSeventhE.code (fun xs => errFirstThirdFifthSeventhE.enc (errFirstThirdFifthSeventhE xs))
  emit "errinfixfirstthirdfifthseventhe" errInfixFirstThirdFifthSeventhE.slots errInfixFirstThirdFifthSeventhE.code (fun xs => errInfixFirstThirdFifthSeventhE.enc (errInfixFirstThirdFifthSeventhE xs))
open Proven.Frontx.Pairs in
#eval emit "addpoints16e" addPoints16E.slots addPoints16E.code (fun xs => addPoints16E.enc (addPoints16E xs))
  (inputs ++ List.zipWith (· ++ ·) (natInputs true) (natInputs true).reverse)
-- inductives, part 2 (`Ind2Examples.lean`, NOTES section 21): first line `indw <L>`, the work block per case: the
-- theorem's space with this input's cells (`Ind.spaceA m nl (fun _ => cells)`; the theorem's `cellsSup` is at
-- least that), or `Ind.spaceA 1 16 (fun n => M * n)` for one function
section
open Proven.Frontx.IndEx Proven.Frontx.IndCmp
def emitIndW (name : String) (code : List (BitVec 32)) (retLen : Bool) (cases : List (List UInt8 × List UInt8 × Nat)) :
    IO Unit := do
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words"
    (String.intercalate "\n" (s!"indw {if retLen then 1 else 0}" :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases"
    (String.join (cases.map fun (x, y, w) => s!"{hx x} {hx y} {w}\n"))
def spW (m nl cells : Nat) (x : List UInt8) : Nat := Proven.Frontx.Ind.spaceA m nl (fun _ => cells) x.length
def possS : List Pos := (List.range 50).map fun i => genP (rnd i 5 % 40)
def posPairs : List (Pos × Pos) := (List.range 50).map fun i => (possS.getD i .one, possS.getD ((i * 7 + 3) % 50) .one)
/-- trees with payloads below `2^64` (the subtype of `eqBinTree`); every third pair equal, every third one payload apart -/
def genS : Nat → Nat → BinTree Nat
  | 0, _ => .leaf
  | d + 1, s => if rnd s d % 4 = 0 then .leaf else .branch (genS d (2 * s + 1)) (key s) (genS d (2 * s + 2))
/-- the payload of the rightmost node, plus one -/
def bump : BinTree Nat → BinTree Nat
  | .leaf => .leaf
  | .branch l x .leaf => .branch l ((x + 1) % 2 ^ 64) .leaf
  | .branch l x r => .branch l x (bump r)
def treePairs : List (BinTree Nat × BinTree Nat) := (List.range 50).map fun i =>
  let t := genS (i % 6 + 1) (i + 3)
  match i % 3 with | 0 => (t, t) | 1 => (t, genS (i % 5 + 1) (i + 11)) | _ => (t, bump t)
def keyTrees : List (Tree Unit × Nat) := (List.range 50).map fun i => (bsts.getD i .leaf, if i % 3 = 0 then 5 else key (i * 17 + 1))
def lvPairs : List (ConLeche.Level × ConLeche.Level) := (List.range 50).map fun i => (levels.getD i .zero, levels.getD ((i * 7 + 3) % 50) .zero)
def ordB (o : Ordering) : List UInt8 := OrdT.enc o
def smallT : BinTree Nat → Bool
  | .leaf => true | .branch l x r => decide (x < 2 ^ 64) && smallT l && smallT r
#eval do
  emitIndW "pos_mul" Pos.mul.code true (posPairs.map fun p =>
    (PosT.enc2 p, PosT.enc (p.1.mul p.2), spW 2 16 (Pos.mul.ind.pg.al (PosT.emb p.1) 0 (PosT.emb p.2)) (PosT.enc2 p)))
  emitIndW "nontail_reverse_ln" NonTail.reverse.code true (lists.map fun l =>
    (Proven.Frontx.IndEx.LN.enc l, Proven.Frontx.IndEx.LN.enc (NonTail.reverse l), spW 2 17 (NonTail.reverse.ind.pg.al (Proven.Frontx.IndEx.LN.emb l) 0 .z) (Proven.Frontx.IndEx.LN.enc l)))
  emitInd "eq_bintree" eqBinTree.code eqBinTree.ind.pg.M false
    (treePairs.map fun p => (BTN.enc2 p, boolB (eqBinTree p.1 p.2)))
  emitInd "pos_comp" Pos.comp.code Pos.comp.ind.pg.M true (posPairs.map fun p => (PosT.enc2 p, ordB (p.1.comp p.2)))
  emitIndW "tree_containsk" containsK.code false (keyTrees.map fun (p : Tree Unit × Nat) =>
    let x := TU.enc p.1 ++ leN 8 p.2; (x, boolB (containsK p.1 p.2), Proven.Frontx.Ind.spaceA 1 16 (fun n => containsK.ind.pg.M * n) x.length))
  emitIndW "tree_findk" findK.code true (keyTrees.map fun (p : Tree Unit × Nat) =>
    let x := TU.enc p.1 ++ leN 8 p.2; (x, OU.enc (findK p.1 p.2), Proven.Frontx.Ind.spaceA 1 16 (fun n => findK.ind.pg.M * n) x.length))
  emitInd "level_combining" ConLeche.Level.combining.code ConLeche.Level.combining.ind.pg.M true
    (lvPairs.map fun (p : ConLeche.Level × ConLeche.Level) => (LevelT.enc2 p, LevelT.enc (ConLeche.Level.combining p.1 p.2)))
  emitIndW "level_simplify" ConLeche.Level.simplify.code true (levels.map fun l =>
    (LevelT.enc l, LevelT.enc l.simplify, spW 2 20 (ConLeche.Level.simplify.ind.pg.al (LevelT.emb l) 0 .z) (LevelT.enc l)))
#eval (treePairs.all fun p => smallT p.1 && smallT p.2, (treePairs.map fun p => eqBinTree p.1 p.2).count true,
  (keyTrees.map fun p => containsK p.1 p.2).count true)
end

-- strings and names (NOTES section 23): names with `str` (ASCII, multi-byte UTF-8, empty) and `num` (0 to
-- `2^64 - 1`) components; pairs: equal, one component changed, a prefix, unrelated; levels with `param` names
section
open Proven.Frontx.IndEx
def strs : List String := ["", "a", "b", "x", "Nat", "succ", "é", "λ", "∀x", "foo_bar", "Nat.add", "ab", "ba", "a\x00b",
  "𝔸", "x🙂y", "\x00", "ü∀𝔸z"]
def genN : Nat → Nat → ConLeche.Name
  | 0, _ => .anonymous
  | d + 1, s => match rnd s d % 3 with
    | 0 => .str (genN d (s + 1)) (strs.getD (rnd s 7 % strs.length) "")
    | 1 => .num (genN d (s + 2)) (match rnd s 3 % 4 with | 0 => 0 | 1 => 2 ^ 64 - 1 | 2 => 7 | _ => rnd s 9)
    | _ => if d = 0 then .anonymous else .str (genN d (s + 3)) (strs.getD (rnd s 11 % strs.length) "")
/-- the last component changed (a string to the next one, a number plus one mod `2^64`) -/
def bumpN : ConLeche.Name → ConLeche.Name
  | .anonymous => .str .anonymous "a"
  | .str p s => .str p (if s = "a" then "b" else "a")
  | .num p n => .num p ((n + 1) % 2 ^ 64)
def namePairs : List (ConLeche.Name × ConLeche.Name) := (List.range 60).map fun i =>
  let n := genN (i % 5 + 1) (i + 1)
  match i % 4 with
  | 0 => (n, n) | 1 => (n, bumpN n) | 2 => (n, .str n "x") | _ => (n, genN (i % 4 + 1) (i + 5))
def genLN : Nat → Nat → ConLeche.Level
  | 0, s => if s % 2 = 0 then .zero else .param (genN (s % 3 + 1) s)
  | d + 1, s => match rnd s d % 8 with
    | 0 => .zero | 1 => .param (genN (s % 3 + 1) s) | 2 | 3 => .succ (genLN d (s + 1))
    | 4 | 5 => .max (genLN d (2 * s)) (genLN d (2 * s + 1)) | _ => .imax (genLN d (2 * s)) (genLN d (2 * s + 1))
/-- the leftmost `param` name bumped (or `zero` ↦ `succ zero`) -/
def bumpL : ConLeche.Level → ConLeche.Level
  | .zero => .succ .zero
  | .param n => .param (bumpN n)
  | .succ u => .succ (bumpL u)
  | .max u v => .max (bumpL u) v
  | .imax u v => .imax (bumpL u) v
def levelPairs : List (ConLeche.Level × ConLeche.Level) := (List.range 60).map fun i =>
  let l := genLN (i % 6) (i + 1)
  match i % 3 with | 0 => (l, l) | 1 => (l, bumpL l) | _ => (l, genLN (i % 5) (i + 7))
#eval do
  emitIndW "name_beq" ConLeche.Name.beq.code false (namePairs.map fun p =>
    (NameT.enc2 p, boolB (p.1.beq p.2), spW 2 16 0 (NameT.enc2 p)))
  emitIndW "name_bbeq" nameBEq.code false (namePairs.map fun p =>
    (NameT.enc2 p, boolB (nameBEq p.1 p.2), spW 2 16 0 (NameT.enc2 p)))
  emitIndW "level_beq" ConLeche.Level.beq.code false (levelPairs.map fun p =>
    (LevelN.enc2 p, boolB (p.1.beq p.2), spW 3 16 0 (LevelN.enc2 p)))
  emitIndW "level_bbeq" levelBEq.code false (levelPairs.map fun p =>
    (LevelN.enc2 p, boolB (levelBEq p.1 p.2), spW 3 16 0 (LevelN.enc2 p)))
#eval ((namePairs.map fun p => p.1.beq p.2).count true, (levelPairs.map fun p => p.1.beq p.2).count true)
end
