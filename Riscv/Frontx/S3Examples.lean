/- **Existing compiled functions recompiled VERBATIM through S3** (`Testing/notes/IR_S3.md`): the functions under
test are the definitions of the old front ends' example files (imported, not copied); `s3_compile` builds the S3
program and the kernel-checked certificates; `S3.compile_correct` (`Riscv/Back/S3Top.lean`) then gives the machine
theorem for each (`N.computes : Computes N.P main id id` is its hypothesis).  Byte formats:
`Riscv/Frontx/S3IO.lean`.  Tests (QEMU + Sail, 50 cases each): `Testing/asm/emit_s3.lean`, `Testing/asm/ir_test.py`.

| entry | function under test (verbatim) | old front end |
|---|---|---|
| `S3Mirror` | `BinTree.mirror` | inductive (`IndExamples`) |
| `S3Graft` | `BinTree.graftLeft` | inductive (`IndExamples`) |
| `S3PosPlus` | `Pos.plus` | inductive (`IndExamples`) |
| `S3EqTree` | `eqBinTree` (`[BEq α]`) | inductive (`Ind2Examples`) |
| `S3TailRev` | `Tail.reverse` | inductive / list (`IndExamples`) |
| `S3NonTailRev` | `NonTail.reverse` (`++`) | inductive / list (`Ind2Examples`) |
| `S3Filter` | `filterGt3` (`NonTail.filter (· > 3)`) | list + higher-order (`ListOutExamples`) |
| `S3Append` | `append` (`List.append`) | list (`ListOutExamples`) |
| `S3Swap` | `swap` (pairs) | data (`DataExamples`) |
| `S3Weekend` | `Weekday.isWeekend` (wildcard match) | inductive (`IndCmpExamples`) |
| `S3ReplaceX` | `replaceX` (structure update) | structure (`PairExamples`) |
| `S3FromOption` | `fromOption` | structure / option (`PairExamples`) |
| `S3Small` | `MythicalCreature.small` | structure (`PairExamples`) |
| `S3Find` | `EarlyReturn.List.find?` (`do`, `return`, `failure` in `Option`) | monad + higher-order (`HofExamples`) |
| `S3PtTree` | `sumPts : BinTree (PPoint UInt64) → PPoint UInt64` (new) | **inductive + structure in one function** |
-/
import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Riscv.Frontx.Ind2Examples
import Riscv.Frontx.IndCmpExamples
import Riscv.Frontx.ListOutExamples
import Riscv.Frontx.DataExamples
import Riscv.Frontx.PairExamples
import Riscv.Frontx.HofExamples

namespace Proven.S3.Ex
open Proven.Frontx.IndEx

def mirrorMain (bs : List UInt8) : List UInt8 := encT (BinTree.mirror (decT bs))
s3_compile S3Mirror := mirrorMain

def graftMain (bs : List UInt8) : List UInt8 :=
  match decTGo bs [] with
  | t2 :: t1 :: _ => encT (BinTree.graftLeft t1 t2)
  | _ => []
s3_compile S3Graft := graftMain

def posPlusMain (bs : List UInt8) : List UInt8 :=
  match decP bs with
  | (a, r) => match decP r with
    | (b, _) => encP (a.plus b)
s3_compile S3PosPlus := posPlusMain

def eqTreeMain (bs : List UInt8) : List UInt8 :=
  match decTGo bs [] with
  | t2 :: t1 :: _ => boolB (eqBinTree t1 t2)
  | _ => []
s3_compile S3EqTree := eqTreeMain

def tailRevMain (bs : List UInt8) : List UInt8 := encW (Tail.reverse (decW bs))
s3_compile S3TailRev := tailRevMain

def nonTailRevMain (bs : List UInt8) : List UInt8 := encW (NonTail.reverse (decW bs))
s3_compile S3NonTailRev := nonTailRevMain

s3_compile S3Filter := Proven.Frontx.BookOut.filterGt3

/-- two byte lists: the first as `1 b` per byte then `0`, the second raw -/
def decL : List UInt8 → List UInt8 × List UInt8
  | [] => ([], [])
  | b :: r => if b == 0 then ([], r) else
    match r with
    | [] => ([], [])
    | x :: r' => match decL r' with
      | (l, rest) => (x :: l, rest)
def appendMain (bs : List UInt8) : List UInt8 :=
  match decL bs with
  | (xs, ys) => Proven.Frontx.BookOut.append xs ys
s3_compile S3Append := appendMain

def swapMain (bs : List UInt8) : List UInt8 :=
  match decW bs with
  | a :: b :: _ => match Proven.Frontx.Data.swap (a, b) with
    | (c, d) => enc8 c ++ enc8 d
  | _ => []
s3_compile S3Swap := swapMain

open Proven.Frontx.IndCmp in
s3_enc Weekday
open Proven.Frontx.IndCmp in
def dayOf (b : UInt8) : Weekday :=
  if b == 0 then .monday else if b == 1 then .tuesday else if b == 2 then .wednesday else
  if b == 3 then .thursday else if b == 4 then .friday else if b == 5 then .saturday else .sunday
def weekendMain (bs : List UInt8) : List UInt8 :=
  match bs with
  | b :: _ => boolB (Proven.Frontx.IndCmp.B.Weekday.isWeekend (dayOf b))
  | [] => []
s3_compile S3Weekend := weekendMain

open Proven.Frontx.Pairs in
s3_enc PPoint
def replaceXMain (bs : List UInt8) : List UInt8 :=
  match decW bs with
  | a :: b :: c :: _ =>
    match Proven.Frontx.Pairs.BetterPlicity.replaceX ({ x := a, y := b } : Proven.Frontx.Pairs.PPoint UInt64) c with
    | { x := x, y := y } => enc8 x ++ enc8 y
  | _ => []
s3_compile S3ReplaceX := replaceXMain

def fromOptionMain (bs : List UInt8) : List UInt8 :=
  match decW bs with
  | d :: x :: _ => enc8 (Proven.Frontx.Pairs.BetterPlicity.fromOption d (some x))
  | [d] => enc8 (Proven.Frontx.Pairs.BetterPlicity.fromOption d none)
  | [] => []
s3_compile S3FromOption := fromOptionMain

open Proven.Frontx.Pairs in
s3_enc MythicalCreature
def smallMain (bs : List UInt8) : List UInt8 :=
  match bs with
  | b :: _ => boolB (Proven.Frontx.Pairs.MythicalCreature.small ⟨b != 0⟩)
  | [] => []
s3_compile S3Small := smallMain

open Proven.Frontx.Pairs in
/-- inductive + structure in one function (no single old front end takes both) -/
def sumPts : BinTree (PPoint UInt64) → PPoint UInt64
  | .leaf => ⟨0, 0⟩
  | .branch l p r =>
    match sumPts l, sumPts r with
    | ⟨ax, ay⟩, ⟨bx, by_⟩ => ⟨ax + p.x + bx, ay + p.y + by_⟩
open Proven.Frontx.Pairs in
def toPts : BinTree UInt64 → BinTree (PPoint UInt64)
  | .leaf => .leaf
  | .branch l x r => .branch (toPts l) ⟨x, x * 3⟩ (toPts r)
def ptTreeMain (bs : List UInt8) : List UInt8 :=
  match sumPts (toPts (decT bs)) with
  | ⟨x, y⟩ => enc8 x ++ enc8 y
s3_compile S3PtTree := ptTreeMain

def findMain (bs : List UInt8) : List UInt8 :=
  match Proven.Frontx.Hof.EarlyReturn.List.find? (· > 3) bs with
  | some x => [1, x]
  | none => [0]
s3_compile S3Find := findMain

end Proven.S3.Ex
