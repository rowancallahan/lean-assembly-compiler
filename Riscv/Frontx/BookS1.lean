/- Book survey 3, first third of the example files (sorted), blocked rows retried verbatim on `main` (4a79eeb).
Each block: `namespace Proven.Frontx.BookS1.R<n>`, book context (`-- ctx`), the book def (`-- TARGET file:line-end`) and the command chosen by signature (`frontx_ind` for user inductives, `frontx_view`+`frontx_compile` for lists, else `frontx_compile`). Not a compiled-on-main list: see BOOK_S1.md. -/
import Riscv.Frontx.Translate
import Riscv.Frontx.RecCmd
import Riscv.Frontx.IndCmd
import Riscv.Frontx.WaCmd
set_option autoImplicit true
set_option maxRecDepth 4000
set_option maxErrors 100000

namespace Proven.Frontx.BookS1.R76


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:122-124
section
open Plus (plus)
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
end

-- ctx Examples/Classes.lean:181-183
section
open Plus (plus)
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)
end

-- ctx Examples/Classes.lean:185-186
section
open Plus (plus)
instance : Plus Pos where
  plus := Pos.plus
end

-- ctx Examples/Classes.lean:193-194
section
open Plus (plus)
instance : Add Pos where
  add := Pos.plus
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:240-244
section
open Plus (plus)
namespace Argh
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
frontx_ind_type TT76_0 := Pos
frontx_ind Argh.posToString on TT76_0
#check @Argh.posToString
end Argh
end

end Proven.Frontx.BookS1.R76

namespace Proven.Frontx.BookS1.R100


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:122-124
section
open Plus (plus)
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
end

-- ctx Examples/Classes.lean:181-183
section
open Plus (plus)
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)
end

-- ctx Examples/Classes.lean:185-186
section
open Plus (plus)
instance : Plus Pos where
  plus := Pos.plus
end

-- ctx Examples/Classes.lean:193-194
section
open Plus (plus)
instance : Add Pos where
  add := Pos.plus
end

-- ctx Examples/Classes.lean:232-234
section
open Plus (plus)
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
end

-- ctx Examples/Classes.lean:240-244
section
open Plus (plus)
namespace Argh
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
end Argh
end

-- ctx Examples/Classes.lean:248-249
section
open Plus (plus)
namespace Argh
instance : ToString Pos where
  toString := posToString true
end Argh
end

-- ctx Examples/Classes.lean:267-268
section
open Plus (plus)
section
instance : ToString Pos where
  toString x := toString (x.toNat)
end
end

-- ctx Examples/Classes.lean:303-305
section
open Plus (plus)
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k
end

-- ctx Examples/Classes.lean:307-308
section
open Plus (plus)
instance : Mul Pos where
  mul := Pos.mul
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:757-759
section
open Plus (plus)
def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)
frontx_ind_type TT100_0 := Pos
frontx_ind addNatPos on TT100_0
#check @addNatPos
end

end Proven.Frontx.BookS1.R100

namespace Proven.Frontx.BookS1.R101


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:122-124
section
open Plus (plus)
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
end

-- ctx Examples/Classes.lean:181-183
section
open Plus (plus)
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)
end

-- ctx Examples/Classes.lean:185-186
section
open Plus (plus)
instance : Plus Pos where
  plus := Pos.plus
end

-- ctx Examples/Classes.lean:193-194
section
open Plus (plus)
instance : Add Pos where
  add := Pos.plus
end

-- ctx Examples/Classes.lean:232-234
section
open Plus (plus)
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
end

-- ctx Examples/Classes.lean:240-244
section
open Plus (plus)
namespace Argh
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
end Argh
end

-- ctx Examples/Classes.lean:248-249
section
open Plus (plus)
namespace Argh
instance : ToString Pos where
  toString := posToString true
end Argh
end

-- ctx Examples/Classes.lean:267-268
section
open Plus (plus)
section
instance : ToString Pos where
  toString x := toString (x.toNat)
end
end

-- ctx Examples/Classes.lean:303-305
section
open Plus (plus)
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k
end

-- ctx Examples/Classes.lean:307-308
section
open Plus (plus)
instance : Mul Pos where
  mul := Pos.mul
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:761-763
section
open Plus (plus)
def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)
frontx_ind_type TT101_0 := Pos
frontx_ind addPosNat on TT101_0
#check @addPosNat
end

end Proven.Frontx.BookS1.R101

namespace Proven.Frontx.BookS1.R118


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:956-958
section
open Plus (plus)
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:961-961
section
open Plus (plus)
def NonEmptyList.toList (xs : NonEmptyList α) := xs.head :: xs.tail
frontx_ind_type TT118_0 := (NonEmptyList Nat)
frontx_ind NonEmptyList.toList on TT118_0
#check @NonEmptyList.toList
end

end Proven.Frontx.BookS1.R118

namespace Proven.Frontx.BookS1.R120


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:956-958
section
open Plus (plus)
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:989-992
section
open Plus (plus)
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | {head := _, tail := []}, _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n
frontx_ind_type TT120_0 := (NonEmptyList Nat)
frontx_ind NonEmptyList.get? on TT120_0
#check @NonEmptyList.get?
end

end Proven.Frontx.BookS1.R120

namespace Proven.Frontx.BookS1.R121


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:956-958
section
open Plus (plus)
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
end

-- ctx Examples/Classes.lean:989-992
section
open Plus (plus)
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | {head := _, tail := []}, _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:997-999
section
open Plus (plus)
namespace UseList
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail[n]?
frontx_ind_type TT121_0 := (NonEmptyList Nat)
frontx_ind UseList.NonEmptyList.get? on TT121_0
#check @UseList.NonEmptyList.get?
end UseList
end

end Proven.Frontx.BookS1.R121

namespace Proven.Frontx.BookS1.R122


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:956-958
section
open Plus (plus)
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:1004-1005
section
open Plus (plus)
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length
frontx_ind_type TT122_0 := (NonEmptyList Nat)
frontx_ind NonEmptyList.inBounds on TT122_0
#check @NonEmptyList.inBounds
end

end Proven.Frontx.BookS1.R122

namespace Proven.Frontx.BookS1.R123


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:956-958
section
open Plus (plus)
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
end

-- ctx Examples/Classes.lean:1004-1005
section
open Plus (plus)
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:1010-1014
section
open Plus (plus)
def NonEmptyList.get (xs : NonEmptyList α)
    (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]
frontx_ind_type TT123_0 := (NonEmptyList Nat)
frontx_ind NonEmptyList.get on TT123_0
#check @NonEmptyList.get
end

end Proven.Frontx.BookS1.R123

namespace Proven.Frontx.BookS1.R145


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:122-124
section
open Plus (plus)
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
end

-- ctx Examples/Classes.lean:181-183
section
open Plus (plus)
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)
end

-- ctx Examples/Classes.lean:185-186
section
open Plus (plus)
instance : Plus Pos where
  plus := Pos.plus
end

-- ctx Examples/Classes.lean:193-194
section
open Plus (plus)
instance : Add Pos where
  add := Pos.plus
end

-- ctx Examples/Classes.lean:232-234
section
open Plus (plus)
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
end

-- ctx Examples/Classes.lean:240-244
section
open Plus (plus)
namespace Argh
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
end Argh
end

-- ctx Examples/Classes.lean:248-249
section
open Plus (plus)
namespace Argh
instance : ToString Pos where
  toString := posToString true
end Argh
end

-- ctx Examples/Classes.lean:267-268
section
open Plus (plus)
section
instance : ToString Pos where
  toString x := toString (x.toNat)
end
end

-- ctx Examples/Classes.lean:303-305
section
open Plus (plus)
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k
end

-- ctx Examples/Classes.lean:307-308
section
open Plus (plus)
instance : Mul Pos where
  mul := Pos.mul
end

-- ctx Examples/Classes.lean:457-459
section
open Plus (plus)
namespace AltPos
structure Pos where
  succ ::
  pred : Nat
end AltPos
end

-- ctx Examples/Classes.lean:757-759
section
open Plus (plus)
def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)
end

-- ctx Examples/Classes.lean:761-763
section
open Plus (plus)
def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)
end

-- ctx Examples/Classes.lean:769-770
section
open Plus (plus)
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos
end

-- ctx Examples/Classes.lean:772-773
section
open Plus (plus)
instance : HAdd Pos Nat Pos where
  hAdd := addPosNat
end

-- ctx Examples/Classes.lean:1122-1123
section
open Plus (plus)
instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat
end

-- ctx Examples/Classes.lean:1127-1128
section
open Plus (plus)
instance : LE Pos where
  le x y := LE.le x.toNat y.toNat
end

-- ctx Examples/Classes.lean:1132-1133
section
open Plus (plus)
instance {x : Pos} {y : Pos} : Decidable (x < y) :=
  (inferInstance : Decidable (x.toNat < y.toNat))
end

-- ctx Examples/Classes.lean:1135-1136
section
open Plus (plus)
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  (inferInstance : Decidable (x.toNat ≤ y.toNat))
end

-- ctx Examples/Classes.lean:1149-1150
section
open Plus (plus)
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  (inferInstance : Decidable (x.toNat < y.toNat))
end

-- ctx Examples/Classes.lean:1199-1202
section
open Plus (plus)
namespace Cmp
inductive Ordering where
  | lt
  | eq
  | gt
end Cmp
end

-- ctx Examples/Classes.lean:1210-1214
section
open Plus (plus)
def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k
end

-- ctx Examples/Classes.lean:1216-1217
section
open Plus (plus)
instance : Ord Pos where
  compare := Pos.comp
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:1245-1247
section
open Plus (plus)
def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)
frontx_ind_type TT145_0 := Pos
frontx_ind_type TT145_1 := AltPos.Pos
frontx_ind hashPos on TT145_0 using TT145_1
#check @hashPos
end

end Proven.Frontx.BookS1.R145

namespace Proven.Frontx.BookS1.R150


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:1255-1257
section
open Plus (plus)
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
end

-- ctx Examples/Classes.lean:1259-1265
section
open Plus (plus)
def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false
end

-- ctx Examples/Classes.lean:1267-1268
section
open Plus (plus)
instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:1270-1277
section
open Plus (plus)
def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1
      (mixHash (hashBinTree left)
        (mixHash (hash x)
          (hashBinTree right)))
frontx_ind_type TT150_0 := (BinTree Nat)
frontx_ind hashBinTree on TT150_0
#check @hashBinTree
end

end Proven.Frontx.BookS1.R150

namespace Proven.Frontx.BookS1.R162


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:956-958
section
open Plus (plus)
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
end

-- ctx Examples/Classes.lean:1299-1299
section
open Plus (plus)
deriving instance ToString for NonEmptyList
end

-- ctx Examples/Classes.lean:1322-1324
section
open Plus (plus)
instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }
end

-- ctx Examples/Classes.lean:1405-1406
section
open Plus (plus)
instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:1442-1446
section
open Plus (plus)
def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail
frontx_ind_type TT162_0 := (NonEmptyList Nat)
frontx_ind concat on TT162_0
#check @concat
end

end Proven.Frontx.BookS1.R162

namespace Proven.Frontx.BookS1.R176


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:1636-1639
section
open Plus (plus)
def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))
frontx_view String.separate
frontx_compile String.separate.view from String.separate.view.eq measure fun B i => B.size - i
#check @String.separate
end

end Proven.Frontx.BookS1.R176

namespace Proven.Frontx.BookS1.R177


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:1671-1675
section
open Plus (plus)
def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropEndWhile (· == '0')
    (noTrailingZeros.dropEndWhile (· == '.')).copy
  else numString
frontx_compile dropDecimals
#check @dropDecimals
end

end Proven.Frontx.BookS1.R177

namespace Proven.Frontx.BookS1.R183


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:1723-1726
section
open Plus (plus)
structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:1737-1738
section
open Plus (plus)
def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }
frontx_ind_type TT183_0 := Monoid
frontx_ind listMonoid on TT183_0
#check @listMonoid
end

end Proven.Frontx.BookS1.R183

namespace Proven.Frontx.BookS1.R184


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:1723-1726
section
open Plus (plus)
structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:1743-1747
section
open Plus (plus)
namespace MMM
def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs
frontx_ind_type TT184_0 := Monoid
frontx_ind MMM.foldMap on TT184_0
#check @MMM.foldMap
end MMM
end

end Proven.Frontx.BookS1.R184

namespace Proven.Frontx.BookS1.R186


-- ctx Examples/Classes.lean:56-57
section
class Plus (α : Type) where
  plus : α → α → α
end

-- ctx Examples/Classes.lean:67-68
section
instance : Plus Nat where
  plus := Nat.add
end

-- ctx Examples/Classes.lean:1723-1726
section
open Plus (plus)
structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier
end

-- ctx Examples/Classes.lean:1753-1754
section
open Plus (plus)
instance : CoeSort Monoid Type where
  coe m := m.Carrier
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes.lean:1759-1763
section
open Plus (plus)
def foldMap (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs
frontx_ind_type TT186_0 := Monoid
frontx_ind foldMap on TT186_0
#check @foldMap
end

end Proven.Frontx.BookS1.R186

namespace Proven.Frontx.BookS1.R223


-- ctx Examples/Classes/Even.lean:4-6
section
namespace Even
inductive Even : Type where
  | zero : Even
  | plusTwo : Even → Even
end Even
end

-- ctx Examples/Classes/Even.lean:8-10
section
namespace Even
def Even.plus : Even → Even → Even
  | Even.zero, k => k
  | Even.plusTwo n, k => Even.plusTwo (n.plus k)
end Even
end

-- ctx Examples/Classes/Even.lean:12-13
section
namespace Even
instance : Add Even where
  add := Even.plus
end Even
end

-- ctx Examples/Classes/Even.lean:21-23
section
namespace Even
def Even.toNat : Even → Nat
  | Even.zero => 0
  | Even.plusTwo n => n.toNat + 2
end Even
end

-- ctx Examples/Classes/Even.lean:25-26
section
namespace Even
instance : ToString Even where
  toString x := toString (x.toNat)
end Even
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes/Even.lean:32-35
section
namespace Even
def Even.mul : Even → Even → Even
  | Even.zero, k => Even.zero
  | Even.plusTwo Even.zero, k => k + k
  | Even.plusTwo n, k => n.mul k + k + k
frontx_ind_type TT223_0 := Even.Even
frontx_ind Even.Even.mul on TT223_0
#check @Even.Even.mul
end Even
end

end Proven.Frontx.BookS1.R223

namespace Proven.Frontx.BookS1.R233


-- ctx Examples/Classes/Even.lean:4-6
section
namespace Even
inductive Even : Type where
  | zero : Even
  | plusTwo : Even → Even
end Even
end

-- ctx Examples/Classes/Even.lean:8-10
section
namespace Even
def Even.plus : Even → Even → Even
  | Even.zero, k => k
  | Even.plusTwo n, k => Even.plusTwo (n.plus k)
end Even
end

-- ctx Examples/Classes/Even.lean:12-13
section
namespace Even
instance : Add Even where
  add := Even.plus
end Even
end

-- ctx Examples/Classes/Even.lean:21-23
section
namespace Even
def Even.toNat : Even → Nat
  | Even.zero => 0
  | Even.plusTwo n => n.toNat + 2
end Even
end

-- ctx Examples/Classes/Even.lean:25-26
section
namespace Even
instance : ToString Even where
  toString x := toString (x.toNat)
end Even
end

-- ctx Examples/Classes/Even.lean:32-35
section
namespace Even
def Even.mul : Even → Even → Even
  | Even.zero, k => Even.zero
  | Even.plusTwo Even.zero, k => k + k
  | Even.plusTwo n, k => n.mul k + k + k
end Even
end

-- ctx Examples/Classes/Even.lean:37-38
section
namespace Even
instance : Mul Even where
  mul := Even.mul
end Even
end

-- ctx Examples/Classes/Even.lean:42-43
section
namespace Even
instance : OfNat Even Nat.zero where
  ofNat := Even.zero
end Even
end

-- ctx Examples/Classes/Even.lean:45-46
section
namespace Even
instance [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := Even.plusTwo (OfNat.ofNat n)
end Even
end

-- ctx Examples/Classes/Even.lean:92-93
section
namespace Other
inductive Even : Type where
  | times2 : Nat → Even
end Other
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/Classes/Even.lean:96-97
section
namespace Other
def Even.add : Even → Even → Even
  | times2 a, times2 b => times2 (a + b)
frontx_ind_type TT233_0 := Even.Even
frontx_ind_type TT233_1 := Other.Even
frontx_ind Other.Even.add on TT233_0 using TT233_1
#check @Other.Even.add
end Other
end

end Proven.Frontx.BookS1.R233

namespace Proven.Frontx.BookS1.R237


#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes.lean:6-9
section
def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"
frontx_compile natOrStringThree
#check @natOrStringThree
end

end Proven.Frontx.BookS1.R237

namespace Proven.Frontx.BookS1.R240


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes.lean:228-231
section
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)
frontx_ind_type TT240_0 := (Vect Nat)
frontx_ind Vect.replicate on TT240_0
#check @Vect.replicate
end

end Proven.Frontx.BookS1.R240

namespace Proven.Frontx.BookS1.R241


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

-- ctx Examples/DependentTypes.lean:228-231
section
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes.lean:237-240
section
namespace Extras
def List.replicate (n : Nat) (x : α) : List α :=
  match n with
  | 0 => []
  | k + 1 => x :: x :: replicate k x
frontx_view Extras.List.replicate
frontx_compile Extras.List.replicate.view from Extras.List.replicate.view.eq measure fun B i => B.size - i
#check @Extras.List.replicate
end Extras
end

end Proven.Frontx.BookS1.R241

namespace Proven.Frontx.BookS1.R242


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes.lean:274-276
section
def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)
frontx_ind_type TT242_0 := (Vect Nat)
frontx_ind Vect.zip on TT242_0
#check @Vect.zip
end

end Proven.Frontx.BookS1.R242

namespace Proven.Frontx.BookS1.R245


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

-- ctx Examples/DependentTypes.lean:274-276
section
def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes.lean:329-331
section
namespace Details
def Vect.zip : (n : Nat) → Vect α n → Vect β n → Vect (α × β) n
  | 0, .nil, .nil => .nil
  | k + 1, .cons x xs, .cons y ys => .cons (x, y) (zip k xs ys)
frontx_ind_type TT245_0 := (Vect Nat)
frontx_ind Details.Vect.zip on TT245_0
#check @Details.Vect.zip
end Details
end

end Proven.Frontx.BookS1.R245

namespace Proven.Frontx.BookS1.R248


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes.lean:347-349
section
def Vect.map : (α → β) → Vect α n → Vect β n
  | f, .nil => .nil
  | f, .cons x xs => .cons (f x) (xs.map f)
frontx_ind_type TT248_0 := (Vect Nat)
frontx_ind Vect.map on TT248_0
#check @Vect.map
end

end Proven.Frontx.BookS1.R248

namespace Proven.Frontx.BookS1.R249


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes.lean:351-353
section
def Vect.zipWith : (α → β → γ) → Vect α n → Vect β n → Vect γ n
  | f, .nil, .nil => .nil
  | f, .cons x xs, .cons y ys => .cons (f x y) (xs.zipWith f ys)
frontx_ind_type TT249_0 := (Vect Nat)
frontx_ind Vect.zipWith on TT249_0
#check @Vect.zipWith
end

end Proven.Frontx.BookS1.R249

namespace Proven.Frontx.BookS1.R250


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes.lean:355-359
section
def Vect.unzip : Vect (α × β) n → Vect α n × Vect β n
  | .nil => (.nil, .nil)
  | .cons (x, y) xys =>
    let (xs, ys) := xys.unzip
    (.cons x xs, .cons y ys)
frontx_ind_type TT250_0 := (Vect Nat)
frontx_ind Vect.unzip on TT250_0
#check @Vect.unzip
end

end Proven.Frontx.BookS1.R250

namespace Proven.Frontx.BookS1.R251


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes.lean:362-364
section
def Vect.push : Vect α n → α → Vect α (n + 1)
  | .nil, x => .cons x .nil
  | .cons y ys, x => .cons y (push ys x)
frontx_ind_type TT251_0 := (Vect Nat)
frontx_ind Vect.push on TT251_0
#check @Vect.push
end

end Proven.Frontx.BookS1.R251

namespace Proven.Frontx.BookS1.R252


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes.lean:366-368
section
def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0, xs => xs
  | n + 1, .cons x xs => xs.drop n
frontx_ind_type TT252_0 := (Vect Nat)
frontx_ind Vect.drop on TT252_0
#check @Vect.drop
end

end Proven.Frontx.BookS1.R252

namespace Proven.Frontx.BookS1.R253


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

-- ctx Examples/DependentTypes.lean:362-364
section
def Vect.push : Vect α n → α → Vect α (n + 1)
  | .nil, x => .cons x .nil
  | .cons y ys, x => .cons y (push ys x)
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes.lean:370-372
section
def Vect.reverse : Vect α n → Vect α n
  | .nil => .nil
  | .cons x xs => xs.reverse.push x
frontx_ind_type TT253_0 := (Vect Nat)
frontx_ind Vect.reverse on TT253_0
#check @Vect.reverse
end

end Proven.Frontx.BookS1.R253

namespace Proven.Frontx.BookS1.R254


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes.lean:375-377
section
def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0, xs => .nil
  | n + 1, .cons x xs => .cons x (xs.take n)
frontx_ind_type TT254_0 := (Vect Nat)
frontx_ind Vect.take on TT254_0
#check @Vect.take
end

end Proven.Frontx.BookS1.R254

namespace Proven.Frontx.BookS1.R256


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
frontx_ind_type TT256_0 := DBType
frontx_ind DBType.asType on TT256_0
#check @DBType.asType
end

end Proven.Frontx.BookS1.R256

namespace Proven.Frontx.BookS1.R257


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
frontx_ind_type TT257_0 := DBType
frontx_ind DBType.beq on TT257_0
#check @DBType.beq
end

end Proven.Frontx.BookS1.R257

namespace Proven.Frontx.BookS1.R263


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:84-87
section
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
frontx_compile Row
#check @Row
end

end Proven.Frontx.BookS1.R263

namespace Proven.Frontx.BookS1.R264


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:84-87
section
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:104-104
section
abbrev Table (s : Schema) := List (Row s)
frontx_compile Table
#check @Table
end

end Proven.Frontx.BookS1.R264

namespace Proven.Frontx.BookS1.R269


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:84-87
section
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:167-174
section
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
frontx_compile Row.bEq
#check @Row.bEq
end

end Proven.Frontx.BookS1.R269

namespace Proven.Frontx.BookS1.R272


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:84-87
section
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
end

-- ctx Examples/DependentTypes/DB.lean:167-174
section
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
end

-- ctx Examples/DependentTypes/DB.lean:176-177
section
instance : BEq (Row s) where
  beq := Row.bEq
end

-- ctx Examples/DependentTypes/DB.lean:182-184
section
inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:193-197
section
def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next
frontx_ind_type TT272_0 := HasCol
frontx_ind Row.get on TT272_0
#check @Row.get
end

end Proven.Frontx.BookS1.R272

namespace Proven.Frontx.BookS1.R275


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:182-184
section
inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t
end

-- ctx Examples/DependentTypes/DB.lean:203-208
section
inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
      HasCol bigger n t →
      Subschema smaller bigger →
      Subschema (⟨n, t⟩ :: smaller) bigger
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:314-318
section
def Subschema.addColumn :
    Subschema smaller bigger →
    Subschema smaller (c :: bigger)
  | .nil  => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn
frontx_ind_type TT275_0 := Subschema
frontx_ind Subschema.addColumn on TT275_0
#check @Subschema.addColumn
end

end Proven.Frontx.BookS1.R275

namespace Proven.Frontx.BookS1.R277


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:84-87
section
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
end

-- ctx Examples/DependentTypes/DB.lean:167-174
section
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
end

-- ctx Examples/DependentTypes/DB.lean:176-177
section
instance : BEq (Row s) where
  beq := Row.bEq
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:330-333
section
def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | c' :: cs, v' => (v, v')
frontx_compile addVal
#check @addVal
end

end Proven.Frontx.BookS1.R277

namespace Proven.Frontx.BookS1.R278


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:84-87
section
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
end

-- ctx Examples/DependentTypes/DB.lean:167-174
section
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
end

-- ctx Examples/DependentTypes/DB.lean:176-177
section
instance : BEq (Row s) where
  beq := Row.bEq
end

-- ctx Examples/DependentTypes/DB.lean:182-184
section
inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t
end

-- ctx Examples/DependentTypes/DB.lean:193-197
section
def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next
end

-- ctx Examples/DependentTypes/DB.lean:203-208
section
inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
      HasCol bigger n t →
      Subschema smaller bigger →
      Subschema (⟨n, t⟩ :: smaller) bigger
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:337-340
section
def Row.project (row : Row s) : (s' : Schema) → Subschema s' s → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)
frontx_ind_type TT278_0 := Subschema
frontx_ind Row.project on TT278_0
#check @Row.project
end

end Proven.Frontx.BookS1.R278

namespace Proven.Frontx.BookS1.R283


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:84-87
section
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
end

-- ctx Examples/DependentTypes/DB.lean:167-174
section
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
end

-- ctx Examples/DependentTypes/DB.lean:176-177
section
instance : BEq (Row s) where
  beq := Row.bEq
end

-- ctx Examples/DependentTypes/DB.lean:182-184
section
inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t
end

-- ctx Examples/DependentTypes/DB.lean:193-197
section
def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next
end

-- ctx Examples/DependentTypes/DB.lean:344-349
section
inductive DBExpr (s : Schema) : DBType → Type where
  | col (n : String) (loc : HasCol s n t) : DBExpr s t
  | eq (e1 e2 : DBExpr s t) : DBExpr s .bool
  | lt (e1 e2 : DBExpr s .int) : DBExpr s .bool
  | and (e1 e2 : DBExpr s .bool) : DBExpr s .bool
  | const : t.asType → DBExpr s t
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:372-377
section
def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2  => evaluate row e1 == evaluate row e2
  | .lt e1 e2  => evaluate row e1 < evaluate row e2
  | .and e1 e2 => evaluate row e1 && evaluate row e2
  | .const v => v
frontx_ind_type TT283_0 := (DBExpr Nat)
frontx_ind DBExpr.evaluate on TT283_0
#check @DBExpr.evaluate
end

end Proven.Frontx.BookS1.R283

namespace Proven.Frontx.BookS1.R284


#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:412-413
section
def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)
frontx_view disjoint
frontx_compile disjoint.view from disjoint.view.eq measure fun B i => B.size - i
#check @disjoint
end

end Proven.Frontx.BookS1.R284

namespace Proven.Frontx.BookS1.R285


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:182-184
section
inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:418-420
section
def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'
frontx_ind_type TT285_0 := HasCol
frontx_ind Schema.renameColumn on TT285_0
#check @Schema.renameColumn
end

end Proven.Frontx.BookS1.R285

namespace Proven.Frontx.BookS1.R287


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:84-87
section
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
end

-- ctx Examples/DependentTypes/DB.lean:167-174
section
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
end

-- ctx Examples/DependentTypes/DB.lean:176-177
section
instance : BEq (Row s) where
  beq := Row.bEq
end

-- ctx Examples/DependentTypes/DB.lean:330-333
section
def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | c' :: cs, v' => (v, v')
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:448-452
section
def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r') => (v, r'.append r2)
frontx_compile Row.append
#check @Row.append
end

end Proven.Frontx.BookS1.R287

namespace Proven.Frontx.BookS1.R288


#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:458-460
section
namespace Mine
def List.flatMap (f : α → List β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x ++ xs.flatMap f
frontx_view Mine.List.flatMap
frontx_compile Mine.List.flatMap.view from Mine.List.flatMap.view.eq measure fun B i => B.size - i
#check @Mine.List.flatMap
end Mine
end

end Proven.Frontx.BookS1.R288

namespace Proven.Frontx.BookS1.R289


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

-- ctx Examples/DependentTypes.lean:347-349
section
def Vect.map : (α → β) → Vect α n → Vect β n
  | f, .nil => .nil
  | f, .cons x xs => .cons (f x) (xs.map f)
end

-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:84-87
section
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
end

-- ctx Examples/DependentTypes/DB.lean:104-104
section
abbrev Table (s : Schema) := List (Row s)
end

-- ctx Examples/DependentTypes/DB.lean:167-174
section
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
end

-- ctx Examples/DependentTypes/DB.lean:176-177
section
instance : BEq (Row s) where
  beq := Row.bEq
end

-- ctx Examples/DependentTypes/DB.lean:330-333
section
def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | c' :: cs, v' => (v, v')
end

-- ctx Examples/DependentTypes/DB.lean:448-452
section
def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r') => (v, r'.append r2)
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:465-467
section
def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) :
    Table (s1 ++ s2) :=
  table1.flatMap fun r1 => table2.map r1.append
frontx_compile Table.cartesianProduct
#check @Table.cartesianProduct
end

end Proven.Frontx.BookS1.R289

namespace Proven.Frontx.BookS1.R290


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

-- ctx Examples/DependentTypes.lean:347-349
section
def Vect.map : (α → β) → Vect α n → Vect β n
  | f, .nil => .nil
  | f, .cons x xs => .cons (f x) (xs.map f)
end

-- ctx Examples/DependentTypes.lean:362-364
section
def Vect.push : Vect α n → α → Vect α (n + 1)
  | .nil, x => .cons x .nil
  | .cons y ys, x => .cons y (push ys x)
end

-- ctx Examples/DependentTypes.lean:370-372
section
def Vect.reverse : Vect α n → Vect α n
  | .nil => .nil
  | .cons x xs => xs.reverse.push x
end

-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:84-87
section
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
end

-- ctx Examples/DependentTypes/DB.lean:104-104
section
abbrev Table (s : Schema) := List (Row s)
end

-- ctx Examples/DependentTypes/DB.lean:167-174
section
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
end

-- ctx Examples/DependentTypes/DB.lean:176-177
section
instance : BEq (Row s) where
  beq := Row.bEq
end

-- ctx Examples/DependentTypes/DB.lean:330-333
section
def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | c' :: cs, v' => (v, v')
end

-- ctx Examples/DependentTypes/DB.lean:448-452
section
def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r') => (v, r'.append r2)
end

-- ctx Examples/DependentTypes/DB.lean:465-467
section
def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) :
    Table (s1 ++ s2) :=
  table1.flatMap fun r1 => table2.map r1.append
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:472-478
section
namespace OrElse
def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) :
    Table (s1 ++ s2) := Id.run do
  let mut out : Table (s1 ++ s2) := []
  for r1 in table1 do
    for r2 in table2 do
      out := (r1.append r2) :: out
  pure out.reverse
frontx_compile OrElse.Table.cartesianProduct
#check @OrElse.Table.cartesianProduct
end OrElse
end

end Proven.Frontx.BookS1.R290

namespace Proven.Frontx.BookS1.R291


#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:493-494
section
def List.without [BEq α] (source banned : List α) : List α :=
  source.filter fun r => !(banned.contains r)
frontx_view List.without
frontx_compile List.without.view from List.without.view.eq measure fun B i => B.size - i
#check @List.without
end

end Proven.Frontx.BookS1.R291

namespace Proven.Frontx.BookS1.R292


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:84-87
section
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
end

-- ctx Examples/DependentTypes/DB.lean:167-174
section
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
end

-- ctx Examples/DependentTypes/DB.lean:176-177
section
instance : BEq (Row s) where
  beq := Row.bEq
end

-- ctx Examples/DependentTypes/DB.lean:182-184
section
inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t
end

-- ctx Examples/DependentTypes/DB.lean:330-333
section
def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | c' :: cs, v' => (v, v')
end

-- ctx Examples/DependentTypes/DB.lean:418-420
section
def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:499-504
section
def Row.rename (c : HasCol s n t) (row : Row s) :
    Row (s.renameColumn c n') :=
  match s, row, c with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => (v, r)
  | _::_::_, (v, r), .there next => addVal v (r.rename next)
frontx_ind_type TT292_0 := HasCol
frontx_ind Row.rename on TT292_0
#check @Row.rename
end

end Proven.Frontx.BookS1.R292

namespace Proven.Frontx.BookS1.R293


-- ctx Examples/DependentTypes.lean:14-16
section
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
end

-- ctx Examples/DependentTypes.lean:19-19
section
deriving instance Repr for Vect
end

-- ctx Examples/DependentTypes.lean:347-349
section
def Vect.map : (α → β) → Vect α n → Vect β n
  | f, .nil => .nil
  | f, .cons x xs => .cons (f x) (xs.map f)
end

-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:74-76
section
structure Column where
  name : String
  contains : DBType
end

-- ctx Examples/DependentTypes/DB.lean:78-78
section
abbrev Schema := List Column
end

-- ctx Examples/DependentTypes/DB.lean:84-87
section
abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)
end

-- ctx Examples/DependentTypes/DB.lean:167-174
section
def Row.bEq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && bEq r1' r2'
end

-- ctx Examples/DependentTypes/DB.lean:176-177
section
instance : BEq (Row s) where
  beq := Row.bEq
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:509-514
section
def prefixRow (row : Row s) :
    Row (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)
frontx_compile prefixRow
#check @prefixRow
end

end Proven.Frontx.BookS1.R293

namespace Proven.Frontx.BookS1.R300


-- ctx Examples/DependentTypes/DB.lean:7-8
section
inductive DBType where
  | int | string | bool
end

-- ctx Examples/DependentTypes/DB.lean:10-13
section
abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
end

-- ctx Examples/DependentTypes/DB.lean:39-43
section
def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int => x == y
  | .string => x == y
  | .bool => x == y
end

-- ctx Examples/DependentTypes/DB.lean:48-49
section
instance {t : DBType} : BEq t.asType where
  beq := t.beq
end

-- ctx Examples/DependentTypes/DB.lean:54-59
section
instance : BEq DBType where
  beq
    | .int, .int => true
    | .string, .string => true
    | .bool, .bool => true
    | _, _ => false
end

-- ctx Examples/DependentTypes/DB.lean:64-69
section
instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int => reprPrec
    | .string => reprPrec
    | .bool => reprPrec
end

-- ctx Examples/DependentTypes/DB.lean:653-655
section
structure NDBType where
  underlying : DBType
  nullable : Bool
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/DB.lean:657-661
section
abbrev NDBType.asType (t : NDBType) : Type :=
  if t.nullable then
    Option t.underlying.asType
  else
    t.underlying.asType
frontx_ind_type TT300_0 := NDBType
frontx_ind NDBType.asType on TT300_0
#check @NDBType.asType
end

end Proven.Frontx.BookS1.R300

namespace Proven.Frontx.BookS1.R302


-- ctx Examples/DependentTypes/Finite.lean:17-18
section
inductive NatOrBool where
  | nat | bool
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/Finite.lean:20-23
section
abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat => Nat
  | .bool => Bool
frontx_ind_type TT302_0 := NatOrBool
frontx_ind NatOrBool.asType on TT302_0
#check @NatOrBool.asType
end

end Proven.Frontx.BookS1.R302

namespace Proven.Frontx.BookS1.R303


-- ctx Examples/DependentTypes/Finite.lean:17-18
section
inductive NatOrBool where
  | nat | bool
end

-- ctx Examples/DependentTypes/Finite.lean:20-23
section
abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat => Nat
  | .bool => Bool
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/Finite.lean:32-39
section
def decode (t : NatOrBool) (input : String) : Option t.asType :=
  match t with
  | .nat => input.toNat?
  | .bool =>
    match input with
    | "true" => some true
    | "false" => some false
    | _ => none
frontx_ind_type TT303_0 := NatOrBool
frontx_ind decode on TT303_0
#check @decode
end

end Proven.Frontx.BookS1.R303

namespace Proven.Frontx.BookS1.R305


-- ctx Examples/DependentTypes/Finite.lean:17-18
section
inductive NatOrBool where
  | nat | bool
end

-- ctx Examples/DependentTypes/Finite.lean:20-23
section
abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat => Nat
  | .bool => Bool
end

-- ctx Examples/DependentTypes/Finite.lean:44-46
section
inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/Finite.lean:48-50
section
abbrev NestedPairs.asType : NestedPairs → Type
  | .nat => Nat
  | .pair t1 t2 => asType t1 × asType t2
frontx_ind_type TT305_0 := NestedPairs
frontx_ind NestedPairs.asType on TT305_0
#check @NestedPairs.asType
end

end Proven.Frontx.BookS1.R305

namespace Proven.Frontx.BookS1.R307


-- ctx Examples/DependentTypes/Finite.lean:17-18
section
inductive NatOrBool where
  | nat | bool
end

-- ctx Examples/DependentTypes/Finite.lean:20-23
section
abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat => Nat
  | .bool => Bool
end

-- ctx Examples/DependentTypes/Finite.lean:44-46
section
inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs
end

-- ctx Examples/DependentTypes/Finite.lean:48-50
section
abbrev NestedPairs.asType : NestedPairs → Type
  | .nat => Nat
  | .pair t1 t2 => asType t1 × asType t2
end

-- ctx Examples/DependentTypes/Finite.lean:63-64
section
instance {t : NestedPairs} : BEq t.asType where
  beq x y := x == y
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/Finite.lean:68-71
section
def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t with
  | .nat => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
frontx_ind_type TT307_0 := NestedPairs
frontx_ind NestedPairs.beq on TT307_0
#check @NestedPairs.beq
end

end Proven.Frontx.BookS1.R307

namespace Proven.Frontx.BookS1.R310


-- ctx Examples/DependentTypes/Finite.lean:17-18
section
inductive NatOrBool where
  | nat | bool
end

-- ctx Examples/DependentTypes/Finite.lean:20-23
section
abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat => Nat
  | .bool => Bool
end

-- ctx Examples/DependentTypes/Finite.lean:44-46
section
inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs
end

-- ctx Examples/DependentTypes/Finite.lean:48-50
section
abbrev NestedPairs.asType : NestedPairs → Type
  | .nat => Nat
  | .pair t1 t2 => asType t1 × asType t2
end

-- ctx Examples/DependentTypes/Finite.lean:63-64
section
instance {t : NestedPairs} : BEq t.asType where
  beq x y := x == y
end

-- ctx Examples/DependentTypes/Finite.lean:68-71
section
def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t with
  | .nat => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
end

-- ctx Examples/DependentTypes/Finite.lean:73-74
section
instance {t : NestedPairs} : BEq t.asType where
  beq x y := t.beq x y
end

-- ctx Examples/DependentTypes/Finite.lean:82-86
section
inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/Finite.lean:88-92
section
abbrev Finite.asType : Finite → Type
  | .unit => Unit
  | .bool => Bool
  | .pair t1 t2 => asType t1 × asType t2
  | .arr dom cod => asType dom → asType cod
frontx_ind_type TT310_0 := Finite
frontx_ind Finite.asType on TT310_0
#check @Finite.asType
end

end Proven.Frontx.BookS1.R310

namespace Proven.Frontx.BookS1.R311


-- ctx Examples/DependentTypes/Finite.lean:82-86
section
inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/Finite.lean:95-99
section
def Finite.count : Finite → Nat
  | .unit => 1
  | .bool => 2
  | .pair t1 t2 => count t1 * count t2
  | .arr dom cod => count cod ^ count dom
frontx_ind_type TT311_0 := Finite
frontx_ind Finite.count on TT311_0
#check @Finite.count
end

end Proven.Frontx.BookS1.R311

namespace Proven.Frontx.BookS1.R312


#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/Finite.lean:103-108
section
def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse
frontx_view List.product
frontx_compile List.product.view from List.product.view.eq measure fun B i => B.size - i
#check @List.product
end

end Proven.Frontx.BookS1.R312

namespace Proven.Frontx.BookS1.R314


#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/Finite.lean:118-120
section
namespace ListExtras
def List.foldr (f : α → β → β) (default : β) : List α → β
  | []     => default
  | a :: l => f a (foldr f default l)
frontx_view ListExtras.List.foldr
frontx_compile ListExtras.List.foldr.view from ListExtras.List.foldr.view.eq measure fun B i => B.size - i
#check @ListExtras.List.foldr
end ListExtras
end

end Proven.Frontx.BookS1.R314

namespace Proven.Frontx.BookS1.R320


-- ctx Examples/DependentTypes/Finite.lean:82-86
section
inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/Finite.lean:215-219
section
def Finite.isSingleton : Finite → Bool
  | .unit => true
  | .bool => false
  | .pair t1 t2 => not (isSingleton t1) || not (isSingleton t2)
  | .arr _ cod => not (isSingleton cod)
frontx_ind_type TT320_0 := Finite
frontx_ind Finite.isSingleton on TT320_0
#check @Finite.isSingleton
end

end Proven.Frontx.BookS1.R320

namespace Proven.Frontx.BookS1.R334


#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/Pitfalls.lean:8-10
section
def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => plusL n k + 1
frontx_compile Nat.plusL
#check @Nat.plusL
end

end Proven.Frontx.BookS1.R334

namespace Proven.Frontx.BookS1.R335


#eval IO.println "@@MARK@@"

-- TARGET Examples/DependentTypes/Pitfalls.lean:15-17
section
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1
frontx_compile Nat.plusR
#check @Nat.plusR
end

end Proven.Frontx.BookS1.R335

namespace Proven.Frontx.BookS1.R378


#eval IO.println "@@MARK@@"

-- TARGET Examples/FunctorApplicativeMonad.lean:557-558
section
namespace ApplicativeToFunctor
def map [Applicative f] (g : α → β) (x : f α) : f β :=
  pure g <*> x
frontx_compile ApplicativeToFunctor.map
#check @ApplicativeToFunctor.map
end ApplicativeToFunctor
end

end Proven.Frontx.BookS1.R378

namespace Proven.Frontx.BookS1.R380


#eval IO.println "@@MARK@@"

-- TARGET Examples/FunctorApplicativeMonad.lean:592-595
section
namespace MonadApplicative
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)
frontx_compile MonadApplicative.seq
#check @MonadApplicative.seq
end MonadApplicative
end

end Proven.Frontx.BookS1.R380

namespace Proven.Frontx.BookS1.R381


#eval IO.println "@@MARK@@"

-- TARGET Examples/FunctorApplicativeMonad.lean:602-605
section
namespace MonadApplicativeDesugar
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β :=
  f >>= fun g =>
  x () >>= fun y =>
  pure (g y)
frontx_compile MonadApplicativeDesugar.seq
#check @MonadApplicativeDesugar.seq
end MonadApplicativeDesugar
end

end Proven.Frontx.BookS1.R381

namespace Proven.Frontx.BookS1.R402


-- ctx Examples/Classes.lean:122-124
section
open Plus (plus)
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
end

-- ctx Examples/Classes.lean:181-183
section
open Plus (plus)
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)
end

-- ctx Examples/Classes.lean:193-194
section
open Plus (plus)
instance : Add Pos where
  add := Pos.plus
end

-- ctx Examples/Classes.lean:232-234
section
open Plus (plus)
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
end

-- ctx Examples/Classes.lean:240-244
section
open Plus (plus)
namespace Argh
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
end Argh
end

-- ctx Examples/Classes.lean:248-249
section
open Plus (plus)
namespace Argh
instance : ToString Pos where
  toString := posToString true
end Argh
end

-- ctx Examples/Classes.lean:267-268
section
open Plus (plus)
section
instance : ToString Pos where
  toString x := toString (x.toNat)
end
end

-- ctx Examples/Classes.lean:303-305
section
open Plus (plus)
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k
end

-- ctx Examples/Classes.lean:307-308
section
open Plus (plus)
instance : Mul Pos where
  mul := Pos.mul
end

-- ctx Examples/Classes.lean:457-459
section
open Plus (plus)
namespace AltPos
structure Pos where
  succ ::
  pred : Nat
end AltPos
end

-- ctx Examples/Classes.lean:757-759
section
open Plus (plus)
def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)
end

-- ctx Examples/Classes.lean:761-763
section
open Plus (plus)
def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)
end

-- ctx Examples/Classes.lean:769-770
section
open Plus (plus)
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos
end

-- ctx Examples/Classes.lean:772-773
section
open Plus (plus)
instance : HAdd Pos Nat Pos where
  hAdd := addPosNat
end

-- ctx Examples/Classes.lean:956-958
section
open Plus (plus)
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
end

-- ctx Examples/Classes.lean:1004-1005
section
open Plus (plus)
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length
end

-- ctx Examples/Classes.lean:1010-1014
section
open Plus (plus)
def NonEmptyList.get (xs : NonEmptyList α)
    (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]
end

-- ctx Examples/Classes.lean:1122-1123
section
open Plus (plus)
instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat
end

-- ctx Examples/Classes.lean:1127-1128
section
open Plus (plus)
instance : LE Pos where
  le x y := LE.le x.toNat y.toNat
end

-- ctx Examples/Classes.lean:1132-1133
section
open Plus (plus)
instance {x : Pos} {y : Pos} : Decidable (x < y) :=
  (inferInstance : Decidable (x.toNat < y.toNat))
end

-- ctx Examples/Classes.lean:1135-1136
section
open Plus (plus)
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  (inferInstance : Decidable (x.toNat ≤ y.toNat))
end

-- ctx Examples/Classes.lean:1149-1150
section
open Plus (plus)
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  (inferInstance : Decidable (x.toNat < y.toNat))
end

-- ctx Examples/Classes.lean:1199-1202
section
open Plus (plus)
namespace Cmp
inductive Ordering where
  | lt
  | eq
  | gt
end Cmp
end

-- ctx Examples/Classes.lean:1210-1214
section
open Plus (plus)
def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k
end

-- ctx Examples/Classes.lean:1216-1217
section
open Plus (plus)
instance : Ord Pos where
  compare := Pos.comp
end

-- ctx Examples/Classes.lean:1299-1299
section
open Plus (plus)
deriving instance ToString for NonEmptyList
end

-- ctx Examples/Classes.lean:1322-1324
section
open Plus (plus)
instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }
end

-- ctx Examples/Monads.lean:23-24
section
namespace Monads.Option
variable {α : Type}
def first (xs : List α) : Option α :=
  xs[0]?
end Monads.Option
end

-- ctx Examples/Monads.lean:148-150
section
namespace FakeExcept
inductive Except (ε : Type) (α : Type) where
  | error : ε → Except ε α
  | ok : α → Except ε α
end FakeExcept
end

-- ctx Examples/Monads.lean:167-170
section
namespace Monads.Err
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x
end Monads.Err
end

-- ctx Examples/Monads.lean:197-198
section
namespace Monads.Err
def first (xs : List α) : Except String α :=
  get xs 0
end Monads.Err
end

-- ctx Examples/Monads.lean:270-270
section
namespace Monads.Err
def ok (x : α) : Except ε α := Except.ok x
end Monads.Err
end

-- ctx Examples/Monads.lean:356-358
section
namespace Monads.Writer
structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
end Monads.Writer
end

-- ctx Examples/Monads.lean:366-366
section
namespace Monads.Writer
deriving instance Repr for WithLog
end Monads.Writer
end

-- ctx Examples/Monads.lean:377-377
section
namespace Monads.Writer
def ok (x : β) : WithLog α β := {log := [], val := x}
end Monads.Writer
end

-- ctx Examples/Monads.lean:488-489
section
namespace Monads.State
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)
end Monads.State
end

-- ctx Examples/Monads.lean:516-517
section
namespace Monads.State
def ok (x : α) : State σ α :=
  fun s => (s, x)
end Monads.State
end

-- ctx Examples/Monads/Many.lean:4-6
section
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α
end

-- ctx Examples/Monads/Many.lean:11-11
section
def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)
end

-- ctx Examples/Monads/Many.lean:16-18
section
def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)
end

-- ctx Examples/Monads/Many.lean:43-47
section
def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)
end

-- ctx Examples/Monads/Many.lean:162-164
section
instance : Monad Many where
  pure := Many.one
  bind := Many.bind
end

-- ctx Examples/Monads/Many.lean:182-186
section
theorem Many.union_assoc : Many.union xs (Many.union ys zs) = Many.union (Many.union xs ys) zs := by
  induction xs <;> simp [union]
  case more x xs ih =>
    funext _
    apply ih
end

-- ctx Examples/Monads/Many.lean:213-266
section
instance : LawfulMonad Many where
  map_const := by
    simp [Functor.map, Functor.mapConst]
  id_map xs := by
    induction xs <;> simp [Functor.map, Many.bind, Function.comp]
    case more x xs ih =>
      specialize ih ()
      simp [Functor.map] at ih
      simp [Many.one, Many.union]
  seqLeft_eq xs ys := by
    induction xs <;> simp [SeqLeft.seqLeft, Seq.seq, Many.bind, Functor.map, Function.comp]
    case more x xs ih =>
      specialize ih ()
      simp only [SeqLeft.seqLeft, Seq.seq, Functor.map] at ih
      simp only [ih]
      apply congrArg
      simp [Many.union, *]

  seqRight_eq xs ys := by
      induction xs with
      | none =>
        simp [SeqRight.seqRight, Many.bind, Seq.seq, Functor.map]
      | more x xs ih =>
        simp [SeqRight.seqRight, Many.bind]
        simp [SeqRight.seqRight] at ih
        rw [ih]
        simp [Seq.seq, Function.const, Functor.map, Many.bind, Function.comp, Many.one, Many.union]

  pure_seq g xs := by
    simp [Functor.map, Seq.seq, pure]

  bind_pure_comp f xs := by
    rfl
  bind_map f xs := by
    simp [bind, Functor.map, Seq.seq]
  pure_bind x f := by
    simp [bind, pure]
  bind_assoc xs f g := by
    induction xs
    case none => simp [bind, Many.bind]
    case more x xs ih =>
      specialize ih ()
      simp only [bind] at ih
      simp only [bind, Many.bind]
      generalize f x = fx
      induction fx with
      | none =>
        simp [Many.union, *]
      | more y ys ih2 =>
        simp only [Many.union, Many.bind, ih2]
        generalize g y = gy
        cases gy with simp [Many.union]
        | more z zs =>
          rw [Many.union_assoc]
end

-- ctx Examples/Monads/Class.lean:24-26
section
namespace Class
variable {α β : Type} {m : Type → Type}
class Monad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β
end Class
end

-- ctx Examples/Monads/Class.lean:32-37
section
instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x
end

-- ctx Examples/Monads/Class.lean:39-44
section
instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x
end

-- ctx Examples/Monads/Class.lean:171-176
section
namespace MyListStuff
variable {α β : Type} {m : Type → Type}
open Monads.State (State get set)
instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'
end MyListStuff
end

-- ctx Examples/Monads/Class.lean:246-251
section
namespace MyListStuff
variable {α β : Type} {m : Type → Type}
open Monads.State (State get set)
open Monads.Writer (WithLog save isEven)
instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
end MyListStuff
end

-- ctx Examples/Monads/Class.lean:657-657
section
def Reader (ρ : Type) (α : Type) : Type := ρ → α
end

-- ctx Examples/Monads/Class.lean:778-780
section
namespace Temp
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result env) env
end Temp
end

-- ctx Examples/Monads/Class.lean:787-790
section
def Reader.bind
    (result : Reader ρ α)
    (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env
end

-- ctx Examples/Monads/Class.lean:808-808
section
def Reader.pure (x : α) : Reader ρ α := fun _ => x
end

-- ctx Examples/Monads/Class.lean:885-887
section
instance : Monad (Reader ρ) where
  pure x := fun _ => x
  bind x f := fun env => f (x env) env
end

-- ctx Examples/Monads/Class.lean:890-916
section
instance : LawfulMonad (Reader ρ) where
  map_const := by
    simp [Functor.mapConst, Function.comp, Functor.map]
  id_map x := by
    funext
    simp [Functor.map, id, Function.comp]
  seqLeft_eq x _ := by
    funext
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, Function.comp]
  seqRight_eq _ y := by
    funext
    simp [SeqRight.seqRight, Seq.seq, Functor.map, Function.comp]
  pure_seq g x := by
    funext
    simp [Seq.seq, Functor.map, pure, Function.comp]
  bind_pure_comp f x := by
    funext
    simp [Functor.map, bind, pure, Function.comp]
  bind_map f x := by
    funext
    simp [Seq.seq, bind, Functor.map, Function.comp]
  pure_bind x f := by
    funext
    simp [pure, bind]
  bind_assoc x f g := by
    funext
    simp [bind]
end

-- ctx Examples/Monads/Class.lean:965-969
section
namespace Exercises
namespace Busted
set_option linter.unusedVariables false in
instance : Monad Option where
  pure x := some x
  bind opt next := none
end Busted
end Exercises
end

-- ctx Examples/Monads/Class.lean:977-982
section
namespace Exercises
open Monads.Writer (WithLog save)
instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
end Exercises
end

-- ctx Examples/Monads/Class.lean:986-986
section
namespace Exercises
open Monads.Writer (WithLog save)
deriving instance Repr for WithLog
end Exercises
end

-- ctx Examples/FunctorApplicativeMonad.lean:385-387
section
structure Pair (α β : Type) : Type where
  first : α
  second : β
end

-- ctx Examples/FunctorApplicativeMonad.lean:449-456
section
instance : LawfulFunctor (Pair α) where
  id_map x := by
    simp [Functor.map]
  map_const := by
    simp [Functor.mapConst, Functor.map]
  comp_map g h x := by
    cases x
    simp [Function.comp, Functor.map]
end

-- ctx Examples/FunctorApplicativeMonad.lean:482-482
section
def Pair.pure (x : β) : Pair α β := Pair.mk _ x
end

-- ctx Examples/FunctorApplicativeMonad.lean:592-595
section
namespace MonadApplicative
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)
end MonadApplicative
end

-- ctx Examples/FunctorApplicativeMonad.lean:1268-1277
section
open MonadApplicative in
def Validate.orElse
    (a : Validate ε α)
    (b : Unit → Validate ε α) :
    Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/FunctorApplicativeMonad.lean:1501-1503
section
open MonadApplicative in
def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, ys => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)
frontx_ind_type TT402_0 := (Many Nat)
frontx_ind Many.orElse on TT402_0
#check @Many.orElse
end

end Proven.Frontx.BookS1.R402

namespace Proven.Frontx.BookS1.R408


-- ctx Examples/Classes.lean:122-124
section
open Plus (plus)
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
end

-- ctx Examples/Classes.lean:181-183
section
open Plus (plus)
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)
end

-- ctx Examples/Classes.lean:193-194
section
open Plus (plus)
instance : Add Pos where
  add := Pos.plus
end

-- ctx Examples/Classes.lean:232-234
section
open Plus (plus)
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
end

-- ctx Examples/Classes.lean:240-244
section
open Plus (plus)
namespace Argh
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
end Argh
end

-- ctx Examples/Classes.lean:248-249
section
open Plus (plus)
namespace Argh
instance : ToString Pos where
  toString := posToString true
end Argh
end

-- ctx Examples/Classes.lean:267-268
section
open Plus (plus)
section
instance : ToString Pos where
  toString x := toString (x.toNat)
end
end

-- ctx Examples/Classes.lean:303-305
section
open Plus (plus)
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k
end

-- ctx Examples/Classes.lean:307-308
section
open Plus (plus)
instance : Mul Pos where
  mul := Pos.mul
end

-- ctx Examples/Classes.lean:457-459
section
open Plus (plus)
namespace AltPos
structure Pos where
  succ ::
  pred : Nat
end AltPos
end

-- ctx Examples/Classes.lean:757-759
section
open Plus (plus)
def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)
end

-- ctx Examples/Classes.lean:761-763
section
open Plus (plus)
def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)
end

-- ctx Examples/Classes.lean:769-770
section
open Plus (plus)
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos
end

-- ctx Examples/Classes.lean:772-773
section
open Plus (plus)
instance : HAdd Pos Nat Pos where
  hAdd := addPosNat
end

-- ctx Examples/Classes.lean:956-958
section
open Plus (plus)
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
end

-- ctx Examples/Classes.lean:1004-1005
section
open Plus (plus)
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length
end

-- ctx Examples/Classes.lean:1010-1014
section
open Plus (plus)
def NonEmptyList.get (xs : NonEmptyList α)
    (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]
end

-- ctx Examples/Classes.lean:1122-1123
section
open Plus (plus)
instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat
end

-- ctx Examples/Classes.lean:1127-1128
section
open Plus (plus)
instance : LE Pos where
  le x y := LE.le x.toNat y.toNat
end

-- ctx Examples/Classes.lean:1132-1133
section
open Plus (plus)
instance {x : Pos} {y : Pos} : Decidable (x < y) :=
  (inferInstance : Decidable (x.toNat < y.toNat))
end

-- ctx Examples/Classes.lean:1135-1136
section
open Plus (plus)
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  (inferInstance : Decidable (x.toNat ≤ y.toNat))
end

-- ctx Examples/Classes.lean:1149-1150
section
open Plus (plus)
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  (inferInstance : Decidable (x.toNat < y.toNat))
end

-- ctx Examples/Classes.lean:1199-1202
section
open Plus (plus)
namespace Cmp
inductive Ordering where
  | lt
  | eq
  | gt
end Cmp
end

-- ctx Examples/Classes.lean:1210-1214
section
open Plus (plus)
def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k
end

-- ctx Examples/Classes.lean:1216-1217
section
open Plus (plus)
instance : Ord Pos where
  compare := Pos.comp
end

-- ctx Examples/Classes.lean:1299-1299
section
open Plus (plus)
deriving instance ToString for NonEmptyList
end

-- ctx Examples/Classes.lean:1322-1324
section
open Plus (plus)
instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }
end

-- ctx Examples/Monads.lean:23-24
section
namespace Monads.Option
variable {α : Type}
def first (xs : List α) : Option α :=
  xs[0]?
end Monads.Option
end

-- ctx Examples/Monads.lean:148-150
section
namespace FakeExcept
inductive Except (ε : Type) (α : Type) where
  | error : ε → Except ε α
  | ok : α → Except ε α
end FakeExcept
end

-- ctx Examples/Monads.lean:167-170
section
namespace Monads.Err
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x
end Monads.Err
end

-- ctx Examples/Monads.lean:197-198
section
namespace Monads.Err
def first (xs : List α) : Except String α :=
  get xs 0
end Monads.Err
end

-- ctx Examples/Monads.lean:270-270
section
namespace Monads.Err
def ok (x : α) : Except ε α := Except.ok x
end Monads.Err
end

-- ctx Examples/Monads.lean:356-358
section
namespace Monads.Writer
structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
end Monads.Writer
end

-- ctx Examples/Monads.lean:366-366
section
namespace Monads.Writer
deriving instance Repr for WithLog
end Monads.Writer
end

-- ctx Examples/Monads.lean:377-377
section
namespace Monads.Writer
def ok (x : β) : WithLog α β := {log := [], val := x}
end Monads.Writer
end

-- ctx Examples/Monads.lean:488-489
section
namespace Monads.State
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)
end Monads.State
end

-- ctx Examples/Monads.lean:516-517
section
namespace Monads.State
def ok (x : α) : State σ α :=
  fun s => (s, x)
end Monads.State
end

-- ctx Examples/Monads/Many.lean:4-6
section
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α
end

-- ctx Examples/Monads/Many.lean:11-11
section
def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)
end

-- ctx Examples/Monads/Many.lean:16-18
section
def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)
end

-- ctx Examples/Monads/Many.lean:43-47
section
def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)
end

-- ctx Examples/Monads/Many.lean:162-164
section
instance : Monad Many where
  pure := Many.one
  bind := Many.bind
end

-- ctx Examples/Monads/Many.lean:182-186
section
theorem Many.union_assoc : Many.union xs (Many.union ys zs) = Many.union (Many.union xs ys) zs := by
  induction xs <;> simp [union]
  case more x xs ih =>
    funext _
    apply ih
end

-- ctx Examples/Monads/Many.lean:213-266
section
instance : LawfulMonad Many where
  map_const := by
    simp [Functor.map, Functor.mapConst]
  id_map xs := by
    induction xs <;> simp [Functor.map, Many.bind, Function.comp]
    case more x xs ih =>
      specialize ih ()
      simp [Functor.map] at ih
      simp [Many.one, Many.union]
  seqLeft_eq xs ys := by
    induction xs <;> simp [SeqLeft.seqLeft, Seq.seq, Many.bind, Functor.map, Function.comp]
    case more x xs ih =>
      specialize ih ()
      simp only [SeqLeft.seqLeft, Seq.seq, Functor.map] at ih
      simp only [ih]
      apply congrArg
      simp [Many.union, *]

  seqRight_eq xs ys := by
      induction xs with
      | none =>
        simp [SeqRight.seqRight, Many.bind, Seq.seq, Functor.map]
      | more x xs ih =>
        simp [SeqRight.seqRight, Many.bind]
        simp [SeqRight.seqRight] at ih
        rw [ih]
        simp [Seq.seq, Function.const, Functor.map, Many.bind, Function.comp, Many.one, Many.union]

  pure_seq g xs := by
    simp [Functor.map, Seq.seq, pure]

  bind_pure_comp f xs := by
    rfl
  bind_map f xs := by
    simp [bind, Functor.map, Seq.seq]
  pure_bind x f := by
    simp [bind, pure]
  bind_assoc xs f g := by
    induction xs
    case none => simp [bind, Many.bind]
    case more x xs ih =>
      specialize ih ()
      simp only [bind] at ih
      simp only [bind, Many.bind]
      generalize f x = fx
      induction fx with
      | none =>
        simp [Many.union, *]
      | more y ys ih2 =>
        simp only [Many.union, Many.bind, ih2]
        generalize g y = gy
        cases gy with simp [Many.union]
        | more z zs =>
          rw [Many.union_assoc]
end

-- ctx Examples/Monads/Class.lean:24-26
section
namespace Class
variable {α β : Type} {m : Type → Type}
class Monad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β
end Class
end

-- ctx Examples/Monads/Class.lean:32-37
section
instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x
end

-- ctx Examples/Monads/Class.lean:39-44
section
instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x
end

-- ctx Examples/Monads/Class.lean:171-176
section
namespace MyListStuff
variable {α β : Type} {m : Type → Type}
open Monads.State (State get set)
instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'
end MyListStuff
end

-- ctx Examples/Monads/Class.lean:246-251
section
namespace MyListStuff
variable {α β : Type} {m : Type → Type}
open Monads.State (State get set)
open Monads.Writer (WithLog save isEven)
instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
end MyListStuff
end

-- ctx Examples/Monads/Class.lean:657-657
section
def Reader (ρ : Type) (α : Type) : Type := ρ → α
end

-- ctx Examples/Monads/Class.lean:778-780
section
namespace Temp
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result env) env
end Temp
end

-- ctx Examples/Monads/Class.lean:787-790
section
def Reader.bind
    (result : Reader ρ α)
    (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env
end

-- ctx Examples/Monads/Class.lean:808-808
section
def Reader.pure (x : α) : Reader ρ α := fun _ => x
end

-- ctx Examples/Monads/Class.lean:885-887
section
instance : Monad (Reader ρ) where
  pure x := fun _ => x
  bind x f := fun env => f (x env) env
end

-- ctx Examples/Monads/Class.lean:890-916
section
instance : LawfulMonad (Reader ρ) where
  map_const := by
    simp [Functor.mapConst, Function.comp, Functor.map]
  id_map x := by
    funext
    simp [Functor.map, id, Function.comp]
  seqLeft_eq x _ := by
    funext
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map, Function.comp]
  seqRight_eq _ y := by
    funext
    simp [SeqRight.seqRight, Seq.seq, Functor.map, Function.comp]
  pure_seq g x := by
    funext
    simp [Seq.seq, Functor.map, pure, Function.comp]
  bind_pure_comp f x := by
    funext
    simp [Functor.map, bind, pure, Function.comp]
  bind_map f x := by
    funext
    simp [Seq.seq, bind, Functor.map, Function.comp]
  pure_bind x f := by
    funext
    simp [pure, bind]
  bind_assoc x f g := by
    funext
    simp [bind]
end

-- ctx Examples/Monads/Class.lean:965-969
section
namespace Exercises
namespace Busted
set_option linter.unusedVariables false in
instance : Monad Option where
  pure x := some x
  bind opt next := none
end Busted
end Exercises
end

-- ctx Examples/Monads/Class.lean:977-982
section
namespace Exercises
open Monads.Writer (WithLog save)
instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
end Exercises
end

-- ctx Examples/Monads/Class.lean:986-986
section
namespace Exercises
open Monads.Writer (WithLog save)
deriving instance Repr for WithLog
end Exercises
end

-- ctx Examples/FunctorApplicativeMonad.lean:385-387
section
structure Pair (α β : Type) : Type where
  first : α
  second : β
end

-- ctx Examples/FunctorApplicativeMonad.lean:449-456
section
instance : LawfulFunctor (Pair α) where
  id_map x := by
    simp [Functor.map]
  map_const := by
    simp [Functor.mapConst, Functor.map]
  comp_map g h x := by
    cases x
    simp [Function.comp, Functor.map]
end

-- ctx Examples/FunctorApplicativeMonad.lean:482-482
section
def Pair.pure (x : β) : Pair α β := Pair.mk _ x
end

-- ctx Examples/FunctorApplicativeMonad.lean:592-595
section
namespace MonadApplicative
def seq [Monad m] (f : m (α → β)) (x : Unit → m α) : m β := do
  let g ← f
  let y ← x ()
  pure (g y)
end MonadApplicative
end

-- ctx Examples/FunctorApplicativeMonad.lean:1464-1467
section
open MonadApplicative in
inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError
end

-- ctx Examples/FunctorApplicativeMonad.lean:1469-1470
section
open MonadApplicative in
instance : Append TreeError where
  append := .both
end

#eval IO.println "@@MARK@@"

-- TARGET Examples/FunctorApplicativeMonad.lean:1588-1589
section
open MonadApplicative in
section
def report : TreeError → String
  | _ => "TODO (exercise)"
frontx_ind_type TT408_0 := TreeError
frontx_ind report on TT408_0
#check @report
end
end

end Proven.Frontx.BookS1.R408

namespace Proven.Frontx.BookS1.R410


#eval IO.println "@@MARK@@"

-- TARGET Examples/FunctorApplicativeMonad/ActualDefs.lean:29-29
section
def simpleConst  (x : α) (_ : β) : α := x
frontx_compile simpleConst
#check @simpleConst
end

end Proven.Frontx.BookS1.R410
