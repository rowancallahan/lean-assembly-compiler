/- User inductives with payload (`frontx_ind_type`, `frontx_ind`, `Riscv/Frontx/IndCmd.lean`): book and con-leche
functions copied verbatim (provenance per block; the blocks are wrapped in this file's namespace), each with a
generated `Implements1` theorem `f.implements1`. -/
import Riscv.Frontx.IndCmd

namespace Proven.Frontx.IndEx

/-! ## fp-lean (Functional Programming in Lean) @0abeea5 -/

-- examples/Examples/Classes.lean:1255-1257
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

-- examples/Examples/Induction.lean:318-321
def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r =>
    1 + l.count + r.count

-- examples/Examples/Monads/Conveniences.lean:53-55
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

-- examples/Examples/Induction.lean:516-519
def BinTree.graftLeft (root newBranch : BinTree α) : BinTree α :=
  match root with
  | .leaf => newBranch
  | .branch l x r => .branch (l.graftLeft newBranch) x r

frontx_ind_type BTN := BinTree Nat
frontx_ind BinTree.count on BTN
frontx_ind BinTree.mirror on BTN
frontx_ind BinTree.graftLeft on BTN

-- examples/Examples/Classes.lean:122-124
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

-- examples/Examples/Classes.lean:232-234
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

-- examples/Examples/Classes.lean:181-183
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

frontx_ind_type PosT := Pos
frontx_ind Pos.toNat on PosT
frontx_ind Pos.plus on PosT

-- examples/Examples/ProgramsProofs/TCO.lean:6-8
def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

-- examples/Examples/ProgramsProofs/TCO.lean:40-45
def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs

-- examples/Examples/ProgramsProofs/TCO.lean:102-107
def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs

frontx_ind_type LN := List Nat
frontx_ind NonTail.sum on LN
frontx_ind Tail.sum on LN
frontx_ind Tail.reverse on LN
-- the core library's `List.append` (Lean 4.29 `Init/Prelude.lean`), `xs ++ ys` on two inputs
frontx_ind List.append on LN

end Proven.Frontx.IndEx

/-! ## con-leche @6810492 (via `Testing/conleche/Orig.lean` @739d261 of branch `conleche-survey`; same namespaces) -/

namespace ConLeche

-- Kernel/Name.lean:28-39
inductive Name where
  | anonymous
  | str (pre : Name) (s : String)
  | num (pre : Name) (n : Nat)
with
  /-- The cached hash of a name (official: the `uint64` in the `Name`
  object's header). -/
  @[computed_field] hashData : Name → UInt64
    | .anonymous => 1723
    | .str p s => mixHash (mixHash 1 p.hashData) (hash s)
    | .num p n => mixHash (mixHash 2 p.hashData) (hash n)
deriving Repr, Inhabited

-- Kernel/Name.lean:43-43
instance : Hashable Name := ⟨Name.hashData⟩

-- Kernel/Expr.lean:38-52
inductive Level where
  | zero
  | succ (u : Level)
  | max (u v : Level)
  | imax (u v : Level)
  | param (n : Name)
with
  /-- The cached hash of a level. -/
  @[computed_field] hashData : Level → UInt64
    | .zero => 1
    | .succ u => mixHash 3 u.hashData
    | .max u v => mixHash 5 (mixHash u.hashData v.hashData)
    | .imax u v => mixHash 7 (mixHash u.hashData v.hashData)
    | .param n => mixHash 11 (hash n)
deriving Repr, Inhabited

-- Kernel/Expr.lean:187-191
def levelHasParam : Level → Bool
  | .zero => false
  | .param _ => true
  | .succ u => levelHasParam u
  | .max u v | .imax u v => levelHasParam u || levelHasParam v

end ConLeche

namespace ConLeche.Level

-- Kernel/Level.lean:55-60
def isNeverZero : Level → Bool
  | .zero => false
  | .param _ => false
  | .succ _ => true
  | .max l r => isNeverZero l || isNeverZero r
  | .imax _ r => isNeverZero r

end ConLeche.Level

namespace Proven.Frontx.IndEx
-- the `Name` of `param` is dropped from the byte format (neither function reads it)
frontx_ind_type LevelT := ConLeche.Level
frontx_ind ConLeche.levelHasParam on LevelT
frontx_ind ConLeche.Level.isNeverZero on LevelT
end Proven.Frontx.IndEx
