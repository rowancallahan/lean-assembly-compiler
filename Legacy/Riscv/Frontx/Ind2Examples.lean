/- Inductives, part 2 (NOTES section 21): programs of several functions (a call of another function of the
program: `E.ext`), matches on several values and on computed values, `let`, `=` with a constant, `Option`
results, the scalar argument from the input.  Library and book code copied verbatim (provenance per block), each
with a generated `Implements1` theorem `f.implements1`.

Space: a program of one function allocating at most `M` cells per input node keeps the linear bound
(`Ind.space M` / `Ind.spaceA 1 16 (fun n => M * n)`).  A program with calls of other functions can allocate more
than a fixed number of cells per node (`Pos.mul` allocates `|n| · |k|` cells, `NonTail.reverse` `n² / 2`): its
statement has `Ind.spaceA m nl (cellsSup …)`, `cellsSup … n` the largest cell count (`Pg.al`, the constructor
applications evaluated) over all inputs of `n` bytes (`Compiler/IndSup.lean`). -/
import Legacy.Riscv.Frontx.IndCmpExamples

/-! ## fp-lean (Functional Programming in Lean) @0abeea5 -/

namespace Proven.Frontx.IndEx

-- examples/Examples/Classes.lean:193-194
instance : Add Pos where
  add := Pos.plus

-- examples/Examples/Classes.lean:303-305
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

-- `Pos.mul` calls `Pos.plus` (through `+`): two functions
frontx_ind Pos.mul on PosT

-- examples/Examples/ProgramsProofs/TCO.lean:74-76
def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

-- `++` is the core library's `List.append`: two functions
frontx_ind NonTail.reverse on LN

-- examples/Examples/Classes.lean:1259-1265
def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

-- a match on two trees: the second one's tag and fields are read from its cell
frontx_ind eqBinTree on BTN

-- examples/Examples/Classes.lean:1210-1214
def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

-- an `Ordering` result (the type of `IndCmpExamples`, `OrdT`)
frontx_ind Pos.comp on PosT using Proven.Frontx.IndCmp.OrdT

end Proven.Frontx.IndEx

/-! ## Lean 4 v4.29.0 `doc/examples/bintree.lean` -/

namespace Proven.Frontx.IndCmp

-- doc/examples/bintree.lean:40-49
def Tree.find? (t : Tree β) (k : Nat) : Option β :=
  match t with
  | leaf => none
  | node left key value right =>
    if k < key then
      left.find? k
    else if key < k then
      right.find? k
    else
      some value

frontx_ind_type OU := Option Unit

/-- entry: is the key in the tree (the key is the 8 bytes after the tree) -/
def containsK (t : Tree Unit) (k : Nat) : Bool := t.contains k
/-- entry: `find?` with the key from the input; an `Option Unit` result -/
def findK (t : Tree Unit) (k : Nat) : Option Unit := t.find? k

frontx_ind containsK on TU
frontx_ind findK on TU using OU

end Proven.Frontx.IndCmp

/-! ## con-leche @6810492: `Level.combining`, `Level.simplify` (the decidable equalities only as instances) -/

namespace ConLeche

-- Kernel/Name.lean:47-61
def Name.decEq : (a b : Name) → Decidable (a = b)
  | .anonymous, .anonymous => isTrue rfl
  | .str p s, .str q t =>
    match Name.decEq p q with
    | isTrue hp => if hs : s = t then isTrue (by rw [hp, hs])
                   else isFalse (fun e => hs (Name.str.inj e).2)
    | isFalse hp => isFalse (fun e => hp (Name.str.inj e).1)
  | .num p n, .num q m =>
    match Name.decEq p q with
    | isTrue hp => if hn : n = m then isTrue (by rw [hp, hn])
                   else isFalse (fun e => hn (Name.num.inj e).2)
    | isFalse hp => isFalse (fun e => hp (Name.num.inj e).1)
  | .anonymous, .str .. | .anonymous, .num .. | .str .., .anonymous
  | .str .., .num .. | .num .., .anonymous | .num .., .str .. =>
    isFalse (fun e => Name.noConfusion e)

-- Kernel/Name.lean:112-112
instance : DecidableEq Name := Name.decEq

-- Kernel/Expr.lean:59-83
def Level.decEq : (a b : Level) → Decidable (a = b)
  | .zero, .zero => isTrue rfl
  | .succ u, .succ v =>
    match Level.decEq u v with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun e => h (Level.succ.inj e))
  | .max u v, .max u' v' =>
    match Level.decEq u u', Level.decEq v v' with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse (fun e => h (Level.max.inj e).1)
    | _, isFalse h' => isFalse (fun e => h' (Level.max.inj e).2)
  | .imax u v, .imax u' v' =>
    match Level.decEq u u', Level.decEq v v' with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse (fun e => h (Level.imax.inj e).1)
    | _, isFalse h' => isFalse (fun e => h' (Level.imax.inj e).2)
  | .param n, .param m =>
    if h : n = m then isTrue (by rw [h])
    else isFalse (fun e => h (Level.param.inj e))
  | .zero, .succ .. | .zero, .max .. | .zero, .imax .. | .zero, .param ..
  | .succ .., .zero | .succ .., .max .. | .succ .., .imax .. | .succ .., .param ..
  | .max .., .zero | .max .., .succ .. | .max .., .imax .. | .max .., .param ..
  | .imax .., .zero | .imax .., .succ .. | .imax .., .max .. | .imax .., .param ..
  | .param .., .zero | .param .., .succ .. | .param .., .max .. | .param .., .imax .. =>
    isFalse (fun e => Level.noConfusion e)

-- Kernel/Expr.lean:130-130
instance : DecidableEq Level := Level.decEq

end ConLeche

namespace ConLeche.Level

-- Kernel/Level.lean:63-67
def combining : Level → Level → Level
  | .zero, r => r
  | l, .zero => l
  | .succ l, .succ r => .succ (combining l r)
  | l, r => .max l r

-- Kernel/Level.lean:70-82
def simplify : Level → Level
  | .zero => .zero
  | .param n => .param n
  | .succ l => .succ (simplify l)
  | .max l r => combining (simplify l) (simplify r)
  | .imax l r =>
    let ls := simplify l
    let rs := simplify r
    if ls = .zero || ls = .succ .zero then rs
    else match rs with
      | .zero => .zero
      | .succ _ => combining ls rs
      | _ => .imax ls rs

end ConLeche.Level

namespace Proven.Frontx.IndEx
-- a match on two levels (overlapping patterns, the current node `me`)
frontx_ind ConLeche.Level.combining on LevelT
-- `let`, `=` with constants, a match on a computed level, calls of `combining`: two functions
frontx_ind ConLeche.Level.simplify on LevelT
end Proven.Frontx.IndEx
