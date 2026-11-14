/- `XPipe`: the `Pipe` language extended with more Lean standard-library list functions on bytes.

New stages (besides every old `Stage`, embedded by `XStage.base`):
* `red r`: a reduction to a fixed-format result, encoded by `Spec/Encode.lean` (`enc`):
  `List.length`, `List.sum` (byte, and 64-bit word of the `Nat` sum), `List.countP`, `List.count`, `List.any`,
  `List.all`, `List.contains`, `List.isEmpty` (all `BitVec 64` / `UInt8` / `Bool`), `List.head?`,
  `List.getLast?`, `List.find?`, `List.min?`, `List.max?` (`Option UInt8`), `List.findIdx`, `List.idxOf`
  (`BitVec 64`).
* `filter p`, `takeWhile p`, `dropWhile p` (data-dependent length; one stateful-filter loop).
* `appendC c`: `l ++ c` for a constant list `c` (prepending is `reverse, appendC c.reverse, reverse`).

Translation: every stage is an `AStmt` list over the same view state `CS` as `Pipe` (`Compiler/Front/Pipe.lean`):
the view is `[s, s+m)` with `s = a4`, `m = a1`; the result of a reduction / filter / append is the clean view
`out[0..m)` with the (possibly data-dependent) length in `a1`.  Variables: `a2` loop counter, `a5`
accumulator / filter state, `a6` element, `a7` filter write index. -/
import Compiler.Front.Pipe
import Spec.Encode

namespace Proven

/-! ## Byte predicates -/

def BCmp.eval : BCmp → UInt8 → UInt8 → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)

/-- Boolean conditions on the element `x` -/
inductive BPred where
  | cmp (c : BCmp) (a b : BExp)
  | and (p q : BPred)
  | or (p q : BPred)
  | not (p : BPred)
  | tt
  | ff
  deriving Repr

def BPred.denote (x : UInt8) : BPred → Bool
  | .cmp c a b => c.eval (a.denote 0 x) (b.denote 0 x)
  | .and p q => p.denote x && q.denote x
  | .or p q => p.denote x || q.denote x
  | .not p => !p.denote x
  | .tt => true
  | .ff => false

def BPred.noAcc : BPred → Bool
  | .cmp _ a b => a.noAcc && b.noAcc
  | .and p q | .or p q => p.noAcc && q.noAcc
  | .not p => p.noAcc
  | .tt | .ff => true

/-- the predicate as a 0/1 byte expression -/
def BPred.bit : BPred → BExp
  | .cmp c a b => .ite c a b (.lit 1) (.lit 0)
  | .and p q => .bin .and p.bit q.bit
  | .or p q => .bin .or p.bit q.bit
  | .not p => .bin .xor p.bit (.lit 1)
  | .tt => .lit 1
  | .ff => .lit 0

/-! ## Reductions -/

inductive Red where
  | length
  | sum8
  | sum64
  | countP (p : BPred)
  | count (b : UInt8)
  | any (p : BPred)
  | all (p : BPred)
  | contains (b : UInt8)
  | isEmpty
  | head
  | getLast
  | find (p : BPred)
  | min
  | max
  | findIdx (p : BPred)
  | idxOf (b : UInt8)
  deriving Repr

/-- the spec encoding (`Spec/Encode.lean`) of the standard-library function's result -/
def Red.denote : Red → List UInt8 → List UInt8
  | .length, l => enc (BitVec.ofNat 64 l.length)
  | .sum8, l => enc l.sum
  | .sum64, l => enc (BitVec.ofNat 64 (l.map UInt8.toNat).sum)
  | .countP p, l => enc (BitVec.ofNat 64 (l.countP p.denote))
  | .count b, l => enc (BitVec.ofNat 64 (l.count b))
  | .any p, l => enc (l.any p.denote)
  | .all p, l => enc (l.all p.denote)
  | .contains b, l => enc (l.contains b)
  | .isEmpty, l => enc l.isEmpty
  | .head, l => enc l.head?
  | .getLast, l => enc l.getLast?
  | .find p, l => enc (l.find? p.denote)
  | .min, l => enc l.min?
  | .max, l => enc l.max?
  | .findIdx p, l => enc (BitVec.ofNat 64 (l.findIdx p.denote))
  | .idxOf b, l => enc (BitVec.ofNat 64 (l.idxOf b))

/-- `x = b` -/
def eqB (b : UInt8) : BPred := .cmp .eq .x (.lit b)

/-- `1 + 256 x`: the word of `some x` -/
def optSomeE : AExp := .bin .add (.const 1) (.bin .shl (.var 6) (.const 8))
/-- the tag bit of an option word -/
def optTagE : AExp := .bin .and (.var 5) (.const 1)
/-- the value byte of an option word -/
def optValE : AExp := .bin .lshr (.var 5) (.const 8)

/-- reduction code parameters: `(init, loop?, step, fin, k, len)`: `a5 := init` (over `a1 = m`); if `loop?`,
`for i < m: a6 := view[i]; a5 := step`; `a5 := fin`; store the `k` low bytes of `a5`; `a1 := len` -/
structure RedC where
  init : AExp
  loop : Bool
  step : AExp
  fin : Option AExp
  k : Nat
  len : Option AExp

def Red.code : Red → RedC
  | .length => ⟨.var 1, false, .var 5, none, 8, none⟩
  | .isEmpty => ⟨.bin .eq (.var 1) (.const 0), false, .var 5, none, 1, none⟩
  | .sum8 => ⟨.const 0, true, (BExp.bin .add .acc .x).tr, none, 1, none⟩
  | .sum64 => ⟨.const 0, true, .bin .add (.var 5) (.var 6), none, 8, none⟩
  | .countP p => ⟨.const 0, true, .bin .add (.var 5) p.bit.tr, none, 8, none⟩
  | .count b => ⟨.const 0, true, .bin .add (.var 5) (eqB b).bit.tr, none, 8, none⟩
  | .any p => ⟨.const 0, true, .bin .or (.var 5) p.bit.tr, none, 1, none⟩
  | .contains b => ⟨.const 0, true, .bin .or (.var 5) (eqB b).bit.tr, none, 1, none⟩
  | .all p => ⟨.const 1, true, .bin .and (.var 5) p.bit.tr, none, 1, none⟩
  | .head | .getLast => ⟨.const 0, true, .ite optTagE (.var 5) optSomeE, none, 2,
      some (.bin .add optTagE (.const 1))⟩
  | .find p => ⟨.const 0, true, .ite optTagE (.var 5) (.ite p.bit.tr optSomeE (.const 0)), none, 2,
      some (.bin .add optTagE (.const 1))⟩
  | .min => ⟨.const 0, true,
      .bin .add (.const 1) (.bin .shl (.ite optTagE (.ite (.bin .ult (.var 6) optValE) (.var 6) optValE) (.var 6)) (.const 8)),
      none, 2, some (.bin .add optTagE (.const 1))⟩
  | .max => ⟨.const 0, true,
      .bin .add (.const 1) (.bin .shl (.ite optTagE (.ite (.bin .ult optValE (.var 6)) (.var 6) optValE) (.var 6)) (.const 8)),
      none, 2, some (.bin .add optTagE (.const 1))⟩
  | .findIdx p => ⟨.const 0, true,
      .ite optTagE (.var 5) (.ite p.bit.tr (.bin .or (.var 5) (.const 1)) (.bin .add (.var 5) (.const 2))),
      some (.bin .lshr (.var 5) (.const 1)), 8, none⟩
  | .idxOf b => ⟨.const 0, true,
      .ite optTagE (.var 5) (.ite (eqB b).bit.tr (.bin .or (.var 5) (.const 1)) (.bin .add (.var 5) (.const 2))),
      some (.bin .lshr (.var 5) (.const 1)), 8, none⟩

/-- old stages run first (`head?` on one element; `getLast?` = `head?` of the reversal) -/
def Red.pre : Red → Pipe
  | .head => [.take 1]
  | .getLast => [.reverse, .take 1]
  | _ => []

def Red.chk : Red → Option String
  | .countP p | .any p | .all p | .find p | .findIdx p =>
    if p.noAcc then none else some "predicate mentions the fold accumulator"
  | _ => none

/-! ## Extended stages -/

inductive XStage where
  | base (st : Stage)
  | red (r : Red)
  | filter (p : BPred)
  | takeWhile (p : BPred)
  | dropWhile (p : BPred)
  | appendC (c : List UInt8)
  deriving Repr

def XStage.denote : XStage → List UInt8 → List UInt8
  | .base st, l => st.denote l
  | .red r, l => r.denote l
  | .filter p, l => l.filter p.denote
  | .takeWhile p, l => l.takeWhile p.denote
  | .dropWhile p, l => l.dropWhile p.denote
  | .appendC c, l => l ++ c

abbrev XPipe := List XStage

def XPipe.denote (p : XPipe) (xs : List UInt8) : List UInt8 := p.foldl (fun l st => st.denote l) xs

theorem XPipe.denote_append (p q : XPipe) (xs : List UInt8) :
    XPipe.denote (p ++ q) xs = q.denote (p.denote xs) := by simp [XPipe.denote]

/-- an upper bound of the output length -/
def XStage.len : XStage → Nat → Nat
  | .base st, n => st.len n
  | .red r, _ => r.code.k
  | .filter _, n | .takeWhile _, n | .dropWhile _, n => n
  | .appendC c, n => n + c.length

def XStage.chk : XStage → Option String
  | .base st => st.chk
  | .red r => r.chk
  | .filter p | .takeWhile p | .dropWhile p =>
    if p.noAcc then none else some "predicate mentions the fold accumulator"
  | .appendC c => if c.length < 2 ^ 32 then none else some "append: constant list too long"

/-! ## Translation -/

def optA (v : Fin 8) : Option AExp → List AStmt
  | none => []
  | some e => [.assign v e]

/-- the code of a reduction on the view `cs` -/
def redC (cs : CS) (c : RedC) : List AStmt :=
  [.assign 5 c.init] ++ (if c.loop then [loopV 1 (.seq (fetch cs) (.assign 5 c.step))] else []) ++
    optA 5 c.fin ++ emitC c.k ++ optA 1 c.len

def preC : Pipe → CS → List AStmt × CS
  | [], cs => ([], cs)
  | st :: r, cs => ((stageC st cs).1 ++ (preC r (stageC st cs).2).1, (preC r (stageC st cs).2).2)

/-- stateful filter: state `a5` (from `s0`), keep `x` iff `K ≠ 0`, next state `N`; written to `out[a7]` -/
def sfC (cs : CS) (K N : BExp) (s0 : UInt8) : List AStmt :=
  (if cs.onOut then mat cs else []) ++
  [.assign 5 (.const (zx s0)), .assign 7 (.const 0),
   loopV 1 (.seq (fetch (if cs.onOut then csClean else cs))
     (.seq (.store 1 (.var 7) (.var 6))
     (.seq (.assign 7 (.bin .add (.var 7) (.ite K.tr (.const 1) (.const 0))))
       (.assign 5 N.tr)))),
   .assign 1 (.var 7), .assign 4 (.const 0)]

def appStores : Nat → List UInt8 → List AStmt
  | _, [] => []
  | j, b :: r => .store 1 (.bin .add (.var 1) (.const (.ofNat 64 j))) (.const (zx b)) :: appStores (j + 1) r

def appC (cs : CS) (c : List UInt8) : List AStmt :=
  mat cs ++ appStores 0 c ++ [.assign 1 (.bin .add (.var 1) (.const (.ofNat 64 c.length)))]

def takeK (p : BPred) : BExp := .bin .and .acc p.bit
def dropK (p : BPred) : BExp := .bin .xor (.bin .and .acc p.bit) (.lit 1)

def xstageC : XStage → CS → List AStmt × CS
  | .base st, cs => stageC st cs
  | .red r, cs => ((preC r.pre cs).1 ++ redC (preC r.pre cs).2 r.code, csClean)
  | .filter p, cs => (sfC cs p.bit (.lit 0) 0, csClean)
  | .takeWhile p, cs => (sfC cs (takeK p) (takeK p) 1, csClean)
  | .dropWhile p, cs => (sfC cs (dropK p) (takeK p) 1, csClean)
  | .appendC c, cs => (appC cs c, csClean)

def xstmts : XPipe → CS → List AStmt
  | [], cs => mat cs
  | st :: r, cs => (xstageC st cs).1 ++ xstmts r (xstageC st cs).2

def XPipe.prog (p : XPipe) : AStmt := (xstmts p cs0).foldl .seq (.assign 4 (.const 0))

/-! ## Output-block space -/

def XStage.space : XStage → CS → Nat → Nat
  | .base st, cs, n => st.space cs n
  | .red r, _, _ => r.code.k
  | .filter _, _, n | .takeWhile _, _, n | .dropWhile _, _, n => n
  | .appendC c, _, n => n + c.length

def XPipe.need : XPipe → CS → Nat → Nat
  | [], cs, n => if cs.clean then 0 else n
  | st :: r, cs, n => max (st.space cs n) (XPipe.need r (xstageC st cs).2 (st.len n))

/-- output-block bytes the compiled pipe needs for an input of `n` bytes -/
def XPipe.space (p : XPipe) (n : Nat) : Nat := XPipe.need p cs0 n

end Proven
