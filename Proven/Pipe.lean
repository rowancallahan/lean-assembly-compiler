/- `Pipe`: a combinator language for byte-list functions `List UInt8 → List UInt8`, with its denotation as
plain Lean list functions, and its translation to `AStmt` programs (`Pipe.prog`).

Stages (applied left to right): `map e` (`e` a byte expression over the element), `take n`, `drop n`,
`reverse`, `sort` (`List.mergeSort`), `fold e i` (byte accumulator, result = 1 byte), `foldW w i`
(64-bit accumulator, result = its 8 little-endian bytes).

Compilation scheme.  Blocks: 0 = input (base `a0`), 1 = output (base `a3`); no scratch, no stack.
The current list is a *view*: a window `[s, s+m)` of the input or the output block, read forwards or
backwards, with pending byte maps.  `m` is `a1`, `s` is `a4`; `take`/`drop` only move `s`/`m`, `reverse`
flips a compile-time flag, `map` appends to the pending list (so `map`/`take`/`drop`/`reverse` chains fuse
into one loop).  The view is written out ("materialized") to `out[0..m)` at the end and before a `sort`
(one loop; preceded by an in-place reversal if the view reads the output block backwards); a fold runs
one loop over the view and then stores the accumulator bytes.
Variables: `a2` loop counter, `a5` accumulator / temporary, `a6` element, `a7` temporary. -/
import Proven.SortMachine

namespace Proven

/-! ## Byte expressions -/

inductive BOp where | add | sub | and | or | xor
  deriving DecidableEq, Repr
inductive BCmp where | lt | le | eq
  deriving DecidableEq, Repr

def BOp.eval : BOp → UInt8 → UInt8 → UInt8
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b

/-- byte expressions over the element `x` and (in a `fold`) the accumulator `acc` -/
inductive BExp where
  | x
  | acc
  | lit (c : UInt8)
  | bin (op : BOp) (a b : BExp)
  /-- `if a ⋈ b then t else e` -/
  | ite (c : BCmp) (a b t e : BExp)
  deriving Repr

def BExp.denote (acc x : UInt8) : BExp → UInt8
  | .x => x
  | .acc => acc
  | .lit c => c
  | .bin op a b => op.eval (a.denote acc x) (b.denote acc x)
  | .ite .lt a b t e => if a.denote acc x < b.denote acc x then t.denote acc x else e.denote acc x
  | .ite .le a b t e => if a.denote acc x ≤ b.denote acc x then t.denote acc x else e.denote acc x
  | .ite .eq a b t e => if a.denote acc x = b.denote acc x then t.denote acc x else e.denote acc x

def BExp.noAcc : BExp → Bool
  | .x | .lit _ => true
  | .acc => false
  | .bin _ a b => a.noAcc && b.noAcc
  | .ite _ a b t e => a.noAcc && b.noAcc && t.noAcc && e.noAcc

/-- a byte, zero-extended to a word -/
def zx (u : UInt8) : BitVec 64 := u.toBitVec.setWidth 64

/-- `e &&& 0xff` -/
def mask8 (e : AExp) : AExp := .bin .and e (.const 255)

/-- the word expression computing `zx (e.denote acc x)` from `a5 = zx acc`, `a6 = zx x` -/
def BExp.tr : BExp → AExp
  | .x => .var 6
  | .acc => .var 5
  | .lit c => .const (zx c)
  | .bin .add a b => mask8 (.bin .add a.tr b.tr)
  | .bin .sub a b => mask8 (.bin .sub a.tr b.tr)
  | .bin .and a b => .bin .and a.tr b.tr
  | .bin .or a b => .bin .or a.tr b.tr
  | .bin .xor a b => .bin .xor a.tr b.tr
  | .ite .lt a b t e => .ite (.bin .ult a.tr b.tr) t.tr e.tr
  | .ite .le a b t e => .ite (.bin .ult b.tr a.tr) e.tr t.tr
  | .ite .eq a b t e => .ite (.bin .eq a.tr b.tr) t.tr e.tr

/-! ## Word expressions (fold steps with a 64-bit accumulator) -/

inductive WExp where
  | acc
  /-- the element, zero-extended -/
  | x
  | const (c : BitVec 64)
  | bin (op : Op) (a b : WExp)
  /-- `a` if `c ≠ 0`, else `b` -/
  | ite (c a b : WExp)
  deriving Repr

def WExp.denote (acc : BitVec 64) (x : UInt8) : WExp → BitVec 64
  | .acc => acc
  | .x => x.toBitVec.setWidth 64
  | .const c => c
  | .bin op a b => op.eval (a.denote acc x) (b.denote acc x)
  | .ite c a b => if c.denote acc x = 0 then b.denote acc x else a.denote acc x

def WExp.tr : WExp → AExp
  | .acc => .var 5
  | .x => .var 6
  | .const c => .const c
  | .bin op a b => .bin op a.tr b.tr
  | .ite c a b => .ite c.tr a.tr b.tr

/-! ## Stages and pipes -/

/-- the `k` low bytes of `a`, least significant first -/
def leBytes (a : BitVec 64) (k : Nat) : List UInt8 :=
  (List.range k).map fun j => ⟨(a >>> (8 * j)).setWidth 8⟩

inductive Stage where
  | map (e : BExp)
  | take (n : Nat)
  | drop (n : Nat)
  | reverse
  | sort
  /-- byte fold: the one-byte list `[foldl step init]` -/
  | fold (step : BExp) (init : UInt8)
  /-- word fold: the 8 little-endian bytes of `foldl step init` -/
  | foldW (step : WExp) (init : BitVec 64)
  deriving Repr

def Stage.denote : Stage → List UInt8 → List UInt8
  | .map e, l => l.map fun x => e.denote 0 x
  | .take n, l => l.take n
  | .drop n, l => l.drop n
  | .reverse, l => l.reverse
  | .sort, l => l.mergeSort leU
  | .fold e i, l => [l.foldl (fun a x => e.denote a x) i]
  | .foldW w i, l => leBytes (l.foldl (fun a x => w.denote a x) i) 8

/-- a pipe is a list of stages, applied left to right; composition is `++` (`Pipe.denote_append`) -/
abbrev Pipe := List Stage

def Pipe.denote (p : Pipe) (xs : List UInt8) : List UInt8 := p.foldl (fun l st => st.denote l) xs

theorem Pipe.denote_append (p q : Pipe) (xs : List UInt8) : Pipe.denote (p ++ q) xs = q.denote (p.denote xs) := by
  simp [Pipe.denote]

/-- output length as a function of the input length -/
def Stage.len : Stage → Nat → Nat
  | .map _, n | .reverse, n | .sort, n => n
  | .take k, n => min k n
  | .drop k, n => n - k
  | .fold .., _ => 1
  | .foldW .., _ => 8

def Pipe.len (p : Pipe) (n : Nat) : Nat := p.foldl (fun n st => st.len n) n

/-- static restrictions on a stage; `some reason` = rejected -/
def Stage.chk : Stage → Option String
  | .map e => if e.noAcc then none else some "map: the body mentions the fold accumulator"
  | .take n => if n < 2 ^ 64 then none else some s!"take: count {n} does not fit 64 bits"
  | .drop n => if n < 2 ^ 64 then none else some s!"drop: count {n} does not fit 64 bits"
  | _ => none

/-! ## Translation to statements -/

/-- compile-time state of the view: which block it reads, direction, whether `s = 0` is known, pending maps -/
structure CS where
  onOut : Bool
  rev : Bool
  s0 : Bool
  gs : List AExp

def cs0 : CS := ⟨false, false, true, []⟩
/-- the list is `out[0..m)` -/
def csClean : CS := ⟨true, false, true, []⟩
def CS.clean (cs : CS) : Bool := cs.onOut && !cs.rev && cs.s0 && cs.gs.isEmpty

/-- `min n m` -/
def minE (n : Nat) : AExp := .ite (.bin .ult (.const (.ofNat 64 n)) (.var 1)) (.const (.ofNat 64 n)) (.var 1)

/-- block index of view element `a2`: `s + i`, or `s + m - 1 - i` -/
def vIdx (rev : Bool) : AExp :=
  if rev then .bin .sub (.bin .sub (.bin .add (.var 4) (.var 1)) (.const 1)) (.var 2)
  else .bin .add (.var 4) (.var 2)

def fetchG (p : AStmt) : List AExp → AStmt
  | [] => p
  | g :: gs => fetchG (.seq p (.assign 6 g)) gs

/-- `a6 :=` view element `a2`, with the pending maps applied -/
def fetch (cs : CS) : AStmt := fetchG (.load 6 (if cs.onOut then 1 else 0) (vIdx cs.rev)) cs.gs

/-- `for a2 in [0, a_c)` -/
def loopV (c : Fin 8) (body : AStmt) : AStmt :=
  .seq (.assign 2 (.const 0))
    (.loop (.bin .ult (.var 2) (.var c)) (.seq body (.assign 2 (.bin .add (.var 2) (.const 1)))))

/-- reverse `out[s, s+m)` in place -/
def revC : List AStmt :=
  [.assign 7 (.bin .lshr (.var 1) (.const 1)),
   loopV 7 (.seq (.load 5 1 (vIdx false)) (.seq (.load 6 1 (vIdx true))
     (.seq (.store 1 (vIdx false) (.var 6)) (.store 1 (vIdx true) (.var 5)))))]

/-- write the view to `out[0..m)` -/
def mat (cs : CS) : List AStmt :=
  if cs.clean then [] else
    (if cs.onOut && cs.rev then revC else []) ++
    [loopV 1 (.seq (fetch { cs with rev := cs.rev && !cs.onOut }) (.store 1 (.var 2) (.var 6))),
     .assign 4 (.const 0)]

/-- `out[0..k) :=` the low `k` bytes of `a5`; the view becomes `out[0..k)` -/
def emitC (k : Nat) : List AStmt :=
  [.assign 1 (.const (.ofNat 64 k)),
   loopV 1 (.store 1 (.var 2) (.bin .lshr (.var 5) (.bin .shl (.var 2) (.const 3)))),
   .assign 4 (.const 0)]

/-- fold the view into `a5` with step `S`, then emit `k` bytes -/
def foldC (cs : CS) (S : AExp) (init : BitVec 64) (k : Nat) : List AStmt :=
  [.assign 5 (.const init), loopV 1 (.seq (fetch cs) (.assign 5 S))] ++ emitC k

def stageC : Stage → CS → List AStmt × CS
  | .map e, cs => ([], { cs with gs := cs.gs ++ [e.tr] })
  | .take n, cs =>
    if cs.rev then
      ([.assign 4 (.bin .add (.var 4) (.bin .sub (.var 1) (minE n))), .assign 1 (minE n)], { cs with s0 := false })
    else ([.assign 1 (minE n)], cs)
  | .drop n, cs =>
    if cs.rev then ([.assign 1 (.bin .sub (.var 1) (minE n))], cs)
    else ([.assign 4 (.bin .add (.var 4) (minE n)), .assign 1 (.bin .sub (.var 1) (minE n))], { cs with s0 := false })
  | .reverse, cs => ([], { cs with rev := !cs.rev })
  | .sort, cs => (mat cs ++ [insProg, .assign 4 (.const 0)], csClean)
  | .fold e i, cs => (foldC cs e.tr (zx i) 1, csClean)
  | .foldW w i, cs => (foldC cs w.tr i 8, csClean)

def stmts : Pipe → CS → List AStmt
  | [], cs => mat cs
  | st :: r, cs => (stageC st cs).1 ++ stmts r (stageC st cs).2

/-- the statement program of a pipe: `a4 := 0`, the stages, the final materialization -/
def Pipe.prog (p : Pipe) : AStmt := (stmts p cs0).foldl .seq (.assign 4 (.const 0))

/-! ## Output-block space -/

/-- bytes of the output block a stage writes, for a view of length `n` -/
def Stage.space : Stage → CS → Nat → Nat
  | .sort, cs, n => if cs.clean then 0 else n
  | .fold .., _, _ => 1
  | .foldW .., _, _ => 8
  | _, _, _ => 0

def Pipe.need : Pipe → CS → Nat → Nat
  | [], cs, n => if cs.clean then 0 else n
  | st :: r, cs, n => max (st.space cs n) (Pipe.need r (stageC st cs).2 (st.len n))

/-- size of the output block the compiled pipe needs for an input of `n` bytes: the largest
materialized intermediate list (`≥` the result length) -/
def Pipe.space (p : Pipe) (n : Nat) : Nat := Pipe.need p cs0 n

end Proven
