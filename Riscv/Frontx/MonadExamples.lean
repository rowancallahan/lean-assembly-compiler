/- Monads by specialisation (NOTES §29): targets.

Book text verbatim from fp-lean @0abeea5 (`leanprover/fp-lean`, `examples/Examples/MonadTransformers/Do.lean`, line
numbers given; anchors and `#eval`s dropped).  Each entry point `g : ByteArray → R` is ours: it runs the monadic
definition on the input bytes (`.run s₀` for a state, a known predicate for `count`).  `frontx_monad_entry g` /
`frontx_monad_fn g` specialise the monad (`SpecMonad.lean`), compile the first-order copy with the existing
translator and add `g.prog`/`g.exec`; `frontx_implements[_bytes] g` the machine theorem `g.implements1` (about `g`
itself).  Nothing is proved by hand. -/
import Riscv.Frontx.SpecMonad
import Riscv.Frontx.Impl1

namespace Proven.Frontx.Mon
open Proven Proven.Frontx

/-! ## fp-lean, `MonadTransformers/Do.lean:62-84`: `count`, `countNot`, polymorphic in `[Monad m] [MonadState Nat m]` -/

namespace ThenDoUnless

def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    if ← p x then
      modify (· + 1)
    count p xs

def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    unless ← p x do
      modify (· + 1)
    countNot p xs

end ThenDoUnless

/-- `count` at `StateM Nat` with a pure predicate -/
def countGt3 (xs : ByteArray) : Unit × Nat :=
  (ThenDoUnless.count (m := StateM Nat) (fun x => pure (x > 3)) xs.data.toList).run 0
frontx_monad_entry countGt3 with fun B i acc => i ≤ B.size ∧ acc + (B.size - i) < 2 ^ 64
frontx_implements_bytes countGt3

/-- `countNot` at `StateM Nat` -/
def countNotGt3 (xs : ByteArray) : Unit × Nat :=
  (ThenDoUnless.countNot (m := StateM Nat) (fun x => pure (x > 3)) xs.data.toList).run 0
frontx_monad_entry countNotGt3 with fun B i acc => i ≤ B.size ∧ acc + (B.size - i) < 2 ^ 64
frontx_implements_bytes countNotGt3

/-- `count` at `StateT Nat (Except String)`, the predicate throws on a zero byte -/
def countGt3Exc (xs : ByteArray) : Except String (Unit × Nat) :=
  (ThenDoUnless.count (m := StateT Nat (Except String))
    (fun x => if x = 0 then throw "zero" else pure (x > 3)) xs.data.toList).run 0
frontx_monad_entry countGt3Exc with fun B i acc => i ≤ B.size ∧ acc + (B.size - i) < 2 ^ 64
frontx_implements_bytes countGt3Exc

/-! ## fp-lean, `MonadTransformers/Do.lean:105-130`: `EarlyReturn.runCatch` and `Desugared.List.find?` (`ExceptT α Option`,
`throw`, `monadLift`; §27 could not do it) -/

namespace EarlyReturn

def runCatch [Monad m] (action : ExceptT α m α) : m α := do
  match ← action with
  | Except.ok x => pure x
  | Except.error x => pure x

namespace Desugared
def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs =>
    runCatch do
      if p x then throw x else pure ()
      monadLift (find? p xs)
end Desugared

end EarlyReturn

def desFindGt3 (xs : ByteArray) : Option UInt8 := EarlyReturn.Desugared.List.find? (· > 3) xs.data.toList
frontx_monad_entry desFindGt3
frontx_implements desFindGt3

/-! ## fp-lean, `MonadTransformers/Do.lean:324-350`: `for` loops: early `return`, `continue`, `let mut` in `Id.run do` -/

namespace Loops

def List.find? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if p x then return x
  failure

namespace Cont
def List.find? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if not (p x) then continue
    return x
  failure
end Cont

def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  for x in xs do
    if p x then found := found + 1
  return found

end Loops

def loopFindGt3 (xs : ByteArray) : Option UInt8 := Loops.List.find? (· > 3) xs.data.toList
frontx_monad_entry loopFindGt3
frontx_implements loopFindGt3

def contFindGt3 (xs : ByteArray) : Option UInt8 := Loops.Cont.List.find? (· > 3) xs.data.toList
frontx_monad_entry contFindGt3
frontx_implements contFindGt3

def loopCountSp (xs : ByteArray) : Nat := Loops.List.count (· == 32) xs.data.toList
frontx_monad_entry loopCountSp with fun B i acc => i ≤ B.size ∧ acc + (B.size - i) < 2 ^ 64
frontx_implements loopCountSp

/-! ## fp-lean, `MonadTransformers/Do.lean:354-400`: `Mut.St.two` (a `StateT Nat Id` block run on `0`), `Mut.three`,
`Mut.six` (`for` over a literal list, unrolled) -/

namespace Mut

namespace St
def two : Nat :=
  let block : StateT Nat Id Nat := do
    modify (· + 1)
    modify (· + 1)
    return (← get)
  let (result, _finalState) := block 0
  result
end St

def three : Nat := Id.run do
  let mut x := 0
  for _ in [1, 2, 3] do
    x := x + 1
  return x

def six : Nat := Id.run do
  let mut x := 0
  for y in [1, 2, 3] do
    x := x + y
  return x

end Mut

def twoE (_xs : ByteArray) : Nat := Mut.St.two
frontx_monad_fn twoE
frontx_implements twoE

def threeE (_xs : ByteArray) : Nat := Mut.three
frontx_monad_fn threeE
frontx_implements threeE

def sixE (_xs : ByteArray) : Nat := Mut.six
frontx_monad_fn sixE
frontx_implements sixE

/-! ## This repo: the other monads and operations (`StateT σ (Except ε)` with `throw` and `try … catch`, `ReaderT`
over `StateM`, `get`/`set`, a structure as the state, `[MonadExcept]` at `Except`, `tryCatch` in `Except`) -/

/-- `StateT Nat (Except String)`: sum of the bytes, `throw` on a zero -/
def sumNZ : List UInt8 → StateT Nat (Except String) Unit
  | [] => pure ()
  | x :: xs => do
    if x = 0 then throw "zero"
    modify (· + x.toNat)
    sumNZ xs
def sumNZE (xs : ByteArray) : Except String (Unit × Nat) := (sumNZ xs.data.toList).run 0
frontx_monad_entry sumNZE with fun B i acc => i ≤ B.size ∧ acc + 255 * (B.size - i) < 2 ^ 64
frontx_implements_bytes sumNZE

/-- `try … catch` inside the loop body: an error is caught and counted -/
def countZeros : List UInt8 → StateT Nat (Except String) Unit
  | [] => pure ()
  | x :: xs => do
    try
      if x = 0 then throw "zero"
    catch _ =>
      modify (· + 1)
    countZeros xs
def countZerosE (xs : ByteArray) : Except String (Unit × Nat) := (countZeros xs.data.toList).run 0
frontx_monad_entry countZerosE with fun B i acc => i ≤ B.size ∧ acc + (B.size - i) < 2 ^ 64
frontx_implements_bytes countZerosE

/-- `ReaderT UInt8 (StateM Nat)`: the threshold is read from the environment -/
def countAboveR : List UInt8 → ReaderT UInt8 (StateM Nat) Unit
  | [] => pure ()
  | x :: xs => do
    let k ← read
    if x > k then modify (· + 1)
    countAboveR xs
def countAboveRE (xs : ByteArray) : Unit × Nat := ((countAboveR xs.data.toList).run 100).run 0
frontx_monad_entry countAboveRE with fun B i _ acc => i ≤ B.size ∧ acc + (B.size - i) < 2 ^ 64
frontx_implements_bytes countAboveRE

/-- `get` / `set`: the running maximum -/
def maxSt : List UInt8 → StateM UInt8 Unit
  | [] => pure ()
  | x :: xs => do
    let m ← get
    if x > m then set x
    maxSt xs
def maxStE (xs : ByteArray) : Unit × UInt8 := (maxSt xs.data.toList).run 0
frontx_monad_entry maxStE
frontx_implements_bytes maxStE

/-- a structure as the state (`modify` with `{ c with … }`) -/
structure Counts where
  lo : Nat
  hi : Nat
def split : List UInt8 → StateM Counts Unit
  | [] => pure ()
  | x :: xs => do
    if x < 128 then modify fun c => { c with lo := c.lo + 1 } else modify fun c => { c with hi := c.hi + 1 }
    split xs
def splitE (xs : ByteArray) : Unit × Counts := (split xs.data.toList).run ⟨0, 0⟩
frontx_monad_entry splitE with fun B i c => i ≤ B.size ∧ c.lo + c.hi + (B.size - i) < 2 ^ 64
frontx_implements_bytes splitE

/-- polymorphic in `[Monad m] [MonadExcept String m]`, used at `Except String`: early `return`, `throw` at the end -/
def firstBig [Monad m] [MonadExcept String m] : List UInt8 → m UInt8
  | [] => throw "none"
  | x :: xs => do
    if x ≥ 200 then return x
    firstBig xs
def firstBigE (xs : ByteArray) : Except String UInt8 := firstBig xs.data.toList
frontx_monad_entry firstBigE
frontx_implements_bytes firstBigE

/-- `tryCatch` in `Except` around a non-recursive helper (no loop: `frontx_monad_fn`) -/
def checkedSub (a b : Nat) : Except String Nat := if b > a then throw "negative" else pure (a - b)
def trySubE (xs : ByteArray) : Except String Nat :=
  tryCatch (do let q ← checkedSub xs.size 3; return q + 1) (fun _ => pure 0)
frontx_monad_fn trySubE
frontx_implements_bytes trySubE

end Proven.Frontx.Mon
