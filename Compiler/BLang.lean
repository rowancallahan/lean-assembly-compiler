/- Byte arrays + word arrays + spill slots, model-free: the source language `BExp`/`BStmt`/`BExec` of the
middle layer (namespace `Proven.Mach`).

A copy of `Proven.BExp`/`BStmt`/`BExec` (`Riscv/Direct/Arr2Code.lean`, which imports the Sail model, so it
cannot be imported here; `Riscv/Back/BStmt.lean` maps it in) extended by WORD ARRAYS: a second heap
`wheap` of blocks of 64-bit words, read by `load64` and written by `store64`.  In memory a word block of
`n` words is `8 n` bytes at an 8-aligned base, word `i` the little-endian bytes `8 i .. 8 i + 7`.

Variables `0 .. 7` live in registers, variables `8 ..` in 8-byte stack slots (`compBF`). -/
import Spec.ArrCode

namespace Proven.Mach

inductive BExp where
  | var (i : Nat)
  | const (c : BitVec 64)
  | bin (op : Op) (a b : BExp)
  /-- `ite c a b` is `a` if `c ≠ 0`, else `b` (both are evaluated) -/
  | ite (c a b : BExp)

abbrev BEnv := Nat → BitVec 64

def BExp.denote (env : BEnv) : BExp → BitVec 64
  | .var i => env i
  | .const c => c
  | .bin op a b => op.eval (a.denote env) (b.denote env)
  | .ite c a b => if c.denote env = 0 then b.denote env else a.denote env

def BExp.depth : BExp → Nat
  | .var _ | .const _ => 0
  | .bin _ a b => max a.depth (b.depth + 1)
  | .ite c a b => max c.depth (max (a.depth + 1) (b.depth + 2))

/-- every variable is `< m` -/
def BExp.vlt (m : Nat) : BExp → Prop
  | .var i => i < m
  | .const _ => True
  | .bin _ a b => a.vlt m ∧ b.vlt m
  | .ite c a b => c.vlt m ∧ a.vlt m ∧ b.vlt m

/-- word blocks -/
abbrev WHeap := List (List (BitVec 64))

structure BState where
  env : BEnv
  heap : Heap
  wheap : WHeap := []

def BEnv.set (σ : BEnv) (v : Nat) (x : BitVec 64) : BEnv := fun i => if i = v then x else σ i

inductive BStmt where
  | assign (v : Nat) (e : BExp)
  /-- `v := block b [i]` (zero-extended byte) -/
  | load (v : Nat) (b : Nat) (i : BExp)
  /-- `block b [i] := low byte of e` -/
  | store (b : Nat) (i e : BExp)
  | seq (p q : BStmt)
  /-- `while c ≠ 0 do body` -/
  | loop (c : BExp) (body : BStmt)
  /-- `v := word block b [i]` -/
  | load64 (v : Nat) (b : Nat) (i : BExp)
  /-- `word block b [i] := e` -/
  | store64 (b : Nat) (i e : BExp)

/-- big-step semantics; an out-of-bounds access has no derivation -/
inductive BExec : BStmt → BState → BState → Prop
  | assign {v e σ} : BExec (.assign v e) σ ⟨σ.env.set v (e.denote σ.env), σ.heap, σ.wheap⟩
  | load {v b i σ} (hb : b < σ.heap.length) (hi : (i.denote σ.env).toNat < σ.heap[b].length) :
      BExec (.load v b i) σ ⟨σ.env.set v (σ.heap[b][(i.denote σ.env).toNat].setWidth 64), σ.heap, σ.wheap⟩
  | store {b i e σ} (hb : b < σ.heap.length) (hi : (i.denote σ.env).toNat < σ.heap[b].length) :
      BExec (.store b i e) σ
        ⟨σ.env, σ.heap.set b (σ.heap[b].set (i.denote σ.env).toNat ((e.denote σ.env).setWidth 8)), σ.wheap⟩
  | seq {p q σ σ₁ σ₂} : BExec p σ σ₁ → BExec q σ₁ σ₂ → BExec (.seq p q) σ σ₂
  | loopF {c b σ} : c.denote σ.env = 0 → BExec (.loop c b) σ σ
  | loopT {c b σ σ₁ σ₂} : c.denote σ.env ≠ 0 → BExec b σ σ₁ → BExec (.loop c b) σ₁ σ₂ →
      BExec (.loop c b) σ σ₂
  | load64 {v b i σ} (hb : b < σ.wheap.length) (hi : (i.denote σ.env).toNat < σ.wheap[b].length) :
      BExec (.load64 v b i) σ ⟨σ.env.set v σ.wheap[b][(i.denote σ.env).toNat], σ.heap, σ.wheap⟩
  | store64 {b i e σ} (hb : b < σ.wheap.length) (hi : (i.denote σ.env).toNat < σ.wheap[b].length) :
      BExec (.store64 b i e) σ
        ⟨σ.env, σ.heap, σ.wheap.set b (σ.wheap[b].set (i.denote σ.env).toNat (e.denote σ.env))⟩

/-- the blocks of the word heap `p` accesses -/
def BStmt.wblocks : BStmt → List Nat
  | .load64 _ b _ | .store64 b _ _ => [b]
  | .seq p q => p.wblocks ++ q.wblocks
  | .loop _ b => b.wblocks
  | _ => []

end Proven.Mach
