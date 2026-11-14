/- Function calls, model-free: the source language `CStmt` / `Fn` / `Prog` and its big-step semantics
`CExec` (namespace `Proven.Mach`).

A program is a finite table of functions (`Prog := List Fn`; a function's name is its index).  A function
has `nlocals` 64-bit locals, the first `nparams` of which are its parameters, a body and a result
expression (`ret`, evaluated after the body: the function's `return`).  Bodies are `CStmt`: the existing
statement language `BStmt` (`base`: assignment, byte/word block load/store, loops without calls),
sequencing, `ite`, `loop`, and `call res f args`.

Variables: `0 .. 7` are GLOBALS (one copy for the whole program, shared by all functions; block base
addresses live here), `8 + j` is LOCAL `j` of the running function.  A call evaluates the arguments in the
caller, runs the callee's body with fresh locals (parameters = arguments, the other locals `0`) and the
current globals / blocks, and assigns the callee's result to `res` in the caller.  Any recursion (also
mutual) is allowed.

`CExec P k p σ σ'`: `p` runs from `σ` to `σ'` using at most `k` bytes of stack below the current frame.
The index `k` is the STACK NEED of the run: `base` statements need nothing, a call needs the callee's frame
(`Fn.frame`, 8 bytes per local + 8 for the return address) plus the need of the callee's body.  There is no
fuel: a diverging or faulting run has no derivation. -/
import Compiler.BLang

namespace Proven.Mach

inductive CStmt where
  /-- a call-free statement -/
  | base (p : BStmt)
  | seq (p q : CStmt)
  /-- `if c ≠ 0 then p else q` -/
  | ite (c : BExp) (p q : CStmt)
  /-- `while c ≠ 0 do body` -/
  | loop (c : BExp) (body : CStmt)
  /-- `res := f(args)` -/
  | call (res : Nat) (f : Nat) (args : List BExp)

structure Fn where
  nparams : Nat
  nlocals : Nat
  body : CStmt
  /-- the result, evaluated in the callee's final state -/
  ret : BExp

abbrev Prog := List Fn

/-- bytes of stack one activation of `F` takes -/
def Fn.frame (F : Fn) : Nat := 8 * (F.nlocals + 1)

/-- the callee's initial variables: the globals, then the arguments, then zeros -/
def callEnv (g : BEnv) (vals : List (BitVec 64)) : BEnv := fun i => if i < 8 then g i else vals.getD (i - 8) 0

/-- the caller's variables after a call: the callee's globals, its own locals -/
def retEnv (caller callee : BEnv) : BEnv := fun i => if i < 8 then callee i else caller i

inductive CExec (P : Prog) : Nat → CStmt → BState → BState → Prop
  | base {k p σ σ'} : BExec p σ σ' → CExec P k (.base p) σ σ'
  | seq {k p q σ σ₁ σ₂} : CExec P k p σ σ₁ → CExec P k q σ₁ σ₂ → CExec P k (.seq p q) σ σ₂
  | iteT {k c p q σ σ'} : c.denote σ.env ≠ 0 → CExec P k p σ σ' → CExec P k (.ite c p q) σ σ'
  | iteF {k c p q σ σ'} : c.denote σ.env = 0 → CExec P k q σ σ' → CExec P k (.ite c p q) σ σ'
  | loopF {k c b σ} : c.denote σ.env = 0 → CExec P k (.loop c b) σ σ
  | loopT {k c b σ σ₁ σ₂} : c.denote σ.env ≠ 0 → CExec P k b σ σ₁ → CExec P k (.loop c b) σ₁ σ₂ →
      CExec P k (.loop c b) σ σ₂
  | call {k k' res f args σ σ₁} (hf : f < P.length) (ha : args.length = P[f].nparams)
      (hk : P[f].frame + k' ≤ k)
      (hb : CExec P k' P[f].body ⟨callEnv σ.env (args.map (·.denote σ.env)), σ.heap, σ.wheap⟩ σ₁) :
      CExec P k (.call res f args) σ
        ⟨(retEnv σ.env σ₁.env).set res (P[f].ret.denote σ₁.env), σ₁.heap, σ₁.wheap⟩

/-- more stack never hurts -/
theorem CExec.mono {P : Prog} {k p σ σ'} (h : CExec P k p σ σ') : ∀ {k'}, k ≤ k' → CExec P k' p σ σ' := by
  induction h with
  | base h => intro _ _; exact .base h
  | seq _ _ ih₁ ih₂ => intro _ hk; exact .seq (ih₁ hk) (ih₂ hk)
  | iteT hc _ ih => intro _ hk; exact .iteT hc (ih hk)
  | iteF hc _ ih => intro _ hk; exact .iteF hc (ih hk)
  | loopF hc => intro _ _; exact .loopF hc
  | loopT hc _ _ ih₁ ih₂ => intro _ hk; exact .loopT hc (ih₁ hk) (ih₂ hk)
  | call hf ha hk hb _ => intro _ hk'; exact .call hf ha (Nat.le_trans hk hk') hb

/-- the fuel-free, bound-free run -/
def CRuns (P : Prog) (p : CStmt) (σ σ' : BState) : Prop := ∃ k, CExec P k p σ σ'

end Proven.Mach
