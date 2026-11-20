/- Clients of the call compiler, each proved end to end against an ordinary Lean function
(`ImplementsW`): non-tail-recursive `sumTo` and `fib`, mutually recursive `isEven` / `isOdd`. -/
import Nano.Base.Riscv.Back.Calls
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

namespace Proven.Mach.Riscv
open Proven.Mach

/-! ## Source-level tools -/

/-- a call whose callee leaves the globals and the blocks alone -/
theorem call_pure {P : Prog} {k k' res f : Nat} {args : List BExp} {σ σ₁ : BState} {v : BitVec 64}
    (hf : f < P.length) (ha : args.length = P[f].nparams) (hk : P[f].frame + k' ≤ k)
    (hb : CExec P k' P[f].body ⟨callEnv σ.env (args.map (·.denote σ.env)), σ.heap, σ.wheap⟩ σ₁)
    (hg : ∀ i, i < 8 → σ₁.env i = σ.env i) (hh : σ₁.heap = σ.heap) (hw : σ₁.wheap = σ.wheap)
    (hv : P[f].ret.denote σ₁.env = v) : CExec P k (.call res f args) σ ⟨σ.env.set res v, σ.heap, σ.wheap⟩ := by
  have := CExec.call (res := res) hf ha hk hb
  rw [hh, hw, hv] at this
  have e : retEnv σ.env σ₁.env = σ.env := funext fun i => by
    unfold retEnv; by_cases h : i < 8
    · rw [ite_pos h, hg i h]
    · rw [ite_neg h]
  rwa [e] at this

/-- the specification of a one-parameter function: called with `a` it returns `v` within `k` bytes of
stack below its frame, globals and blocks unchanged -/
def Spec1 (P : Prog) (F : Fn) (k : Nat) (a v : BitVec 64) : Prop :=
  ∀ (g : BEnv) (H : Heap) (Wh : WHeap), ∃ σ₁, CExec P k F.body ⟨callEnv g [a], H, Wh⟩ σ₁ ∧
    (∀ i, i < 8 → σ₁.env i = g i) ∧ σ₁.heap = H ∧ σ₁.wheap = Wh ∧ F.ret.denote σ₁.env = v

theorem call1 {P : Prog} {F : Fn} {f k k' res : Nat} {e : BExp} {σ : BState} {a v : BitVec 64}
    (hf : f < P.length) (hF : P[f] = F) (hp : F.nparams = 1) (hk : F.frame + k' ≤ k) (ha : e.denote σ.env = a)
    (h : Spec1 P F k' a v) : CExec P k (.call res f [e]) σ ⟨σ.env.set res v, σ.heap, σ.wheap⟩ := by
  subst hF
  obtain ⟨σ₁, hb, hg, hh, hw, hv⟩ := h σ.env σ.heap σ.wheap
  have e1 : [e].map (·.denote σ.env) = [a] := by show [e.denote σ.env] = [a]; rw [ha]
  exact call_pure hf (by rw [hp]; rfl) hk (by rw [e1]; exact hb) hg hh hw hv

theorem setG {env : BEnv} {g : BEnv} {v : Nat} {x : BitVec 64} (hv : 8 ≤ v) (h : ∀ i, i < 8 → env i = g i) :
    ∀ i, i < 8 → env.set v x i = g i := fun i hi => by
  show (if i = v then x else env i) = g i
  rw [ite_neg (by omega), h i hi]

theorem callEnvG (g : BEnv) (vals : List (BitVec 64)) : ∀ i, i < 8 → callEnv g vals i = g i := fun i hi => by
  unfold callEnv; rw [ite_pos hi]

theorem zx_byte (b : UInt8) : b.toBitVec.setWidth 64 = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := b.toNat_lt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  show b.toNat % 2 ^ 64 = b.toNat % 2 ^ 64; rfl

/-- `main`: read the input byte `n`, call function 1 on it, store the result word -/
def mainFn : Fn :=
  ⟨0, 1, .seq (.base (.load 8 0 (.const 0))) (.seq (.call 8 1 [.var 8]) (.base (.store64 0 (.const 0) (.var 8)))),
    .const 0⟩

/-- a program `mainFn :: F :: rest` computes `F` of its one input byte -/
theorem main_computes {F : Fn} {rest : List Fn} {Fv : Nat → BitVec 64} {need : Nat} (hp : F.nparams = 1)
    (hs : ∀ n, n < 256 → Spec1 (mainFn :: F :: rest) F need (BitVec.ofNat 64 n) (Fv n)) :
    Computes (mainFn :: F :: rest) 0 (fun x => Fv (x.headD 0).toNat) (fun x => x.length = 1)
      (fun _ => 16 + (F.frame + need)) := by
  intro x env w0 hpre henv
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 hpre
  refine ⟨_, CExec.call (k' := F.frame + need) (f := 0) (by exact Nat.succ_pos _) rfl (Nat.le_refl _)
    (.seq (.base (BExec.load (v := 8) (b := 0) (i := .const 0) (by exact Nat.succ_pos _) (by exact Nat.succ_pos _)))
      (.seq (call1 (f := 1) (by exact Nat.succ_lt_succ (Nat.succ_pos _)) rfl hp (Nat.le_refl _) (zx_byte b)
          (hs b.toNat b.toNat_lt))
        (.base (BExec.store64 (b := 0) (i := .const 0) (e := .var 8) (by exact Nat.succ_pos _)
          (by exact Nat.succ_pos _))))), rfl⟩

/-! ## `sumTo` -/

/-- the reference: `n + (n - 1) + .. + 1` in 64-bit words -/
def sumTo : Nat → BitVec 64
  | 0 => 0
  | n + 1 => BitVec.ofNat 64 (n + 1) + sumTo n

/-- `sumTo(n) = if n ≠ 0 then n + sumTo(n - 1) else 0`; locals: `n`, `r` -/
def sumFn : Fn :=
  ⟨1, 2, .ite (.var 8) (.call 9 1 [.bin .sub (.var 8) (.const 1)]) (.base (.assign 9 (.const 0))),
    .bin .add (.var 8) (.var 9)⟩

def sumToProg : Prog := [mainFn, sumFn]

theorem ofNat_succ_ne {n : Nat} (h : n + 1 < 2 ^ 64) : BitVec.ofNat 64 (n + 1) ≠ 0 := fun e => by
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt h] at this; exact absurd this (Nat.succ_ne_zero n)

theorem ofNat_pred (n : Nat) : BitVec.ofNat 64 (n + 1) - 1 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega

theorem sum_spec : ∀ n, n < 2 ^ 64 → Spec1 sumToProg sumFn (24 * n) (BitVec.ofNat 64 n) (sumTo n)
  | 0, _ => fun g H Wh =>
    ⟨_, .iteF rfl (.base .assign), setG (by decide) (callEnvG g _), rfl, rfl, rfl⟩
  | n + 1, hn => fun g H Wh =>
    ⟨_, .iteT (ofNat_succ_ne hn) (call1 (f := 1) (by decide) rfl rfl (k' := 24 * n)
        (by show 24 + 24 * n ≤ 24 * (n + 1); omega) (ofNat_pred n) (sum_spec n (by omega))),
      setG (by decide) (callEnvG g _), rfl, rfl, rfl⟩

theorem sumToProg_computes : Computes sumToProg 0 (fun x => sumTo (x.headD 0).toNat) (fun x => x.length = 1)
    (fun _ => 16 + (24 + 24 * 255)) :=
  main_computes rfl fun n hn => fun g H Wh => by
    obtain ⟨σ₁, h, r⟩ := sum_spec n (by omega) g H Wh
    exact ⟨σ₁, h.mono (by omega), r⟩

theorem sumToProg_wf : WfProg sumToProg 0 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · have : f = 0 ∨ f = 1 := by simp [sumToProg] at hf; omega
    rcases this with rfl | rfl <;> wf_calls [sumToProg, mainFn, sumFn]
  · wf_calls [sumToProg, mainFn, sumFn]

/-- **`sumTo` on the Sail model**: one input byte `n`, output `enc (sumTo n)`; recursion depth `n`,
`space = 6184` bytes of stack. -/
theorem sumTo_implements : ImplementsW (callsCode sumToProg 0) (fun x => sumTo (x.headD 0).toNat)
    (fun x => x.length = 1) (fun _ => 16 + (24 + 24 * 255) + 24) :=
  callsCode_implements sumToProg_wf sumToProg_computes

/-! ## `fib` -/

def fibW : Nat → BitVec 64
  | 0 => 0
  | 1 => 1
  | n + 2 => fibW (n + 1) + fibW n

/-- `fib(n) = if 1 < n then fib(n - 1) + fib(n - 2) else n`; locals: `n`, `a`, `b` -/
def fibFn : Fn :=
  ⟨1, 3, .ite (.bin .ult (.const 1) (.var 8))
      (.seq (.call 9 1 [.bin .sub (.var 8) (.const 1)]) (.call 10 1 [.bin .sub (.var 8) (.const 2)]))
      (.base (.assign 9 (.var 8))),
    .bin .add (.var 9) (.var 10)⟩

def fibProg : Prog := [mainFn, fibFn]

theorem one_lt {n : Nat} (h : n + 2 < 2 ^ 64) : Op.eval .ult 1 (BitVec.ofNat 64 (n + 2)) ≠ 0 := by
  have : (1 : BitVec 64) < BitVec.ofNat 64 (n + 2) := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]; show 1 < n + 2; omega
  show (if (1 : BitVec 64) < BitVec.ofNat 64 (n + 2) then (1 : BitVec 64) else 0) ≠ 0
  rw [if_pos this]; decide

theorem ofNat_pred2 (n : Nat) : BitVec.ofNat 64 (n + 2) - 2 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (2 : BitVec 64).toNat = 2 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega

theorem fib_spec : ∀ n, n < 2 ^ 64 → Spec1 fibProg fibFn (32 * n) (BitVec.ofNat 64 n) (fibW n)
  | 0, _ => fun g H Wh =>
    ⟨_, .iteF rfl (.base .assign), setG (by decide) (callEnvG g _), rfl, rfl, rfl⟩
  | 1, _ => fun g H Wh =>
    ⟨_, .iteF rfl (.base .assign), setG (by decide) (callEnvG g _), rfl, rfl, rfl⟩
  | n + 2, hn => fun g H Wh =>
    ⟨_, .iteT (one_lt hn) (.seq
        (call1 (f := 1) (by decide) rfl rfl (k' := 32 * (n + 1)) (by show 32 + 32 * (n + 1) ≤ 32 * (n + 2); omega)
          (ofNat_pred (n + 1)) (fib_spec (n + 1) (by omega)))
        (call1 (f := 1) (by decide) rfl rfl (k' := 32 * n) (by show 32 + 32 * n ≤ 32 * (n + 2); omega)
          (ofNat_pred2 n) (fib_spec n (by omega)))),
      setG (by decide) (setG (by decide) (callEnvG g _)), rfl, rfl, rfl⟩

theorem fibProg_computes : Computes fibProg 0 (fun x => fibW (x.headD 0).toNat) (fun x => x.length = 1)
    (fun _ => 16 + (32 + 32 * 255)) :=
  main_computes rfl fun n hn => fun g H Wh => by
    obtain ⟨σ₁, h, r⟩ := fib_spec n (by omega) g H Wh
    exact ⟨σ₁, h.mono (by omega), r⟩

theorem fibProg_wf : WfProg fibProg 0 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · have : f = 0 ∨ f = 1 := by simp [fibProg] at hf; omega
    rcases this with rfl | rfl <;> wf_calls [fibProg, mainFn, fibFn]
  · wf_calls [fibProg, mainFn, fibFn]

/-- **`fib` on the Sail model** (two non-tail calls per activation) -/
theorem fib_implements : ImplementsW (callsCode fibProg 0) (fun x => fibW (x.headD 0).toNat)
    (fun x => x.length = 1) (fun _ => 16 + (32 + 32 * 255) + 24) :=
  callsCode_implements fibProg_wf fibProg_computes

/-! ## `isEven` / `isOdd` (mutual recursion) -/

mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

def bw (b : Bool) : BitVec 64 := if b then 1 else 0

def evenFn : Fn :=
  ⟨1, 2, .ite (.var 8) (.call 9 2 [.bin .sub (.var 8) (.const 1)]) (.base (.assign 9 (.const 1))), .var 9⟩
def oddFn : Fn :=
  ⟨1, 2, .ite (.var 8) (.call 9 1 [.bin .sub (.var 8) (.const 1)]) (.base (.assign 9 (.const 0))), .var 9⟩

def evenProg : Prog := [mainFn, evenFn, oddFn]

theorem even_spec : ∀ n, n < 2 ^ 64 →
    Spec1 evenProg evenFn (24 * n) (BitVec.ofNat 64 n) (bw (isEven n)) ∧
    Spec1 evenProg oddFn (24 * n) (BitVec.ofNat 64 n) (bw (isOdd n))
  | 0, _ =>
    ⟨fun g H Wh => ⟨_, .iteF rfl (.base .assign), setG (by decide) (callEnvG g _), rfl, rfl, by rw [isEven]; rfl⟩,
     fun g H Wh => ⟨_, .iteF rfl (.base .assign), setG (by decide) (callEnvG g _), rfl, rfl, by rw [isOdd]; rfl⟩⟩
  | n + 1, hn =>
    ⟨fun g H Wh => ⟨_, .iteT (ofNat_succ_ne hn) (call1 (f := 2) (by decide) rfl rfl (k' := 24 * n)
        (by show 24 + 24 * n ≤ 24 * (n + 1); omega) (ofNat_pred n) (even_spec n (by omega)).2),
      setG (by decide) (callEnvG g _), rfl, rfl, by rw [isEven]; rfl⟩,
     fun g H Wh => ⟨_, .iteT (ofNat_succ_ne hn) (call1 (f := 1) (by decide) rfl rfl (k' := 24 * n)
        (by show 24 + 24 * n ≤ 24 * (n + 1); omega) (ofNat_pred n) (even_spec n (by omega)).1),
      setG (by decide) (callEnvG g _), rfl, rfl, by rw [isOdd]; rfl⟩⟩

theorem evenProg_computes : Computes evenProg 0 (fun x => bw (isEven (x.headD 0).toNat)) (fun x => x.length = 1)
    (fun _ => 16 + (24 + 24 * 255)) :=
  main_computes (F := evenFn) (rest := [oddFn]) (Fv := fun n => bw (isEven n)) (need := 24 * 255) rfl
    fun n hn => fun g H Wh => by
    obtain ⟨σ₁, h, r⟩ := (even_spec n (by omega)).1 g H Wh
    exact ⟨σ₁, h.mono (by omega), r⟩

theorem evenProg_wf : WfProg evenProg 0 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · have : f = 0 ∨ f = 1 ∨ f = 2 := by simp [evenProg] at hf; omega
    rcases this with rfl | rfl | rfl <;> wf_calls [evenProg, mainFn, evenFn, oddFn]
  · wf_calls [evenProg, mainFn, evenFn, oddFn]

/-- **mutually recursive `isEven` / `isOdd` on the Sail model** -/
theorem isEven_implements : ImplementsW (callsCode evenProg 0) (fun x => bw (isEven (x.headD 0).toNat))
    (fun x => x.length = 1) (fun _ => 16 + (24 + 24 * 255) + 24) :=
  callsCode_implements evenProg_wf evenProg_computes

end Proven.Mach.Riscv
