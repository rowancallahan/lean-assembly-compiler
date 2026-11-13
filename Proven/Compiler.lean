/- A tiny verified compiler: expressions over `BitVec 64` to RV64I code, run on the Sail model. -/
import Proven.Step
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Proven

/-! ## Source language -/

inductive Op where | add | sub | and | or | xor
  deriving DecidableEq, Repr

def Op.eval : Op → BitVec 64 → BitVec 64 → BitVec 64
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b

/-- Expressions over four 64-bit inputs (passed in `a0..a3`). -/
inductive Exp where
  | var (i : Fin 4)
  | const (c : BitVec 64)
  | bin (op : Op) (a b : Exp)
  deriving Repr

def Exp.denote (env : Fin 4 → BitVec 64) : Exp → BitVec 64
  | .var i => env i
  | .const c => c
  | .bin op a b => op.eval (a.denote env) (b.denote env)

/-- registers needed beyond the result register -/
def Exp.depth : Exp → Nat
  | .var _ | .const _ => 0
  | .bin _ a b => max a.depth (b.depth + 1)

/-! ## Target: RV64I words over a fixed register stack `t0 t1 t2 t3 t4` -/

/-- the register stack: `t0 t1 t2 t3 t4` -/
def T : Nat → Fin 32
  | 0 => 5 | 1 => 6 | 2 => 7 | 3 => 28 | _ => 29
/-- argument registers `a0..a3` -/
def A : Nat → Fin 32
  | 0 => 10 | 1 => 11 | 2 => 12 | _ => 13

def encR (f7 f3 : Nat) (rd rs1 rs2 : Fin 32) : BitVec 32 :=
  BitVec.ofNat 32 (f7 <<< 25 ||| rs2.val <<< 20 ||| rs1.val <<< 15 ||| f3 <<< 12 ||| rd.val <<< 7 ||| 0x33)
def encI (f3 imm : Nat) (rd rs1 : Fin 32) : BitVec 32 :=
  BitVec.ofNat 32 (imm <<< 20 ||| rs1.val <<< 15 ||| f3 <<< 12 ||| rd.val <<< 7 ||| 0x13)

def Op.f7 : Op → Nat | .sub => 0x20 | _ => 0
def Op.f3 : Op → Nat | .add => 0 | .sub => 0 | .and => 7 | .or => 6 | .xor => 4

def iOp (op : Op) (k : Nat) : BitVec 32 := encR op.f7 op.f3 (T k) (T k) (T (k + 1)) -- op tk, tk, tk+1
def iVar (i k : Nat) : BitVec 32 := encR 0 0 (T k) 0 (A i)    -- add tk, x0, ai
def iZero (k : Nat) : BitVec 32 := encI 0 0 (T k) 0           -- addi tk, x0, 0
def iShl (k : Nat) : BitVec 32 := encI 1 1 (T k) (T k)        -- slli tk, tk, 1
def iInc (k : Nat) : BitVec 32 := encI 0 1 (T k) (T k)        -- addi tk, tk, 1
def iRes : BitVec 32 := encR 0 0 10 0 5                        -- add a0, x0, t0
def iRet : BitVec 32 := 0x00008067#32                          -- jalr x0, 0(ra)

/-- build the constant `n` in `t_k`, most significant bit first -/
def genConst (k n : Nat) : List (BitVec 32) :=
  if n = 0 then [iZero k] else genConst k (n / 2) ++ [iShl k] ++ (if n % 2 = 1 then [iInc k] else [])

/-- code leaving the value of `e` in `t_k`, clobbering only `t_k ..` -/
def gen : Exp → Nat → List (BitVec 32)
  | .var i, k => [iVar i k]
  | .const c, k => genConst k c.toNat
  | .bin op a b, k => gen a k ++ gen b (k + 1) ++ [iOp op k]

/-- the compiled function: result in `a0`, then `ret` -/
def compile (e : Exp) : List (BitVec 32) := gen e 0 ++ [iRes, iRet]

/-! ## Step lemmas for every word the compiler emits (each case by `step_word`) -/

set_option linter.unusedVariables false

variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

theorem step_op (op : Op) (k : Nat) (hk : k < 4) (hi : instrAt s pc (iOp op k)) :
    ∃ s', Next s s' (pc + 4) (T k) (op.eval (getX s (T k)) (getX s (T (k + 1)))) s.mem := by
  match k, op with
  | 0, .add => rw [show iOp .add 0 = 0x006282b3#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 0, .sub => rw [show iOp .sub 0 = 0x406282b3#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 0, .and => rw [show iOp .and 0 = 0x0062f2b3#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 0, .or => rw [show iOp .or 0 = 0x0062e2b3#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 0, .xor => rw [show iOp .xor 0 = 0x0062c2b3#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 1, .add => rw [show iOp .add 1 = 0x00730333#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 1, .sub => rw [show iOp .sub 1 = 0x40730333#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 1, .and => rw [show iOp .and 1 = 0x00737333#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 1, .or => rw [show iOp .or 1 = 0x00736333#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 1, .xor => rw [show iOp .xor 1 = 0x00734333#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 2, .add => rw [show iOp .add 2 = 0x01c383b3#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 2, .sub => rw [show iOp .sub 2 = 0x41c383b3#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 2, .and => rw [show iOp .and 2 = 0x01c3f3b3#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 2, .or => rw [show iOp .or 2 = 0x01c3e3b3#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 2, .xor => rw [show iOp .xor 2 = 0x01c3c3b3#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 3, .add => rw [show iOp .add 3 = 0x01de0e33#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 3, .sub => rw [show iOp .sub 3 = 0x41de0e33#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 3, .and => rw [show iOp .and 3 = 0x01de7e33#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 3, .or => rw [show iOp .or 3 = 0x01de6e33#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | 3, .xor => rw [show iOp .xor 3 = 0x01de4e33#32 by decide] at hi; simp only [T, Op.eval]; step_word
  | _ + 4, _ => omega

theorem step_var (i k : Nat) (hk : k < 5) (hi4 : i < 4) (hi : instrAt s pc (iVar i k)) :
    ∃ s', Next s s' (pc + 4) (T k) (getX s (A i)) s.mem := by
  match k, i with
  | 0, 0 => rw [show iVar 0 0 = 0x00a002b3#32 by decide] at hi; simp only [T, A]; step_word
  | 0, 1 => rw [show iVar 1 0 = 0x00b002b3#32 by decide] at hi; simp only [T, A]; step_word
  | 0, 2 => rw [show iVar 2 0 = 0x00c002b3#32 by decide] at hi; simp only [T, A]; step_word
  | 0, 3 => rw [show iVar 3 0 = 0x00d002b3#32 by decide] at hi; simp only [T, A]; step_word
  | 1, 0 => rw [show iVar 0 1 = 0x00a00333#32 by decide] at hi; simp only [T, A]; step_word
  | 1, 1 => rw [show iVar 1 1 = 0x00b00333#32 by decide] at hi; simp only [T, A]; step_word
  | 1, 2 => rw [show iVar 2 1 = 0x00c00333#32 by decide] at hi; simp only [T, A]; step_word
  | 1, 3 => rw [show iVar 3 1 = 0x00d00333#32 by decide] at hi; simp only [T, A]; step_word
  | 2, 0 => rw [show iVar 0 2 = 0x00a003b3#32 by decide] at hi; simp only [T, A]; step_word
  | 2, 1 => rw [show iVar 1 2 = 0x00b003b3#32 by decide] at hi; simp only [T, A]; step_word
  | 2, 2 => rw [show iVar 2 2 = 0x00c003b3#32 by decide] at hi; simp only [T, A]; step_word
  | 2, 3 => rw [show iVar 3 2 = 0x00d003b3#32 by decide] at hi; simp only [T, A]; step_word
  | 3, 0 => rw [show iVar 0 3 = 0x00a00e33#32 by decide] at hi; simp only [T, A]; step_word
  | 3, 1 => rw [show iVar 1 3 = 0x00b00e33#32 by decide] at hi; simp only [T, A]; step_word
  | 3, 2 => rw [show iVar 2 3 = 0x00c00e33#32 by decide] at hi; simp only [T, A]; step_word
  | 3, 3 => rw [show iVar 3 3 = 0x00d00e33#32 by decide] at hi; simp only [T, A]; step_word
  | 4, 0 => rw [show iVar 0 4 = 0x00a00eb3#32 by decide] at hi; simp only [T, A]; step_word
  | 4, 1 => rw [show iVar 1 4 = 0x00b00eb3#32 by decide] at hi; simp only [T, A]; step_word
  | 4, 2 => rw [show iVar 2 4 = 0x00c00eb3#32 by decide] at hi; simp only [T, A]; step_word
  | 4, 3 => rw [show iVar 3 4 = 0x00d00eb3#32 by decide] at hi; simp only [T, A]; step_word
  | _ + 5, _ => omega
  | _, _ + 4 => omega

theorem step_zero (k : Nat) (hk : k < 5) (hi : instrAt s pc (iZero k)) :
    ∃ s', Next s s' (pc + 4) (T k) (0) s.mem := by
  match k with
  | 0 => rw [show iZero 0 = 0x00000293#32 by decide] at hi; simp only [T]; step_word
  | 1 => rw [show iZero 1 = 0x00000313#32 by decide] at hi; simp only [T]; step_word
  | 2 => rw [show iZero 2 = 0x00000393#32 by decide] at hi; simp only [T]; step_word
  | 3 => rw [show iZero 3 = 0x00000e13#32 by decide] at hi; simp only [T]; step_word
  | 4 => rw [show iZero 4 = 0x00000e93#32 by decide] at hi; simp only [T]; step_word
  | _ + 5 => omega

theorem step_shl (k : Nat) (hk : k < 5) (hi : instrAt s pc (iShl k)) :
    ∃ s', Next s s' (pc + 4) (T k) (getX s (T k) <<< 1) s.mem := by
  match k with
  | 0 => rw [show iShl 0 = 0x00129293#32 by decide] at hi; simp only [T]; step_word
  | 1 => rw [show iShl 1 = 0x00131313#32 by decide] at hi; simp only [T]; step_word
  | 2 => rw [show iShl 2 = 0x00139393#32 by decide] at hi; simp only [T]; step_word
  | 3 => rw [show iShl 3 = 0x001e1e13#32 by decide] at hi; simp only [T]; step_word
  | 4 => rw [show iShl 4 = 0x001e9e93#32 by decide] at hi; simp only [T]; step_word
  | _ + 5 => omega

theorem step_inc (k : Nat) (hk : k < 5) (hi : instrAt s pc (iInc k)) :
    ∃ s', Next s s' (pc + 4) (T k) (getX s (T k) + 1) s.mem := by
  match k with
  | 0 => rw [show iInc 0 = 0x00128293#32 by decide] at hi; simp only [T]; step_word
  | 1 => rw [show iInc 1 = 0x00130313#32 by decide] at hi; simp only [T]; step_word
  | 2 => rw [show iInc 2 = 0x00138393#32 by decide] at hi; simp only [T]; step_word
  | 3 => rw [show iInc 3 = 0x001e0e13#32 by decide] at hi; simp only [T]; step_word
  | 4 => rw [show iInc 4 = 0x001e8e93#32 by decide] at hi; simp only [T]; step_word
  | _ + 5 => omega

theorem step_res (hi : instrAt s pc iRes) : ∃ s', Next s s' (pc + 4) 10 (getX s 5) s.mem := by
  rw [show iRes = 0x00500533#32 by decide] at hi; step_word

theorem step_ret (hi : instrAt s pc iRet) (he : (getX s 1).toNat % 2 = 0) :
    ∃ s', Next s s' (getX s 1) 0 0 s.mem := by
  rw [show iRet = 0x00008067#32 by decide] at hi; step_word

omit h hpc hok

/-! ## Running code -/

/-- the words `ws` sit at `pc, pc+4, ...` -/
def codeAt (s : St) (pc : BitVec 64) (ws : List (BitVec 32)) : Prop :=
  ∀ i (hi : i < ws.length), instrAt s (pc + BitVec.ofNat 64 (4 * i)) ws[i]

/-- `[pc, pc + 4n)` is word aligned and in RAM -/
def codeOK (pc : BitVec 64) (n : Nat) : Prop :=
  pc.toNat % 4 = 0 ∧ 0x80000000 ≤ pc.toNat ∧ pc.toNat + 4 * n ≤ 0x100000000

theorem pc_add (pc : BitVec 64) (a b : Nat) :
    pc + BitVec.ofNat 64 (4 * a) + BitVec.ofNat 64 (4 * b) = pc + BitVec.ofNat 64 (4 * (a + b)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem codeAt_append {s : St} {pc : BitVec 64} {l₁ l₂ : List (BitVec 32)} :
    codeAt s pc (l₁ ++ l₂) ↔ codeAt s pc l₁ ∧ codeAt s (pc + BitVec.ofNat 64 (4 * l₁.length)) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by simp; omega); rwa [List.getElem_append_left hi] at this
    · have := h (l₁.length + i) (by simp; omega)
      rwa [List.getElem_append_right (by omega), Nat.add_sub_cancel_left, ← pc_add] at this
  · intro ⟨h₁, h₂⟩ i hi
    by_cases hi' : i < l₁.length
    · rw [List.getElem_append_left hi']; exact h₁ i hi'
    · have := h₂ (i - l₁.length) (by simp at hi; omega)
      rw [List.getElem_append_right (by omega)]
      rwa [pc_add, Nat.add_sub_cancel' (by omega)] at this

theorem codeAt_mem {s s' : St} {pc ws} (hm : s'.mem = s.mem) (h : codeAt s pc ws) : codeAt s' pc ws := by
  intro i hi; have := h i hi; simp only [instrAt, hm] at this ⊢; exact this

theorem codeAt_one {s : St} {pc w} (h : codeAt s pc [w]) : instrAt s pc w := by
  have := h 0 (by simp); simpa using this

theorem codeOK_pcOK {pc : BitVec 64} {n : Nat} (h : codeOK pc n) (hn : 0 < n) : pcOK pc :=
  ⟨h.1, h.2.1, by have := h.2.2; omega⟩

theorem codeOK_append {pc : BitVec 64} {a b : Nat} (h : codeOK pc (a + b)) :
    codeOK pc a ∧ codeOK (pc + BitVec.ofNat 64 (4 * a)) b := by
  obtain ⟨h1, h2, h3⟩ := h
  have : (pc + BitVec.ofNat 64 (4 * a)).toNat = pc.toNat + 4 * a := by
    simp [BitVec.toNat_add]; omega
  exact ⟨⟨h1, h2, by omega⟩, by rw [codeOK, this]; omega⟩

theorem runsTo_next {s s' : St} {pc' rd v m} {P : St → Prop} (hn : Next s s' pc' rd v m)
    (hr : runsTo s' P) : runsTo s P := by
  obtain ⟨n, s'', hs, hp⟩ := hr
  exact ⟨n + 1, s'', ⟨s', hn.ret, hs⟩, hp⟩

/-- `s'` is reached from `s` by running `n` words from `pc`, writing only `t_k ..` -/
structure Ran (s s' : St) (pc : BitVec 64) (n k : Nat) : Prop where
  cfg : Cfg s'
  pc : s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * n))
  mem : s'.mem = s.mem
  keep : ∀ j, (∀ i, k ≤ i → i < 5 → j ≠ T i) → getX s' j = getX s j

theorem Ran.trans {s₁ s₂ s₃ : St} {pc n₁ n₂ k k' k''} (r₁ : Ran s₁ s₂ pc n₁ k)
    (r₂ : Ran s₂ s₃ (pc + BitVec.ofNat 64 (4 * n₁)) n₂ k') (hk : k'' ≤ k) (hk' : k'' ≤ k') :
    Ran s₁ s₃ pc (n₁ + n₂) k'' :=
  ⟨r₂.cfg, by rw [r₂.pc, pc_add], by rw [r₂.mem, r₁.mem],
    fun j hj => by rw [r₂.keep j (fun i hi => hj i (by omega)), r₁.keep j (fun i hi => hj i (by omega))]⟩

theorem Ran.ofNext {s s' : St} {pc k v} (hk : k < 5) (hn : Next s s' (pc + 4) (T k) v s.mem) :
    Ran s s' pc 1 k ∧ getX s' (T k) = v := by
  refine ⟨⟨hn.cfg, by rw [hn.pc]; rfl, hn.mem, fun j hj => ?_⟩, ?_⟩
  · rw [hn.x j]; have := hj k (by omega) hk; simp [this]
  · rw [hn.x]; simp; intro h0; revert h0; match k, hk with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => decide

theorem T_ne_A (k i : Nat) : T k ≠ A i := by
  unfold T A; split <;> split <;> decide

theorem T_inj {i j : Nat} (hi : i < 5) (hj : j < 5) (h : T i = T j) : i = j := by
  match i, j with
  | 0, 0 | 1, 1 | 2, 2 | 3, 3 | 4, 4 => rfl
  | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 1, 0 | 1, 2 | 1, 3 | 1, 4 | 2, 0 | 2, 1 | 2, 3 | 2, 4
  | 3, 0 | 3, 1 | 3, 2 | 3, 4 | 4, 0 | 4, 1 | 4, 2 | 4, 3 => exact absurd h (by decide)
  | _ + 5, _ | _, _ + 5 => omega

theorem Steps.trans : ∀ {n₁ n₂ : Nat} {s₁ s₂ s₃ : St}, Steps n₁ s₁ s₂ → Steps n₂ s₂ s₃ → Steps (n₁ + n₂) s₁ s₃
  | 0, _, _, _, _, h₁, h₂ => by cases h₁; simpa using h₂
  | n + 1, n₂, _, _, _, ⟨s, hr, hs⟩, h₂ => by
    rw [Nat.add_right_comm]; exact ⟨s, hr, Steps.trans hs h₂⟩

def Reach (s s' : St) : Prop := ∃ n, Steps n s s'

theorem Reach.trans {s₁ s₂ s₃ : St} : Reach s₁ s₂ → Reach s₂ s₃ → Reach s₁ s₃
  | ⟨_, h₁⟩, ⟨_, h₂⟩ => ⟨_, Steps.trans h₁ h₂⟩

theorem Reach.next {s s' : St} {pc rd v m} (h : Next s s' pc rd v m) : Reach s s' := ⟨1, s', h.ret, rfl⟩

theorem shl_ofNat (m : Nat) : BitVec.ofNat 64 m <<< 1 = BitVec.ofNat 64 (2 * m) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem inc_ofNat (m : Nat) : BitVec.ofNat 64 m + 1 = BitVec.ofNat 64 (m + 1) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

/-- one emitted word that writes `t_k` -/
theorem run_one {s : St} {pc : BitVec 64} {k : Nat} {w v} (hk : k < 5)
    (hstep : ∃ s', Next s s' (pc + 4) (T k) v s.mem) :
    ∃ s', Reach s s' ∧ Ran s s' pc [w].length k ∧ getX s' (T k) = v := by
  obtain ⟨s', hn⟩ := hstep
  exact ⟨s', Reach.next hn, (Ran.ofNext hk hn).1, (Ran.ofNext hk hn).2⟩

theorem const_ok (k : Nat) (hk : k < 5) : ∀ (n : Nat) {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (genConst k n))
    (hok : codeOK pc (genConst k n).length),
    ∃ s', Reach s s' ∧ Ran s s' pc (genConst k n).length k ∧ getX s' (T k) = BitVec.ofNat 64 n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s h pc hpc hc hok
  rw [genConst] at hc hok ⊢
  split
  · exact run_one hk (step_zero h hpc (codeOK_pcOK hok (by simp)) k hk (codeAt_one hc))
  · rename_i hn
    rw [codeAt_append, codeAt_append] at hc
    rw [List.length_append, List.length_append] at hok ⊢
    obtain ⟨ok1, ok23⟩ := codeOK_append (by rwa [Nat.add_assoc] at hok)
    obtain ⟨ok2, ok3⟩ := codeOK_append ok23
    obtain ⟨s₁, r₁, R₁, v₁⟩ := ih (n / 2) (by omega) h hpc hc.1.1 ok1
    obtain ⟨s₂, hn₂⟩ := step_shl R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) k hk
      (codeAt_one (codeAt_mem R₁.mem hc.1.2))
    obtain ⟨R₂, v₂⟩ := Ran.ofNext hk hn₂
    have R₁₂ := R₁.trans R₂ (Nat.le_refl _) (Nat.le_refl _)
    rw [v₁, shl_ofNat] at v₂
    split
    · rename_i hodd
      have hc3 := codeAt_mem R₁₂.mem hc.2
      rw [← pc_add] at hc3
      obtain ⟨s₃, hn₃⟩ := step_inc R₁₂.cfg R₁₂.pc (codeOK_pcOK (by rwa [← pc_add] at ok3) (by simp)) k hk
        (codeAt_one hc3)
      obtain ⟨R₃, v₃⟩ := Ran.ofNext hk hn₃
      refine ⟨s₃, (r₁.trans (Reach.next hn₂)).trans (Reach.next hn₃), ?_, ?_⟩
      · have := R₁₂.trans (by rw [pc_add]; exact R₃) (Nat.le_refl _) (Nat.le_refl _)
        simpa [Nat.add_assoc] using this
      · rw [v₃, v₂, inc_ofNat]; congr 1; omega
    · refine ⟨s₂, r₁.trans (Reach.next hn₂), by simpa using R₁₂, ?_⟩
      rw [v₂]; congr 1; omega

theorem gen_ok (env : Fin 4 → BitVec 64) : ∀ (e : Exp) (k : Nat) (hk : k + e.depth < 5) {s : St}
    (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (gen e k))
    (hok : codeOK pc (gen e k).length) (henv : ∀ i : Fin 4, getX s (A i) = env i),
    ∃ s', Reach s s' ∧ Ran s s' pc (gen e k).length k ∧ getX s' (T k) = e.denote env
  | .var i, k, hk, s, h, pc, hpc, hc, hok, henv => by
    simp only [gen, Exp.denote] at *
    obtain ⟨s', r, R, v⟩ := run_one (w := iVar i k) (by simp [Exp.depth] at hk; omega)
      (step_var h hpc (codeOK_pcOK hok (by simp)) i k (by simp [Exp.depth] at hk; omega) i.2 (codeAt_one hc))
    exact ⟨s', r, R, by rw [v, henv]⟩
  | .const c, k, hk, s, h, pc, hpc, hc, hok, henv => by
    simp only [gen, Exp.denote] at *
    obtain ⟨s', r, R, v⟩ := const_ok k (by simp [Exp.depth] at hk; omega) c.toNat h hpc hc hok
    exact ⟨s', r, R, by rw [v, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  | .bin op a b, k, hk, s, h, pc, hpc, hc, hok, henv => by
    simp only [gen, Exp.depth, Exp.denote] at *
    rw [codeAt_append, codeAt_append] at hc
    rw [List.length_append, List.length_append] at hok ⊢
    obtain ⟨ok1, ok23⟩ := codeOK_append (by rwa [Nat.add_assoc] at hok)
    obtain ⟨ok2, ok3⟩ := codeOK_append ok23
    obtain ⟨s₁, r₁, R₁, v₁⟩ := gen_ok env a k (by omega) h hpc hc.1.1 ok1 henv
    have henv₁ : ∀ i : Fin 4, getX s₁ (A i) = env i := fun i => by
      rw [R₁.keep _ (fun j _ _ => (T_ne_A j i).symm), henv]
    obtain ⟨s₂, r₂, R₂, v₂⟩ := gen_ok env b (k + 1) (by omega) R₁.cfg R₁.pc
      (codeAt_mem R₁.mem hc.1.2) ok2 henv₁
    have R₁₂ := R₁.trans R₂ (Nat.le_refl _) (Nat.le_succ _)
    have va : getX s₂ (T k) = a.denote env := by
      rw [R₂.keep _ (fun j hj hj5 he => by have := T_inj (by omega) hj5 he; omega), v₁]
    have hc3 := codeAt_mem R₁₂.mem hc.2
    rw [← pc_add] at hc3
    obtain ⟨s₃, hn₃⟩ := step_op R₁₂.cfg R₁₂.pc (codeOK_pcOK (by rwa [← pc_add] at ok3) (by simp))
      op k (by omega) (codeAt_one hc3)
    obtain ⟨R₃, v₃⟩ := Ran.ofNext (by omega) hn₃
    refine ⟨s₃, (r₁.trans r₂).trans (Reach.next hn₃), ?_, by rw [v₃, va, v₂]⟩
    have := R₁₂.trans (by rw [pc_add]; exact R₃) (Nat.le_refl _) (Nat.le_refl _)
    simpa [Nat.add_assoc] using this

/-- **Compiler correctness**: from any `Cfg` state with the code at `pc` and the return address
in `ra`, the Sail model runs (without traps) to `ra` with `a0 = e.denote (a0, a1, a2, a3)`,
memory unchanged and callee-saved registers kept. -/
theorem compile_ok (e : Exp) (he : e.depth < 5) {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compile e))
    (hok : codeOK pc (compile e).length) (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      getX s' 10 = e.denote (fun i => getX s (A i)) ∧ Cfg s' ∧ s'.mem = s.mem ∧
      calleeSavedKept s s' := by
  simp only [compile] at hc hok
  rw [codeAt_append] at hc
  rw [List.length_append] at hok
  obtain ⟨ok1, ok2⟩ := codeOK_append hok
  obtain ⟨s₁, ⟨n₁, st₁⟩, R₁, v₁⟩ := gen_ok (fun i => getX s (A i)) e 0 (by omega) h hpc hc.1 ok1 (fun _ => rfl)
  have hc2 := codeAt_mem R₁.mem hc.2
  obtain ⟨s₂, hn₂⟩ := step_res R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) (by simpa using hc2 0 (by simp))
  have hra₁ : getX s₁ 1 = getX s 1 := R₁.keep 1 (fun i _ hi => by
    match i, hi with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => decide)
  have hra₂ : getX s₂ 1 = getX s 1 := by rw [hn₂.x]; simp [hra₁]
  have hc2' := codeAt_mem hn₂.mem hc2
  obtain ⟨s₃, hn₃⟩ := step_ret hn₂.cfg hn₂.pc
    (codeOK_pcOK (by rw [pc_add]; exact (codeOK_append (a := 1) (b := 1) (by rw [← pc_add] at ok2 ⊢; exact ok2)).2) (by simp))
    (by have := hc2' 1 (by simp); rw [pc_add] at this ⊢; simpa using this) (by rw [hra₂]; exact hra)
  refine ⟨n₁ + 2, s₃, Steps.trans st₁ ⟨s₂, hn₂.ret, s₃, hn₃.ret, rfl⟩, ?_, ?_, hn₃.cfg, ?_, ?_⟩
  · rw [hn₃.pc, hra₂]
  · rw [hn₃.x]; simp; rw [hn₂.x]; simp [v₁]
  · rw [hn₃.mem, hn₂.mem, R₁.mem]
  · have keep : ∀ j : Fin 32, (∀ i, i < 5 → j ≠ T i) → j ≠ 10 → getX s₃ j = getX s j := by
      intro j hj h10
      rw [hn₃.x]; simp; rw [hn₂.x]; simp [h10]; exact R₁.keep j (fun i _ hi => hj i hi)
    have ne : ∀ j : Fin 32, j ∈ [2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] →
        (∀ i, i < 5 → j ≠ T i) ∧ j ≠ 10 := by
      intro j hj
      refine ⟨fun i hi => ?_, by revert hj; decide +revert⟩
      match i, hi with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [T]; revert hj; decide +revert
    have h₃ := hn₃.cfg
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₃.x2, h.x2, keep 2 (ne 2 (by decide)).1 (ne 2 (by decide)).2]
    · rw [h₃.x8, h.x8, keep 8 (ne 8 (by decide)).1 (ne 8 (by decide)).2]
    · rw [h₃.x9, h.x9, keep 9 (ne 9 (by decide)).1 (ne 9 (by decide)).2]
    · rw [h₃.x18, h.x18, keep 18 (ne 18 (by decide)).1 (ne 18 (by decide)).2]
    · rw [h₃.x19, h.x19, keep 19 (ne 19 (by decide)).1 (ne 19 (by decide)).2]
    · rw [h₃.x20, h.x20, keep 20 (ne 20 (by decide)).1 (ne 20 (by decide)).2]
    · rw [h₃.x21, h.x21, keep 21 (ne 21 (by decide)).1 (ne 21 (by decide)).2]
    · rw [h₃.x22, h.x22, keep 22 (ne 22 (by decide)).1 (ne 22 (by decide)).2]
    · rw [h₃.x23, h.x23, keep 23 (ne 23 (by decide)).1 (ne 23 (by decide)).2]
    · rw [h₃.x24, h.x24, keep 24 (ne 24 (by decide)).1 (ne 24 (by decide)).2]
    · rw [h₃.x25, h.x25, keep 25 (ne 25 (by decide)).1 (ne 25 (by decide)).2]
    · rw [h₃.x26, h.x26, keep 26 (ne 26 (by decide)).1 (ne 26 (by decide)).2]
    · rw [h₃.x27, h.x27, keep 27 (ne 27 (by decide)).1 (ne 27 (by decide)).2]

end Proven
