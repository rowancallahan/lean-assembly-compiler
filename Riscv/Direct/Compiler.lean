/- A tiny verified compiler: the proof that `compile` (`Proven/Code.lean`) is correct on the Sail RV64 model. -/
import Riscv.Steps.Words
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven

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
      rw [pc_add]; simpa using this
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
  keep : ∀ j, (∀ i, k ≤ i → i < 11 → j ≠ T i) → getX s' j = getX s j

theorem Ran.trans {s₁ s₂ s₃ : St} {pc n₁ n₂ k k' k''} (r₁ : Ran s₁ s₂ pc n₁ k)
    (r₂ : Ran s₂ s₃ (pc + BitVec.ofNat 64 (4 * n₁)) n₂ k') (hk : k'' ≤ k) (hk' : k'' ≤ k') :
    Ran s₁ s₃ pc (n₁ + n₂) k'' :=
  ⟨r₂.cfg, by rw [r₂.pc, pc_add], by rw [r₂.mem, r₁.mem],
    fun j hj => by rw [r₂.keep j (fun i hi => hj i (by omega)), r₁.keep j (fun i hi => hj i (by omega))]⟩

theorem T_ne_0' : ∀ k < 11, T k ≠ 0 := by decide
theorem T_ne_1' : ∀ k < 11, T k ≠ 1 := by decide
theorem T_ne_0 (k : Nat) (hk : k < 11) : T k ≠ 0 := T_ne_0' k hk

theorem Ran.ofNext {s s' : St} {pc k v} (hk : k < 11) (hn : Next s s' (pc + 4) (T k) v s.mem) :
    Ran s s' pc 1 k ∧ getX s' (T k) = v := by
  refine ⟨⟨hn.cfg, by rw [hn.pc]; rfl, hn.mem, fun j hj => ?_⟩, ?_⟩
  · rw [hn.x j]; have := hj k (by omega) hk; simp [this]
  · have : T k ≠ 0 := T_ne_0 k hk
    rw [hn.x]; simp [this]

theorem T_ne_A' : ∀ k < 11, ∀ i < 4, T k ≠ A i := by decide

theorem T_inj' : ∀ i < 11, ∀ j < 11, T i = T j → i = j := by decide

theorem T_inj {i j : Nat} (hi : i < 11) (hj : j < 11) (h : T i = T j) : i = j := T_inj' i hi j hj h

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
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

/-- one emitted word that writes `t_k` -/
theorem run_one {s : St} {pc : BitVec 64} {k : Nat} {w : BitVec 32} {v : BitVec 64} (hk : k < 11)
    (hstep : ∃ s', Next s s' (pc + 4) (T k) v s.mem) :
    ∃ s', Reach s s' ∧ Ran s s' pc [w].length k ∧ getX s' (T k) = v := by
  obtain ⟨s', hn⟩ := hstep
  exact ⟨s', Reach.next hn, (Ran.ofNext hk hn).1, (Ran.ofNext hk hn).2⟩

theorem const_ok (k : Nat) (hk : k < 11) : ∀ (n : Nat) {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (genConst k n))
    (hok : codeOK pc (genConst k n).length),
    ∃ s', Reach s s' ∧ Ran s s' pc (genConst k n).length k ∧ getX s' (T k) = BitVec.ofNat 64 n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s h pc hpc hc hok
  rw [genConst] at hc hok ⊢
  by_cases hn : n = 0
  · subst hn
    simp only [↓reduceIte] at hc hok ⊢
    exact run_one hk (step_zero h hpc (codeOK_pcOK hok (by simp)) k hk (codeAt_one hc))
  · simp only [hn, ↓reduceIte] at hc hok ⊢
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
    by_cases hodd : n % 2 = 1
    · simp only [hodd, ↓reduceIte] at hc ok3 ⊢
      have hc3 := codeAt_mem R₁₂.mem hc.2
      rw [List.length_append] at hc3
      rw [pc_add] at ok3
      obtain ⟨s₃, hn₃⟩ := step_inc R₁₂.cfg R₁₂.pc (codeOK_pcOK ok3 (by simp)) k hk (codeAt_one hc3)
      obtain ⟨R₃, v₃⟩ := Ran.ofNext hk hn₃
      refine ⟨s₃, (r₁.trans (Reach.next hn₂)).trans (Reach.next hn₃), ?_, ?_⟩
      · have := R₁₂.trans R₃ (Nat.le_refl _) (Nat.le_refl _)
        simpa [Nat.add_assoc] using this
      · rw [v₃, v₂, inc_ofNat]; congr 1; omega
    · simp only [hodd, ↓reduceIte, List.length_nil, Nat.add_zero] at hc ok3 ⊢
      refine ⟨s₂, r₁.trans (Reach.next hn₂), R₁₂, ?_⟩
      rw [v₂]; congr 1; omega

theorem Ran.refl {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (k : Nat) :
    Ran s s pc 0 k := ⟨h, by simpa using hpc, rfl, fun _ _ => rfl⟩

/-- run one word writing `t_j` (`k ≤ j`), then the rest `ws` -/
theorem run_cons {s : St} {pc : BitVec 64} {k j : Nat} {w : BitVec 32} {ws : List (BitVec 32)}
    {v : BitVec 64} {P : St → Prop} (hkj : k ≤ j) (hj : j < 11) (h : Cfg s)
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (w :: ws)) (hok : codeOK pc (w :: ws).length)
    (hstep : pcOK pc → instrAt s pc w → ∃ s', Next s s' (pc + 4) (T j) v s.mem)
    (hrest : ∀ s', Cfg s' → s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * 1)) →
      codeAt s' (pc + BitVec.ofNat 64 (4 * 1)) ws → codeOK (pc + BitVec.ofNat 64 (4 * 1)) ws.length →
      (∀ r, getX s' r = if r = T j then v else getX s r) →
      ∃ s'', Reach s' s'' ∧ Ran s' s'' (pc + BitVec.ofNat 64 (4 * 1)) ws.length k ∧ P s'') :
    ∃ s'', Reach s s'' ∧ Ran s s'' pc (w :: ws).length k ∧ P s'' := by
  change codeAt s pc ([w] ++ ws) at hc
  rw [show (w :: ws).length = [w].length + ws.length by simp [Nat.add_comm]] at hok
  rw [codeAt_append] at hc
  obtain ⟨ok1, ok2⟩ := codeOK_append hok
  obtain ⟨s₁, hn⟩ := hstep (codeOK_pcOK ok1 (by simp)) (codeAt_one hc.1)
  obtain ⟨R₁, -⟩ := Ran.ofNext hj hn
  obtain ⟨s₂, r₂, R₂, p₂⟩ := hrest s₁ R₁.cfg R₁.pc (codeAt_mem R₁.mem hc.2) ok2
    (fun r => by rw [hn.x]; by_cases hr : r = T j <;> simp [hr, T_ne_0 j hj])
  refine ⟨s₂, (Reach.next hn).trans r₂, ?_, p₂⟩
  have := R₁.trans R₂ hkj (Nat.le_refl _)
  simpa [Nat.add_comm] using this

theorem run_nil {s : St} {pc : BitVec 64} {k : Nat} {P : St → Prop} (h : Cfg s)
    (hpc : s.regs.get? .PC = some pc) (hp : P s) :
    ∃ s', Reach s s' ∧ Ran s s' pc ([] : List (BitVec 32)).length k ∧ P s' :=
  ⟨s, ⟨0, rfl⟩, Ran.refl h hpc k, hp⟩

theorem xor_eq_zero (a b : BitVec 64) : a ^^^ b = 0 ↔ a = b :=
  ⟨fun e => by simpa [BitVec.xor_assoc] using congrArg (· ^^^ b) e, fun e => by simp [e]⟩

theorem op_ok (op : Op) (k : Nat) (hk : k + 1 < 11) {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (opCode op k)) (hok : codeOK pc (opCode op k).length) :
    ∃ s', Reach s s' ∧ Ran s s' pc (opCode op k).length k ∧
      getX s' (T k) = op.eval (getX s (T k)) (getX s (T (k + 1))) := by
  unfold opCode at *
  by_cases he : op = .eq
  · subst he; simp only [↓reduceIte] at *
    refine run_cons (Nat.le_refl _) (by omega) h hpc hc hok (fun ok hi => step_op h hpc ok .eq k (by omega) hi) ?_
    intro s₁ h₁ hpc₁ hc₁ ok₁ hx₁
    refine run_cons (Nat.le_refl _) (by omega) h₁ hpc₁ hc₁ ok₁ (fun ok hi => step_seqz h₁ hpc₁ ok k (by omega) hi) ?_
    intro s₂ h₂ hpc₂ hc₂ ok₂ hx₂
    refine run_nil h₂ hpc₂ ?_
    simp only [hx₂, hx₁, if_pos rfl, Op.raw, Op.eval, xor_eq_zero, ↓reduceIte]
  · simp only [he, ↓reduceIte] at hc hok ⊢
    refine run_cons (Nat.le_refl _) (by omega) h hpc hc hok (fun ok hi => step_op h hpc ok op k (by omega) hi) ?_
    intro s₁ h₁ hpc₁ hc₁ ok₁ hx₁
    refine run_nil h₁ hpc₁ ?_
    simp only [hx₁, if_pos rfl, Op.raw, if_neg he, ↓reduceIte]

theorem sel_val (c a b : BitVec 64) :
    (-(if c = 0 then 0 else 1) &&& (a ^^^ b)) ^^^ b = if c = 0 then b else a := by
  by_cases hc : c = 0
  · rw [if_pos hc, if_pos hc]; simp
  · rw [if_neg hc, if_neg hc, show -(1 : BitVec 64) = BitVec.allOnes 64 by decide, BitVec.allOnes_and,
      BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem sel_ok (k : Nat) (hk : k + 2 < 11) {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (selCode k)) (hok : codeOK pc (selCode k).length) :
    ∃ s', Reach s s' ∧ Ran s s' pc (selCode k).length k ∧
      getX s' (T k) = if getX s (T k) = 0 then getX s (T (k + 2)) else getX s (T (k + 1)) := by
  have ne : ∀ {i j}, i < j → j < 11 → T j ≠ T i := fun hij hj he => by
    have := T_inj hj (by omega) he; omega
  have n10 : T (k + 1) ≠ T k := ne (by omega) (by omega)
  have n20 : T (k + 2) ≠ T k := ne (by omega) (by omega)
  have n21 : T (k + 2) ≠ T (k + 1) := ne (by omega) (by omega)
  unfold selCode at *
  refine run_cons (Nat.le_refl _) (by omega) h hpc hc hok (fun ok hi => step_snez h hpc ok k (by omega) hi) ?_
  intro s₁ h₁ hpc₁ hc₁ ok₁ hx₁
  refine run_cons (Nat.le_refl _) (by omega) h₁ hpc₁ hc₁ ok₁ (fun ok hi => step_neg h₁ hpc₁ ok k (by omega) hi) ?_
  intro s₂ h₂ hpc₂ hc₂ ok₂ hx₂
  refine run_cons (Nat.le_succ _) (by omega) h₂ hpc₂ hc₂ ok₂
    (fun ok hi => step_op h₂ hpc₂ ok .xor (k + 1) (by omega) hi) ?_
  intro s₃ h₃ hpc₃ hc₃ ok₃ hx₃
  refine run_cons (Nat.le_refl _) (by omega) h₃ hpc₃ hc₃ ok₃ (fun ok hi => step_op h₃ hpc₃ ok .and k (by omega) hi) ?_
  intro s₄ h₄ hpc₄ hc₄ ok₄ hx₄
  refine run_cons (Nat.le_refl _) (by omega) h₄ hpc₄ hc₄ ok₄ (fun ok hi => step_xor2 h₄ hpc₄ ok k (by omega) hi) ?_
  intro s₅ h₅ hpc₅ hc₅ ok₅ hx₅
  refine run_nil h₅ hpc₅ ?_
  simp only [Nat.add_assoc, Nat.reduceAdd] at hx₃
  simp only [hx₅, hx₄, hx₃, hx₂, hx₁, n10, n20, n21, Ne.symm n10, if_pos rfl, if_false, Op.raw, Op.eval,
    reduceCtorEq, ↓reduceIte]
  exact sel_val _ _ _

theorem gen_ok (env : Fin 4 → BitVec 64) : ∀ (e : Exp) (k : Nat) (hk : k + e.depth < 11) {s : St}
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
      rw [R₁.keep _ (fun j _ hj => (T_ne_A' j hj i i.2).symm), henv]
    obtain ⟨s₂, r₂, R₂, v₂⟩ := gen_ok env b (k + 1) (by omega) R₁.cfg R₁.pc
      (codeAt_mem R₁.mem hc.1.2) ok2 henv₁
    have R₁₂ := R₁.trans R₂ (Nat.le_refl _) (Nat.le_succ _)
    have va : getX s₂ (T k) = a.denote env := by
      rw [R₂.keep _ (fun j hj hj5 he => by have := T_inj (by omega) hj5 he; omega), v₁]
    have hc3 := codeAt_mem R₁₂.mem hc.2
    rw [List.length_append] at hc3
    rw [pc_add] at ok3
    obtain ⟨s₃, r₃, R₃, v₃⟩ := op_ok op k (by omega) R₁₂.cfg R₁₂.pc hc3 ok3
    refine ⟨s₃, (r₁.trans r₂).trans r₃, ?_, by rw [v₃, va, v₂]⟩
    have := R₁₂.trans R₃ (Nat.le_refl _) (Nat.le_refl _)
    simpa [Nat.add_assoc] using this
  | .ite c a b, k, hk, s, h, pc, hpc, hc, hok, henv => by
    simp only [gen, Exp.depth, Exp.denote] at *
    rw [codeAt_append, codeAt_append, codeAt_append] at hc
    rw [List.length_append, List.length_append, List.length_append] at hok ⊢
    obtain ⟨ok123, ok4⟩ := codeOK_append hok
    obtain ⟨ok12, ok3⟩ := codeOK_append ok123
    obtain ⟨ok1, ok2⟩ := codeOK_append ok12
    have keepA : ∀ {s s' : St} {pc n j}, Ran s s' pc n j → ∀ i : Fin 4, getX s' (A i) = getX s (A i) :=
      fun R i => R.keep _ (fun j _ hj => (T_ne_A' j hj i i.2).symm)
    obtain ⟨s₁, r₁, R₁, v₁⟩ := gen_ok env c k (by omega) h hpc hc.1.1.1 ok1 henv
    obtain ⟨s₂, r₂, R₂, v₂⟩ := gen_ok env a (k + 1) (by omega) R₁.cfg R₁.pc
      (codeAt_mem R₁.mem hc.1.1.2) ok2 (fun i => by rw [keepA R₁, henv])
    have R₁₂ := R₁.trans R₂ (Nat.le_refl _) (Nat.le_succ _)
    have hc3 := codeAt_mem R₁₂.mem hc.1.2
    rw [List.length_append] at hc3
    obtain ⟨s₃, r₃, R₃, v₃⟩ := gen_ok env b (k + 2) (by omega) R₁₂.cfg R₁₂.pc hc3 ok3
      (fun i => by rw [keepA R₁₂, henv])
    have R₁₂₃ := R₁₂.trans R₃ (Nat.le_refl _) (by omega)
    have ne : ∀ {i j}, i < j → j < 11 → T j ≠ T i := fun hij hj he => by
      have := T_inj hj (by omega) he; omega
    have vc : getX s₃ (T k) = c.denote env := by
      rw [R₃.keep _ (fun j hj hj11 => (ne (by omega) hj11).symm),
        R₂.keep _ (fun j hj hj11 => (ne (by omega) hj11).symm), v₁]
    have va : getX s₃ (T (k + 1)) = a.denote env := by
      rw [R₃.keep _ (fun j hj hj11 => (ne (by omega) hj11).symm), v₂]
    have hc4 := codeAt_mem R₁₂₃.mem hc.2
    rw [List.length_append, List.length_append] at hc4
    obtain ⟨s₄, r₄, R₄, v₄⟩ := sel_ok k (by omega) R₁₂₃.cfg R₁₂₃.pc hc4 ok4
    refine ⟨s₄, ((r₁.trans r₂).trans r₃).trans r₄, ?_, by rw [v₄, vc, va, v₃]⟩
    have := R₁₂₃.trans R₄ (Nat.le_refl _) (Nat.le_refl _)
    simpa [Nat.add_assoc] using this

/-- **Compiler correctness**: from any `Cfg` state with the code at `pc` and the return address
in `ra`, the Sail model runs (without traps) to `ra` with `a0 = e.denote (a0, a1, a2, a3)`,
memory unchanged and callee-saved registers kept. -/
theorem compile_ok (e : Exp) (he : e.depth < 11) {s : St} (h : Cfg s) {pc : BitVec 64}
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
  have hra₁ : getX s₁ 1 = getX s 1 := R₁.keep 1 (fun i _ hi => (T_ne_1' i hi).symm)
  have hra₂ : getX s₂ 1 = getX s 1 := by rw [hn₂.x, if_neg (by decide), hra₁]
  have hc2' := codeAt_mem hn₂.mem hc2
  obtain ⟨s₃, hn₃⟩ := step_ret hn₂.cfg hn₂.pc
    (codeOK_pcOK (codeOK_append (a := 1) (b := 1) ok2).2 (by simp))
    (by simpa using hc2' 1 (by simp)) (by rw [hra₂]; exact hra)
  refine ⟨n₁ + 2, s₃, Steps.trans st₁ ⟨s₂, hn₂.ret, s₃, hn₃.ret, rfl⟩, ?_, ?_, hn₃.cfg, ?_, ?_⟩
  · rw [hn₃.pc, hra₂]
  · rw [hn₃.x, if_neg (by decide), hn₂.x, if_pos (by decide)]; exact v₁
  · rw [hn₃.mem, hn₂.mem, R₁.mem]
  · have keep : ∀ j : Fin 32, (∀ i, i < 11 → j ≠ T i) → j ≠ 10 → getX s₃ j = getX s j := by
      intro j hj h10
      rw [hn₃.x, if_neg (by simp), hn₂.x, if_neg (by simp [h10])]
      exact R₁.keep j (fun i _ hi => hj i hi)
    have ne : ∀ j ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 32)),
        (∀ i, i < 11 → j ≠ T i) ∧ j ≠ 10 := by decide
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
