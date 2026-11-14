/- Correctness of `gen8` (expressions over 8 variables `a0..a7`, temporaries `t0..t6`) on the Sail model.
The same proof as `gen_ok` (`Proven/Compiler.lean`), with the frame `Ran7`: only `t_k .. t6` change. -/
import Riscv.Steps.ArrWords

set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Proven

/-- `s'` is reached from `s` by running `n` words from `pc`, writing only `t_k .. t6` -/
structure Ran7 (s s' : St) (pc : BitVec 64) (n k : Nat) : Prop where
  cfg : Cfg s'
  pc : s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * n))
  mem : s'.mem = s.mem
  keep : ∀ j, (∀ i, k ≤ i → i < 7 → j ≠ T i) → getX s' j = getX s j

theorem Ran7.trans {s₁ s₂ s₃ : St} {pc n₁ n₂ k k' k''} (r₁ : Ran7 s₁ s₂ pc n₁ k)
    (r₂ : Ran7 s₂ s₃ (pc + BitVec.ofNat 64 (4 * n₁)) n₂ k') (hk : k'' ≤ k) (hk' : k'' ≤ k') :
    Ran7 s₁ s₃ pc (n₁ + n₂) k'' :=
  ⟨r₂.cfg, by rw [r₂.pc, pc_add], by rw [r₂.mem, r₁.mem],
    fun j hj => by rw [r₂.keep j (fun i hi => hj i (by omega)), r₁.keep j (fun i hi => hj i (by omega))]⟩

theorem Ran7.ofNext {s s' : St} {pc k v} (hk : k < 7) (hn : Next s s' (pc + 4) (T k) v s.mem) :
    Ran7 s s' pc 1 k ∧ getX s' (T k) = v := by
  refine ⟨⟨hn.cfg, by rw [hn.pc]; rfl, hn.mem, fun j hj => ?_⟩, ?_⟩
  · rw [hn.x j]; have := hj k (by omega) hk; simp [this]
  · have : T k ≠ 0 := T_ne_0 k (by omega)
    rw [hn.x]; simp [this]

theorem Ran7.refl {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (k : Nat) :
    Ran7 s s pc 0 k := ⟨h, by simpa using hpc, rfl, fun _ _ => rfl⟩

theorem T_ne_A8' : ∀ k < 7, ∀ i : Fin 8, T k ≠ A8 i := by decide

theorem Ran7.keepA {s s' : St} {pc n k} (R : Ran7 s s' pc n k) (i : Fin 8) : getX s' (A8 i) = getX s (A8 i) :=
  R.keep _ (fun j _ hj => (T_ne_A8' j hj i).symm)

theorem run_one7 {s : St} {pc : BitVec 64} {k : Nat} {w : BitVec 32} {v : BitVec 64} (hk : k < 7)
    (hstep : ∃ s', Next s s' (pc + 4) (T k) v s.mem) :
    ∃ s', Reach s s' ∧ Ran7 s s' pc [w].length k ∧ getX s' (T k) = v := by
  obtain ⟨s', hn⟩ := hstep
  exact ⟨s', Reach.next hn, (Ran7.ofNext hk hn).1, (Ran7.ofNext hk hn).2⟩

theorem const_ok7 (k : Nat) (hk : k < 7) : ∀ (n : Nat) {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (genConst k n))
    (hok : codeOK pc (genConst k n).length),
    ∃ s', Reach s s' ∧ Ran7 s s' pc (genConst k n).length k ∧ getX s' (T k) = BitVec.ofNat 64 n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s h pc hpc hc hok
  rw [genConst] at hc hok ⊢
  by_cases hn : n = 0
  · subst hn
    simp only [↓reduceIte] at hc hok ⊢
    exact run_one7 hk (step_zero h hpc (codeOK_pcOK hok (by simp)) k (by omega) (codeAt_one hc))
  · simp only [hn, ↓reduceIte] at hc hok ⊢
    rw [codeAt_append, codeAt_append] at hc
    rw [List.length_append, List.length_append] at hok ⊢
    obtain ⟨ok1, ok23⟩ := codeOK_append (by rwa [Nat.add_assoc] at hok)
    obtain ⟨ok2, ok3⟩ := codeOK_append ok23
    obtain ⟨s₁, r₁, R₁, v₁⟩ := ih (n / 2) (by omega) h hpc hc.1.1 ok1
    obtain ⟨s₂, hn₂⟩ := step_shl R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) k (by omega)
      (codeAt_one (codeAt_mem R₁.mem hc.1.2))
    obtain ⟨R₂, v₂⟩ := Ran7.ofNext hk hn₂
    have R₁₂ := R₁.trans R₂ (Nat.le_refl _) (Nat.le_refl _)
    rw [v₁, shl_ofNat] at v₂
    by_cases hodd : n % 2 = 1
    · simp only [hodd, ↓reduceIte] at hc ok3 ⊢
      have hc3 := codeAt_mem R₁₂.mem hc.2
      rw [List.length_append] at hc3
      rw [pc_add] at ok3
      obtain ⟨s₃, hn₃⟩ := step_inc R₁₂.cfg R₁₂.pc (codeOK_pcOK ok3 (by simp)) k (by omega) (codeAt_one hc3)
      obtain ⟨R₃, v₃⟩ := Ran7.ofNext hk hn₃
      refine ⟨s₃, (r₁.trans (Reach.next hn₂)).trans (Reach.next hn₃), ?_, ?_⟩
      · have := R₁₂.trans R₃ (Nat.le_refl _) (Nat.le_refl _)
        simpa [Nat.add_assoc] using this
      · rw [v₃, v₂, inc_ofNat]; congr 1; omega
    · simp only [hodd, ↓reduceIte, List.length_nil, Nat.add_zero] at hc ok3 ⊢
      refine ⟨s₂, r₁.trans (Reach.next hn₂), R₁₂, ?_⟩
      rw [v₂]; congr 1; omega

theorem run_cons7 {s : St} {pc : BitVec 64} {k j : Nat} {w : BitVec 32} {ws : List (BitVec 32)}
    {v : BitVec 64} {P : St → Prop} (hkj : k ≤ j) (hj : j < 7) (h : Cfg s)
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (w :: ws)) (hok : codeOK pc (w :: ws).length)
    (hstep : pcOK pc → instrAt s pc w → ∃ s', Next s s' (pc + 4) (T j) v s.mem)
    (hrest : ∀ s', Cfg s' → s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * 1)) →
      codeAt s' (pc + BitVec.ofNat 64 (4 * 1)) ws → codeOK (pc + BitVec.ofNat 64 (4 * 1)) ws.length →
      (∀ r, getX s' r = if r = T j then v else getX s r) →
      ∃ s'', Reach s' s'' ∧ Ran7 s' s'' (pc + BitVec.ofNat 64 (4 * 1)) ws.length k ∧ P s'') :
    ∃ s'', Reach s s'' ∧ Ran7 s s'' pc (w :: ws).length k ∧ P s'' := by
  change codeAt s pc ([w] ++ ws) at hc
  rw [show (w :: ws).length = [w].length + ws.length by simp [Nat.add_comm]] at hok
  rw [codeAt_append] at hc
  obtain ⟨ok1, ok2⟩ := codeOK_append hok
  obtain ⟨s₁, hn⟩ := hstep (codeOK_pcOK ok1 (by simp)) (codeAt_one hc.1)
  obtain ⟨R₁, -⟩ := Ran7.ofNext hj hn
  obtain ⟨s₂, r₂, R₂, p₂⟩ := hrest s₁ R₁.cfg R₁.pc (codeAt_mem R₁.mem hc.2) ok2
    (fun r => by rw [hn.x]; by_cases hr : r = T j <;> simp [hr, T_ne_0 j (by omega)])
  refine ⟨s₂, (Reach.next hn).trans r₂, ?_, p₂⟩
  have := R₁.trans R₂ hkj (Nat.le_refl _)
  simpa [Nat.add_comm] using this

theorem run_nil7 {s : St} {pc : BitVec 64} {k : Nat} {P : St → Prop} (h : Cfg s)
    (hpc : s.regs.get? .PC = some pc) (hp : P s) :
    ∃ s', Reach s s' ∧ Ran7 s s' pc ([] : List (BitVec 32)).length k ∧ P s' :=
  ⟨s, ⟨0, rfl⟩, Ran7.refl h hpc k, hp⟩

theorem op_ok7 (op : Op) (k : Nat) (hk : k + 1 < 7) {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (opCode op k)) (hok : codeOK pc (opCode op k).length) :
    ∃ s', Reach s s' ∧ Ran7 s s' pc (opCode op k).length k ∧
      getX s' (T k) = op.eval (getX s (T k)) (getX s (T (k + 1))) := by
  unfold opCode at *
  by_cases he : op = .eq
  · subst he; simp only [↓reduceIte] at *
    refine run_cons7 (Nat.le_refl _) (by omega) h hpc hc hok (fun ok hi => step_op h hpc ok .eq k (by omega) hi) ?_
    intro s₁ h₁ hpc₁ hc₁ ok₁ hx₁
    refine run_cons7 (Nat.le_refl _) (by omega) h₁ hpc₁ hc₁ ok₁ (fun ok hi => step_seqz h₁ hpc₁ ok k (by omega) hi) ?_
    intro s₂ h₂ hpc₂ hc₂ ok₂ hx₂
    refine run_nil7 h₂ hpc₂ ?_
    simp only [hx₂, hx₁, if_pos rfl, Op.raw, Op.eval, xor_eq_zero, ↓reduceIte]
  · simp only [he, ↓reduceIte] at hc hok ⊢
    refine run_cons7 (Nat.le_refl _) (by omega) h hpc hc hok (fun ok hi => step_op h hpc ok op k (by omega) hi) ?_
    intro s₁ h₁ hpc₁ hc₁ ok₁ hx₁
    refine run_nil7 h₁ hpc₁ ?_
    simp only [hx₁, if_pos rfl, Op.raw, if_neg he, ↓reduceIte]

theorem sel_ok7 (k : Nat) (hk : k + 2 < 7) {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (selCode k)) (hok : codeOK pc (selCode k).length) :
    ∃ s', Reach s s' ∧ Ran7 s s' pc (selCode k).length k ∧
      getX s' (T k) = if getX s (T k) = 0 then getX s (T (k + 2)) else getX s (T (k + 1)) := by
  have ne : ∀ {i j}, i < j → j < 11 → T j ≠ T i := fun hij hj he => by
    have := T_inj hj (by omega) he; omega
  have n10 : T (k + 1) ≠ T k := ne (by omega) (by omega)
  have n20 : T (k + 2) ≠ T k := ne (by omega) (by omega)
  have n21 : T (k + 2) ≠ T (k + 1) := ne (by omega) (by omega)
  unfold selCode at *
  refine run_cons7 (Nat.le_refl _) (by omega) h hpc hc hok (fun ok hi => step_snez h hpc ok k (by omega) hi) ?_
  intro s₁ h₁ hpc₁ hc₁ ok₁ hx₁
  refine run_cons7 (Nat.le_refl _) (by omega) h₁ hpc₁ hc₁ ok₁ (fun ok hi => step_neg h₁ hpc₁ ok k (by omega) hi) ?_
  intro s₂ h₂ hpc₂ hc₂ ok₂ hx₂
  refine run_cons7 (Nat.le_succ _) (by omega) h₂ hpc₂ hc₂ ok₂
    (fun ok hi => step_op h₂ hpc₂ ok .xor (k + 1) (by omega) hi) ?_
  intro s₃ h₃ hpc₃ hc₃ ok₃ hx₃
  refine run_cons7 (Nat.le_refl _) (by omega) h₃ hpc₃ hc₃ ok₃ (fun ok hi => step_op h₃ hpc₃ ok .and k (by omega) hi) ?_
  intro s₄ h₄ hpc₄ hc₄ ok₄ hx₄
  refine run_cons7 (Nat.le_refl _) (by omega) h₄ hpc₄ hc₄ ok₄ (fun ok hi => step_xor2 h₄ hpc₄ ok k (by omega) hi) ?_
  intro s₅ h₅ hpc₅ hc₅ ok₅ hx₅
  refine run_nil7 h₅ hpc₅ ?_
  simp only [Nat.add_assoc, Nat.reduceAdd] at hx₃
  simp only [hx₅, hx₄, hx₃, hx₂, hx₁, n10, n20, n21, Ne.symm n10, if_pos rfl, if_false, Op.raw, Op.eval,
    reduceCtorEq, ↓reduceIte]
  exact sel_val _ _ _

theorem gen8_ok (env : AEnv) : ∀ (e : AExp) (k : Nat) (hk : k + e.depth < 7) {s : St}
    (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (gen8 e k))
    (hok : codeOK pc (gen8 e k).length) (henv : ∀ i : Fin 8, getX s (A8 i) = env i),
    ∃ s', Reach s s' ∧ Ran7 s s' pc (gen8 e k).length k ∧ getX s' (T k) = e.denote env
  | .var i, k, hk, s, h, pc, hpc, hc, hok, henv => by
    simp only [gen8, AExp.denote] at *
    obtain ⟨s', r, R, v⟩ := run_one7 (w := iVar8 i k) (by simp [AExp.depth] at hk; omega)
      (step_var8 h hpc (codeOK_pcOK hok (by simp)) i k (by simp [AExp.depth] at hk; omega) (codeAt_one hc))
    exact ⟨s', r, R, by rw [v, henv]⟩
  | .const c, k, hk, s, h, pc, hpc, hc, hok, henv => by
    simp only [gen8, AExp.denote] at *
    obtain ⟨s', r, R, v⟩ := const_ok7 k (by simp [AExp.depth] at hk; omega) c.toNat h hpc hc hok
    exact ⟨s', r, R, by rw [v, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  | .bin op a b, k, hk, s, h, pc, hpc, hc, hok, henv => by
    simp only [gen8, AExp.depth, AExp.denote] at *
    rw [codeAt_append, codeAt_append] at hc
    rw [List.length_append, List.length_append] at hok ⊢
    obtain ⟨ok1, ok23⟩ := codeOK_append (by rwa [Nat.add_assoc] at hok)
    obtain ⟨ok2, ok3⟩ := codeOK_append ok23
    obtain ⟨s₁, r₁, R₁, v₁⟩ := gen8_ok env a k (by omega) h hpc hc.1.1 ok1 henv
    obtain ⟨s₂, r₂, R₂, v₂⟩ := gen8_ok env b (k + 1) (by omega) R₁.cfg R₁.pc
      (codeAt_mem R₁.mem hc.1.2) ok2 (fun i => by rw [R₁.keepA, henv])
    have R₁₂ := R₁.trans R₂ (Nat.le_refl _) (Nat.le_succ _)
    have va : getX s₂ (T k) = a.denote env := by
      rw [R₂.keep _ (fun j hj hj5 he => by have := T_inj (by omega) (by omega) he; omega), v₁]
    have hc3 := codeAt_mem R₁₂.mem hc.2
    rw [List.length_append] at hc3
    rw [pc_add] at ok3
    obtain ⟨s₃, r₃, R₃, v₃⟩ := op_ok7 op k (by omega) R₁₂.cfg R₁₂.pc hc3 ok3
    refine ⟨s₃, (r₁.trans r₂).trans r₃, ?_, by rw [v₃, va, v₂]⟩
    have := R₁₂.trans R₃ (Nat.le_refl _) (Nat.le_refl _)
    simpa [Nat.add_assoc] using this
  | .ite c a b, k, hk, s, h, pc, hpc, hc, hok, henv => by
    simp only [gen8, AExp.depth, AExp.denote] at *
    rw [codeAt_append, codeAt_append, codeAt_append] at hc
    rw [List.length_append, List.length_append, List.length_append] at hok ⊢
    obtain ⟨ok123, ok4⟩ := codeOK_append hok
    obtain ⟨ok12, ok3⟩ := codeOK_append ok123
    obtain ⟨ok1, ok2⟩ := codeOK_append ok12
    obtain ⟨s₁, r₁, R₁, v₁⟩ := gen8_ok env c k (by omega) h hpc hc.1.1.1 ok1 henv
    obtain ⟨s₂, r₂, R₂, v₂⟩ := gen8_ok env a (k + 1) (by omega) R₁.cfg R₁.pc
      (codeAt_mem R₁.mem hc.1.1.2) ok2 (fun i => by rw [R₁.keepA, henv])
    have R₁₂ := R₁.trans R₂ (Nat.le_refl _) (Nat.le_succ _)
    have hc3 := codeAt_mem R₁₂.mem hc.1.2
    rw [List.length_append] at hc3
    obtain ⟨s₃, r₃, R₃, v₃⟩ := gen8_ok env b (k + 2) (by omega) R₁₂.cfg R₁₂.pc hc3 ok3
      (fun i => by rw [R₁₂.keepA, henv])
    have R₁₂₃ := R₁₂.trans R₃ (Nat.le_refl _) (by omega)
    have ne : ∀ {i j}, i < j → j < 11 → T j ≠ T i := fun hij hj he => by
      have := T_inj hj (by omega) he; omega
    have vc : getX s₃ (T k) = c.denote env := by
      rw [R₃.keep _ (fun j hj hj11 => (ne (by omega) (by omega)).symm),
        R₂.keep _ (fun j hj hj11 => (ne (by omega) (by omega)).symm), v₁]
    have va : getX s₃ (T (k + 1)) = a.denote env := by
      rw [R₃.keep _ (fun j hj hj11 => (ne (by omega) (by omega)).symm), v₂]
    have hc4 := codeAt_mem R₁₂₃.mem hc.2
    rw [List.length_append, List.length_append] at hc4
    obtain ⟨s₄, r₄, R₄, v₄⟩ := sel_ok7 k (by omega) R₁₂₃.cfg R₁₂₃.pc hc4 ok4
    refine ⟨s₄, ((r₁.trans r₂).trans r₃).trans r₄, ?_, by rw [v₄, vc, va, v₃]⟩
    have := R₁₂₃.trans R₄ (Nat.le_refl _) (Nat.le_refl _)
    simpa [Nat.add_assoc] using this

end Proven
