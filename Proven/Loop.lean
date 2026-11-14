/- A structured source language with `while` loops on top of `Exp`, its compiler to RV64I (`gen` for
expressions, `beq`/`jal` for loops) and the correctness proof on the Sail model.

Variables: the four machine words `a0..a3` (`x10..x13`), which `gen` reads (`Exp.var i` is `a_i`) and
never uses as temporaries; expression temporaries are `t0..t6, a4..a7` (`T`). -/
import Proven.BranchWords
import Proven.LoopRule
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Proven

/-! ## Source language -/

abbrev Env := Fin 4 → BitVec 64

def Env.set (σ : Env) (v : Fin 4) (x : BitVec 64) : Env := fun i => if i = v then x else σ i

inductive Stmt where
  /-- `a_v := e` -/
  | assign (v : Fin 4) (e : Exp)
  | seq (a b : Stmt)
  /-- `while c ≠ 0 do body` -/
  | loop (c : Exp) (body : Stmt)

/-- big-step semantics: `Exec p σ σ'` iff `p` started in `σ` terminates in `σ'` -/
inductive Exec : Stmt → Env → Env → Prop
  | assign {v e σ} : Exec (.assign v e) σ (σ.set v (e.denote σ))
  | seq {a b σ σ₁ σ₂} : Exec a σ σ₁ → Exec b σ₁ σ₂ → Exec (.seq a b) σ σ₂
  | loopF {c b σ} : c.denote σ = 0 → Exec (.loop c b) σ σ
  | loopT {c b σ σ₁ σ₂} : c.denote σ ≠ 0 → Exec b σ σ₁ → Exec (.loop c b) σ₁ σ₂ → Exec (.loop c b) σ σ₂

/-- Loops via a user-supplied measure: if every iteration runs `body` to a state with smaller `μ` and
the same final value `F`, and `F` is the identity where the loop exits, the loop runs from `σ` to `F σ`. -/
theorem Exec.loop_of {c : Exp} {b : Stmt} (μ : Env → Nat) (F : Env → Env)
    (hstep : ∀ σ, c.denote σ ≠ 0 → ∃ σ₁, Exec b σ σ₁ ∧ μ σ₁ < μ σ ∧ F σ₁ = F σ)
    (hexit : ∀ σ, c.denote σ = 0 → F σ = σ) : ∀ σ, Exec (.loop c b) σ (F σ) := by
  intro σ
  induction h : μ σ using Nat.strongRecOn generalizing σ with
  | ind n ih =>
    by_cases hc : c.denote σ = 0
    · rw [hexit σ hc]; exact .loopF hc
    · obtain ⟨σ₁, hb, hlt, hF⟩ := hstep σ hc
      rw [← hF]; exact .loopT hc hb (ih _ (h ▸ hlt) σ₁ rfl)

/-! ## Compiler -/

/-- `add a_v, x0, t0` -/
def iMv (v : Fin 4) : BitVec 32 := encR 0 0 (A v) 0 5
/-- `beq t0, x0, +4n` -/
def iBeqz (n : Nat) : BitVec 32 := wB 0 5 0 (BitVec.ofNat 12 (2 * n))
/-- `jal x0, -4n` -/
def iJmp (n : Nat) : BitVec 32 := wJ 0 (BitVec.ofNat 20 (2 ^ 20 - 2 * n))

def compileS : Stmt → List (BitVec 32)
  | .assign v e => gen e 0 ++ [iMv v]
  | .seq a b => compileS a ++ compileS b
  | .loop c b => gen c 0 ++ [iBeqz ((compileS b).length + 2)] ++ compileS b ++
      [iJmp ((gen c 0).length + 1 + (compileS b).length)]

/-- as a function: run the statement, then `ret` -/
def compileF (p : Stmt) : List (BitVec 32) := compileS p ++ [iRet]

/-- expressions fit the 11 temporaries; loop bodies fit the `beq` range -/
def Stmt.wf : Stmt → Prop
  | .assign _ e => e.depth < 11
  | .seq a b => a.wf ∧ b.wf
  | .loop c b => c.depth < 11 ∧ b.wf ∧ (gen c 0).length + (compileS b).length + 2 < 1024

/-! ## Step lemmas for the new words -/

section
variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

theorem step_mv0 (hi : instrAt s pc (iMv 0)) : ∃ s', Next s s' (pc + 4) 10 (getX s 5) s.mem := by
  rw [show iMv 0 = 0x00500533#32 by decide] at hi; step_word
theorem step_mv1 (hi : instrAt s pc (iMv 1)) : ∃ s', Next s s' (pc + 4) 11 (getX s 5) s.mem := by
  rw [show iMv 1 = 0x005005b3#32 by decide] at hi; step_word
theorem step_mv2 (hi : instrAt s pc (iMv 2)) : ∃ s', Next s s' (pc + 4) 12 (getX s 5) s.mem := by
  rw [show iMv 2 = 0x00500633#32 by decide] at hi; step_word
theorem step_mv3 (hi : instrAt s pc (iMv 3)) : ∃ s', Next s s' (pc + 4) 13 (getX s 5) s.mem := by
  rw [show iMv 3 = 0x005006b3#32 by decide] at hi; step_word

theorem step_mv (v : Fin 4) (hi : instrAt s pc (iMv v)) : ∃ s', Next s s' (pc + 4) (A v) (getX s 5) s.mem := by
  obtain ⟨_ | _ | _ | _ | v, hv⟩ := v
  · exact step_mv0 h hpc hok hi
  · exact step_mv1 h hpc hok hi
  · exact step_mv2 h hpc hok hi
  · exact step_mv3 h hpc hok hi
  · omega

end

theorem app0_toNat {w} (x : BitVec w) : (x +++ (0#1 : BitVec 1)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_append]; simp [Nat.shiftLeft_eq]; omega

theorem boff_fwd (n : Nat) (hn : 2 * n < 2048) : boff (BitVec.ofNat 12 (2 * n)) = BitVec.ofNat 64 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [boff, sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend]
  simp [BitVec.msb_eq_decide, app0_toNat]
  split <;> omega

theorem joff_back (n : Nat) (h0 : 0 < n) (hn : 2 * n ≤ 2 ^ 19) :
    joff (BitVec.ofNat 20 (2 ^ 20 - 2 * n)) = 0 - BitVec.ofNat 64 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [joff, sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend]
  simp [BitVec.msb_eq_decide, BitVec.toNat_sub, app0_toNat]
  split <;> omega

/-! ## Frames -/

/-- `s'` differs from `s` at most in the PC, the temporaries `T` and the variables `A` -/
structure Frame (s s' : St) : Prop where
  cfg : Cfg s'
  mem : s'.mem = s.mem
  keep : ∀ j : Fin 32, (∀ i, i < 11 → j ≠ T i) → (∀ i : Fin 4, j ≠ A i) → getX s' j = getX s j

theorem Frame.trans {s₁ s₂ s₃ : St} (f₁ : Frame s₁ s₂) (f₂ : Frame s₂ s₃) : Frame s₁ s₃ :=
  ⟨f₂.cfg, by rw [f₂.mem, f₁.mem], fun j h1 h2 => by rw [f₂.keep j h1 h2, f₁.keep j h1 h2]⟩

theorem Frame.ofRan {s s' : St} {pc n} (R : Ran s s' pc n 0) : Frame s s' :=
  ⟨R.cfg, R.mem, fun j h1 _ => R.keep j fun i _ hi => h1 i hi⟩

theorem Frame.ofNext {s s' : St} {pc rd v} (hn : Next s s' pc rd v s.mem) (hrd : rd = 0 ∨ ∃ i : Fin 4, rd = A i) :
    Frame s s' := by
  refine ⟨hn.cfg, hn.mem, fun j h1 h2 => ?_⟩
  rw [hn.x j]
  rcases hrd with rfl | ⟨i, rfl⟩
  · simp
  · simp [h2 i]

theorem Next.keep0 {s s' : St} {pc v m} (hn : Next s s' pc 0 v m) (j : Fin 32) : getX s' j = getX s j := by
  rw [hn.x]; simp

theorem A_inj' : ∀ i < 4, ∀ j < 4, A i = A j → i = j := by decide
theorem A_ne_0' : ∀ i < 4, A i ≠ 0 := by decide

theorem keepA {s s' : St} {pc n} (R : Ran s s' pc n 0) (i : Fin 4) : getX s' (A i) = getX s (A i) :=
  R.keep _ (fun j _ hj => (T_ne_A' j hj i i.2).symm)

theorem pc_jmp (pc : BitVec 64) (n : Nat) : pc + BitVec.ofNat 64 (4 * n) + (0 - BitVec.ofNat 64 (4 * n)) = pc := by
  bv_omega

/-! ## Correctness -/

theorem execS_ok : ∀ {p : Stmt} {σ σ' : Env}, Exec p σ σ' → p.wf → ∀ {s : St} {pc : BitVec 64}, Cfg s →
    s.regs.get? .PC = some pc → codeAt s pc (compileS p) → codeOK pc (compileS p).length →
    (∀ i : Fin 4, getX s (A i) = σ i) →
    ∃ s', Reach s s' ∧ Frame s s' ∧ s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * (compileS p).length)) ∧
      ∀ i : Fin 4, getX s' (A i) = σ' i
  | _, σ, _, .assign (v := v) (e := e), hp, s, pc, h, hpc, hc, hok, henv => by
    simp only [compileS, Stmt.wf] at hp hc hok ⊢
    rw [codeAt_append] at hc
    rw [List.length_append] at hok ⊢
    obtain ⟨ok1, ok2⟩ := codeOK_append hok
    obtain ⟨s₁, r₁, R₁, v₁⟩ := gen_ok σ e 0 (by omega) h hpc hc.1 ok1 henv
    obtain ⟨s₂, hn⟩ := step_mv R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) v
      (codeAt_one (codeAt_mem R₁.mem hc.2))
    refine ⟨s₂, r₁.trans (Reach.next hn), (Frame.ofRan R₁).trans (Frame.ofNext hn (.inr ⟨v, rfl⟩)),
      by rw [hn.pc, ← pc_add]; rfl, fun i => ?_⟩
    rw [hn.x, keepA R₁]
    by_cases hiv : i = v
    · subst hiv; simp [Env.set, A_ne_0' i i.2, ← v₁]; rfl
    · have : A i ≠ A v := fun e => hiv (Fin.ext (A_inj' i i.2 v v.2 e))
      rw [if_neg (fun h => this h.1)]; simp only [Env.set, if_neg hiv]; exact henv i
  | _, σ, _, .seq (a := a) (b := b) ha hb, hp, s, pc, h, hpc, hc, hok, henv => by
    simp only [compileS, Stmt.wf] at hp hc hok ⊢
    rw [codeAt_append] at hc
    rw [List.length_append] at hok ⊢
    obtain ⟨ok1, ok2⟩ := codeOK_append hok
    obtain ⟨s₁, r₁, F₁, pc₁, v₁⟩ := execS_ok ha hp.1 h hpc hc.1 ok1 henv
    obtain ⟨s₂, r₂, F₂, pc₂, v₂⟩ := execS_ok hb hp.2 F₁.cfg pc₁ (codeAt_mem F₁.mem hc.2) ok2 v₁
    exact ⟨s₂, r₁.trans r₂, F₁.trans F₂, by rw [pc₂, pc_add], v₂⟩
  | _, σ, _, .loopF (c := c) (b := b) hc0, hp, s, pc, h, hpc, hc, hok, henv => by
    simp only [Stmt.wf] at hp
    obtain ⟨hp1, hp2, hp3⟩ := hp
    rw [compileS] at hc hok ⊢
    rw [codeAt_append, codeAt_append, codeAt_append] at hc
    simp only [List.length_append, List.length_singleton] at hok ⊢
    obtain ⟨ok123, ok4⟩ := codeOK_append hok
    obtain ⟨ok12, ok3⟩ := codeOK_append ok123
    obtain ⟨ok1, ok2⟩ := codeOK_append ok12
    obtain ⟨s₁, r₁, R₁, v₁⟩ := gen_ok σ c 0 (by omega) h hpc hc.1.1.1 ok1 henv
    obtain ⟨s₂, hn⟩ := step_beq_5_0 R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) _
      (codeAt_one (codeAt_mem R₁.mem hc.1.1.2))
    have hcond : bcond 0 (getX s₁ 5) (getX s₁ 0) = true := by
      rw [show getX s₁ 0 = 0 from rfl, show getX s₁ 5 = c.denote σ from v₁, hc0]; rfl
    refine ⟨s₂, r₁.trans (Reach.next hn), (Frame.ofRan R₁).trans (Frame.ofNext hn (.inl rfl)), ?_,
      fun i => by rw [hn.keep0, keepA R₁, henv]⟩
    rw [hn.pc, if_pos hcond, boff_fwd ((compileS b).length + 2) (by omega), pc_add]
    congr 3; omega
  | _, σ, σ₂, .loopT (c := c) (b := b) (σ₁ := σ₁) hc0 hb hl, hp, s, pc, h, hpc, hc, hok, henv => by
    have hp' := hp
    simp only [Stmt.wf] at hp'
    obtain ⟨hp1, hp2, hp3⟩ := hp'
    have hcode := hc
    have hok0 := hok
    rw [compileS] at hc hok
    rw [codeAt_append, codeAt_append, codeAt_append] at hc
    simp only [List.length_append, List.length_singleton] at hok
    obtain ⟨ok123, ok4⟩ := codeOK_append hok
    obtain ⟨ok12, ok3⟩ := codeOK_append ok123
    obtain ⟨ok1, ok2⟩ := codeOK_append ok12
    obtain ⟨s₁, r₁, R₁, v₁⟩ := gen_ok σ c 0 (by omega) h hpc hc.1.1.1 ok1 henv
    obtain ⟨s₂, hn⟩ := step_beq_5_0 R₁.cfg R₁.pc (codeOK_pcOK ok2 (by simp)) _
      (codeAt_one (codeAt_mem R₁.mem hc.1.1.2))
    have hcond : bcond 0 (getX s₁ 5) (getX s₁ 0) = false := by
      rw [show getX s₁ 0 = 0 from rfl, show getX s₁ 5 = c.denote σ from v₁]; simpa [bcond] using hc0
    have F₂ := (Frame.ofRan R₁).trans (Frame.ofNext hn (.inl rfl))
    have henv₂ : ∀ i : Fin 4, getX s₂ (A i) = σ i := fun i => by
      rw [hn.keep0, keepA R₁, henv]
    have hpc₂ : s₂.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * ((gen c 0).length + 1))) := by
      rw [hn.pc, hcond]; simp only [Bool.false_eq_true, if_false]
      rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4 * 1) from rfl, pc_add]
    have hc3 : codeAt s₂ (pc + BitVec.ofNat 64 (4 * ((gen c 0).length + 1))) (compileS b) := by
      have := codeAt_mem F₂.mem hc.1.2; rwa [List.length_append, List.length_singleton] at this
    obtain ⟨s₃, r₃, F₃, pc₃, v₃⟩ := execS_ok hb hp2 F₂.cfg hpc₂ hc3 ok3 henv₂
    rw [pc_add] at pc₃
    have hc4 : codeAt s₃ (pc + BitVec.ofNat 64 (4 * ((gen c 0).length + 1 + (compileS b).length)))
        [iJmp ((gen c 0).length + 1 + (compileS b).length)] := by
      have := codeAt_mem (F₂.trans F₃).mem hc.2
      rwa [List.length_append, List.length_append, List.length_singleton] at this
    obtain ⟨s₄, hn₄⟩ := step_jal_0 F₃.cfg pc₃ (codeOK_pcOK ok4 (by simp)) _ (codeAt_one hc4)
    have F₄ := (F₂.trans F₃).trans (Frame.ofNext hn₄ (.inl rfl))
    have hpc₄ : s₄.regs.get? .PC = some pc := by
      rw [hn₄.pc, joff_back _ (by omega) (by omega), pc_jmp]
    have henv₄ : ∀ i : Fin 4, getX s₄ (A i) = σ₁ i := fun i => by
      rw [hn₄.keep0, v₃]
    obtain ⟨s₅, r₅, F₅, pc₅, v₅⟩ := execS_ok hl hp F₄.cfg hpc₄ (codeAt_mem F₄.mem hcode) hok0 henv₄
    exact ⟨s₅, (((r₁.trans (Reach.next hn)).trans r₃).trans (Reach.next hn₄)).trans r₅, F₄.trans F₅, pc₅, v₅⟩

theorem calleeSaved_of_frame {s s' : St} (h : Cfg s) (f : Frame s s') : calleeSavedKept s s' := by
  have ne : ∀ j ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 32)),
      (∀ i, i < 11 → j ≠ T i) ∧ ∀ i : Fin 4, j ≠ A i := by decide
  have k : ∀ j ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 32)), getX s' j = getX s j :=
    fun j hj => f.keep j (ne j hj).1 (ne j hj).2
  have h₃ := f.cfg
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₃.x2, h.x2, k 2 (by decide)]
  · rw [h₃.x8, h.x8, k 8 (by decide)]
  · rw [h₃.x9, h.x9, k 9 (by decide)]
  · rw [h₃.x18, h.x18, k 18 (by decide)]
  · rw [h₃.x19, h.x19, k 19 (by decide)]
  · rw [h₃.x20, h.x20, k 20 (by decide)]
  · rw [h₃.x21, h.x21, k 21 (by decide)]
  · rw [h₃.x22, h.x22, k 22 (by decide)]
  · rw [h₃.x23, h.x23, k 23 (by decide)]
  · rw [h₃.x24, h.x24, k 24 (by decide)]
  · rw [h₃.x25, h.x25, k 25 (by decide)]
  · rw [h₃.x26, h.x26, k 26 (by decide)]
  · rw [h₃.x27, h.x27, k 27 (by decide)]

/-- **Correctness of `compileS`**: if the source program `p` terminates from `σ` (the values of `a0..a3`)
in `σ'`, the Sail model runs the code `compileS p` (placed anywhere in RAM) without traps to its end,
with `a0..a3 = σ'`, memory unchanged, callee-saved registers and `Cfg` kept. -/
theorem compileS_ok {p : Stmt} (hp : p.wf) {σ σ' : Env} (hex : Exec p σ σ') {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compileS p)) (hok : codeOK pc (compileS p).length)
    (henv : ∀ i : Fin 4, getX s (A i) = σ i) :
    runsTo s fun s' => s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * (compileS p).length)) ∧
      (∀ i : Fin 4, getX s' (A i) = σ' i) ∧ Cfg s' ∧ s'.mem = s.mem ∧ calleeSavedKept s s' := by
  obtain ⟨s', r, F, hpc', v⟩ := execS_ok hex hp h hpc hc hok henv
  exact runsTo_of_reach r ⟨hpc', v, F.cfg, F.mem, calleeSaved_of_frame h F⟩

/-- **Correctness of `compileF`** (a called function): from the inputs `a0..a3`, if `p` terminates, the
code returns to `ra` with `a0..a3` = the final variables. -/
theorem compileF_ok {p : Stmt} (hp : p.wf) {σ' : Env} {s : St} (hex : Exec p (fun i => getX s (A i)) σ')
    (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compileF p))
    (hok : codeOK pc (compileF p).length) (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ (∀ i : Fin 4, getX s' (A i) = σ' i) ∧ Cfg s' ∧
      s'.mem = s.mem ∧ calleeSavedKept s s' := by
  simp only [compileF] at hc hok
  rw [codeAt_append] at hc
  rw [List.length_append] at hok
  obtain ⟨ok1, ok2⟩ := codeOK_append hok
  obtain ⟨s₁, r₁, F₁, pc₁, v₁⟩ := execS_ok hex hp h hpc hc.1 ok1 (fun _ => rfl)
  have hra₁ : getX s₁ 1 = getX s 1 := F₁.keep 1 (by decide) (by decide)
  obtain ⟨s₂, hn⟩ := step_ret F₁.cfg pc₁ (codeOK_pcOK ok2 (by simp)) (codeAt_one (codeAt_mem F₁.mem hc.2))
    (by rw [hra₁]; exact hra)
  have F₂ := F₁.trans (Frame.ofNext hn (.inl rfl))
  refine runsTo_of_reach (r₁.trans (Reach.next hn)) ⟨by rw [hn.pc, hra₁], fun i => ?_, F₂.cfg, F₂.mem,
    calleeSaved_of_frame h F₂⟩
  rw [hn.keep0]; exact v₁ i

end Proven
