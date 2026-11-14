/- Middle layer, statements with `while` loops: `Stmt` to abstract operations and its correctness, proved
from the interface laws only.

`Stmt`/`Exec` are a model-free copy of `Proven.Stmt`/`Proven.Exec` (`Proven/Loop.lean` imports the Sail
model, so it cannot be imported here); `Proven/Mach/RiscvStmt.lean` maps one to the other.
Branch distances are in target words: the compiler is parameterised by the target's encoding lengths
(`M.code`, `M.lenBz`, `M.lenJmp`), and the range side conditions are the target's `bzOK` / `jmpOK`. -/
import Proven.Mach.Exp

namespace Proven.Mach

abbrev Env := Fin 4 → BitVec 64

def Env.set (σ : Env) (v : Fin 4) (x : BitVec 64) : Env := fun i => if i = v then x else σ i

inductive Stmt where
  | assign (v : Fin 4) (e : Exp)
  | seq (a b : Stmt)
  /-- `while c ≠ 0 do body` -/
  | loop (c : Exp) (body : Stmt)

inductive Exec : Stmt → Env → Env → Prop
  | assign {v e σ} : Exec (.assign v e) σ (σ.set v (e.denote σ))
  | seq {a b σ σ₁ σ₂} : Exec a σ σ₁ → Exec b σ₁ σ₂ → Exec (.seq a b) σ σ₂
  | loopF {c b σ} : c.denote σ = 0 → Exec (.loop c b) σ σ
  | loopT {c b σ σ₁ σ₂} : c.denote σ ≠ 0 → Exec b σ σ₁ → Exec (.loop c b) σ₁ σ₂ → Exec (.loop c b) σ σ₂

theorem v4_inj {i j : Fin 4} (h : v4 i = v4 j) : i = j := by revert i j; decide

namespace Machine
variable (M : Machine)

/-- the statement compiler (abstract operations) -/
def compS : Stmt → List AOp
  | .assign v e => mgenE e 0 ++ [.mov (v4 v) (rk 0)]
  | .seq a b => compS a ++ compS b
  | .loop c b => mgenE c 0 ++ [.bz (rk 0) ((M.code (compS b)).length + M.lenBz + M.lenJmp)] ++ compS b ++
      [.jmp ((M.code (mgenE c 0)).length + M.lenBz + (M.code (compS b)).length)]

/-- as a function: run the statement, then return -/
def compF (p : Stmt) : List AOp := M.compS p ++ [.ret]

/-- expressions fit the 11 temporaries; branch distances in the target's range -/
def wf : Stmt → Prop
  | .assign _ e => e.depth < 11
  | .seq a b => wf a ∧ wf b
  | .loop c b => c.depth < 11 ∧ wf b ∧ M.bzOK ((M.code (M.compS b)).length + M.lenBz + M.lenJmp) ∧
      M.jmpOK ((M.code (mgenE c 0)).length + M.lenBz + (M.code (M.compS b)).length)

theorem code_loop (c : Exp) (b : Stmt) : M.code (M.compS (.loop c b)) = M.code (mgenE c 0) ++
    M.enc (.bz (rk 0) ((M.code (M.compS b)).length + M.lenBz + M.lenJmp)) ++ M.code (M.compS b) ++
    M.enc (.jmp ((M.code (mgenE c 0)).length + M.lenBz + (M.code (M.compS b)).length)) := by
  simp only [compS, code_append, code_one]

theorem len_loop (c : Exp) (b : Stmt) : (M.code (M.compS (.loop c b))).length =
    (M.code (mgenE c 0)).length + M.lenBz + (M.code (M.compS b)).length + M.lenJmp := by
  rw [code_loop]; simp only [List.length_append, M.len_bz, M.len_jmp]

theorem execS_ok : ∀ {p : Stmt} {σ σ' : Env}, Exec p σ σ' → M.wf p → ∀ {s : M.S} {pc : BitVec 64},
    M.At s pc (M.code (M.compS p)) → (∀ i, M.get s (v4 i) = σ i) →
    M.runsTo s fun s' => M.Done s s' (next pc (M.code (M.compS p)).length) ∧ M.mem s' = M.mem s ∧
      ∀ i, M.get s' (v4 i) = σ' i
  | _, σ, _, .assign (v := v) (e := e), hp, s, pc, hA, henv => by
    simp only [compS, wf, code_append, code_one, List.length_append] at hp hA ⊢
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA
    rw [← next_add]
    refine M.seq_run (M.genE_ok σ e 0 (by omega) hA1 henv) fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    have hmov : MovOK (v4 v) (rk 0) := by unfold MovOK; rw [v4_val, rk_val (by omega)]; omega
    refine M.runsTo_mono (M.law_mov hmov (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2))
      fun s₂ ⟨d₂, st, m₂⟩ => ⟨d₂, m₂.trans m₁, fun i => ?_⟩
    rw [st (v4 i)]
    by_cases hiv : i = v
    · subst hiv; rw [ite_pos rfl, v₁]; simp only [Env.set, ite_pos]
    · rw [ite_neg (fun e => hiv (v4_inj e)), k₁ _ (.inr (by rw [v4_val]; omega)), henv]
      simp only [Env.set]; rw [ite_neg hiv]
  | _, σ, _, .seq (a := a) (b := b) ha hb, hp, s, pc, hA, henv => by
    simp only [compS, wf, code_append, List.length_append] at hp hA ⊢
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA
    rw [← next_add]
    refine M.seq_run (execS_ok ha hp.1 hA1 henv) fun s₁ d₁ ⟨m₁, v₁⟩ => ?_
    exact M.runsTo_mono (execS_ok hb hp.2 (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2) v₁)
      fun s₂ ⟨d₂, m₂, v₂⟩ => ⟨d₂, m₂.trans m₁, v₂⟩
  | _, σ, _, .loopF (c := c) (b := b) hc0, hp, s, pc, hA, henv => by
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
    rw [code_loop] at hA
    rw [len_loop]
    obtain ⟨hA123, -, -⟩ := Core.At.split _ hA
    obtain ⟨hA12, -, -⟩ := Core.At.split _ hA123
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    refine M.seq_run (M.genE_ok σ c 0 (by omega) hA1 henv) fun s₁ d₁ ⟨m₁, v₁, k₁⟩ => ?_
    refine M.runsTo_mono (M.law_bz (rk_val (by omega)) hp3 (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2))
      fun s₂ ⟨d₂, st, m₂⟩ => ⟨?_, m₂.trans m₁, fun i => by rw [st, k₁ _ (.inr (by rw [v4_val]; omega)), henv]⟩
    rw [v₁, ite_pos hc0, next_add] at d₂
    rw [show (M.code (mgenE c 0)).length + M.lenBz + (M.code (M.compS b)).length + M.lenJmp =
      (M.code (mgenE c 0)).length + ((M.code (M.compS b)).length + M.lenBz + M.lenJmp) by omega]
    exact d₂
  | _, σ, σ₂, .loopT (c := c) (b := b) (σ₁ := σ₁) hc0 hb hl, hp, s, pc, hA, henv => by
    have hp' := hp
    obtain ⟨hp1, hp2, hp3, hp4⟩ := hp'
    have hA0 := hA
    rw [code_loop] at hA
    obtain ⟨hA123, hc4, ho4⟩ := Core.At.split _ hA
    obtain ⟨hA12, hc3, ho3⟩ := Core.At.split _ hA123
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA12
    simp only [List.length_append, M.len_bz] at hc3 ho3 hc4 ho4
    rw [← next_add] at hc3 ho3
    rw [← next_add, ← next_add] at hc4 ho4
    refine M.runsTo_trans (M.genE_ok σ c 0 (by omega) hA1 henv) fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    refine M.runsTo_trans (M.law_bz (rk_val (by omega)) hp3 (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    rw [v₁, ite_neg hc0, M.len_bz] at d₂
    have henv₂ : ∀ i, M.get s₂ (v4 i) = σ i := fun i => by
      rw [st₂, k₁ _ (.inr (by rw [v4_val]; omega)), henv]
    have m₂₀ := m₂.trans m₁
    refine M.runsTo_trans (execS_ok hb hp2 (Core.Done.at _ d₂ (M.codeAt_mem m₂₀ hc3) ho3) henv₂)
      fun s₃ ⟨d₃, m₃, v₃⟩ => ?_
    have m₃₀ := m₃.trans m₂₀
    refine M.runsTo_trans (M.law_jmp hp4 (Core.Done.at _ d₃ (M.codeAt_mem m₃₀ hc4) ho4))
      fun s₄ ⟨d₄, st₄, m₄⟩ => ?_
    rw [next_add, next_add, ← Nat.add_assoc, next_jmp] at d₄
    have m₄₀ := m₄.trans m₃₀
    refine M.runsTo_mono (execS_ok hl hp (Core.Done.at _ d₄ (M.codeAt_mem m₄₀ hA0.code) hA0.codeOK)
      fun i => by rw [st₄, v₃]) fun s₅ ⟨d₅, m₅, v₅⟩ => ⟨?_, m₅.trans m₄₀, v₅⟩
    exact Core.Done.trans _ d₁ (Core.Done.trans _ d₂ (Core.Done.trans _ d₃ (Core.Done.trans _ d₄ d₅)))

/-- **`Stmt` compiler correctness from the interface laws** (as a function: return to `ra`). -/
theorem compF_ok {p : Stmt} (hp : M.wf p) {σ' : Env} {s : M.S} (hex : Exec p (fun i => M.get s (v4 i)) σ')
    {pc : BitVec 64} (hA : M.At s pc (M.code (M.compF p))) (hra : M.retOK (M.ra s)) :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ (∀ i, M.get s' (v4 i) = σ' i) ∧ M.ok s' ∧ M.mem s' = M.mem s ∧
      M.keep s s' := by
  simp only [compF, code_append, code_one] at hA
  obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA
  refine M.runsTo_trans (M.execS_ok hex hp hA1 fun _ => rfl) fun s₁ ⟨d₁, m₁, v₁⟩ => ?_
  have e₁ : M.ra s₁ = M.ra s := M.keep_ra d₁.keep
  refine M.runsTo_mono (M.law_ret (by rw [e₁]; exact hra) (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2))
    fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
  have d := Core.Done.trans _ d₁ d₂
  rw [e₁] at d
  exact ⟨d.hpc, fun i => by rw [st₂, v₁], d.ok, m₂.trans m₁, d.keep⟩

end Machine
end Proven.Mach
