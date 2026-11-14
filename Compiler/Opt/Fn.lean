/- A compiled function: IR code over virtual registers → register assignment `f` (checked injective on the
registers used) → lowering (checked `wf`) → words, then `ret`.  `fn_ok`: an IR execution from the machine's
registers (read through `f`) is simulated up to the return. -/
import Compiler.Opt.Lower
import Compiler.Opt.Alloc

namespace Proven.Mach
open IR

namespace Wide
variable (M : Wide) (sc : Reg) (f : Nat → Reg)

def fn (vars : List Nat) (c : Code Nat) : Option (List (BitVec 32)) :=
  if (injOn f (vars ++ c.regs) && M.wf sc (c.map f)) = true then some (M.W sc (c.map f) ++ M.wenc .ret) else none

variable {M sc f}

theorem fn_ok {ram : Nat → Prop} {fp : Nat} (hram : ∀ a, ram a → M.inRAM a 1) {vars : List Nat} {c : Code Nat}
    {ws : List (BitVec 32)} (hc : M.fn sc f vars c = some ws) {s : M.S} {pc : BitVec 64} (hok : M.ok s)
    (hpc : M.pcIs s pc) (hf : M.Frag ram fp s pc ws) (hra : M.retOK (M.ra s)) {σ' : St Nat}
    (hex : Exec ram fp c ⟨fun x => M.get s (f x), M.mem s⟩ σ') :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ (∀ x, x ∈ vars → f x ≠ sc → M.get s' (f x) = σ'.reg x) ∧
      M.ok s' ∧ M.mem s' = σ'.mem ∧ M.keep s s' := by
  unfold fn at hc
  by_cases hchk : (injOn f (vars ++ c.regs) && M.wf sc (c.map f)) = true
  · rw [ite_pos hchk] at hc
    cases hc
    obtain ⟨hinj, hwf⟩ := and2 hchk
    obtain ⟨τ', hx', hr'⟩ := map_ok (f := f) (U := fun x => x ∈ vars ++ c.regs) ram fp
      (fun x y hx hy => injOn_ok hinj hx hy) hex (fun x hx => List.mem_append.2 (.inr hx))
      (τ := ⟨M.get s, M.mem s⟩) ⟨rfl, fun _ _ => rfl⟩
    refine M.runsTo_trans (low_ok hram hx' hwf hok hpc hf.left ⟨fun _ _ => rfl, rfl⟩) fun s₁ ⟨d₁, m₁, r₁⟩ => ?_
    have e₁ : M.ra s₁ = M.ra s := M.keep_ra d₁.keep
    refine M.runsTo_mono (M.w_ret (by rw [e₁]; exact hra) ((hf.right.mf m₁).at d₁.ok d₁.hpc))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    have d := Core.Done.trans _ d₁ d₂
    rw [e₁] at d
    refine ⟨d.hpc, fun x hx hs => ?_, d.ok, ?_, d.keep⟩
    · rw [st₂, r₁.1 _ hs]; exact hr'.2 x (List.mem_append.2 (.inl hx))
    · rw [m₂, r₁.2, hr'.1]
  · rw [ite_neg hchk] at hc; exact nomatch hc

end Wide
end Proven.Mach
