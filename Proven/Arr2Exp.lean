/- Correctness of `genB` (expressions over register variables `a0..a7` and stack slots, temporaries
`t0..t6`) on the Sail model.  The proof of `gen8_ok` (`Proven/ArrExp.lean`) with one new case: a slot
variable is one `ld t_k, 8(j+1)(gp)`. -/
import Proven.Arr2Words
import Proven.ArrExp

set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Proven

/-- the frame: base `fp` 8-aligned, cells `0 .. N` (8 bytes each) in RAM, at most `NS` slots -/
structure FrOK (N fp : Nat) : Prop where
  al : fp % 8 = 0
  lo : 0x80000000 ≤ fp
  hi : fp + 8 * (N + 1) ≤ 0x100000000
  ns : N ≤ NS

/-- `s` holds `env`: variable `i < 8` in `a_i`, `gp = fp`, slot variable `8 + j` in frame cell `j + 1` -/
structure EnvRel (N fp : Nat) (env : BEnv) (s : St) : Prop where
  reg : ∀ i : Fin 8, getX s (A8 i) = env i.val
  gp : getX s 3 = BitVec.ofNat 64 fp
  slot : ∀ j < N, bytesAt s (fp + 8 * (j + 1)) 8 = (le8 (env (8 + j))).map some

theorem bytesAt_mem {s s' : St} (hm : s'.mem = s.mem) (a n : Nat) : bytesAt s' a n = bytesAt s a n := by
  simp only [bytesAt, hm]

theorem three_ne_T : ∀ i < 7, (3 : Fin 32) ≠ T i := by decide

theorem EnvRel.ran7 {N fp env} {s s' : St} (r : EnvRel N fp env s) {pc n k} (R : Ran7 s s' pc n k) :
    EnvRel N fp env s' :=
  ⟨fun i => by rw [R.keepA, r.reg], by rw [R.keep 3 (fun i _ hi => three_ne_T i hi), r.gp],
    fun j hj => by rw [bytesAt_mem R.mem, r.slot j hj]⟩

/-- the address of frame cell `j + 1` -/
theorem slot_addr {N fp : Nat} (hf : FrOK N fp) {j : Nat} (hj : j < N) {g : BitVec 64}
    (hg : g = BitVec.ofNat 64 fp) :
    g + BitVec.ofNat 64 (8 * (j + 1)) = BitVec.ofNat 64 (fp + 8 * (j + 1)) ∧
    (BitVec.ofNat 64 (fp + 8 * (j + 1))).toNat = fp + 8 * (j + 1) ∧
    (0x80000000 ≤ (BitVec.ofNat 64 (fp + 8 * (j + 1))).toNat ∧
      (BitVec.ofNat 64 (fp + 8 * (j + 1))).toNat + 8 ≤ 0x100000000) ∧
    (BitVec.ofNat 64 (fp + 8 * (j + 1))).toNat % 8 = 0 := by
  have := hf.hi; have := hf.lo; have := hf.al
  have e : (BitVec.ofNat 64 (fp + 8 * (j + 1))).toNat = fp + 8 * (j + 1) := by
    simp only [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  refine ⟨by rw [hg, BitVec.ofNat_add], e, by rw [e]; omega, by rw [e]; omega⟩

theorem genB_ok {N fp : Nat} (hf : FrOK N fp) (env : BEnv) : ∀ (e : BExp) (k : Nat) (hk : k + e.depth < 7)
    (hv : e.vlt (8 + N)) {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (genB e k)) (hok : codeOK pc (genB e k).length) (henv : EnvRel N fp env s),
    ∃ s', Reach s s' ∧ Ran7 s s' pc (genB e k).length k ∧ getX s' (T k) = e.denote env
  | .var i, k, hk, hv, s, h, pc, hpc, hc, hok, henv => by
    simp only [genB, BExp.denote, BExp.vlt, BExp.depth] at *
    by_cases hi8 : i < 8
    · simp only [hi8, dite_true] at hc hok ⊢
      obtain ⟨s', r, R, v⟩ := run_one7 (w := iVar8 ⟨i, hi8⟩ k) (by omega)
        (step_var8 h hpc (codeOK_pcOK hok (by simp)) ⟨i, hi8⟩ k (by omega) (codeAt_one hc))
      exact ⟨s', r, R, by rw [v, henv.reg]⟩
    · simp only [hi8, dite_false] at hc hok ⊢
      have hj : i - 8 < N := by omega
      obtain ⟨e1, e2, e3, e4⟩ := slot_addr hf hj henv.gp
      obtain ⟨s', r, R, v⟩ := run_one7 (w := iLdS (i - 8) k) (by omega)
        (step_ldS h hpc (codeOK_pcOK hok (by simp)) (i - 8) k (by have := hf.ns; omega) (by omega)
          (codeAt_one hc) e3 e4 e1 (by rw [e2]; exact henv.slot _ hj))
      exact ⟨s', r, R, by rw [v, show 8 + (i - 8) = i by omega]⟩
  | .const c, k, hk, hv, s, h, pc, hpc, hc, hok, henv => by
    simp only [genB, BExp.denote] at *
    obtain ⟨s', r, R, v⟩ := const_ok7 k (by simp [BExp.depth] at hk; omega) c.toNat h hpc hc hok
    exact ⟨s', r, R, by rw [v, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  | .bin op a b, k, hk, hv, s, h, pc, hpc, hc, hok, henv => by
    simp only [genB, BExp.depth, BExp.denote, BExp.vlt] at *
    rw [codeAt_append, codeAt_append] at hc
    rw [List.length_append, List.length_append] at hok ⊢
    obtain ⟨ok1, ok23⟩ := codeOK_append (by rwa [Nat.add_assoc] at hok)
    obtain ⟨ok2, ok3⟩ := codeOK_append ok23
    obtain ⟨s₁, r₁, R₁, v₁⟩ := genB_ok hf env a k (by omega) hv.1 h hpc hc.1.1 ok1 henv
    obtain ⟨s₂, r₂, R₂, v₂⟩ := genB_ok hf env b (k + 1) (by omega) hv.2 R₁.cfg R₁.pc
      (codeAt_mem R₁.mem hc.1.2) ok2 (henv.ran7 R₁)
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
  | .ite c a b, k, hk, hv, s, h, pc, hpc, hc, hok, henv => by
    simp only [genB, BExp.depth, BExp.denote, BExp.vlt] at *
    rw [codeAt_append, codeAt_append, codeAt_append] at hc
    rw [List.length_append, List.length_append, List.length_append] at hok ⊢
    obtain ⟨ok123, ok4⟩ := codeOK_append hok
    obtain ⟨ok12, ok3⟩ := codeOK_append ok123
    obtain ⟨ok1, ok2⟩ := codeOK_append ok12
    obtain ⟨s₁, r₁, R₁, v₁⟩ := genB_ok hf env c k (by omega) hv.1 h hpc hc.1.1.1 ok1 henv
    obtain ⟨s₂, r₂, R₂, v₂⟩ := genB_ok hf env a (k + 1) (by omega) hv.2.1 R₁.cfg R₁.pc
      (codeAt_mem R₁.mem hc.1.1.2) ok2 (henv.ran7 R₁)
    have R₁₂ := R₁.trans R₂ (Nat.le_refl _) (Nat.le_succ _)
    have hc3 := codeAt_mem R₁₂.mem hc.1.2
    rw [List.length_append] at hc3
    obtain ⟨s₃, r₃, R₃, v₃⟩ := genB_ok hf env b (k + 2) (by omega) hv.2.2 R₁₂.cfg R₁₂.pc hc3 ok3
      (henv.ran7 R₁₂)
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
