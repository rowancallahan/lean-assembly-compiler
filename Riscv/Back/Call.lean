/- The RISC-V instance of the call interface (`Compiler/Call.lean`): `rvC : MachineC` over `rvF`.
Link register `ra` (`x1`), frame register `gp` (`x3`).  `call d` is `jal ra, 4d`; `enterC n` is
`addi gp, gp, -8(n+1); sd ra, 0(gp)`; `leaveC n` is `ld ra, 0(gp); addi gp, gp, 8(n+1)`; `stA m` is
`sd t0, -8m(gp)`.  Every law is proved from the register-generic step lemmas (`Riscv/Steps/Gen*.lean`). -/
import Compiler.Call
import Riscv.Back.Frame
import Riscv.Steps.GenUse
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

/-- the 12-bit immediate `-k` -/
def immN (k : Nat) : BitVec 12 := -(BitVec.ofNat 12 k)

def encC : COp → List (BitVec 32)
  | .call d => [wJ 1 (BitVec.ofInt 20 (2 * d))]
  | .enterC n => [encI 0 (immN (8 * (n + 1))).toNat 3 3, G.encS 3 0 1 3]
  | .leaveC n => [G.encL 3 0 1 3, encI 0 (BitVec.ofNat 12 (8 * (n + 1))).toNat 3 3]
  | .stA m _ => [G.encS 3 (immN (8 * m)) 5 3]

theorem sx_negF : ∀ k : Fin 18, (immN (8 * k.val)).signExtend 64 = -(BitVec.ofNat 64 (8 * k.val)) := by decide
theorem sx_posF : ∀ k : Fin 18, (BitVec.ofNat 12 (8 * k.val)).signExtend 64 = BitVec.ofNat 64 (8 * k.val) := by
  decide
theorem sx_neg {k : Nat} (h : k < 18) : (immN (8 * k)).signExtend 64 = -(BitVec.ofNat 64 (8 * k)) := sx_negF ⟨k, h⟩
theorem sx_pos {k : Nat} (h : k < 18) : (BitVec.ofNat 12 (8 * k)).signExtend 64 = BitVec.ofNat 64 (8 * k) :=
  sx_posF ⟨k, h⟩

theorem subA {x : BitVec 64} {k : Nat} (h : k ≤ x.toNat) :
    x + -(BitVec.ofNat 64 k) = BitVec.ofNat 64 (x.toNat - k) ∧ (BitVec.ofNat 64 (x.toNat - k)).toNat = x.toNat - k := by
  have := x.isLt
  have e : (BitVec.ofNat 64 (x.toNat - k)).toNat = x.toNat - k := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, e⟩
  apply BitVec.eq_of_toNat_eq
  rw [e, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]
  omega

theorem addA (x : BitVec 64) (k : Nat) : x + BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat + k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega

/-- the byte offset of `jal` with the 20-bit field `2 d` is `4 d` -/
theorem joff_call {d : Int} (h1 : -2 ^ 18 ≤ d) (h2 : d < 2 ^ 18) :
    joff (BitVec.ofInt 20 (2 * d)) = BitVec.ofInt 64 (4 * d) := by
  unfold joff
  apply BitVec.eq_of_toInt_eq
  simp only [sign_extend, Sail.BitVec.signExtend]
  rw [BitVec.toInt_signExtend_of_le (by omega)]
  have e : (BitVec.ofInt 20 (2 * d) +++ (0#1 : BitVec 1)) = BitVec.ofInt 21 (4 * d) := by
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofInt 20 (2 * d) ++ (0#1 : BitVec 1)).toNat = _
    rw [BitVec.toNat_append, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
    simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.zero_mod, Nat.or_zero]
    omega
  rw [e, BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  have b1 : (4 * d).bmod (2 ^ (20 + 1)) = 4 * d := by rw [Int.bmod_def]; split <;> omega
  have b2 : (4 * d).bmod (2 ^ 64) = 4 * d := by rw [Int.bmod_def]; split <;> omega
  rw [b1, b2]

/-- everything but the abstract registers, `gp` and `ra` -/
def KC (s s' : St) : Prop := ∀ j : Fin 32, (∀ r : Reg, j ≠ phys r) → j ≠ 3 → j ≠ 1 → getX s' j = getX s j

theorem law_call {d : Int} {s : St} {pc : BitVec 64} (hd : -2 ^ 18 ≤ d ∧ d < 2 ^ 18)
    (hA : core.At s pc (encC (.call d))) :
    core.runsTo s fun s' => core.ok s' ∧ KC s s' ∧ core.pcIs s' (pc + BitVec.ofInt 64 (4 * d)) ∧
      getX s' 1 = next pc 1 ∧ getX s' 3 = getX s 3 ∧ core.Same s s' ∧ core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨s', hn⟩ := G.step_jal h hpc hok 1 (BitVec.ofInt 20 (2 * d)) hi
  rw [joff_call hd.1 hd.2] at hn
  refine run1 hn ⟨hn.cfg, fun j _ _ h1 => by rw [hn.x j]; exact ite_neg (fun e => h1 e.1), hn.pc,
    by rw [hn.x 1]; exact ite_pos ⟨rfl, by decide⟩, by rw [hn.x 3]; exact ite_neg (by decide), fun q => ?_, memOf hn⟩
  show getX s' (phys q) = getX s (phys q)
  rw [hn.x]; exact ite_neg (fun e => phys_ne1 q e.1.symm)

theorem law_stA {m : Nat} {v : Reg} {s : St} {pc : BitVec 64} (hv : v.val = 0) (h1 : 1 ≤ m) (hm : m ≤ NS)
    (hA : core.At s pc (encC (.stA m v))) (hlo : 8 * m ≤ (getX s 3).toNat)
    (hr : core.inRAM ((getX s 3).toNat - 8 * m) 8) (hal : (getX s 3).toNat % 8 = 0) :
    core.runsTo s fun s' => core.Done s s' (next pc (encC (.stA m v)).length) ∧ core.Same s s' ∧
      core.mem s' = (core.mem s).wr ((getX s 3).toNat - 8 * m) (le8 (core.get s v)) := by
  have ev : phys v = 5 := by rw [phys_T v (by omega), hv]; rfl
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨e1, e2⟩ := subA hlo
  have hm' : m < 18 := by simp only [NS] at hm; omega
  obtain ⟨s', hn⟩ := G.step_sd h hpc hok 5 3 (immN (8 * m)) hi (A := BitVec.ofNat 64 ((getX s 3).toNat - 8 * m))
    (by rw [sx_neg hm']; exact e1) (by rw [e2]; exact hr) (by rw [e2]; omega)
  refine run1 hn ⟨ofNext hn (.inl rfl), sameOf hn, ?_⟩
  funext x
  show s'.mem[x]? = _
  rw [hn.mem, e2, storeBytes_wr]
  show _ = Mem.wr (core.mem s) _ (le8 (getX s (phys v))) x
  rw [ev]; rfl

theorem law_enterC {n : Nat} {s : St} {pc : BitVec 64} (hn : n ≤ NS) (hA : core.At s pc (encC (.enterC n)))
    (hlo : 8 * (n + 1) ≤ (getX s 3).toNat) (hr : core.inRAM ((getX s 3).toNat - 8 * (n + 1)) 8)
    (hal : (getX s 3).toNat % 8 = 0) :
    core.runsTo s fun s' => core.ok s' ∧ KC s s' ∧ core.pcIs s' (next pc (encC (.enterC n)).length) ∧
      getX s' 3 = BitVec.ofNat 64 ((getX s 3).toNat - 8 * (n + 1)) ∧ core.Same s s' ∧
      core.mem s' = (core.mem s).wr ((getX s 3).toNat - 8 * (n + 1)) (le8 (getX s 1)) := by
  obtain ⟨h, hpc, hok, hi⟩ := first hA
  obtain ⟨e1, e2⟩ := subA hlo
  have hn' : n + 1 < 18 := by simp only [NS] at hn; omega
  obtain ⟨s₁, hn₁⟩ := G.step_addi h hpc hok 3 3 (immN (8 * (n + 1))) hi
  rw [sx_neg hn', e1] at hn₁
  have sp := Core.At.split _ (l₁ := [encI 0 (immN (8 * (n + 1))).toNat 3 3]) (l₂ := [G.encS 3 0 1 3]) hA
  have hA₁ : core.At s₁ (next pc 1) [G.encS 3 0 1 3] :=
    ⟨hn₁.cfg, hn₁.pc, core.codeAt_mem (memOf hn₁) sp.2.1, sp.2.2⟩
  obtain ⟨h', hpc', hok', hi'⟩ := first1 hA₁
  have g3 : getX s₁ 3 = BitVec.ofNat 64 ((getX s 3).toNat - 8 * (n + 1)) := by
    rw [hn₁.x]; exact ite_pos ⟨rfl, by decide⟩
  have g1 : getX s₁ 1 = getX s 1 := by rw [hn₁.x]; exact ite_neg (by decide)
  obtain ⟨s₂, hn₂⟩ := G.step_sd h' hpc' hok' 1 3 0 hi' (A := BitVec.ofNat 64 ((getX s 3).toNat - 8 * (n + 1)))
    (by rw [g3]; exact BitVec.add_zero _) (by rw [e2]; exact hr) (by rw [e2]; omega)
  refine runsTo_next hn₁ (run1 hn₂ ⟨hn₂.cfg, fun j hj h3 h1 => ?_, ?_, ?_, fun q => ?_, ?_⟩)
  · rw [hn₂.x j, ite_neg (fun e => e.2 e.1), hn₁.x j]; exact ite_neg (fun e => h3 e.1)
  · have := hn₂.pc; rwa [n4 (next pc 1), next_add] at this
  · rw [hn₂.x 3, ite_neg (fun e => e.2 e.1)]; exact g3
  · show getX s₂ (phys q) = getX s (phys q)
    rw [hn₂.x, ite_neg (fun e => e.2 e.1), hn₁.x]; exact ite_neg (fun e => phys_ne3 q e.1.symm)
  · funext x
    show s₂.mem[x]? = _
    rw [hn₂.mem, e2, storeBytes_wr, hn₁.mem, g1]; rfl

theorem law_leaveC {n : Nat} {s : St} {pc : BitVec 64} {w : BitVec 64} (hn : n ≤ NS)
    (hA : core.At s pc (encC (.leaveC n))) (hr : core.inRAM (getX s 3).toNat (8 * (n + 1)))
    (hal : (getX s 3).toNat % 8 = 0) (hb : bytes (core.mem s) (getX s 3).toNat 8 = (le8 w).map some) :
    core.runsTo s fun s' => core.ok s' ∧ KC s s' ∧ core.pcIs s' (next pc (encC (.leaveC n)).length) ∧
      getX s' 1 = w ∧ getX s' 3 = BitVec.ofNat 64 ((getX s 3).toNat + 8 * (n + 1)) ∧ core.Same s s' ∧
      core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first hA
  have hn' : n + 1 < 18 := by simp only [NS] at hn; omega
  obtain ⟨hr1, hr2⟩ := hr
  have hr2' : (getX s 3).toNat + 8 * (n + 1) ≤ 0x100000000 := hr2
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bytesAt_le8 (bytes_le8 hb)
  obtain ⟨s₁, hn₁⟩ := G.step_ld h hpc hok 1 3 0 hi (A := getX s 3) (BitVec.add_zero _) ⟨hr1, by omega⟩ hal
    h0 h1 h2 h3 h4 h5 h6 h7
  rw [Proven.le8_cat] at hn₁
  have sp := Core.At.split _ (l₁ := [G.encL 3 0 1 3]) (l₂ := [encI 0 (BitVec.ofNat 12 (8 * (n + 1))).toNat 3 3]) hA
  have hA₁ : core.At s₁ (next pc 1) [encI 0 (BitVec.ofNat 12 (8 * (n + 1))).toNat 3 3] :=
    ⟨hn₁.cfg, hn₁.pc, core.codeAt_mem (memOf hn₁) sp.2.1, sp.2.2⟩
  obtain ⟨h', hpc', hok', hi'⟩ := first1 hA₁
  have g3 : getX s₁ 3 = getX s 3 := by rw [hn₁.x]; exact ite_neg (by decide)
  obtain ⟨s₂, hn₂⟩ := G.step_addi h' hpc' hok' 3 3 (BitVec.ofNat 12 (8 * (n + 1))) hi'
  rw [sx_pos hn', g3, addA] at hn₂
  refine runsTo_next hn₁ (run1 hn₂ ⟨hn₂.cfg, fun j hj h3 h1 => ?_, ?_, ?_, ?_, fun q => ?_, ?_⟩)
  · rw [hn₂.x j, ite_neg (fun e => h3 e.1), hn₁.x j]; exact ite_neg (fun e => h1 e.1)
  · have := hn₂.pc; rwa [n4 (next pc 1), next_add] at this
  · rw [hn₂.x 1, ite_neg (by decide), hn₁.x 1]; exact ite_pos ⟨rfl, by decide⟩
  · rw [hn₂.x 3]; exact ite_pos ⟨rfl, by decide⟩
  · show getX s₂ (phys q) = getX s (phys q)
    rw [hn₂.x, ite_neg (fun e => phys_ne3 q e.1.symm), hn₁.x]; exact ite_neg (fun e => phys_ne1 q e.1.symm)
  · exact (memOf hn₂).trans (memOf hn₁)

/-- **The Sail RV64 model is a `MachineC`.** -/
def rvC : MachineC where
  toMachineF := rvF
  encC := encC
  keepC := KC
  callOK d := -2 ^ 18 ≤ d ∧ d < 2 ^ 18
  lenCall := 1
  len_call _ := rfl
  keepC_of_keepF h j hj h3 _ := h j hj h3
  keepC_trans h₁ h₂ j hj h3 h1 := (h₂ j hj h3 h1).trans (h₁ j hj h3 h1)
  keepF_of_keepC h e j hj h3 := by
    by_cases h1 : j = 1
    · subst h1; exact e
    · exact h j hj h3 h1
  retOK_al v h := by show v.toNat % 2 = 0; omega
  law_call := law_call
  law_enterC := law_enterC
  law_leaveC := law_leaveC
  law_stA := law_stA

end Proven.Mach.Riscv
