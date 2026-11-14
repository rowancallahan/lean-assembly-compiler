/- Register-generic step lemmas for loads and stores with arbitrary base register and 12-bit offset:
`lb lbu lh lhu lw lwu ld`, `sb sh sw sd` (machinery: `Riscv/Steps/GenTac.lean`, the memory side as in
`Riscv/Steps/MemStep.lean` / `Arr2Step.lean`).  The data address is a variable `A` with hypotheses
`hA : getX s rs1 + imm.signExtend 64 = A`, `ha : 0x80000000 ≤ A.toNat ∧ A.toNat + n ≤ 0x100000000` and,
for `n > 1`, `hal : A.toNat % n = 0`. -/
import Riscv.Steps.GenBranch
import Riscv.Steps.MemStep
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven
namespace G

theorem imm_cat (imm : BitVec 12) : (imm.extractLsb' 5 7 ++ imm.extractLsb' 0 5 : BitVec 12) = imm := by bits

/-! ## Alignment and page checks of 2- and 4-byte accesses -/

@[simp] theorem aligned_v4' {x : BitVec 64} (h : x.toNat % 4 = 0) : is_aligned_vaddr (.Virtaddr x) 4 = true := by
  simp [is_aligned_vaddr, toNatInt_eq, Int.tmod_eq_emod]; omega
@[simp] theorem aligned_p4' {x : BitVec 64} (h : x.toNat % 4 = 0) : is_aligned_paddr (.Physaddr x) 4 = true := by
  simp [is_aligned_paddr, toNatInt_eq, Int.tmod_eq_emod]; omega
@[simp] theorem tmod4 {x : BitVec 64} (h : x.toNat % 4 = 0) : Int.tmod (x.toNat : Int) 4 = 0 := by
  simp [Int.tmod_eq_emod]; omega
@[simp] theorem aligned_v2 {x : BitVec 64} (h : x.toNat % 2 = 0) : is_aligned_vaddr (.Virtaddr x) 2 = true := by
  simp [is_aligned_vaddr, toNatInt_eq, Int.tmod_eq_emod]; omega
@[simp] theorem aligned_p2 {x : BitVec 64} (h : x.toNat % 2 = 0) : is_aligned_paddr (.Physaddr x) 2 = true := by
  simp [is_aligned_paddr, toNatInt_eq, Int.tmod_eq_emod]; omega
@[simp] theorem tmod2 {x : BitVec 64} (h : x.toNat % 2 = 0) : Int.tmod (x.toNat : Int) 2 = 0 := by
  simp [Int.tmod_eq_emod]; omega

theorem same_page_n {x M : BitVec 64} {k : Nat} (hk : k ≤ 3) (h : x.toNat % 2 ^ k = 0)
    (hM : M = 0xFFFFFFFFFFFFF000#64) : (x &&& M) = (x + BitVec.ofNat 64 (2 ^ k) - 1#64 &&& M) := by
  have h7 : x &&& BitVec.ofNat 64 (2 ^ k - 1) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hk; omega), Nat.and_two_pow_sub_one_eq_mod]
    simpa using h
  have : x + BitVec.ofNat 64 (2 ^ k) - 1#64 = x ||| BitVec.ofNat 64 (2 ^ k - 1) := by
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ h7]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hk
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]; omega
  subst hM; rw [this, BitVec.and_or_distrib_right]
  have : BitVec.ofNat 64 (2 ^ k - 1) &&& 0xFFFFFFFFFFFFF000#64 = 0 := by
    have : ∀ k, k ≤ 3 → BitVec.ofNat 64 (2 ^ k - 1) &&& 0xFFFFFFFFFFFFF000#64 = 0 := by decide
    exact this k hk
  simp [this]

@[simp] theorem page4 (s : St) {x : BitVec 64} (h : x.toNat % 4 = 0) :
    split_on_page_boundary x 4 s = .ok ((4 : Int), (0 : Int)) s := by
  simp [split_on_page_boundary, Sail.BitVec.length, zeros, BitVec.addInt, BitVec.subInt]
  split
  · rfl
  · next hn => exact absurd (same_page_n (k := 2) (by decide) h (by decide)) hn
@[simp] theorem page2 (s : St) {x : BitVec 64} (h : x.toNat % 2 = 0) :
    split_on_page_boundary x 2 s = .ok ((2 : Int), (0 : Int)) s := by
  simp [split_on_page_boundary, Sail.BitVec.length, zeros, BitVec.addInt, BitVec.subInt]
  split
  · rfl
  · next hn => exact absurd (same_page_n (k := 1) (by decide) h (by decide)) hn

theorem pageG (s : St) {x : BitVec 64} {n : Nat} (k : Nat) (hn : n = 2 ^ k) (hk : k ≤ 3) (h : x.toNat % n = 0) :
    split_on_page_boundary (bits_of_virtaddr (pm_transform_PA (.Virtaddr x) 0)) n s = .ok ((n : Int), (0 : Int)) s := by
  subst hn
  simp only [pm_transform_PA_0, bits_of_virtaddr_mk]
  simp [split_on_page_boundary, Sail.BitVec.length, zeros, BitVec.addInt, BitVec.subInt]
  split
  · rfl
  · next hn => exact absurd (same_page_n hk h (by decide)) hn
theorem page8G (s : St) {x : BitVec 64} (h : x.toNat % 8 = 0) :
    split_on_page_boundary (bits_of_virtaddr (pm_transform_PA (.Virtaddr x) 0)) 8 s = .ok ((8 : Int), (0 : Int)) s :=
  pageG s 3 rfl (by decide) h
theorem page4G (s : St) {x : BitVec 64} (h : x.toNat % 4 = 0) :
    split_on_page_boundary (bits_of_virtaddr (pm_transform_PA (.Virtaddr x) 0)) 4 s = .ok ((4 : Int), (0 : Int)) s :=
  pageG s 2 rfl (by decide) h
theorem page2G (s : St) {x : BitVec 64} (h : x.toNat % 2 = 0) :
    split_on_page_boundary (bits_of_virtaddr (pm_transform_PA (.Virtaddr x) 0)) 2 s = .ok ((2 : Int), (0 : Int)) s :=
  pageG s 1 rfl (by decide) h

@[simp] theorem extend_false_n {k : Nat} (x : BitVec k) : extend_value false x = x.signExtend 64 := by
  simp [extend_value, sign_extend, Sail.BitVec.signExtend]
@[simp] theorem upd_full16 (x : BitVec 16) : Sail.BitVec.updateSubrange (0#16) 15 0 x = x := by
  ext i hi; simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
@[simp] theorem ext8_setWidth {n w : Nat} (x : BitVec n) (i : Nat) (h : i + 8 ≤ w) :
    (x.setWidth w).extractLsb' i 8 = x.extractLsb' i 8 := by
  ext j hj; simp; omega

/-! ## Encodings -/

/-- `l<f3> rd, imm(rs1)` (`f3`: 0 lb, 1 lh, 2 lw, 3 ld, 4 lbu, 5 lhu, 6 lwu) -/
def encL (f3 : Nat) (imm : BitVec 12) (rd rs1 : Fin 32) : BitVec 32 :=
  BitVec.ofNat 32 (imm.toNat <<< 20 ||| rs1.val <<< 15 ||| f3 <<< 12 ||| rd.val <<< 7 ||| 0x03)
/-- `s<f3> rs2, imm(rs1)` (`f3`: 0 sb, 1 sh, 2 sw, 3 sd) -/
def encS (f3 : BitVec 3) (imm : BitVec 12) (rs2 rs1 : Fin 32) : BitVec 32 :=
  imm.extractLsb' 5 7 ++ (BitVec.ofFin rs2 : BitVec 5) ++ (BitVec.ofFin rs1 : BitVec 5) ++ f3 ++ imm.extractLsb' 0 5 ++
    (0x23#7 : BitVec 7)

theorem encL_eq (f3 : Nat) (imm : BitVec 12) (rd rs1 : Fin 32) :
    encL f3 imm rd rs1 = BitVec.ofNat 32 (f3 <<< 12 ||| 0x03) ||| fI rd rs1 imm := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [encL, fI, BitVec.getLsbD_ofNat, BitVec.getLsbD_or, Nat.testBit_or, Nat.testBit_shiftLeft]
  enc_bits
theorem encS_eq (f3 : BitVec 3) (imm : BitVec 12) (rs2 rs1 : Fin 32) :
    encS f3 imm rs2 rs1 = ((0#17 : BitVec 17) +++ f3 +++ (0#5 : BitVec 5) +++ (0x23#7 : BitVec 7)) ||| fS rs1 rs2 imm := by
  simp only [encS, fS]; bits

set_option hygiene false in
/-- `gstep_core` for loads/stores: `range_subset` / `split_on_page_boundary` frozen, the data range from `ha` -/
macro "gmem_core" : tactic => `(tactic| (
  · intro s h hpc hi hQ
    simp only [Proven.getX_eq] at hQ
    have hok' := hok; obtain ⟨_, _, _⟩ := hok'
    have hf := Proven.fetch_cfg h hpc hok hi (Proven.G.rvc_or (by decide) (by first | with_reducible exact Proven.G.fR_low2 .. | with_reducible exact Proven.G.fI_low2 .. | with_reducible exact Proven.G.fSh_low2 .. | with_reducible exact Proven.G.fU_low2 .. | with_reducible exact Proven.G.fS_low2 .. | with_reducible exact Proven.G.fB_low2 .. | with_reducible exact Proven.G.fJ_low2 ..))
    rw [Proven.bytes_eq] at hf
    have hd := Proven.dispatch_cfg h
    have hram := Proven.in_ram (by decide) ha.1 ha.2
    have hxp := h.xpresent
    cfg_facts h
    obtain ⟨_, _, _, _, _, _⟩ := h.pma
    have := h.present .pmpaddr_n (by simp)
    sail_eval frozen[LeanRV64D.Functions.fetch, LeanRV64D.Functions.dispatchInterrupt, LeanRV64D.Functions.pmpCheck,
        LeanRV64D.Functions.rX_bits, LeanRV64D.Functions.wX_bits, LeanRV64D.Functions.range_subset,
        LeanRV64D.Functions.split_on_page_boundary]
      [*, Proven.pmp_none, Std.ExtDHashMap.contains_insert, BitVec.add_sub_cancel, LeanRV64D.Functions.matching_pma_region,
      LeanRV64D.Functions.matching_pma_region_bits_range, LeanRV64D.Functions.override_PMA, LeanRV64D.Functions.hartSupports, LeanRV64D.Functions.zopz0zIzJ_u,
      LeanRV64D.Functions.zopz0zI_u, LeanRV64D.Functions.zopz0zKzJ_u, LeanRV64D.Functions.zopz0zK_u, LeanRV64D.Functions.zopz0zI_s, LeanRV64D.Functions.zopz0zKzJ_s,
      BitVec.toNat_sub, BitVec.toNat_add, Proven.G.F_imm, Proven.G.fB_dec, Proven.G.fJ_dec,
      Proven.G.add_boff_even', Proven.G.add_joff_even', Proven.add_boff_even, Proven.add_joff_even,
      Proven.G.fR_rd, Proven.G.fR_rs1, Proven.G.fR_rs2, Proven.G.fR_zero, Proven.G.fR_rdne, Proven.G.fR_known, Proven.G.fR_mismatch, Proven.G.fR_ne, Proven.G.fI_rd, Proven.G.fI_rs1, Proven.G.fI_imm, Proven.G.fI_zero, Proven.G.fI_rdne, Proven.G.fI_known, Proven.G.fI_mismatch, Proven.G.fI_ne, Proven.G.fSh_rd, Proven.G.fSh_rs1, Proven.G.fSh_sh, Proven.G.fSh_zero, Proven.G.fSh_rdne, Proven.G.fSh_known, Proven.G.fSh_mismatch, Proven.G.fSh_ne, Proven.G.fU_rd, Proven.G.fU_imm, Proven.G.fU_zero, Proven.G.fU_rdne, Proven.G.fU_known, Proven.G.fU_mismatch, Proven.G.fU_ne, Proven.G.fS_rs1, Proven.G.fS_rs2, Proven.G.fS_hi, Proven.G.fS_lo, Proven.G.fS_zero, Proven.G.fS_known, Proven.G.fS_mismatch, Proven.G.fS_ne, Proven.G.fB_rs1, Proven.G.fB_rs2, Proven.G.fB_zero, Proven.G.fB_known, Proven.G.fB_mismatch, Proven.G.fB_ne, Proven.G.fJ_rd, Proven.G.fJ_zero, Proven.G.fJ_rdne, Proven.G.fJ_known, Proven.G.fJ_mismatch, Proven.G.fJ_ne,
      Proven.sail_ext, Proven.setw_ext, Proven.G.imm_cat, LeanRV64D.Functions.regval_from_reg,
      Proven.aligned_v8, Proven.aligned_p8, Proven.tmod8, Proven.page8, Proven.page1, Proven.G.aligned_v4', Proven.G.aligned_p4',
      Proven.G.tmod4, Proven.G.page4, Proven.G.aligned_v2, Proven.G.aligned_p2, Proven.G.tmod2, Proven.G.page2, Proven.G.page8G, Proven.G.page4G, Proven.G.page2G, Proven.xval_insert_npc, Proven.G.sign_extend_eq,
      Proven.rX_bits_ok, Proven.wX_bits_ok, Proven.G.reg_matches, Proven.G.reg_back, Proven.xpresent_insert]
    all_goals simp [Proven.stepF, Proven.update0_even, Proven.ze32, Proven.boff, Proven.joff, Proven.G.update0_evenB, Proven.storeBytes_le8, Proven.extend_false64, Proven.upd_full64, *]
  all_goals simp))

open Lean Meta Elab Tactic in
/-- `step_word` for words with symbolic fields (same interface) -/
elab "gmem" : tactic => withMainContext do
  let ty := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  let .app _ (.lam _ _ body _) := ty | throwError "gmem: expected ∃ s', Next s s' .."
  let args := body.getAppArgs
  unless body.isAppOfArity ``Next 6 do throwError "gmem: expected ∃ s', Next s s' .."
  let s := args[0]!
  let fn (e : Expr) : TacticM Term := do
    if e.hasLooseBVars then throwError "gmem: {e} mentions s'"
    Term.exprToSyntax (← mkLambdaFVars #[s] e)
  let (npc, v, mem) := (← fn args[2]!, ← fn args[4]!, ← fn args[5]!)
  let mut side : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || [`h, `hpc, `hi].contains d.userName then continue
    let t ← instantiateMVars d.type
    if (← isProp t) && t.containsFVar s.fvarId! then side := side.push d.toExpr
  let qBody ← side.foldrM (fun p acc => do mkAppM ``And #[← inferType p, acc]) (mkConst ``True)
  let qPf ← side.foldrM (fun p acc => mkAppM ``And.intro #[p, acc]) (mkConst ``True.intro)
  let q ← Term.exprToSyntax (← mkLambdaFVars #[s] qBody)
  let hq ← Term.exprToSyntax qPf
  let sT ← Term.exprToSyntax s
  evalTactic (← `(tactic| refine Proven.next_of (s := $sT) (npc := $npc) (v := $v) (mem := $mem)
    (Q := $q) ?_ $(mkIdent `h) $(mkIdent `hpc) $(mkIdent `hi) $hq
    (by set_option linter.unnecessarySimpa false in simpa using $hq) ?_ ?_ ?_))
  evalTactic (← `(tactic| gmem_core))

variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

set_option hygiene false in
macro "genm" : tactic => `(tactic| (
  first | rw [Proven.G.encL_eq] at hi | rw [Proven.G.encS_eq] at hi
  try simp only [Nat.reduceShiftLeft, Nat.reduceOr, BitVec.reduceAppend] at hi))

/-! ## Loads -/

theorem step_lbu (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encL 4 imm rd rs1)) {A : BitVec 64}
    (hA : getX s rs1 + imm.signExtend 64 = A) (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 1 ≤ 0x100000000)
    {b : BitVec 8} (hb : s.mem[A.toNat]? = some b) :
    ∃ s', Next s s' (pc + 4) rd (b.setWidth 64) s.mem := by genm; gmem

theorem step_ld (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encL 3 imm rd rs1)) {A : BitVec 64}
    (hA : getX s rs1 + imm.signExtend 64 = A) (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 8 ≤ 0x100000000)
    (hal : A.toNat % 8 = 0) {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8}
    (h0 : s.mem[A.toNat]? = some b0) (h1 : s.mem[A.toNat + 1]? = some b1) (h2 : s.mem[A.toNat + 2]? = some b2)
    (h3 : s.mem[A.toNat + 3]? = some b3) (h4 : s.mem[A.toNat + 4]? = some b4) (h5 : s.mem[A.toNat + 5]? = some b5)
    (h6 : s.mem[A.toNat + 6]? = some b6) (h7 : s.mem[A.toNat + 7]? = some b7) :
    ∃ s', Next s s' (pc + 4) rd (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) s.mem := by genm; gmem

theorem step_lb (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encL 0 imm rd rs1)) {A : BitVec 64}
    (hA : getX s rs1 + imm.signExtend 64 = A) (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 1 ≤ 0x100000000)
    {b0 : BitVec 8} (h0 : s.mem[A.toNat]? = some b0) :
    ∃ s', Next s s' (pc + 4) rd (b0.signExtend 64) s.mem := by genm; gmem
theorem step_lh (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encL 1 imm rd rs1)) {A : BitVec 64}
    (hA : getX s rs1 + imm.signExtend 64 = A) (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 2 ≤ 0x100000000)
    (hal : A.toNat % 2 = 0)
    {b0 b1 : BitVec 8} (h0 : s.mem[A.toNat]? = some b0) (h1 : s.mem[A.toNat + 1]? = some b1) :
    ∃ s', Next s s' (pc + 4) rd ((b1 ++ b0 : BitVec 16).signExtend 64) s.mem := by genm; gmem
theorem step_lhu (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encL 5 imm rd rs1)) {A : BitVec 64}
    (hA : getX s rs1 + imm.signExtend 64 = A) (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 2 ≤ 0x100000000)
    (hal : A.toNat % 2 = 0)
    {b0 b1 : BitVec 8} (h0 : s.mem[A.toNat]? = some b0) (h1 : s.mem[A.toNat + 1]? = some b1) :
    ∃ s', Next s s' (pc + 4) rd ((b1 ++ b0 : BitVec 16).setWidth 64) s.mem := by genm; gmem
theorem step_lw (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encL 2 imm rd rs1)) {A : BitVec 64}
    (hA : getX s rs1 + imm.signExtend 64 = A) (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 4 ≤ 0x100000000)
    (hal : A.toNat % 4 = 0)
    {b0 b1 b2 b3 : BitVec 8} (h0 : s.mem[A.toNat]? = some b0) (h1 : s.mem[A.toNat + 1]? = some b1) (h2 : s.mem[A.toNat + 2]? = some b2) (h3 : s.mem[A.toNat + 3]? = some b3) :
    ∃ s', Next s s' (pc + 4) rd ((b3 ++ b2 ++ b1 ++ b0 : BitVec 32).signExtend 64) s.mem := by genm; gmem
theorem step_lwu (rd rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encL 6 imm rd rs1)) {A : BitVec 64}
    (hA : getX s rs1 + imm.signExtend 64 = A) (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 4 ≤ 0x100000000)
    (hal : A.toNat % 4 = 0)
    {b0 b1 b2 b3 : BitVec 8} (h0 : s.mem[A.toNat]? = some b0) (h1 : s.mem[A.toNat + 1]? = some b1) (h2 : s.mem[A.toNat + 2]? = some b2) (h3 : s.mem[A.toNat + 3]? = some b3) :
    ∃ s', Next s s' (pc + 4) rd ((b3 ++ b2 ++ b1 ++ b0 : BitVec 32).setWidth 64) s.mem := by genm; gmem

/-! ## Stores -/

theorem step_sb (rs2 rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encS 0 imm rs2 rs1)) {A : BitVec 64}
    (hA : getX s rs1 + imm.signExtend 64 = A) (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 1 ≤ 0x100000000) :
    ∃ s', Next s s' (pc + 4) 0 0 (s.mem.insert A.toNat ((getX s rs2).setWidth 8)) := by genm; gmem

theorem step_sd (rs2 rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encS 3 imm rs2 rs1)) {A : BitVec 64}
    (hA : getX s rs1 + imm.signExtend 64 = A) (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 8 ≤ 0x100000000)
    (hal : A.toNat % 8 = 0) :
    ∃ s', Next s s' (pc + 4) 0 0 (storeBytes s.mem A.toNat (le8 (getX s rs2))) := by genm; gmem

theorem step_sh (rs2 rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encS 1 imm rs2 rs1)) {A : BitVec 64}
    (hA : getX s rs1 + imm.signExtend 64 = A) (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 2 ≤ 0x100000000)
    (hal : A.toNat % 2 = 0) :
    ∃ s', Next s s' (pc + 4) 0 0 ((s.mem.insert (A.toNat) ((getX s rs2).extractLsb' 0 8)).insert (A.toNat + 1) ((getX s rs2).extractLsb' 8 8)) := by genm; gmem
theorem step_sw (rs2 rs1 : Fin 32) (imm : BitVec 12) (hi : instrAt s pc (encS 2 imm rs2 rs1)) {A : BitVec 64}
    (hA : getX s rs1 + imm.signExtend 64 = A) (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 4 ≤ 0x100000000)
    (hal : A.toNat % 4 = 0) :
    ∃ s', Next s s' (pc + 4) 0 0 ((((s.mem.insert (A.toNat) ((getX s rs2).extractLsb' 0 8)).insert (A.toNat + 1) ((getX s rs2).extractLsb' 8 8)).insert (A.toNat + 2) ((getX s rs2).extractLsb' 16 8)).insert (A.toNat + 3) ((getX s rs2).extractLsb' 24 8)) := by genm; gmem

end G
end Proven
