/- `mem_word`: `step_word` for loads and stores.  The only change from `step_word_core`
(`Proven/Step.lean`): `range_subset` is frozen and the PMA range check of the data address is
supplied by `in_ram`.  (Unfolding `range_subset` on a symbolic address makes `simp` produce
`(2^64 - 0x80000000 + x.toNat) % 2^64 ≤ 0x80000000`-style terms whose definitional unfolding sends
the kernel into "deep recursion".) -/
import Riscv.Steps.Step
import Riscv.Direct.MemModel
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Proven

@[simp] theorem aligned_v8 {x : BitVec 64} (h : x.toNat % 8 = 0) : is_aligned_vaddr (.Virtaddr x) 8 = true := by
  simp [is_aligned_vaddr, toNatInt_eq, Int.tmod_eq_emod]; omega
@[simp] theorem aligned_p8 {x : BitVec 64} (h : x.toNat % 8 = 0) : is_aligned_paddr (.Physaddr x) 8 = true := by
  simp [is_aligned_paddr, toNatInt_eq, Int.tmod_eq_emod]; omega
@[simp] theorem tmod8 {x : BitVec 64} (h : x.toNat % 8 = 0) : Int.tmod (x.toNat : Int) 8 = 0 := by
  simp [Int.tmod_eq_emod]; omega

/-- the page-crossing check of an aligned 8-byte access -/
theorem same_page {x M : BitVec 64} (h : x.toNat % 8 = 0) (hM : M = 0xFFFFFFFFFFFFF000#64) :
    (x &&& M) = (x + 8#64 - 1#64 &&& M) := by
  have h7 : x &&& 7#64 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (7#64).toNat = 2^3 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]; simpa using h
  have : x + 8#64 - 1#64 = x ||| 7#64 := by
    rw [← BitVec.add_eq_or_of_and_eq_zero _ _ h7]; bv_omega
  subst hM; rw [this, BitVec.and_or_distrib_right]; simp

/-- `split_on_page_boundary` for an aligned 8-byte and for a 1-byte access: no split -/
@[simp] theorem page8 (s : St) {x : BitVec 64} (h : x.toNat % 8 = 0) :
    split_on_page_boundary x 8 s = .ok ((8 : Int), (0 : Int)) s := by
  simp [split_on_page_boundary, Sail.BitVec.length, zeros, BitVec.addInt, BitVec.subInt]
  split
  · rfl
  · next hn => exact absurd (same_page h (by decide)) hn
theorem page8' (s : St) {x : BitVec 64} (h : x.toNat % 8 = 0) :
    split_on_page_boundary (bits_of_virtaddr (pm_transform_PA (.Virtaddr (regval_from_reg x + 0#64)) 0)) 8 s =
      .ok ((8 : Int), (0 : Int)) s := by
  simp [page8 s h]
@[simp] theorem page1 (s : St) (x : BitVec 64) :
    split_on_page_boundary x 1 s = .ok ((1 : Int), (0 : Int)) s := by
  simp [split_on_page_boundary, Sail.BitVec.length, zeros, BitVec.addInt, BitVec.subInt, BitVec.add_sub_cancel]
  rfl

@[simp] theorem extend_false64 (x : BitVec 64) : extend_value false x = x := by
  simp [extend_value, sign_extend, Sail.BitVec.signExtend]
@[simp] theorem upd_full64 (x : BitVec 64) : Sail.BitVec.updateSubrange (0#64) 63 0 x = x := by
  ext i hi; simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']
theorem storeBytes_le8 (m : Mem) (a : Nat) (x : BitVec 64) : storeBytes m a (le8 x) =
    (((((((m.insert a (x.extractLsb' 0 8)).insert (a + 1) (x.extractLsb' 8 8)).insert (a + 2) (x.extractLsb' 16 8)).insert
      (a + 3) (x.extractLsb' 24 8)).insert (a + 4) (x.extractLsb' 32 8)).insert (a + 5) (x.extractLsb' 40 8)).insert
      (a + 6) (x.extractLsb' 48 8)).insert (a + 7) (x.extractLsb' 56 8) := rfl

set_option hygiene false in
macro "mem_word_core" : tactic => `(tactic| (
  · intro s h hpc hi hQ
    simp only [Proven.getX_eq] at hQ
    have hok' := hok; obtain ⟨_, _, _⟩ := hok'
    have hram := Proven.in_ram (by decide) hQ.1.1 hQ.1.2
    have hf := Proven.fetch_cfg h hpc hok hi (by decide)
    have hd := Proven.dispatch_cfg h
    cfg_facts h
    obtain ⟨_, _, _, _, _, _⟩ := h.pma
    have := h.present .pmpaddr_n (by simp)
    sail_eval frozen[LeanRV64D.Functions.fetch, LeanRV64D.Functions.dispatchInterrupt, LeanRV64D.Functions.pmpCheck, LeanRV64D.Functions.range_subset, LeanRV64D.Functions.split_on_page_boundary] [*, Proven.pmp_none, Std.ExtDHashMap.contains_insert, BitVec.add_sub_cancel, LeanRV64D.Functions.matching_pma_region,
      LeanRV64D.Functions.matching_pma_region_bits_range, LeanRV64D.Functions.override_PMA, LeanRV64D.Functions.hartSupports,
      LeanRV64D.Functions.zopz0zI_u, LeanRV64D.Functions.zopz0zKzJ_u, LeanRV64D.Functions.zopz0zK_u, LeanRV64D.Functions.zopz0zI_s, LeanRV64D.Functions.zopz0zKzJ_s,
      Proven.aligned_v8, Proven.aligned_p8, Proven.tmod8, Proven.page8, Proven.page8', Proven.page1]
    all_goals simp [Proven.stepF, Proven.xset, Proven.update0_even, Proven.storeBytes_le8, Proven.extend_false64, Proven.upd_full64, *]
  all_goals simp))

open Lean Meta Elab Tactic in
/-- `step_word` with `mem_word_core`; the first side hypothesis must be
`0x80000000 ≤ x.toNat ∧ x.toNat + n ≤ 0x100000000` for the data address `x`. -/
elab "mem_word" : tactic => withMainContext do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let .app _ (.lam _ _ body _) := ty | throwError "mem_word: expected ∃ s', Next s s' .."
  let args := body.getAppArgs
  unless body.isAppOfArity ``Next 6 do throwError "mem_word: expected ∃ s', Next s s' .."
  let s := args[0]!
  let fn (e : Expr) : TacticM Term := do
    if e.hasLooseBVars then throwError "mem_word: {e} mentions s'"
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
  evalTactic (← `(tactic| mem_word_core))

end Proven
