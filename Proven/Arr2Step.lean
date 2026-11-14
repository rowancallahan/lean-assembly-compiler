/- `mem_word2`: `mem_word` (`Proven/MemStep.lean`) for loads/stores with an immediate offset.
The data address is a variable `A` with a side hypothesis `getX s rs1 + imm = A` (so `simp` rewrites the
model's `x[rs1] + imm` to `A`), and the RAM-range hypothesis must be named `ha`
(`0x80000000 ≤ A.toNat ∧ A.toNat + n ≤ 0x100000000`); `regval_from_reg` is unfolded. -/
import Proven.MemStep
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven

theorem page8A (s : St) {x : BitVec 64} (h : x.toNat % 8 = 0) :
    split_on_page_boundary (bits_of_virtaddr (pm_transform_PA (.Virtaddr x) 0)) 8 s =
      .ok ((8 : Int), (0 : Int)) s := by
  simp [page8 s h]

set_option hygiene false in
macro "mem_word2_core" : tactic => `(tactic| (
  · intro s h hpc hi hQ
    simp only [Proven.getX_eq] at hQ
    have hok' := hok; obtain ⟨_, _, _⟩ := hok'
    have hram := Proven.in_ram (by decide) ha.1 ha.2
    have hf := Proven.fetch_cfg h hpc hok hi (by decide)
    have hd := Proven.dispatch_cfg h
    cfg_facts h
    obtain ⟨_, _, _, _, _, _⟩ := h.pma
    have := h.present .pmpaddr_n (by simp)
    sail_eval frozen[LeanRV64D.Functions.fetch, LeanRV64D.Functions.dispatchInterrupt, LeanRV64D.Functions.pmpCheck, LeanRV64D.Functions.range_subset, LeanRV64D.Functions.split_on_page_boundary] [*, Proven.pmp_none, Std.ExtDHashMap.contains_insert, BitVec.add_sub_cancel, LeanRV64D.Functions.matching_pma_region,
      LeanRV64D.Functions.matching_pma_region_bits_range, LeanRV64D.Functions.override_PMA, LeanRV64D.Functions.hartSupports,
      LeanRV64D.Functions.zopz0zI_u, LeanRV64D.Functions.zopz0zKzJ_u, LeanRV64D.Functions.zopz0zK_u, LeanRV64D.Functions.zopz0zI_s, LeanRV64D.Functions.zopz0zKzJ_s,
      LeanRV64D.Functions.regval_from_reg, Proven.aligned_v8, Proven.aligned_p8, Proven.tmod8, Proven.page8, Proven.page8', Proven.page8A, Proven.page1]
    all_goals simp [Proven.stepF, Proven.xset, Proven.update0_even, Proven.storeBytes_le8, Proven.extend_false64, Proven.upd_full64, *]
  all_goals simp))

open Lean Meta Elab Tactic in
/-- `step_word` with `mem_word2_core`; needs `ha : 0x80000000 ≤ A.toNat ∧ A.toNat + n ≤ 0x100000000` in context. -/
elab "mem_word2" : tactic => withMainContext do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let .app _ (.lam _ _ body _) := ty | throwError "mem_word2: expected ∃ s', Next s s' .."
  let args := body.getAppArgs
  unless body.isAppOfArity ``Next 6 do throwError "mem_word2: expected ∃ s', Next s s' .."
  let s := args[0]!
  let fn (e : Expr) : TacticM Term := do
    if e.hasLooseBVars then throwError "mem_word2: {e} mentions s'"
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
  evalTactic (← `(tactic| mem_word2_core))


end Proven
