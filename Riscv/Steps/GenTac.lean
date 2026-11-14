/- Machinery for register-generic step lemmas: an instruction word is `c ||| f` with `c` the concrete
fields (opcode, funct3, funct7) and `f` the symbolic fields (registers, immediates), zero elsewhere.
As in `Riscv/Steps/Branch.lean`, the decoder's bit-range tests are decided by `*_known` / `*_mismatch`
/ `*_ne` (a range inside the concrete fields) and `*_imm` (a range inside the symbolic fields); a mask
`K` says which bits are concrete, and a hypothesis `f &&& K = 0` in context lets `simp` discharge them.
Registers are read and written through `rX_bits_ok` / `wX_bits_ok` (`GenRegs.lean`). -/
import Riscv.Steps.GenRegs
import Riscv.Steps.Branch
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Proven
namespace G

/-! ## Masks of the concrete fields -/

/-- R-type: funct7, funct3, opcode -/
def KR : BitVec 32 := 0xFE00707F#32
/-- I/S/B-type: funct3, opcode -/
def KI : BitVec 32 := 0x0000707F#32
/-- RV64 shift-immediate: funct6, funct3, opcode -/
def KS : BitVec 32 := 0xFC00707F#32
/-- U/J-type: opcode -/
def KU : BitVec 32 := 0x0000007F#32

@[simp] theorem R_known {c m : BitVec 32} (hm : m &&& KR = 0) {lo n} (hk : ∀ i < n, KR.getLsbD (lo + i) = true) :
    (c ||| m).extractLsb' lo n = c.extractLsb' lo n := ext_known hm hk
@[simp] theorem R_mismatch {c m : BitVec 32} (hm : m &&& KR = 0) {lo n} {d : BitVec n}
    (hk : ∃ i < n, KR.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| m).extractLsb' lo n = d) = False := ext_mismatch hm hk
@[simp] theorem R_ne {c m d : BitVec 32} (hm : m &&& KR = 0)
    (hk : ∃ i < 32, KR.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) : ((c ||| m) = d) = False :=
  word_ne hm hk
@[simp] theorem I_known {c m : BitVec 32} (hm : m &&& KI = 0) {lo n} (hk : ∀ i < n, KI.getLsbD (lo + i) = true) :
    (c ||| m).extractLsb' lo n = c.extractLsb' lo n := ext_known hm hk
@[simp] theorem I_mismatch {c m : BitVec 32} (hm : m &&& KI = 0) {lo n} {d : BitVec n}
    (hk : ∃ i < n, KI.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| m).extractLsb' lo n = d) = False := ext_mismatch hm hk
@[simp] theorem I_ne {c m d : BitVec 32} (hm : m &&& KI = 0)
    (hk : ∃ i < 32, KI.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) : ((c ||| m) = d) = False :=
  word_ne hm hk
@[simp] theorem S_known {c m : BitVec 32} (hm : m &&& KS = 0) {lo n} (hk : ∀ i < n, KS.getLsbD (lo + i) = true) :
    (c ||| m).extractLsb' lo n = c.extractLsb' lo n := ext_known hm hk
@[simp] theorem S_mismatch {c m : BitVec 32} (hm : m &&& KS = 0) {lo n} {d : BitVec n}
    (hk : ∃ i < n, KS.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| m).extractLsb' lo n = d) = False := ext_mismatch hm hk
@[simp] theorem S_ne {c m d : BitVec 32} (hm : m &&& KS = 0)
    (hk : ∃ i < 32, KS.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) : ((c ||| m) = d) = False :=
  word_ne hm hk
@[simp] theorem U_known {c m : BitVec 32} (hm : m &&& KU = 0) {lo n} (hk : ∀ i < n, KU.getLsbD (lo + i) = true) :
    (c ||| m).extractLsb' lo n = c.extractLsb' lo n := ext_known hm hk
@[simp] theorem U_mismatch {c m : BitVec 32} (hm : m &&& KU = 0) {lo n} {d : BitVec n}
    (hk : ∃ i < n, KU.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| m).extractLsb' lo n = d) = False := ext_mismatch hm hk
@[simp] theorem U_ne {c m d : BitVec 32} (hm : m &&& KU = 0)
    (hk : ∃ i < 32, KU.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) : ((c ||| m) = d) = False :=
  word_ne hm hk
/-- a range with no concrete bit set: a slice of the symbolic fields -/
@[simp] theorem F_imm {c m : BitVec 32} {lo n} (hk : ∀ i < n, c.getLsbD (lo + i) = false) :
    (c ||| m).extractLsb' lo n = m.extractLsb' lo n := ext_imm hk

/-! ## Symbolic fields -/

/-- R-type register fields -/
def fR (rd rs1 rs2 : Fin 32) : BitVec 32 :=
  (0#7 : BitVec 7) +++ (BitVec.ofFin rs2 : BitVec 5) +++ (BitVec.ofFin rs1 : BitVec 5) +++ (0#3 : BitVec 3) +++
    (BitVec.ofFin rd : BitVec 5) +++ (0#7 : BitVec 7)

macro "kbits" : tactic => `(tactic| (simp only [KR, KI, KS, KU, fR]; bits))

theorem fR_K (rd rs1 rs2) : fR rd rs1 rs2 &&& KR = 0 := by kbits
@[simp] theorem fR_rd (rd rs1 rs2) : (fR rd rs1 rs2).extractLsb' 7 5 = BitVec.ofFin rd := by simp only [fR]; bits
@[simp] theorem fR_rs1 (rd rs1 rs2) : (fR rd rs1 rs2).extractLsb' 15 5 = BitVec.ofFin rs1 := by simp only [fR]; bits
@[simp] theorem fR_rs2 (rd rs1 rs2) : (fR rd rs1 rs2).extractLsb' 20 5 = BitVec.ofFin rs2 := by simp only [fR]; bits

/-- an R-type word: `c` concrete (e.g. `0x33 ||| f3 <<< 12 ||| f7 <<< 25`) -/
def wR (c : BitVec 32) (rd rs1 rs2 : Fin 32) : BitVec 32 := c ||| fR rd rs1 rs2

theorem low2_or {c m : BitVec 32} (hc : c.extractLsb' 0 2 = 3#2) (hm : m.extractLsb' 0 2 = 0#2) :
    (c ||| m).extractLsb' 0 2 = 3#2 := by
  rw [← hc]; ext i hi
  have := congrArg (·.getLsbD i) hm; simp at this; simp [this hi]
theorem rvc_or {c m : BitVec 32} (hc : c.extractLsb' 0 2 = 3#2) (hm : m.extractLsb' 0 2 = 0#2) :
    isRVC (BitVec.setWidth 16 ((c ||| m).extractLsb' 24 8 ++ (c ||| m).extractLsb' 16 8 ++
      (c ||| m).extractLsb' 8 8 ++ (c ||| m).extractLsb' 0 8)) = false := rvc_of (low2_or hc hm)
theorem fR_low2 (rd rs1 rs2) : (fR rd rs1 rs2).extractLsb' 0 2 = 0#2 := by simp only [fR]; bits

/-! ## Finishing: the model's final register map as `xset` of `stepF` -/

theorem xval_ins {m : Regs} {r : Register} {v} (hr : r ∉ xregs := by decide) (j : Fin 32) :
    xval (m.insert r v) j = xval m j := xval_insert_other hr j

/-! ## The tactic -/

set_option hygiene false in
/-- `step_word_core` for a word `c ||| f` with symbolic fields; `hm : f &&& K = 0` and
`hlow : f.extractLsb' 0 2 = 0` must be provable by `gfield` -/
macro "gstep_core" : tactic => `(tactic| (
  · intro s h hpc hi hQ
    simp only [Proven.getX_eq] at hQ
    have hok' := hok; obtain ⟨_, _, _⟩ := hok'
    have hf := Proven.fetch_cfg h hpc hok hi (Proven.G.rvc_or (by decide) (by first | exact Proven.G.fR_low2 ..))
    rw [Proven.bytes_eq] at hf
    have hd := Proven.dispatch_cfg h
    have hxp := h.xpresent
    have hK := Proven.G.fR_K
    cfg_facts h
    obtain ⟨_, _, _, _, _, _⟩ := h.pma
    have := h.present .pmpaddr_n (by simp)
    sail_eval frozen[LeanRV64D.Functions.fetch, LeanRV64D.Functions.dispatchInterrupt, LeanRV64D.Functions.pmpCheck,
        LeanRV64D.Functions.rX_bits, LeanRV64D.Functions.wX_bits]
      [*, Proven.pmp_none, Std.ExtDHashMap.contains_insert, BitVec.add_sub_cancel, LeanRV64D.Functions.matching_pma_region,
      LeanRV64D.Functions.matching_pma_region_bits_range, LeanRV64D.Functions.override_PMA, LeanRV64D.Functions.hartSupports, LeanRV64D.Functions.range_subset, LeanRV64D.Functions.zopz0zIzJ_u,
      LeanRV64D.Functions.zopz0zI_u, LeanRV64D.Functions.zopz0zKzJ_u, LeanRV64D.Functions.zopz0zK_u, LeanRV64D.Functions.zopz0zI_s, LeanRV64D.Functions.zopz0zKzJ_s,
      BitVec.toNat_sub, BitVec.toNat_add, Proven.G.R_known, Proven.G.R_mismatch, Proven.G.R_ne, Proven.G.F_imm,
      Proven.G.fR_rd, Proven.G.fR_rs1, Proven.G.fR_rs2, Proven.sail_ext, Proven.setw_ext,
      Proven.rX_bits_ok, Proven.wX_bits_ok, Proven.xpresent_insert]
    all_goals simp [Proven.stepF, Proven.update0_even, *]
  all_goals simp))

open Lean Meta Elab Tactic in
/-- `step_word` for words with symbolic fields (same interface) -/
elab "gstep" : tactic => withMainContext do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let .app _ (.lam _ _ body _) := ty | throwError "gstep: expected ∃ s', Next s s' .."
  let args := body.getAppArgs
  unless body.isAppOfArity ``Next 6 do throwError "gstep: expected ∃ s', Next s s' .."
  let s := args[0]!
  let fn (e : Expr) : TacticM Term := do
    if e.hasLooseBVars then throwError "gstep: {e} mentions s'"
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
  evalTactic (← `(tactic| gstep_core))

example (rd rs1 rs2 : Fin 32) : (BitVec.extractLsb' 0 15 (51#32 ||| fR rd rs1 rs2) = 24595#15) = False := by
  have hK := fR_K
  simp (config := {decide := true}) [R_mismatch, hK]
example (rd rs1 rs2 : Fin 32) : (BitVec.extractLsb' 0 15 (51#32 ||| fR rd rs1 rs2) = 24595#15) = False := by
  apply R_mismatch (fR_K ..)
  decide
variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

theorem t_add_X (rd rs1 rs2 : Fin 32) (hi : instrAt s pc (wR 0x33#32 rd rs1 rs2)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs1 + getX s rs2) s.mem := by
  sorry

end G
end Proven
