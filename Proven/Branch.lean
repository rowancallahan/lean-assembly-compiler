/- Branches and jumps with a SYMBOLIC offset on the Sail RV64 model: the machinery.
An instruction word is `c ||| imm o`: `c` holds the concrete fields (opcode, funct3, registers) and
`imm o` the offset bits scattered as the format prescribes (zero elsewhere).  The decoder only ever
tests bit ranges of the word; a range inside the concrete fields evaluates to a literal (`B_known`),
a test that disagrees with a concrete bit is `False` (`B_mismatch`), and a range inside the
immediate fields is a slice of `imm o` (`B_imm`), which `immB_dec` reassembles to `o`.
The per-word lemmas are generated into `Proven/BranchWords.lean` by `Proven/gen_branch.py`. -/
import Proven.Words
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Proven

/-! ## Words -/

/-- B-type immediate bits of the byte offset `o ++ 0` (13 bits, signed), zero elsewhere -/
def immB (o : BitVec 12) : BitVec 32 :=
  o.extractLsb' 11 1 +++ o.extractLsb' 4 6 +++ (0#13 : BitVec 13) +++ o.extractLsb' 0 4 +++
    o.extractLsb' 10 1 +++ (0#7 : BitVec 7)
/-- J-type immediate bits of the byte offset `o ++ 0` (21 bits, signed), zero elsewhere -/
def immJ (o : BitVec 20) : BitVec 32 :=
  o.extractLsb' 19 1 +++ o.extractLsb' 0 10 +++ o.extractLsb' 10 1 +++ o.extractLsb' 11 8 +++ (0#12 : BitVec 12)

/-- `b<f3> rs1, rs2, 2*o` (`f3`: 0 beq, 1 bne, 4 blt, 5 bge, 6 bltu, 7 bgeu) -/
def wB (f3 : BitVec 3) (rs1 rs2 : BitVec 5) (o : BitVec 12) : BitVec 32 :=
  ((0#7 : BitVec 7) +++ rs2 +++ rs1 +++ f3 +++ (0#5 : BitVec 5) +++ (0x63#7 : BitVec 7)) ||| immB o
/-- `jal rd, 2*o` -/
def wJ (rd : BitVec 5) (o : BitVec 20) : BitVec 32 := ((0#20 : BitVec 20) +++ rd +++ (0x6f#7 : BitVec 7)) ||| immJ o

/-- the byte offset of a branch / jump, as the model computes it -/
def boff (o : BitVec 12) : BitVec 64 := sign_extend (m := 64) (o +++ (0#1 : BitVec 1))
def joff (o : BitVec 20) : BitVec 64 := sign_extend (m := 64) (o +++ (0#1 : BitVec 1))

/-! ## Bit-range lemmas -/

def KB : BitVec 32 := 0x01fff07f#32
def KJ : BitVec 32 := 0x00000fff#32

/-! Bit-level proofs, kernel-checked (no `bv_decide`, whose proofs add `native_decide`-style axioms):
`bits` proves `x = y` for fixed-width `x y` by checking `getLsbD i` for each `i` in turn. -/

theorem fa_succ {P : Nat → Prop} {n : Nat} (h0 : P 0) (hs : ∀ i, i < n → P (i + 1)) : ∀ i, i < n + 1 → P i
  | 0, _ => h0
  | i + 1, h => hs i (by omega)
theorem fa_zero {P : Nat → Prop} : ∀ i, i < 0 → P i := fun _ h => absurd h (Nat.not_lt_zero _)

/-- one bit: `rw` (not `simp`: the widths are sums) through appends and slices, then evaluate -/
macro "bit1" : tactic => `(tactic| (
  try simp only [Nat.reduceAdd, BitVec.getLsbD_and, BitVec.getLsbD_or]
  repeat (first | rw [BitVec.getLsbD_append] | rw [BitVec.getLsbD_extractLsb'] | rw [BitVec.getLsbD_or] |
    rw [BitVec.getLsbD_and])
  try simp only [Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd, reduceIte, decide_true, decide_false, Bool.true_and,
    Bool.false_and]
  all_goals simp (config := {decide := true}) [BitVec.getLsbD_extractLsb', KB, KJ]))
macro "bits" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq; intro i hi; revert i
  try simp only [Nat.reduceAdd]
  repeat (first | exact fa_zero | refine fa_succ (by bit1) ?_)))
theorem immB_K (o) : immB o &&& KB = 0 := by simp only [immB]; bits
theorem immJ_K (o) : immJ o &&& KJ = 0 := by simp only [immJ]; bits

theorem ext_known {c m K : BitVec 32} (hm : m &&& K = 0) {lo n : Nat}
    (hk : ∀ i < n, K.getLsbD (lo + i) = true) : (c ||| m).extractLsb' lo n = c.extractLsb' lo n := by
  ext i hi
  have := congrArg (·.getLsbD (lo + i)) hm
  simp [hk i hi] at this
  simp [this]

theorem ext_mismatch {c m K : BitVec 32} (hm : m &&& K = 0) {lo n : Nat} {d : BitVec n}
    (hk : ∃ i < n, K.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| m).extractLsb' lo n = d) = False := by
  obtain ⟨i, hi, hK, hd⟩ := hk
  have := congrArg (·.getLsbD (lo + i)) hm
  simp [hK] at this
  simp only [eq_iff_iff, iff_false]; intro he
  apply hd; rw [← he]; simp [hi, this]

theorem ext_imm {c m : BitVec 32} {lo n : Nat} (hk : ∀ i < n, c.getLsbD (lo + i) = false) :
    (c ||| m).extractLsb' lo n = m.extractLsb' lo n := by
  ext i hi; simp [hk i hi]

theorem word_ne {c m K d : BitVec 32} (hm : m &&& K = 0)
    (hk : ∃ i < 32, K.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) : ((c ||| m) = d) = False := by
  have := ext_mismatch hm hk; simpa using this

@[simp] theorem B_known {c : BitVec 32} {o lo n} (hk : ∀ i < n, KB.getLsbD (lo + i) = true) :
    (c ||| immB o).extractLsb' lo n = c.extractLsb' lo n := ext_known (immB_K o) hk
@[simp] theorem B_mismatch {c : BitVec 32} {o lo n} {d : BitVec n}
    (hk : ∃ i < n, KB.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| immB o).extractLsb' lo n = d) = False := ext_mismatch (immB_K o) hk
@[simp] theorem B_ne {c d : BitVec 32} {o}
    (hk : ∃ i < 32, KB.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) :
    ((c ||| immB o) = d) = False := word_ne (immB_K o) hk
@[simp] theorem B_imm {c : BitVec 32} {o lo n} (hk : ∀ i < n, c.getLsbD (lo + i) = false) :
    (c ||| immB o).extractLsb' lo n = (immB o).extractLsb' lo n := ext_imm hk

@[simp] theorem J_known {c : BitVec 32} {o lo n} (hk : ∀ i < n, KJ.getLsbD (lo + i) = true) :
    (c ||| immJ o).extractLsb' lo n = c.extractLsb' lo n := ext_known (immJ_K o) hk
@[simp] theorem J_mismatch {c : BitVec 32} {o lo n} {d : BitVec n}
    (hk : ∃ i < n, KJ.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| immJ o).extractLsb' lo n = d) = False := ext_mismatch (immJ_K o) hk
@[simp] theorem J_ne {c d : BitVec 32} {o}
    (hk : ∃ i < 32, KJ.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) :
    ((c ||| immJ o) = d) = False := word_ne (immJ_K o) hk
@[simp] theorem J_imm {c : BitVec 32} {o lo n} (hk : ∀ i < n, c.getLsbD (lo + i) = false) :
    (c ||| immJ o).extractLsb' lo n = (immJ o).extractLsb' lo n := ext_imm hk

theorem sail_ext (x : BitVec 32) (hi lo : Nat) :
    Sail.BitVec.extractLsb x hi lo = x.extractLsb' lo (hi - lo + 1) := rfl
theorem setw_ext (x : BitVec 32) (k : Nat) (hk : k ≤ 32) : x.setWidth k = x.extractLsb' 0 k := by
  ext i hi; simp

theorem immB_dec (o : BitVec 12) :
    (BitVec.extractLsb' 31 1 (immB o) +++ BitVec.extractLsb' 7 1 (immB o) +++ BitVec.extractLsb' 25 6 (immB o) +++
      BitVec.extractLsb' 8 4 (immB o) +++ (0#1 : BitVec 1) : BitVec 13) = o +++ (0#1 : BitVec 1) := by
  simp only [immB]; bits
theorem immJ_dec (o : BitVec 20) :
    (BitVec.extractLsb' 31 1 (immJ o) +++ BitVec.extractLsb' 12 8 (immJ o) +++ BitVec.extractLsb' 20 1 (immJ o) +++
      BitVec.extractLsb' 21 10 (immJ o) +++ (0#1 : BitVec 1) : BitVec 21) = o +++ (0#1 : BitVec 1) := by
  simp only [immJ]; bits

theorem boff_even (o : BitVec 12) : (sign_extend (m := 64) (o +++ (0#1 : BitVec 1))).toNat % 2 = 0 := by
  have : (sign_extend (m := 64) (o +++ (0#1 : BitVec 1))).getLsbD 0 = false := by
    simp only [sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend]; rw [BitVec.getLsbD_append]; simp
  simpa [BitVec.getLsbD, Nat.testBit_zero] using this
theorem joff_even (o : BitVec 20) : (sign_extend (m := 64) (o +++ (0#1 : BitVec 1))).toNat % 2 = 0 := by
  have : (sign_extend (m := 64) (o +++ (0#1 : BitVec 1))).getLsbD 0 = false := by
    simp only [sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend]; rw [BitVec.getLsbD_append]; simp
  simpa [BitVec.getLsbD, Nat.testBit_zero] using this

theorem add_boff_even (a : Nat) (o : BitVec 12) :
    (a + (sign_extend (m := 64) (o +++ (0#1 : BitVec 1))).toNat) % 2 = a % 2 := by
  have := boff_even o; omega
theorem add_joff_even (a : Nat) (o : BitVec 20) :
    (a + (sign_extend (m := 64) (o +++ (0#1 : BitVec 1))).toNat) % 2 = a % 2 := by
  have := joff_even o; omega

theorem bytes_eq (w : BitVec 32) :
    (w.extractLsb' 24 8 +++ w.extractLsb' 16 8 +++ w.extractLsb' 8 8 +++ w.extractLsb' 0 8 : BitVec 32) = w := by
  bits
theorem ze32 (x : BitVec 32) : zero_extend (m := 32) x = x := by simp [zero_extend, Sail.BitVec.zeroExtend]

theorem low2_wB (f3 rs1 rs2 o) : (wB f3 rs1 rs2 o).extractLsb' 0 2 = 3#2 := by simp only [wB, immB]; bits
theorem low2_wJ (rd o) : (wJ rd o).extractLsb' 0 2 = 3#2 := by simp only [wJ, immJ]; bits
theorem rvc_of {w : BitVec 32} (h : w.extractLsb' 0 2 = 3#2) : isRVC (BitVec.setWidth 16 (w.extractLsb' 24 8 ++
    w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8)) = false := by
  rw [bytes_eq]
  have : (BitVec.setWidth 16 w).extractLsb' 0 2 = 3#2 := by rw [← h]; ext i hi; simp; omega
  simp [isRVC, Sail.BitVec.extractLsb, BitVec.extractLsb, this]
theorem rvc_wB (f3 rs1 rs2 o) : isRVC (BitVec.setWidth 16 ((wB f3 rs1 rs2 o).extractLsb' 24 8 ++
    (wB f3 rs1 rs2 o).extractLsb' 16 8 ++ (wB f3 rs1 rs2 o).extractLsb' 8 8 ++ (wB f3 rs1 rs2 o).extractLsb' 0 8)) =
    false := rvc_of (low2_wB ..)
theorem rvc_wJ (rd o) : isRVC (BitVec.setWidth 16 ((wJ rd o).extractLsb' 24 8 ++
    (wJ rd o).extractLsb' 16 8 ++ (wJ rd o).extractLsb' 8 8 ++ (wJ rd o).extractLsb' 0 8)) = false :=
  rvc_of (low2_wJ ..)

/-! ## The tactic -/

set_option hygiene false in
/-- `step_word_core` for a word `wB .. o` / `wJ .. o` with a symbolic offset `o` -/
macro "bstep_core" : tactic => `(tactic| (
  · intro s h hpc hi hQ
    simp only [Proven.getX_eq] at hQ
    have hok' := hok; obtain ⟨_, _, _⟩ := hok'
    have hf := Proven.fetch_cfg h hpc hok hi (by first | with_reducible exact Proven.rvc_wB .. | with_reducible exact Proven.rvc_wJ ..)
    rw [Proven.bytes_eq] at hf; simp only [Proven.wB, Proven.wJ] at hf
    have hd := Proven.dispatch_cfg h
    cfg_facts h
    obtain ⟨_, _, _, _, _, _⟩ := h.pma
    have := h.present .pmpaddr_n (by simp)
    sail_eval frozen[LeanRV64D.Functions.fetch, LeanRV64D.Functions.dispatchInterrupt, LeanRV64D.Functions.pmpCheck] [*, Proven.pmp_none, Std.ExtDHashMap.contains_insert, BitVec.add_sub_cancel, LeanRV64D.Functions.matching_pma_region,
      LeanRV64D.Functions.matching_pma_region_bits_range, LeanRV64D.Functions.override_PMA, LeanRV64D.Functions.hartSupports, LeanRV64D.Functions.range_subset, LeanRV64D.Functions.zopz0zIzJ_u,
      LeanRV64D.Functions.zopz0zI_u, LeanRV64D.Functions.zopz0zKzJ_u, LeanRV64D.Functions.zopz0zK_u, LeanRV64D.Functions.zopz0zI_s, LeanRV64D.Functions.zopz0zKzJ_s,
      BitVec.toNat_sub, BitVec.toNat_add, Proven.B_known, Proven.B_mismatch, Proven.B_ne, Proven.B_imm, Proven.J_known,
      Proven.J_mismatch, Proven.J_ne, Proven.J_imm, Proven.immB_dec, Proven.immJ_dec, Proven.add_boff_even, Proven.add_joff_even, Proven.sail_ext, Proven.setw_ext]
    all_goals simp [Proven.stepF, Proven.xset, Proven.update0_even, Proven.wB, Proven.wJ, Proven.ze32, Proven.boff,
      Proven.joff, *]
  all_goals simp))

open Lean Meta Elab Tactic in
/-- `step_word` for branch/jump words with a symbolic offset (same interface) -/
elab "bstep" : tactic => withMainContext do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let .app _ (.lam _ _ body _) := ty | throwError "bstep: expected ∃ s', Next s s' .."
  let args := body.getAppArgs
  unless body.isAppOfArity ``Next 6 do throwError "bstep: expected ∃ s', Next s s' .."
  let s := args[0]!
  let fn (e : Expr) : TacticM Term := do
    if e.hasLooseBVars then throwError "bstep: {e} mentions s'"
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
  evalTactic (← `(tactic| bstep_core))

/-! ## Branch conditions -/

/-- the branch condition of funct3 `f3` -/
def bcond (f3 : Nat) (a b : BitVec 64) : Bool :=
  match f3 with
  | 0 => a == b | 1 => a != b | 4 => a.slt b | 5 => !a.slt b | 6 => a.ult b | _ => !a.ult b

end Proven
