/- L3: the AArch64 backend `Proven.Arm.gen` (Proven/CompilerArm.lean) is correct at the decode+execute layer of
the Sail ARM model: running the emitted words through `__DecodeA64` leaves `e.denote env` in `x0`.

Layer: decode+execute only (`__DecodeA64`, with `SEE := -1` before each word as `step_model` does). Not included:
instruction fetch from memory, the PC update, interrupts/exceptions, `__TopLevel`, and the final `ret`. -/
import Arm.Words
import Proven.CompilerArm
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace ArmProof
open Proven

/-! ## Running word lists -/

/-- the model runs `ws` in order (word `i` decoded with `pc + 4 i`, `SEE := -1` before each) from `s` to `s'` -/
def RunM : Int → List (BitVec 32) → St → St → Prop
  | _, [], s, s' => s' = s
  | pc, w :: ws, s, s'' => ∃ s', __DecodeA64 pc w (reset s) = .ok () s' ∧ RunM (pc + 4) ws s' s''

/-- the small machine runs `ws` -/
def runA (ws : List (BitVec 32)) (a : AState) : AState := ws.foldl (fun a w => armStep w a) a

theorem Frame.refl (s : St) : Frame s s := ⟨rfl, fun _ _ _ _ => rfl⟩

theorem Frame.trans {s₁ s₂ s₃ : St} (h₁ : Frame s₁ s₂) (h₂ : Frame s₂ s₃) : Frame s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, fun r hr hp hs => (h₂.2 r hr hp hs).trans (h₁.2 r hr hp hs)⟩

/-- simulation: on emitted words the model follows the small machine -/
theorem run_sim : ∀ (ws : List (BitVec 32)) (pc : Int) (s : St) (a : AState), (∀ w ∈ ws, w ∈ emitted) →
    ArmCfg s → Abs s a → ∃ s', RunM pc ws s s' ∧ Abs s' (runA ws a) ∧ ArmCfg s' ∧ Frame s s'
  | [], _, s, _, _, hc, ha => ⟨s, rfl, ha, hc, Frame.refl s⟩
  | w :: ws, pc, s, a, hw, hc, ha => by
    obtain ⟨s₁, h₁, ha₁, hc₁, hf₁⟩ := armStep_ok (hw w (List.mem_cons_self ..)) pc s a hc ha
    obtain ⟨s₂, h₂, ha₂, hc₂, hf₂⟩ :=
      run_sim ws (pc + 4) s₁ (armStep w a) (fun w' h => hw w' (List.mem_cons_of_mem _ h)) hc₁ ha₁
    exact ⟨s₂, ⟨s₁, h₁, h₂⟩, ha₂, hc₂, hf₁.trans hf₂⟩

/-! ## The small machine on the backend's code -/

theorem runA_append (l₁ l₂ : List (BitVec 32)) (a : AState) : runA (l₁ ++ l₂) a = runA l₂ (runA l₁ a) :=
  List.foldl_append ..

theorem runA_nil (a : AState) : runA [] a = a := rfl

theorem setX_x (a : AState) {d : Nat} (hd : d ≠ 31) (v : BitVec 64) (j : Nat) :
    (a.setX d v).x j = if j = d then v else a.x j := by simp [AState.setX, hd]

theorem T_lt : ∀ k < 11, Arm.T k < 31 := by decide +kernel
theorem T_inj : ∀ i < 11, ∀ j < 11, Arm.T i = Arm.T j → i = j := by decide +kernel
theorem T_ne_A : ∀ k < 11, ∀ i < 4, Arm.T k ≠ i := by decide +kernel
theorem T_ne_0 : ∀ k < 11, Arm.T k ≠ 0 := by decide +kernel

theorem lo_v (x y : BitVec 64) : (if y.toNat ≤ x.toNat then 0#64 else 1#64) = if x < y then 1#64 else 0#64 := by
  have : x < y ↔ ¬ y.toNat ≤ x.toNat := by rw [BitVec.lt_def]; omega
  by_cases h : y.toNat ≤ x.toNat <;> simp [h, this]
theorem sub_zero_iff (x y : BitVec 64) : x - y = 0 ↔ x = y := by
  have := x.isLt; have := y.isLt
  rw [← BitVec.toNat_inj, ← BitVec.toNat_inj, BitVec.toNat_sub]; simp; omega
theorem eq_v (x y : BitVec 64) : (if x - y = 0#64 then 1#64 else 0#64) = if x = y then 1#64 else 0#64 := by
  simp only [show (0#64 : BitVec 64) = 0 from rfl, sub_zero_iff]
theorem slt_v (x y : BitVec 64) :
    (if (x - y).msb = !decide ((x.toInt - y.toInt).bmod 18446744073709551616 = x.toInt - y.toInt) then 0#64 else 1#64)
      = if x.slt y = true then 1#64 else 0#64 := by
  have h1 := BitVec.toInt_lt (x := x); have h2 := BitVec.le_toInt (x := x)
  have h3 := BitVec.toInt_lt (x := y); have h4 := BitVec.le_toInt (x := y)
  simp only [BitVec.msb_eq_toInt, BitVec.toInt_sub, BitVec.slt_iff_toInt_lt]
  simp only [Int.bmod] at *
  by_cases h : x.toInt < y.toInt <;> simp [h] <;> split <;> omega
/-- `a'` is `a` with `x d := v` -/
def Upd (a a' : AState) (d : Nat) (v : BitVec 64) : Prop := ∀ j, a'.x j = if j = d then v else a.x j

theorem op_small (op : Op) (k : Nat) (hk : k < 10) (a : AState) :
    Upd a (runA (Arm.opCode op k) a) (Arm.T k) (op.eval (a.x (Arm.T k)) (a.x (Arm.T (k + 1)))) := by
  intro j
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
    k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  all_goals cases op
  all_goals simp [runA, Arm.opCode, Arm.selCode, Arm.iVar, Arm.iZero, Arm.iShl, Arm.iInc, Arm.iRes, Arm.rrr, Arm.cmp, Arm.cset, Arm.T, armStep,
    AState.rd, setX_x, AState.setSub, Op.eval, cond_cs, cond_ge, cond_ne, lo_v, eq_v, slt_v, sub_zero_iff]

theorem sel_small (k : Nat) (hk : k < 9) (a : AState) :
    Upd a (runA (Arm.selCode k) a) (Arm.T k)
      (if a.x (Arm.T k) = 0 then a.x (Arm.T (k + 2)) else a.x (Arm.T (k + 1))) := by
  intro j
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
    k = 6 ∨ k = 7 ∨ k = 8 := by omega
  all_goals simp [runA, Arm.opCode, Arm.selCode, Arm.iVar, Arm.iZero, Arm.iShl, Arm.iInc, Arm.iRes, Arm.rrr, Arm.cmp, Arm.cset, Arm.T, armStep,
    AState.rd, setX_x, AState.setSub, Op.eval, cond_cs, cond_ge, cond_ne, lo_v, eq_v, slt_v, sub_zero_iff]
  all_goals split <;> simp_all

theorem var_small (i k : Nat) (hi : i < 4) (hk : k < 11) (a : AState) :
    Upd a (runA [Arm.iVar i k] a) (Arm.T k) (a.x i) := by
  intro j
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
    k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
  all_goals simp [runA, Arm.opCode, Arm.selCode, Arm.iVar, Arm.iZero, Arm.iShl, Arm.iInc, Arm.iRes, Arm.rrr, Arm.cmp, Arm.cset, Arm.T, armStep,
    AState.rd, setX_x, AState.setSub, Op.eval, cond_cs, cond_ge, cond_ne, lo_v, eq_v, slt_v, sub_zero_iff]

theorem zero_small (k : Nat) (hk : k < 11) (a : AState) : Upd a (runA [Arm.iZero k] a) (Arm.T k) 0 := by
  intro j
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
    k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
  all_goals simp [runA, Arm.opCode, Arm.selCode, Arm.iVar, Arm.iZero, Arm.iShl, Arm.iInc, Arm.iRes, Arm.rrr, Arm.cmp, Arm.cset, Arm.T, armStep,
    AState.rd, setX_x, AState.setSub, Op.eval, cond_cs, cond_ge, cond_ne, lo_v, eq_v, slt_v, sub_zero_iff]

theorem shl_small (k : Nat) (hk : k < 11) (a : AState) :
    Upd a (runA [Arm.iShl k] a) (Arm.T k) (a.x (Arm.T k) + a.x (Arm.T k)) := by
  intro j
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
    k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
  all_goals simp [runA, Arm.opCode, Arm.selCode, Arm.iVar, Arm.iZero, Arm.iShl, Arm.iInc, Arm.iRes, Arm.rrr, Arm.cmp, Arm.cset, Arm.T, armStep,
    AState.rd, setX_x, AState.setSub, Op.eval, cond_cs, cond_ge, cond_ne, lo_v, eq_v, slt_v, sub_zero_iff]

theorem inc_small (k : Nat) (hk : k < 11) (a : AState) : Upd a (runA [Arm.iInc k] a) (Arm.T k) (a.x (Arm.T k) + 1) := by
  intro j
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨
    k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 := by omega
  all_goals simp [runA, Arm.opCode, Arm.selCode, Arm.iVar, Arm.iZero, Arm.iShl, Arm.iInc, Arm.iRes, Arm.rrr, Arm.cmp, Arm.cset, Arm.T, armStep,
    AState.rd, setX_x, AState.setSub, Op.eval, cond_cs, cond_ge, cond_ne, lo_v, eq_v, slt_v, sub_zero_iff]

theorem res_small (a : AState) : Upd a (runA [Arm.iRes] a) 0 (a.x 9) := by
  intro j; simp [runA, Arm.opCode, Arm.selCode, Arm.iVar, Arm.iZero, Arm.iShl, Arm.iInc, Arm.iRes, Arm.rrr, Arm.cmp, Arm.cset, Arm.T, armStep,
    AState.rd, setX_x, AState.setSub, Op.eval, cond_cs, cond_ge, cond_ne, lo_v, eq_v, slt_v, sub_zero_iff]

/-! ## Correctness of `gen` on the small machine -/

/-- the registers `gen e k` may write are `T k ..` -/
def Keep (k : Nat) (a a' : AState) : Prop := ∀ j, (∀ i, k ≤ i → i < 11 → j ≠ Arm.T i) → a'.x j = a.x j

theorem Upd.keep {a a' : AState} {k : Nat} {v : BitVec 64} (h : Upd a a' (Arm.T k) v) (hk : k < 11) : Keep k a a' :=
  fun j hj => by rw [h j, if_neg (hj k (Nat.le_refl _) hk)]

theorem Keep.trans {k k' : Nat} {a₁ a₂ a₃ : AState} (h₁ : Keep k a₁ a₂) (h₂ : Keep k' a₂ a₃) (hk : k ≤ k') : Keep k a₁ a₃ :=
  fun j hj => by rw [h₂ j (fun i hi => hj i (by omega)), h₁ j hj]

theorem shl_ofNat (m : Nat) : BitVec.ofNat 64 m + BitVec.ofNat 64 m = BitVec.ofNat 64 (2 * m) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

theorem inc_ofNat (m : Nat) : BitVec.ofNat 64 m + 1 = BitVec.ofNat 64 (m + 1) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem const_small (k : Nat) (hk : k < 11) : ∀ (n : Nat) (a : AState),
    (runA (Arm.genConst k n) a).x (Arm.T k) = BitVec.ofNat 64 n ∧ Keep k a (runA (Arm.genConst k n) a) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro a
  rw [Arm.genConst]
  by_cases hn : n = 0
  · subst hn; simp only [↓reduceIte]
    have h := zero_small k hk a
    exact ⟨by rw [h]; simp, h.keep hk⟩
  · simp only [hn, ↓reduceIte, runA_append]
    obtain ⟨v₁, k₁⟩ := ih (n / 2) (by omega) a
    have h₂ := shl_small k hk (runA (Arm.genConst k (n / 2)) a)
    rw [v₁, shl_ofNat] at h₂
    by_cases hodd : n % 2 = 1
    · simp only [hodd, ↓reduceIte]
      have h₃ := inc_small k hk (runA [Arm.iShl k] (runA (Arm.genConst k (n / 2)) a))
      rw [h₂, if_pos rfl, inc_ofNat] at h₃
      refine ⟨by rw [h₃, if_pos rfl]; congr 1; omega, (k₁.trans (h₂.keep hk) (Nat.le_refl _)).trans (h₃.keep hk) (Nat.le_refl _)⟩
    · simp only [hodd, ↓reduceIte]
      rw [runA_nil]
      refine ⟨by rw [h₂, if_pos rfl]; congr 1; omega, k₁.trans (h₂.keep hk) (Nat.le_refl _)⟩

theorem T_ne {i j : Nat} (hij : i < j) (hj : j < 11) : Arm.T j ≠ Arm.T i := fun h => by
  have := T_inj j hj i (by omega) h; omega

theorem gen_small (env : Fin 4 → BitVec 64) : ∀ (e : Exp) (k : Nat) (a : AState), k + e.depth < 11 →
    (∀ i : Fin 4, a.x i = env i) → (runA (Arm.gen e k) a).x (Arm.T k) = e.denote env ∧ Keep k a (runA (Arm.gen e k) a)
  | .var i, k, a, hk, henv => by
    simp only [Arm.gen, Exp.denote, Exp.depth] at *
    have h := var_small i k i.2 (by omega) a
    exact ⟨by rw [h, if_pos rfl, henv], h.keep (by omega)⟩
  | .const c, k, a, hk, henv => by
    simp only [Arm.gen, Exp.denote, Exp.depth] at *
    obtain ⟨v, kp⟩ := const_small k (by omega) c.toNat a
    exact ⟨by rw [v, BitVec.ofNat_toNat, BitVec.setWidth_eq], kp⟩
  | .bin op x y, k, a, hk, henv => by
    simp only [Arm.gen, Exp.depth, Exp.denote, runA_append] at *
    obtain ⟨v₁, k₁⟩ := gen_small env x k a (by omega) henv
    have henv₁ : ∀ i : Fin 4, (runA (Arm.gen x k) a).x i = env i := fun i => by
      rw [k₁ i (fun j _ hj h => T_ne_A j hj i i.2 h.symm), henv]
    obtain ⟨v₂, k₂⟩ := gen_small env y (k + 1) _ (by omega) henv₁
    have h₃ := op_small op k (by omega) (runA (Arm.gen y (k + 1)) (runA (Arm.gen x k) a))
    refine ⟨by rw [h₃, if_pos rfl, v₂, k₂ _ (fun i hi hi' h => T_ne (by omega) hi' h.symm), v₁],
      (k₁.trans k₂ (by omega)).trans (h₃.keep (by omega)) (Nat.le_refl _)⟩
  | .ite c x y, k, a, hk, henv => by
    simp only [Arm.gen, Exp.depth, Exp.denote, runA_append] at *
    obtain ⟨v₁, k₁⟩ := gen_small env c k a (by omega) henv
    have keepA : ∀ {k a a'}, Keep k a a' → (∀ i : Fin 4, a.x i = env i) → ∀ i : Fin 4, a'.x i = env i :=
      fun kp he i => by rw [kp i (fun j _ hj h => T_ne_A j hj i i.2 h.symm), he]
    obtain ⟨v₂, k₂⟩ := gen_small env x (k + 1) _ (by omega) (keepA k₁ henv)
    obtain ⟨v₃, k₃⟩ := gen_small env y (k + 2) _ (by omega) (keepA k₂ (keepA k₁ henv))
    have h₄ := sel_small k (by omega) (runA (Arm.gen y (k + 2)) (runA (Arm.gen x (k + 1)) (runA (Arm.gen c k) a)))
    refine ⟨?_, ((k₁.trans k₂ (by omega)).trans k₃ (by omega)).trans (h₄.keep (by omega)) (Nat.le_refl _)⟩
    rw [h₄, if_pos rfl, v₃, k₃ _ (fun i hi hi' h => T_ne (by omega) hi' h.symm),
      k₃ _ (fun i hi hi' h => T_ne (by omega) hi' h.symm), k₂ _ (fun i hi hi' h => T_ne (by omega) hi' h.symm), v₁, v₂]

/-! ## Every word of `gen` is in `emitted` -/

theorem var_mem : ∀ i < 4, ∀ k < 11, Arm.iVar i k ∈ emitted := by decide +kernel
theorem zero_mem : ∀ k < 11, Arm.iZero k ∈ emitted := by decide +kernel
theorem shl_mem : ∀ k < 11, Arm.iShl k ∈ emitted := by decide +kernel
theorem inc_mem : ∀ k < 11, Arm.iInc k ∈ emitted := by decide +kernel
theorem rrr_mem_0 : ∀ k < 10, Arm.rrr 0x8B000000 (Arm.T k) (Arm.T k) (Arm.T (k + 1)) ∈ emitted := by decide +kernel
theorem rrr_mem_1 : ∀ k < 10, Arm.rrr 0xCB000000 (Arm.T k) (Arm.T k) (Arm.T (k + 1)) ∈ emitted := by decide +kernel
theorem rrr_mem_2 : ∀ k < 10, Arm.rrr 0x8A000000 (Arm.T k) (Arm.T k) (Arm.T (k + 1)) ∈ emitted := by decide +kernel
theorem rrr_mem_3 : ∀ k < 10, Arm.rrr 0xAA000000 (Arm.T k) (Arm.T k) (Arm.T (k + 1)) ∈ emitted := by decide +kernel
theorem rrr_mem_4 : ∀ k < 10, Arm.rrr 0xCA000000 (Arm.T k) (Arm.T k) (Arm.T (k + 1)) ∈ emitted := by decide +kernel
theorem rrr_mem_5 : ∀ k < 10, Arm.rrr 0x9AC02000 (Arm.T k) (Arm.T k) (Arm.T (k + 1)) ∈ emitted := by decide +kernel
theorem rrr_mem_6 : ∀ k < 10, Arm.rrr 0x9AC02400 (Arm.T k) (Arm.T k) (Arm.T (k + 1)) ∈ emitted := by decide +kernel
theorem rrr_mem_7 : ∀ k < 10, Arm.rrr 0x9AC02800 (Arm.T k) (Arm.T k) (Arm.T (k + 1)) ∈ emitted := by decide +kernel
theorem cmp_mem : ∀ k < 10, Arm.cmp k ∈ emitted := by decide +kernel
theorem cset_mem_1 : ∀ k < 10, Arm.cset 1 k ∈ emitted := by decide +kernel
theorem cset_mem_2 : ∀ k < 10, Arm.cset 2 k ∈ emitted := by decide +kernel
theorem cset_mem_10 : ∀ k < 10, Arm.cset 10 k ∈ emitted := by decide +kernel
theorem op_mem (op : Op) (k : Nat) (hk : k < 10) : ∀ w ∈ Arm.opCode op k, w ∈ emitted := by
  intro w hw
  cases op <;> simp only [Arm.opCode, List.mem_cons, List.not_mem_nil, or_false] at hw <;> rcases hw with rfl | rfl
  · exact rrr_mem_0 k hk
  · exact rrr_mem_1 k hk
  · exact rrr_mem_2 k hk
  · exact rrr_mem_3 k hk
  · exact rrr_mem_4 k hk
  · exact rrr_mem_5 k hk
  · exact rrr_mem_6 k hk
  · exact rrr_mem_7 k hk
  · exact cmp_mem k hk
  · exact cset_mem_2 k hk
  · exact cmp_mem k hk
  · exact cset_mem_10 k hk
  · exact cmp_mem k hk
  · exact cset_mem_1 k hk
theorem cmp0_mem : ∀ k < 9, BitVec.ofNat 32 (0xF100001F ||| Arm.T k <<< 5) ∈ emitted := by decide +kernel
theorem csel_mem : ∀ k < 9, Arm.rrr 0x9A801000 (Arm.T k) (Arm.T (k + 1)) (Arm.T (k + 2)) ∈ emitted := by decide +kernel
theorem sel_mem (k : Nat) (hk : k < 9) : ∀ w ∈ Arm.selCode k, w ∈ emitted := by
  intro w hw
  simp only [Arm.selCode, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact cmp0_mem k hk
  · exact csel_mem k hk
theorem res_mem : Arm.iRes ∈ emitted := by decide +kernel

theorem const_mem (k : Nat) (hk : k < 11) : ∀ n, ∀ w ∈ Arm.genConst k n, w ∈ emitted := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro w hw
  rw [Arm.genConst] at hw
  split at hw
  · simp at hw; subst hw; exact zero_mem k hk
  · simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with (hw | rfl) | hw
    · exact ih (n / 2) (by omega) w hw
    · exact shl_mem k hk
    · split at hw <;> simp at hw; subst hw; exact inc_mem k hk

theorem gen_mem : ∀ (e : Exp) (k : Nat), k + e.depth < 11 → ∀ w ∈ Arm.gen e k, w ∈ emitted
  | .var i, k, hk, w, hw => by
    simp only [Arm.gen, Exp.depth, List.mem_singleton] at hk hw; subst hw; exact var_mem i i.2 k (by omega)
  | .const c, k, hk, w, hw => by simp only [Arm.gen, Exp.depth] at hk hw; exact const_mem k (by omega) _ w hw
  | .bin op x y, k, hk, w, hw => by
    simp only [Arm.gen, Exp.depth, List.mem_append] at hk hw
    rcases hw with (hw | hw) | hw
    · exact gen_mem x k (by omega) w hw
    · exact gen_mem y (k + 1) (by omega) w hw
    · exact op_mem op k (by omega) w hw
  | .ite c x y, k, hk, w, hw => by
    simp only [Arm.gen, Exp.depth, List.mem_append] at hk hw
    rcases hw with ((hw | hw) | hw) | hw
    · exact gen_mem c k (by omega) w hw
    · exact gen_mem x (k + 1) (by omega) w hw
    · exact gen_mem y (k + 2) (by omega) w hw
    · exact sel_mem k (by omega) w hw

/-! ## The theorem -/

theorem ofBool_beq_one (b : BitVec 1) : BitVec.ofBool (b == 1#1) = b := by
  have : b = 0#1 ∨ b = 1#1 := by
    have := b.isLt
    rcases (show b.toNat = 0 ∨ b.toNat = 1 by omega) with h | h
    · exact .inl (BitVec.eq_of_toNat_eq h)
    · exact .inr (BitVec.eq_of_toNat_eq h)
  rcases this with rfl | rfl <;> rfl

/-- **L3, backend correctness at the decode+execute layer.** From any model state with
`SPESampleInFlight = false` (`ArmCfg`), all of `X0..X30` and PSTATE present, and `X0..X3 = env`, running the words of
`Arm.gen e 0 ++ [Arm.iRes]` (all of `Arm.compile e` except the final `ret`) through `__DecodeA64` in order, with
`SEE := -1` before each, succeeds and ends with `X0 = e.denote env`; memory and every register other than
`X0..X30`, PSTATE, SEE are unchanged, and so are the `X` registers outside `x0` and the temporaries `x4..x7, x9..x15`.
This is the decode+execute layer: it does not include instruction fetch from memory, PC update, interrupts or `ret`. -/
theorem compile_ok_exec (e : Exp) (he : e.depth < 11) (env : Fin 4 → BitVec 64) (pc : Int) (s : St)
    (hc : ArmCfg s) (hx : ∀ i < 31, (xget s.regs i).isSome) (hp : (s.regs.get? .PSTATE).isSome)
    (henv : ∀ i : Fin 4, xget s.regs i = some (env i)) :
    ∃ s', RunM pc (Arm.gen e 0 ++ [Arm.iRes]) s s' ∧ xget s'.regs 0 = some (e.denote env) ∧
      (∀ j < 31, (∀ i < 11, j ≠ Arm.T i) → j ≠ 0 → xget s'.regs j = xget s.regs j) ∧ ArmCfg s' ∧ Frame s s' := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hp
  let a : AState := ⟨fun i => (xget s.regs i).getD 0, p.N == 1#1, p.Z == 1#1, p.C == 1#1, p.V == 1#1⟩
  have hxa : ∀ i < 31, xget s.regs i = some (a.x i) := fun i hi => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hx i hi); simp [a, hv]
  have ha : Abs s a := ⟨hxa, p, hp, (ofBool_beq_one _).symm, (ofBool_beq_one _).symm, (ofBool_beq_one _).symm,
    (ofBool_beq_one _).symm⟩
  have hmem : ∀ w ∈ Arm.gen e 0 ++ [Arm.iRes], w ∈ emitted := fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · exact gen_mem e 0 (by omega) w hw
    · rw [List.mem_singleton.mp hw]; exact res_mem
  obtain ⟨s', hr, ha', hc', hf⟩ := run_sim _ pc s a hmem hc ha
  have henv' : ∀ i : Fin 4, a.x i = env i := fun i => by
    have := (hxa i (by omega)).symm.trans (henv i); exact Option.some.inj this
  obtain ⟨v, kp⟩ := gen_small env e 0 a (by omega) henv'
  have hres := res_small (runA (Arm.gen e 0) a)
  rw [runA_append] at ha'
  refine ⟨s', hr, ?_, fun j hj hT h0 => ?_, hc', hf⟩
  · rw [ha'.x 0 (by decide), hres, if_pos rfl, show (9 : Nat) = Arm.T 0 from rfl, v]
  · rw [ha'.x j hj, hres, if_neg h0, kp j (fun i _ hi h => hT i hi h), hxa j hj]

end ArmProof
