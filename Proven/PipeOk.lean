/- What compiles: a decidable syntactic condition `Pipe.ok` that implies `compileP` succeeds
(`compileP_of_ok`).  `Pipe.ok p`: every stage passes `Stage.chk` (take/drop counts `< 2^64`), every
map/fold expression translates to depth `≤ 6` (`BExp.tr_depth_le`: nesting height `≤ 3` is enough for byte
expressions), and the total expression size `Pipe.cost p` (a bound on the words of all map/fold
expressions) is `≤ 950`, so every loop body is within the `beq` range. -/
import Proven.PipeMachine

set_option linter.unusedVariables false

namespace Proven

/-! ## Code size of expressions -/

theorem genConst_len : ∀ (b n k : Nat), n < 2 ^ b → (genConst k n).length ≤ 2 * b + 1
  | 0, n, k, h => by
    have : n = 0 := by simpa using h
    subst this; rw [genConst]; simp
  | b + 1, n, k, h => by
    rw [genConst]
    split
    · simp
    · have := genConst_len b (n / 2) k (by rw [Nat.pow_succ] at h; omega)
      simp only [List.length_append, List.length_singleton]
      split <;> simp <;> omega

theorem opCode_len (op : Op) (k : Nat) : (opCode op k).length ≤ 2 := by
  unfold opCode; split <;> simp

/-- a bound on the number of words of `e.tr` -/
def BExp.size : BExp → Nat
  | .x | .acc => 1
  | .lit _ => 17
  | .bin op a b => a.size + b.size + (if op = .add ∨ op = .sub then 19 else 1)
  | .ite _ a b t e => a.size + b.size + t.size + e.size + 7

theorem BExp.gen_len : ∀ (e : BExp) (k : Nat), (gen8 e.tr k).length ≤ e.size
  | .x, k => by simp [BExp.tr, gen8, BExp.size]
  | .acc, k => by simp [BExp.tr, gen8, BExp.size]
  | .lit c, k => by
    simp only [BExp.tr, gen8, BExp.size]
    exact genConst_len 8 _ k (by rw [zx_toNat]; exact c.toNat_lt)
  | .bin op a b, k => by
    have := BExp.gen_len a k; have := BExp.gen_len b (k + 1)
    have h255 := genConst_len 8 255 (k + 1) (by decide)
    cases op <;> simp [BExp.tr, mask8, gen8, BExp.size, opCode] <;> omega
  | .ite c a b t e, k => by
    have := BExp.gen_len a k; have := BExp.gen_len b (k + 1)
    have := BExp.gen_len b k; have := BExp.gen_len a (k + 1)
    have := BExp.gen_len t (k + 1); have := BExp.gen_len e (k + 2)
    have := BExp.gen_len e (k + 1); have := BExp.gen_len t (k + 2)
    cases c <;> simp [BExp.tr, gen8, BExp.size, opCode, selCode] <;> omega

def BExp.height : BExp → Nat
  | .x | .acc | .lit _ => 0
  | .bin _ a b => max a.height b.height + 1
  | .ite _ a b t e => max (max a.height b.height) (max t.height e.height) + 1

/-- temporaries needed by a byte expression: at most twice its nesting height (plus the result) -/
theorem BExp.tr_depth_le : ∀ e : BExp, e.tr.depth ≤ 2 * e.height
  | .x => by simp [BExp.tr, AExp.depth]
  | .acc => by simp [BExp.tr, AExp.depth]
  | .lit c => by simp [BExp.tr, AExp.depth]
  | .bin op a b => by
    have := BExp.tr_depth_le a; have := BExp.tr_depth_le b
    cases op <;> simp only [BExp.tr, mask8, AExp.depth, BExp.height] <;> omega
  | .ite c a b t e => by
    have := BExp.tr_depth_le a; have := BExp.tr_depth_le b
    have := BExp.tr_depth_le t; have := BExp.tr_depth_le e
    cases c <;> simp only [BExp.tr, AExp.depth, BExp.height] <;> omega

/-- a bound on the number of words of `w.tr` -/
def WExp.size : WExp → Nat
  | .acc | .x => 1
  | .const _ => 129
  | .bin _ a b => a.size + b.size + 2
  | .ite c a b => c.size + a.size + b.size + 5

theorem WExp.gen_len : ∀ (w : WExp) (k : Nat), (gen8 w.tr k).length ≤ w.size
  | .acc, k => by simp [WExp.tr, gen8, WExp.size]
  | .x, k => by simp [WExp.tr, gen8, WExp.size]
  | .const c, k => by
    simp only [WExp.tr, gen8, WExp.size]
    exact genConst_len 64 _ k c.isLt
  | .bin op a b, k => by
    have := WExp.gen_len a k; have := WExp.gen_len b (k + 1); have := opCode_len op k
    simp only [WExp.tr, gen8, WExp.size, List.length_append]; omega
  | .ite c a b, k => by
    have := WExp.gen_len c k; have := WExp.gen_len a (k + 1); have := WExp.gen_len b (k + 2)
    simp [WExp.tr, gen8, WExp.size, selCode]; omega

/-! ## The condition -/

def Stage.cost : Stage → Nat
  | .map e => e.size + 1
  | .fold e _ => e.size
  | .foldW w _ => w.size
  | _ => 0

def Stage.shallow : Stage → Bool
  | .map e | .fold e _ => decide (e.tr.depth ≤ 6)
  | .foldW w _ => decide (w.tr.depth ≤ 6)
  | _ => true

def Pipe.cost : Pipe → Nat
  | [] => 0
  | st :: r => st.cost + Pipe.cost r

/-- **what compiles**: stage checks pass, expressions are shallow, total expression size `≤ 950` words -/
def Pipe.ok (p : Pipe) : Bool :=
  p.all (fun st => st.chk.isNone && st.shallow) && decide (Pipe.cost p ≤ 950)

/-! ## Well-formedness of the generated statements -/

abbrev bv2 : List (Fin 8) := [0, 3]

def gsW : List AExp → Nat
  | [] => 0
  | g :: gs => (gen8 g 0).length + 1 + gsW gs

theorem gsW_append (a b : List AExp) : gsW (a ++ b) = gsW a + gsW b := by
  induction a with
  | nil => simp [gsW]
  | cons g gs ih => simp [gsW, ih]; omega

theorem fetchG_len : ∀ (gs : List AExp) (p : AStmt),
    (compileA bv2 (fetchG p gs)).length = (compileA bv2 p).length + gsW gs
  | [], p => by simp [fetchG, gsW]
  | g :: gs, p => by simp [fetchG, gsW, fetchG_len gs, compileA]; omega

theorem fetchG_wf : ∀ (gs : List AExp) (p : AStmt), p.wf bv2 → (∀ g ∈ gs, g.depth < 7) → (fetchG p gs).wf bv2
  | [], p, hp, _ => hp
  | g :: gs, p, hp, hg =>
    fetchG_wf gs _ ⟨hp, hg g (List.mem_cons_self ..), by decide⟩ fun g' h => hg g' (List.mem_cons_of_mem _ h)

theorem wf_of_err {p : AStmt} (h : wfErr bv2 p = none) : p.wf bv2 := (wfErr_iff _ _).1 h

theorem fetch_wf (cs : CS) (hg : ∀ g ∈ cs.gs, g.depth < 7) :
    (fetch cs).wf bv2 ∧ (compileA bv2 (fetch cs)).length ≤ 14 + gsW cs.gs := by
  obtain ⟨a, b, c, gs⟩ := cs
  refine ⟨fetchG_wf _ _ ?_ hg, ?_⟩
  · cases a <;> cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      exact wf_of_err (by decide +kernel)
  · simp only [fetch, fetchG_len]
    have : (compileA bv2 (.load 6 (if a = true then 1 else 0) (vIdx b))).length ≤ 14 := by
      cases a <;> cases b <;> decide +kernel
    omega

theorem loopV_wf {c : Fin 8} (hc : c = 1 ∨ c = 7) {body : AStmt} (hb : body.wf bv2)
    (hl : (compileA bv2 body).length ≤ 1000) : (loopV c body).wf bv2 := by
  have h1 : (gen8 (.bin .ult (.var 2) (.var c)) 0).length = 3 := by simp [gen8, opCode]
  have h2 : (compileA bv2 (.assign 2 (.bin .add (.var 2) (.const 1)))).length = 6 := by decide +kernel
  refine ⟨⟨by simp [AExp.depth], by decide⟩, by simp [AExp.depth], ⟨hb, by simp [AExp.depth], by decide⟩, ?_⟩
  rw [h1, compileA, List.length_append, h2]; omega

theorem revC_wf : ∀ s ∈ revC, s.wf bv2 := by
  intro s hs
  simp only [revC, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> exact wf_of_err (by decide +kernel)

theorem assign_const_wf (v : Fin 8) (hv : v ∉ bv2) (c : BitVec 64) : (AStmt.assign v (.const c)).wf bv2 :=
  ⟨by simp [AExp.depth], hv⟩

theorem mat_wf (cs : CS) (hg : ∀ g ∈ cs.gs, g.depth < 7) (hW : gsW cs.gs ≤ 950) : ∀ s ∈ mat cs, s.wf bv2 := by
  intro s hs
  unfold mat at hs
  split at hs
  · simp at hs
  · have hf := fetch_wf { cs with rev := cs.rev && !cs.onOut } hg
    have hst : (AStmt.store 1 (.var 2) (.var 6)).wf bv2 ∧ (compileA bv2 (.store 1 (.var 2) (.var 6))).length = 5 :=
      ⟨wf_of_err (by decide +kernel), by decide +kernel⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with hs | rfl | rfl
    · split at hs
      · exact revC_wf s hs
      · simp at hs
    · refine loopV_wf (.inl rfl) ⟨hf.1, hst.1⟩ ?_
      rw [compileA, List.length_append, hst.2]; have := hf.2; dsimp only at this; omega
    · exact assign_const_wf 4 (by decide) _

theorem emitC_wf (k : Nat) : ∀ s ∈ emitC k, s.wf bv2 := by
  intro s hs
  simp only [emitC, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact assign_const_wf 1 (by decide) _
  · exact wf_of_err (by decide +kernel)
  · exact assign_const_wf 4 (by decide) _

theorem foldC_wf (cs : CS) (hg : ∀ g ∈ cs.gs, g.depth < 7) (S : AExp) (hS : S.depth ≤ 6) (init : BitVec 64)
    (k : Nat) (hW : gsW cs.gs + (gen8 S 0).length ≤ 950) : ∀ s ∈ foldC cs S init k, s.wf bv2 := by
  intro s hs
  simp only [foldC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
  have hf := fetch_wf cs hg
  rcases hs with (rfl | rfl) | hs
  · exact assign_const_wf 5 (by decide) _
  · refine loopV_wf (.inl rfl) ⟨hf.1, by omega, by decide⟩ ?_
    simp only [compileA, List.length_append, List.length_singleton]; have := hf.2; omega
  · exact emitC_wf k s hs

theorem insProg_wf : insProg.wf bv2 := sortProg_wf.2.2

theorem minE_depth (n : Nat) : (minE n).depth = 2 := by simp [minE, AExp.depth]

theorem stage_wf (st : Stage) (cs : CS) (hs : st.shallow = true) (hg : ∀ g ∈ cs.gs, g.depth < 7)
    (hW : gsW cs.gs + st.cost ≤ 950) :
    (∀ s ∈ (stageC st cs).1, s.wf bv2) ∧ (∀ g ∈ (stageC st cs).2.gs, g.depth < 7) ∧
      gsW (stageC st cs).2.gs ≤ gsW cs.gs + st.cost := by
  cases st with
  | map e =>
    simp only [Stage.shallow, decide_eq_true_eq] at hs
    refine ⟨by simp [stageC], fun g hgm => ?_, ?_⟩
    · simp only [stageC, List.mem_append, List.mem_singleton] at hgm
      rcases hgm with h | rfl
      · exact hg g h
      · omega
    · have := BExp.gen_len e 0
      simp only [stageC, gsW_append, gsW, Stage.cost]; omega
  | reverse => exact ⟨by simp [stageC], hg, by simp [stageC]⟩
  | take n =>
    simp only [stageC]
    split
    · refine ⟨fun s hs => ?_, hg, by simp⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> simp [AStmt.wf, AExp.depth, minE_depth]
    · refine ⟨fun s hs => ?_, hg, by simp⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs; simp [AStmt.wf, minE_depth]
  | drop n =>
    simp only [stageC]
    split
    · refine ⟨fun s hs => ?_, hg, by simp⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs; simp [AStmt.wf, AExp.depth, minE_depth]
    · refine ⟨fun s hs => ?_, hg, by simp⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> simp [AStmt.wf, AExp.depth, minE_depth]
  | sort =>
    refine ⟨fun s hs => ?_, by simp [stageC, csClean], by simp [stageC, csClean, gsW]⟩
    simp only [stageC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with hs | rfl | rfl
    · exact mat_wf cs hg (by omega) s hs
    · exact insProg_wf
    · exact assign_const_wf 4 (by decide) _
  | fold e i =>
    simp only [Stage.shallow, decide_eq_true_eq] at hs
    have := BExp.gen_len e 0
    exact ⟨foldC_wf cs hg _ hs _ _ (by simp only [Stage.cost] at hW; omega), by simp [stageC, csClean],
      by simp [stageC, csClean, gsW]⟩
  | foldW w i =>
    simp only [Stage.shallow, decide_eq_true_eq] at hs
    have := WExp.gen_len w 0
    exact ⟨foldC_wf cs hg _ hs _ _ (by simp only [Stage.cost] at hW; omega), by simp [stageC, csClean],
      by simp [stageC, csClean, gsW]⟩

theorem stmts_wf : ∀ (p : Pipe) (cs : CS), (∀ st ∈ p, st.shallow = true) → (∀ g ∈ cs.gs, g.depth < 7) →
    gsW cs.gs + Pipe.cost p ≤ 950 → ∀ s ∈ stmts p cs, s.wf bv2
  | [], cs, _, hg, hW => mat_wf cs hg (by simp only [Pipe.cost] at hW; omega)
  | st :: r, cs, hs, hg, hW => by
    simp only [Pipe.cost] at hW
    obtain ⟨h1, h2, h3⟩ := stage_wf st cs (hs st (List.mem_cons_self ..)) hg (by omega)
    intro s hm
    simp only [stmts, List.mem_append] at hm
    rcases hm with hm | hm
    · exact h1 s hm
    · exact stmts_wf r _ (fun s' h => hs s' (List.mem_cons_of_mem _ h)) h2 (by omega) s hm

theorem foldl_seq_wf : ∀ (l : List AStmt) (a : AStmt), a.wf bv2 → (∀ s ∈ l, s.wf bv2) → (l.foldl .seq a).wf bv2
  | [], a, ha, _ => ha
  | b :: l, a, ha, hl =>
    foldl_seq_wf l _ ⟨ha, hl b (List.mem_cons_self ..)⟩ fun s h => hl s (List.mem_cons_of_mem _ h)

theorem Pipe.chkErr_of : ∀ {p : Pipe}, (∀ st ∈ p, st.chk = none) → Pipe.chkErr p = none
  | [], _ => rfl
  | st :: r, h => by
    simp only [Pipe.chkErr, h st (List.mem_cons_self ..)]
    exact Pipe.chkErr_of fun s hs => h s (List.mem_cons_of_mem _ hs)

/-- **`Pipe.ok` pipes compile.** -/
theorem compileP_of_ok {p : Pipe} (h : Pipe.ok p = true) : ∃ code, compileP p = .ok code := by
  simp only [Pipe.ok, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
  have hc := Pipe.chkErr_of fun st hs => (h.1 st hs).1
  have hw : wfErr bv2 (Pipe.prog p) = none := (wfErr_iff _ _).2
    (foldl_seq_wf _ _ (assign_const_wf 4 (by decide) _)
      (stmts_wf p cs0 (fun st hs => (h.1 st hs).2) (by simp [cs0]) (by simp only [cs0, gsW]; omega)))
  exact ⟨compileAF [0, 3] (Pipe.prog p), by simp only [compileP, hc, hw]⟩

/-! ## Pipes without `sort`/`fold` need exactly the result size -/

def Stage.isView : Stage → Bool
  | .map _ | .take _ | .drop _ | .reverse => true
  | _ => false

theorem Pipe.need_view : ∀ (p : Pipe) (cs : CS) (n : Nat), (∀ st ∈ p, st.isView = true) → cs.onOut = false →
    Pipe.need p cs n = Pipe.len p n
  | [], cs, n, _, hO => by simp [Pipe.need, Pipe.len, CS.clean, hO]
  | st :: r, cs, n, hv, hO => by
    have h1 := hv st (List.mem_cons_self ..)
    have ih := fun cs' h => Pipe.need_view r cs' (st.len n) (fun s hs => hv s (List.mem_cons_of_mem _ hs)) h
    cases st <;> simp only [Stage.isView, Bool.false_eq_true] at h1 <;>
      simp only [Pipe.need, Stage.space, Pipe.len, List.foldl_cons, Nat.zero_max] <;> apply ih <;>
      simp only [stageC] <;> (try split) <;> exact hO

/-- a `map`/`take`/`drop`/`reverse` pipe is an `ImplementsMapped`: output block of the result size -/
theorem compileP_view {p : Pipe} {code : List (BitVec 32)} (h : compileP p = .ok code)
    (hv : p.all Stage.isView = true) : ImplementsMapped code (Pipe.denote p) :=
  compileP_mapped h fun n => by
    rw [Pipe.space, Pipe.need_view p cs0 n (by simpa [List.all_eq_true] using hv) rfl]; exact Nat.le_refl _

end Proven
