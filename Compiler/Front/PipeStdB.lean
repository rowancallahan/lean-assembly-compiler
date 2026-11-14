/- The `XPipe` program in the statement language with spill slots (`BStmt`, `Riscv/Direct/Arr2Code.lean`), so
that `List.mergeSort` can use the proved O(n log n) bottom-up merge sort (`Riscv/Direct/SortMergeSrc.lean`),
which needs a scratch block and 7 spill slots.

Blocks: 0 = input (base `v0`), 1 = output (base `v3`), 2 = scratch (base `v2`): `bv = [0, 3, 2]`.
Every `AStmt` stage of `XPipe.prog` is reused with its variables renamed (`rn`): `a2` (the loop counter)
becomes `v7`, `a7` becomes the slot `v8`, the others stay; so `v2` keeps the scratch base.
A `sort` stage is: the view materialized to `out[0..m)` (as before), copied to `scr[0..m)`, then the merge
sort `scr → out` (`msortG 2 1 2`); a sort of the input itself (`cs0`) is `msortG 0 1 2` directly. -/
import Compiler.Front.PipeStdMachine
import Riscv.Direct.SortMergeMachine
import Riscv.Direct.Arr2F

set_option linter.unusedVariables false

namespace Proven

/-! ## Renaming `AStmt` into `BStmt` -/

def rn (i : Fin 8) : Nat := if i.val = 2 then 7 else if i.val = 7 then 8 else i.val

theorem rn_inj : ∀ {i j : Fin 8}, rn i = rn j → i = j := by decide
theorem rn_ne2 : ∀ i : Fin 8, rn i ≠ 2 := by decide
theorem rn_lt : ∀ i : Fin 8, rn i < 9 := by decide

def AExp.rB : AExp → BExp
  | .var i => .var (rn i)
  | .const c => .const c
  | .bin op a b => .bin op a.rB b.rB
  | .ite c a b => .ite c.rB a.rB b.rB

def AStmt.rB : AStmt → BStmt
  | .assign v e => .assign (rn v) e.rB
  | .load v b i => .load (rn v) b i.rB
  | .store b i e => .store b i.rB e.rB
  | .seq p q => .seq p.rB q.rB
  | .loop c b => .loop c.rB b.rB

/-- `τ` holds the `AState` `σ` (renamed), with extra blocks `X` after its blocks -/
def Corr (X : Heap) (σ : AState) (τ : BState) : Prop := (∀ i, τ.env (rn i) = σ.env i) ∧ τ.heap = σ.heap ++ X

theorem AExp.denote_rB {σ : AState} {τ : BState} (h : ∀ i, τ.env (rn i) = σ.env i) :
    ∀ e : AExp, e.rB.denote τ.env = e.denote σ.env
  | .var i => h i
  | .const c => rfl
  | .bin op a b => by simp only [AExp.rB, BExp.denote, AExp.denote, AExp.denote_rB h a, AExp.denote_rB h b]
  | .ite c a b => by
    simp only [AExp.rB, BExp.denote, AExp.denote, AExp.denote_rB h c, AExp.denote_rB h a, AExp.denote_rB h b]

theorem env_set_rB {σe : AEnv} {τe : BEnv} (h : ∀ i, τe (rn i) = σe i) (v : Fin 8) (x : BitVec 64) :
    ∀ i, (τe.set (rn v) x) (rn i) = (σe.set v x) i := by
  intro i
  simp only [BEnv.set, AEnv.set]
  by_cases hv : i = v
  · subst hv; simp
  · have : rn i ≠ rn v := fun e => hv (rn_inj e)
    simp [this, hv, h i]

/-- **Embedding with renaming**: a run of an `AStmt` is a run of its renamed `BStmt`; extra blocks and the
variables outside the image of `rn` are untouched -/
theorem AExec.rB {p : AStmt} {σ σ' : AState} (h : AExec p σ σ') :
    ∀ {X : Heap} {τ : BState}, Corr X σ τ →
    ∃ τ', BExec p.rB τ τ' ∧ Corr X σ' τ' ∧ ∀ j, (∀ i, rn i ≠ j) → τ'.env j = τ.env j := by
  induction h with
  | @assign v e σ =>
    intro X τ ⟨he, hh⟩
    refine ⟨_, .assign, ⟨fun i => ?_, hh⟩, fun j hj => ?_⟩
    · dsimp only; rw [AExp.denote_rB he]; exact env_set_rB he v _ i
    · simp only [BEnv.set, if_neg (Ne.symm (hj v))]
  | @load v b i σ hb hi =>
    intro X τ ⟨he, hh⟩
    have hg : τ.heap[b]? = some σ.heap[b] := by rw [hh, List.getElem?_append_left hb, List.getElem?_eq_getElem hb]
    refine ⟨_, BExec.load' hg (by rw [AExp.denote_rB he]) (List.getElem?_eq_getElem hi), ⟨fun j => ?_, hh⟩,
      fun j hj => ?_⟩
    · exact env_set_rB he v _ j
    · simp only [BEnv.set, if_neg (Ne.symm (hj v))]
  | @store b i e σ hb hi =>
    intro X τ ⟨he, hh⟩
    have hg : τ.heap[b]? = some σ.heap[b] := by rw [hh, List.getElem?_append_left hb, List.getElem?_eq_getElem hb]
    refine ⟨_, BExec.store' (e := e.rB) hg (by rw [AExp.denote_rB he]) hi, ⟨he, ?_⟩, fun j _ => rfl⟩
    dsimp only; rw [hh, List.set_append_left _ _ hb, AExp.denote_rB he]
  | seq _ _ ih1 ih2 =>
    intro X τ hc
    obtain ⟨τ₁, x1, c1, k1⟩ := ih1 hc
    obtain ⟨τ₂, x2, c2, k2⟩ := ih2 c1
    exact ⟨τ₂, .seq x1 x2, c2, fun j hj => (k2 j hj).trans (k1 j hj)⟩
  | loopF hc =>
    intro X τ hcr
    exact ⟨τ, .loopF (by rw [AExp.denote_rB hcr.1]; exact hc), hcr, fun _ _ => rfl⟩
  | loopT hc _ _ ih1 ih2 =>
    intro X τ hcr
    obtain ⟨τ₁, x1, c1, k1⟩ := ih1 hcr
    obtain ⟨τ₂, x2, c2, k2⟩ := ih2 c1
    exact ⟨τ₂, .loopT (by rw [AExp.denote_rB hcr.1]; exact hc) x1 x2, c2, fun j hj => (k2 j hj).trans (k1 j hj)⟩

end Proven
