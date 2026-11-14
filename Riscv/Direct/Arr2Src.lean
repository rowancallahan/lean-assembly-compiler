/- Source-level tools for `BStmt` (no machine): loops via invariant + measure, variables a program
never assigns are kept, value lemmas for `ofNat` arithmetic. -/
import Riscv.Direct.Arr2Code

namespace Proven

theorem BExec.loop_inv {c : BExp} {b : BStmt} (I Q : BState → Prop) (μ : BState → Nat)
    (hstep : ∀ σ, I σ → c.denote σ.env ≠ 0 → ∃ σ₁, BExec b σ σ₁ ∧ I σ₁ ∧ μ σ₁ < μ σ)
    (hexit : ∀ σ, I σ → c.denote σ.env = 0 → Q σ) : ∀ σ, I σ → ∃ σ', BExec (.loop c b) σ σ' ∧ Q σ' := by
  intro σ
  induction h : μ σ using Nat.strongRecOn generalizing σ with
  | ind n ih =>
    intro hI
    by_cases hc : c.denote σ.env = 0
    · exact ⟨σ, .loopF hc, hexit σ hI hc⟩
    · obtain ⟨σ₁, hb, hI₁, hlt⟩ := hstep σ hI hc
      obtain ⟨σ', hl, hQ⟩ := ih _ (h ▸ hlt) σ₁ rfl hI₁
      exact ⟨σ', .loopT hc hb hl, hQ⟩

def BStmt.assigns : BStmt → List Nat
  | .assign v _ | .load v _ _ => [v]
  | .store .. => []
  | .seq p q => p.assigns ++ q.assigns
  | .loop _ b => b.assigns

theorem BExec.env_keep {p : BStmt} {σ σ' : BState} (h : BExec p σ σ') {v : Nat} (hv : v ∉ p.assigns) :
    σ'.env v = σ.env v := by
  induction h with
  | assign => simp only [BStmt.assigns, List.mem_singleton] at hv; simp [BEnv.set, hv]
  | load => simp only [BStmt.assigns, List.mem_singleton] at hv; simp [BEnv.set, hv]
  | store => rfl
  | seq _ _ ih1 ih2 =>
    simp only [BStmt.assigns, List.mem_append, not_or] at hv; rw [ih2 hv.2, ih1 hv.1]
  | loopF => rfl
  | loopT _ _ _ ih1 ih2 => simp only [BStmt.assigns] at ih1 hv ih2; rw [ih2 hv, ih1 hv]

theorem BExec.heap_length {p : BStmt} {σ σ' : BState} (h : BExec p σ σ') : σ'.heap.length = σ.heap.length := by
  induction h with
  | store => simp
  | seq _ _ ih1 ih2 => rw [ih2, ih1]
  | loopT _ _ _ ih1 ih2 => rw [ih2, ih1]
  | _ => rfl

/-- `load`/`store`/`assign` with the block and index given by equations (no dependent indexing) -/
theorem BExec.load' {v b : Nat} {i : BExp} {σ : BState} {B : List (BitVec 8)} {j : Nat} {x : BitVec 8}
    (hb : σ.heap[b]? = some B) (hj : (i.denote σ.env).toNat = j) (hx : B[j]? = some x) :
    BExec (.load v b i) σ ⟨σ.env.set v (x.setWidth 64), σ.heap⟩ := by
  have hb' : b < σ.heap.length := by
    rcases Nat.lt_or_ge b σ.heap.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hb; cases hb
  have e1 : σ.heap[b] = B := by rw [List.getElem?_eq_getElem hb'] at hb; exact Option.some.inj hb
  have hj' : j < B.length := by
    rcases Nat.lt_or_ge j B.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; cases hx
  have e2 : B[j] = x := by rw [List.getElem?_eq_getElem hj'] at hx; exact Option.some.inj hx
  have := BExec.load (v := v) hb' (i := i) (by rw [hj, e1]; exact hj')
  subst e1; subst hj; rwa [e2] at this

theorem BExec.store' {b : Nat} {i e : BExp} {σ : BState} {B : List (BitVec 8)} {j : Nat}
    (hb : σ.heap[b]? = some B) (hj : (i.denote σ.env).toNat = j) (hjl : j < B.length) :
    BExec (.store b i e) σ ⟨σ.env, σ.heap.set b (B.set j ((e.denote σ.env).setWidth 8))⟩ := by
  have hb' : b < σ.heap.length := by
    rcases Nat.lt_or_ge b σ.heap.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hb; cases hb
  have e1 : σ.heap[b] = B := by rw [List.getElem?_eq_getElem hb'] at hb; exact Option.some.inj hb
  have := BExec.store (e := e) hb' (i := i) (by rw [hj, e1]; exact hjl)
  subst e1; subst hj; exact this

theorem BExec.assign' {v : Nat} {e : BExp} {σ σ' : BState} (h : σ' = ⟨σ.env.set v (e.denote σ.env), σ.heap⟩) :
    BExec (.assign v e) σ σ' := h ▸ .assign

/-- the state after `v := e` -/
def BState.asg (σ : BState) (v : Nat) (e : BExp) : BState := ⟨σ.env.set v (e.denote σ.env), σ.heap⟩

theorem BExec.asg {v : Nat} {e : BExp} {σ : BState} : BExec (.assign v e) σ (σ.asg v e) := .assign
@[simp] theorem BState.asg_heap (σ : BState) (v : Nat) (e : BExp) : (σ.asg v e).heap = σ.heap := rfl
@[simp] theorem BState.asg_env (σ : BState) (v : Nat) (e : BExp) (j : Nat) :
    (σ.asg v e).env j = if j = v then e.denote σ.env else σ.env j := rfl

/-! ## Values -/

theorem ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    Op.eval .ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = if a < b then 1 else 0 := by
  simp only [Op.eval]; congr 1; apply propext
  rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem add_ofNat (a b : Nat) : Op.eval .add (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

theorem ite01_eq0 (p : Prop) [Decidable p] : ((if p then 1 else 0 : BitVec 64) = 0) ↔ ¬p := by
  by_cases hp : p <;> simp [hp]

theorem xor01 (p : Prop) [Decidable p] : Op.eval .xor (if p then 1 else 0 : BitVec 64) 1 = if ¬p then 1 else 0 := by
  by_cases hp : p <;> simp [hp, Op.eval]

theorem toNat_ofNat' {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

end Proven
