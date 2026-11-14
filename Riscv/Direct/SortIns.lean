/- Insertion sort on a byte array, compiled by `compileA` and proved end to end:
the output block holds a sorted permutation of the input, hence `List.mergeSort`'s result.

Program (`sortProg`; block 0 = input at `a0`, length `a1`; block 1 = output at `a3`):
```
a2 := a1; mapProg (var 6)                 -- copy: out := in   (uses a4, a5, a6)
a2 := 0
while a2 < a1 {                           -- i = a2
  a5 := out[a2]; a4 := a2; a7 := 1        -- key, j, continue
  while a7 {
    a6 := out[a4 ≠ 0 ? a4 - 1 : 0]
    a7 := (0 < a4) & (a5 < a6)            -- shift?
    out[a4] := a7 ≠ 0 ? a6 : a5           -- shift a6 up, or drop the key into the hole
    a4 := a4 - a7
  }
  a2 := a2 + 1
}
```
The inner loop is branch-free: the store writes `key` into the hole when it stops. -/
import Riscv.Examples.ArrExamples

set_option linter.unusedVariables false

namespace Proven

/-! ## Generic: variables a program never assigns are kept -/

def AStmt.assigns : AStmt → List (Fin 8)
  | .assign v _ | .load v _ _ => [v]
  | .store .. => []
  | .seq p q => p.assigns ++ q.assigns
  | .loop _ b => b.assigns

theorem AExec.env_keep {p : AStmt} {σ σ' : AState} (h : AExec p σ σ') {v : Fin 8} (hv : v ∉ p.assigns) :
    σ'.env v = σ.env v := by
  induction h with
  | assign => simp only [AStmt.assigns, List.mem_singleton] at hv; simp [AEnv.set, hv]
  | load => simp only [AStmt.assigns, List.mem_singleton] at hv; simp [AEnv.set, hv]
  | store => rfl
  | seq _ _ ih1 ih2 =>
    simp only [AStmt.assigns, List.mem_append, not_or] at hv; rw [ih2 hv.2, ih1 hv.1]
  | loopF => rfl
  | loopT _ _ _ ih1 ih2 => simp only [AStmt.assigns] at ih1 hv ih2; rw [ih2 hv, ih1 hv]

/-! ## List lemmas -/

abbrev Sorted (l : List (BitVec 8)) : Prop := l.Pairwise (· ≤ ·)

theorem le_last {l : List (BitVec 8)} (hs : Sorted l) {k : Nat} (hk : k < l.length) :
    ∀ z ∈ l.take (k + 1), z ≤ l[k] := by
  intro z hz
  obtain ⟨m, hm, rfl⟩ := List.mem_take_iff_getElem.mp hz
  by_cases hmk : m = k
  · subst hmk; exact BitVec.le_refl _
  · exact List.pairwise_iff_getElem.mp hs m k (by omega) hk (by omega)

theorem sorted_insert {l : List (BitVec 8)} (hs : Sorted l) {j : Nat} {key : BitVec 8}
    (h1 : ∀ z ∈ l.take j, z ≤ key) (h2 : ∀ z ∈ l.drop j, key ≤ z) : Sorted (l.take j ++ key :: l.drop j) := by
  have hs' := hs; rw [← List.take_append_drop j l] at hs'
  obtain ⟨p1, p2, p3⟩ := List.pairwise_append.mp hs'
  refine List.pairwise_append.mpr ⟨p1, List.pairwise_cons.mpr ⟨h2, p2⟩, fun a ha b hb => ?_⟩
  rcases List.mem_cons.mp hb with rfl | hb
  · exact h1 a ha
  · exact p3 a ha b hb

theorem hole_set {pre rest : List (BitVec 8)} {j : Nat} (hj : j ≤ pre.length) (y v : BitVec 8) :
    (pre.take j ++ y :: (pre.drop j ++ rest)).set j v = pre.take j ++ v :: (pre.drop j ++ rest) := by
  have hl : (pre.take j).length = j := by simp; omega
  rw [List.set_append_right _ _ (by rw [hl]; exact Nat.le_refl _), hl, Nat.sub_self, List.set_cons_zero]

theorem hole_shift {pre rest : List (BitVec 8)} {j : Nat} (h0 : 0 < j) (hj : j ≤ pre.length) :
    pre.take j ++ pre[j - 1] :: (pre.drop j ++ rest) =
      pre.take (j - 1) ++ pre[j - 1] :: (pre.drop (j - 1) ++ rest) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [List.take_succ_eq_append_getElem (by omega), List.drop_eq_getElem_cons (i := k) (by omega),
    List.append_assoc]; rfl

theorem hole_get {pre rest : List (BitVec 8)} {j : Nat} (h0 : 0 < j) (hj : j ≤ pre.length) (y : BitVec 8)
    (h : j - 1 < (pre.take j ++ y :: (pre.drop j ++ rest)).length) :
    (pre.take j ++ y :: (pre.drop j ++ rest))[j - 1] = pre[j - 1] := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_take]

theorem hole_length {pre rest : List (BitVec 8)} {j : Nat} (hj : j ≤ pre.length) (y : BitVec 8) :
    (pre.take j ++ y :: (pre.drop j ++ rest)).length = pre.length + 1 + rest.length := by
  simp; omega

/-! ## Expression values -/

theorem bv8_lt (a b : BitVec 8) : a.setWidth 64 < b.setWidth 64 ↔ a < b := by
  simp only [BitVec.lt_def, BitVec.toNat_setWidth]
  have := a.isLt; have := b.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem and01 (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : BitVec 64) &&& (if q then 1 else 0)) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem setWidth8_64 (x : BitVec 8) : (x.setWidth 64).setWidth 8 = x := setWidth_setWidth8 x

/-! ## The program -/

def idxE : AExp := .ite (.var 4) (.bin .sub (.var 4) (.const 1)) (.const 0)
def cE : AExp := .bin .and (.bin .ult (.const 0) (.var 4)) (.bin .ult (.var 5) (.var 6))
def valE : AExp := .ite (.var 7) (.var 6) (.var 5)

def innerBody : AStmt :=
  .seq (.load 6 1 idxE) (.seq (.assign 7 cE) (.seq (.store 1 (.var 4) valE) (.assign 4 (.bin .sub (.var 4) (.var 7)))))
def outerBody : AStmt :=
  .seq (.load 5 1 (.var 2)) (.seq (.assign 4 (.var 2)) (.seq (.assign 7 (.const 1))
    (.seq (.loop (.var 7) innerBody) (.assign 2 (.bin .add (.var 2) (.const 1))))))
def insProg : AStmt := .seq (.assign 2 (.const 0)) (.loop (.bin .ult (.var 2) (.var 1)) outerBody)
def sortProg : AStmt := .seq (.assign 2 (.var 1)) (.seq (mapProg (.var 6)) insProg)

/-! ## Inner loop: insert `key` into the sorted `pre` -/

theorem idxE_val {env : AEnv} {j : Nat} (h4 : env 4 = BitVec.ofNat 64 j) (hj : j < 2 ^ 64) :
    (idxE.denote env).toNat = j - 1 := by
  simp only [idxE, AExp.denote, Op.eval, h4]
  by_cases h0 : j = 0
  · subst h0; simp
  · rw [if_neg (fun e => h0 (by have := congrArg BitVec.toNat e; simp at this; omega))]
    rw [BitVec.toNat_sub]; simp; omega

theorem cE_val {env : AEnv} {j : Nat} {key t : BitVec 8} (h4 : env 4 = BitVec.ofNat 64 j) (hj : j < 2 ^ 64)
    (h5 : env 5 = key.setWidth 64) (h6 : env 6 = t.setWidth 64) :
    cE.denote env = if 0 < j ∧ key < t then 1 else 0 := by
  simp only [cE, AExp.denote, Op.eval, h4, h5, h6, bv8_lt, and01]
  congr 1; apply propext; rw [BitVec.lt_def]; simp; omega

theorem inner_exec (xs pre rest : List (BitVec 8)) (key : BitVec 8) (hs : Sorted pre)
    (hn : pre.length < 2 ^ 63) (σ : AState) (hh : σ.heap = [xs, pre ++ key :: rest])
    (h5 : σ.env 5 = key.setWidth 64) (h4 : σ.env 4 = BitVec.ofNat 64 pre.length) (h7 : σ.env 7 = 1) :
    ∃ σ', AExec (.loop (.var 7) innerBody) σ σ' ∧ ∃ j ≤ pre.length,
      σ'.heap = [xs, pre.take j ++ key :: (pre.drop j ++ rest)] ∧
      (∀ z ∈ pre.take j, z ≤ key) ∧ (∀ z ∈ pre.drop j, key < z) := by
  obtain ⟨σ', hl, hq⟩ := AExec.loop_inv (c := .var 7) (b := innerBody)
    (fun τ => τ.env 5 = key.setWidth 64 ∧ ∃ j ≤ pre.length, τ.env 4 = BitVec.ofNat 64 j ∧
      (∀ z ∈ pre.drop j, key < z) ∧
      ((τ.env 7 = 1 ∧ ∃ y, τ.heap = [xs, pre.take j ++ y :: (pre.drop j ++ rest)]) ∨
       (τ.env 7 = 0 ∧ τ.heap = [xs, pre.take j ++ key :: (pre.drop j ++ rest)] ∧ ∀ z ∈ pre.take j, z ≤ key)))
    (fun τ => ∃ j ≤ pre.length, τ.heap = [xs, pre.take j ++ key :: (pre.drop j ++ rest)] ∧
      (∀ z ∈ pre.take j, z ≤ key) ∧ (∀ z ∈ pre.drop j, key < z))
    (fun τ => if τ.env 7 = 0 then 0 else (τ.env 4).toNat + 1)
    (fun ⟨env, heap⟩ ⟨h5, j, hj, h4, hgt, hcase⟩ hc => by
      dsimp only at h5 h4 hgt hcase hc ⊢
      simp only [AExp.denote] at hc
      obtain ⟨h7, y, hh⟩ : env 7 = 1 ∧ ∃ y, heap = [xs, pre.take j ++ y :: (pre.drop j ++ rest)] := by
        rcases hcase with h | ⟨h7, -⟩
        · exact h
        · exact absurd h7 hc
      subst hh
      have hjn : j < 2 ^ 64 := by omega
      have hlen := hole_length (rest := rest) hj y
      have hidx := idxE_val h4 hjn
      have hidx' : (idxE.denote env).toNat < (pre.take j ++ y :: (pre.drop j ++ rest)).length := by omega
      refine ⟨_, .seq (.load (b := 1) (by simp) (by simpa using hidx'))
        (.seq .assign (.seq (.store (b := 1) (by simp) (by simp [AEnv.set, AExp.denote, h4]; omega)) .assign)), ?_⟩
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.set_cons_succ, List.set_cons_zero,
        List.length_cons]
      generalize ht0 : (pre.take j ++ y :: (pre.drop j ++ rest))[(idxE.denote env).toNat] = t
      have hc1 : cE.denote (env.set 6 (t.setWidth 64)) = if 0 < j ∧ key < t then 1 else 0 :=
        cE_val (by simp [AEnv.set, h4]) hjn (by simp [AEnv.set, h5]) (by simp [AEnv.set])
      simp only [hc1]
      have hj4 : (BitVec.ofNat 64 j).toNat = j := by simp; omega
      change (_ ∧ _) ∧ _
      by_cases hsh : 0 < j ∧ key < t
      · -- shift: the hole moves down
        have ht : t = pre[j - 1]'(by omega) := ht0.symm.trans (by simp only [hidx]; exact hole_get hsh.1 hj y _)
        refine ⟨⟨by simp [AEnv.set, h5], j - 1, by omega, ?_, ?_, .inl ⟨by simp [AEnv.set, hsh], pre[j - 1]'(by omega), ?_⟩⟩, ?_⟩
        · simp [AEnv.set, AExp.denote, Op.eval, hsh, h4]
          apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp; omega
        · intro z hz
          have e2 : pre.drop (j - 1) = pre[j - 1] :: pre.drop j := by
            rw [List.drop_eq_getElem_cons (i := j - 1) (by omega), Nat.sub_add_cancel hsh.1]
          rw [e2] at hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact ht ▸ hsh.2
          · exact hgt z hz
        · show _ = _
          simp [valE, AEnv.set, AExp.denote, hsh, h4, hj4, setWidth8_64]
          rw [hole_set hj]
          exact (congrArg (fun v => pre.take j ++ v :: (pre.drop j ++ rest)) ht).trans (hole_shift hsh.1 hj)
        · simp [AEnv.set, AExp.denote, Op.eval, hsh, h4, h7]; omega
      · -- stop: the key drops into the hole
        have hle : ∀ z ∈ pre.take j, z ≤ key := by
          intro z hz
          have h0 : 0 < j := by
            rcases Nat.eq_zero_or_pos j with rfl | h0
            · simp at hz
            · exact h0
          have hlt : ¬ key < t := fun h => hsh ⟨h0, h⟩
          have ht : t = pre[j - 1]'(by omega) := ht0.symm.trans (by simp only [hidx]; exact hole_get h0 hj y _)
          have := le_last hs (k := j - 1) (by omega) z (by rw [Nat.sub_add_cancel h0]; exact hz)
          rw [← ht] at this
          exact BitVec.le_trans this (by rw [BitVec.le_def]; rw [BitVec.lt_def] at hlt; omega)
        refine ⟨⟨by simp [AEnv.set, h5], j, hj, ?_, hgt, .inr ⟨by simp [AEnv.set, hsh], ?_, hle⟩⟩, ?_⟩
        · simp [AEnv.set, AExp.denote, Op.eval, hsh, h4]
        · show _ = _
          simp [valE, AEnv.set, AExp.denote, hsh, h4, h5, hj4, setWidth8_64]
          exact hole_set hj y key
        · simp [AEnv.set, hsh, h7])
    (fun ⟨env, heap⟩ ⟨h5, j, hj, h4, hgt, hcase⟩ hc => by
      dsimp only at h5 h4 hgt hcase hc ⊢
      simp only [AExp.denote] at hc
      rcases hcase with ⟨h7, -⟩ | ⟨h7, hh, hle⟩
      · rw [hc] at h7; exact absurd h7 (by decide)
      · exact ⟨j, hj, hh, hle, hgt⟩)
    σ ⟨h5, pre.length, Nat.le_refl _, h4, by simp, .inl ⟨h7, key, by simpa using hh⟩⟩
  exact ⟨σ', hl, hq⟩

/-! ## Outer loop and the whole program -/

theorem toNat_eq_ofNat {a : BitVec 64} {i : Nat} (h : a.toNat = i) : a = BitVec.ofNat 64 i := by
  subst h; simp

theorem ins_exec (xs arr0 : List (BitVec 8)) (σ : AState) (hh : σ.heap = [xs, arr0])
    (h1 : σ.env 1 = BitVec.ofNat 64 arr0.length) (hn : arr0.length < 2 ^ 63) :
    ∃ σ', AExec insProg σ σ' ∧ ∃ arr, σ'.heap = [xs, arr] ∧ arr.Perm arr0 ∧ Sorted arr := by
  have hL : (BitVec.ofNat 64 arr0.length).toNat = arr0.length := by simp; omega
  obtain ⟨σ₁, hl, hq⟩ := AExec.loop_inv (c := .bin .ult (.var 2) (.var 1)) (b := outerBody)
    (fun τ => τ.env 1 = BitVec.ofNat 64 arr0.length ∧ (τ.env 2).toNat ≤ arr0.length ∧
      ∃ arr, τ.heap = [xs, arr] ∧ arr.length = arr0.length ∧ arr.Perm arr0 ∧ Sorted (arr.take (τ.env 2).toNat))
    (fun τ => ∃ arr, τ.heap = [xs, arr] ∧ arr.Perm arr0 ∧ Sorted arr)
    (fun τ => arr0.length - (τ.env 2).toNat)
    (fun ⟨env, heap⟩ ⟨h1, hle, arr, hh, hlen, hp, hs⟩ hc => by
      dsimp only at h1 hle hh hs ⊢
      simp only [AExp.denote, ult_ne, h1, hL] at hc
      subst hh
      have hi : (env 2).toNat < arr.length := by omega
      let i := (env 2).toNat
      have harr : arr = arr.take i ++ arr[i] :: arr.drop (i + 1) := by
        rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
      have hpl : (arr.take i).length = i := by simp; omega
      -- the inner loop, from the state after `a5 := out[i]; a4 := i; a7 := 1`
      let env₃ : AEnv := ((env.set 5 (arr[i].setWidth 64)).set 4 (env 2)).set 7 1
      obtain ⟨σ₄, hex₄, j, hj, hh₄, hle₄, hgt₄⟩ := inner_exec xs (arr.take i) (arr.drop (i + 1)) arr[i]
        hs (by omega) ⟨env₃, [xs, arr]⟩ (by rw [← harr])
        (by simp [env₃, AEnv.set]) (by simp [env₃, AEnv.set, hpl, i]) (by simp [env₃, AEnv.set])
      have k1 : σ₄.env 1 = env 1 := by
        rw [hex₄.env_keep (by decide)]; simp [env₃, AEnv.set]
      have k2 : σ₄.env 2 = env 2 := by
        rw [hex₄.env_keep (by decide)]; simp [env₃, AEnv.set]
      have e2 := toNat_inc (show (env 2).toNat < arr0.length by omega) (show arr0.length < 2 ^ 64 by omega)
      refine ⟨_, .seq (.load (b := 1) (by simp) (by simpa using hi)) (.seq .assign (.seq .assign
        (.seq hex₄ .assign))), ⟨?_, ?_, ?_⟩, ?_⟩
      · simp only [AEnv.set, Fin.reduceEq, if_false]; exact k1.trans h1
      · simp only [AEnv.set, if_true, AExp.denote, Op.eval, k2]; rw [e2]; omega
      · let P := (arr.take i).take j ++ arr[i] :: (arr.take i).drop j
        have hP : P.length = i + 1 := by simp [P]; omega
        refine ⟨P ++ arr.drop (i + 1), by rw [hh₄]; simp [P], by simp [hP]; omega, ?_, ?_⟩
        · refine List.Perm.trans ?_ hp
          conv => rhs; rw [harr]
          simp only [P, List.append_assoc, List.cons_append]
          refine List.perm_middle.trans ?_
          rw [← List.append_assoc, List.take_append_drop]
          exact List.perm_middle.symm
        · simp only [AEnv.set, if_true, AExp.denote, Op.eval, k2]; rw [e2]
          rw [List.take_left' hP]
          exact sorted_insert hs hle₄ fun z hz => BitVec.le_of_lt (hgt₄ z hz)
      · simp only [AEnv.set, if_true, AExp.denote, Op.eval, k2]; rw [e2]; omega)
    (fun ⟨env, heap⟩ ⟨h1, hle, arr, hh, hlen, hp, hs⟩ hc => by
      dsimp only at h1 hle hh hs ⊢
      have : ¬ (env 2).toNat < arr0.length := fun hlt =>
        (ult_ne (a := env 2) (b := env 1)).2 (by rw [h1, hL]; exact hlt) hc
      refine ⟨arr, hh, hp, ?_⟩
      rwa [List.take_of_length_le (by omega)] at hs)
    ⟨σ.env.set 2 0, σ.heap⟩ ⟨by simpa [AEnv.set] using h1, by simp [AEnv.set], arr0, hh, rfl, List.Perm.refl _,
      by simp [AEnv.set]⟩
  exact ⟨σ₁, .seq (AExec.assign' rfl) hl, hq⟩

theorem sortProg_exec (xs out : List (BitVec 8)) (σ : AState) (hh : σ.heap = [xs, out])
    (h1 : σ.env 1 = BitVec.ofNat 64 xs.length) (hn : xs.length < 2 ^ 63) (hout : out.length = xs.length) :
    ∃ σ', AExec sortProg σ σ' ∧ ∃ arr, σ'.heap = [xs, arr] ∧ arr.Perm xs ∧ Sorted arr := by
  have hL : (BitVec.ofNat 64 xs.length).toNat = xs.length := by simp; omega
  let σ₁ : AState := ⟨σ.env.set 2 (σ.env 1), σ.heap⟩
  obtain ⟨σ₂, hex₂, hh₂⟩ := mapProg_exec (.var 6) id (fun env x he => by simp [AExp.denote, he, setWidth_setWidth8])
    σ₁ xs out hh (by simp [σ₁, AEnv.set, h1]) (by omega) (by simp [σ₁, AEnv.set, h1, hL]; omega)
  have k1 : σ₂.env 1 = σ.env 1 := by rw [hex₂.env_keep (by decide)]; simp [σ₁, AEnv.set]
  simp only [σ₁, AEnv.set, if_true, h1, hL, List.take_length, List.map_id, Nat.min_self] at hh₂
  rw [← hout, List.drop_length, List.append_nil] at hh₂
  obtain ⟨σ₃, hex₃, arr, hh₃, hp, hs⟩ := ins_exec xs xs σ₂ hh₂ (k1.trans h1) hn
  exact ⟨σ₃, .seq (AExec.assign' rfl) (.seq hex₂ hex₃), arr, hh₃, hp, hs⟩

/-- sorted permutations of a list are unique (`≤` on `BitVec 8` is antisymmetric) -/
theorem sorted_perm_eq {a b : List (BitVec 8)} (ha : Sorted a) (hb : Sorted b) (hp : a.Perm b) : a = b :=
  hp.eq_of_pairwise (fun _ _ _ _ h1 h2 => BitVec.le_antisymm h1 h2) ha hb

def leB (a b : BitVec 8) : Bool := decide (a ≤ b)

theorem sorted_mergeSort (xs : List (BitVec 8)) : Sorted (xs.mergeSort leB) := by
  have := List.pairwise_mergeSort (le := leB)
    (fun a b c h1 h2 => by simp only [leB, decide_eq_true_eq] at *; exact BitVec.le_trans h1 h2)
    (fun a b => by simp only [leB, Bool.or_eq_true, decide_eq_true_eq]; exact BitVec.le_total a b) xs
  exact this.imp fun h => by simpa [leB] using h

/-- the insertion sort computes `List.mergeSort` -/
theorem sortProg_mergeSort (xs out : List (BitVec 8)) (σ : AState) (hh : σ.heap = [xs, out])
    (h1 : σ.env 1 = BitVec.ofNat 64 xs.length) (hn : xs.length < 2 ^ 63) (hout : out.length = xs.length) :
    ∃ σ', AExec sortProg σ σ' ∧ σ'.heap = [xs, xs.mergeSort leB] := by
  obtain ⟨σ', hex, arr, hh', hp, hs⟩ := sortProg_exec xs out σ hh h1 hn hout
  exact ⟨σ', hex, by rw [hh', sorted_perm_eq hs (sorted_mergeSort xs) (hp.trans (List.mergeSort_perm xs leB).symm)]⟩

end Proven
