/- Insertion sort with a gcc-like inner loop, as a `Mach.BStmt` program (so it goes through the optimising
`compBFO`, whose register assignment is free), proved to compute `List.mergeSort` and in `Implements1Raw` form.
Blocks: input (`a0`, length `a1`), output (`a3`); `a2` is the (unused) word block.
```
  out := in                                  -- mapK (.var 1) (.var 6)
  i := 1
  while i < n {
    v := out[i]; t := out[0]
    out[0] := v < t ? v : t; v := v < t ? t : v   -- out[0] := min, key := max: out[0] ≤ key is a sentinel
    j := i; t := out[j - 1]
    while v < t { out[j] := t; j := j - 1; t := out[j - 1] }   -- no `j ≠ 0` test: the sentinel stops it
    out[j] := v; i := i + 1 }
```
Swapping the key with `out[0]` when it is smaller keeps the prefix a sorted permutation, so the result is the
sorted permutation, i.e. `List.mergeSort`. -/
import Legacy.Riscv.Examples.Implements1Opt

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

open Proven (ult_ne toNat_inc toNat_ofNat_lt map_take_set setWidth_setWidth8)

def ltVT : Mach.BExp := .bin .ult (.var 6) (.var 7)
def jm1 : Mach.BExp := .bin .sub (.var 5) (.const 1)

def insInner : Mach.BStmt :=
  .seq (.store 1 (.var 5) (.var 7)) (.seq (.assign 5 jm1) (.load 7 1 jm1))

def insOuter : Mach.BStmt :=
  .seq (.load 6 1 (.var 4)) (.seq (.load 7 1 (.const 0))
  (.seq (.store 1 (.const 0) (.ite ltVT (.var 6) (.var 7))) (.seq (.assign 6 (.ite ltVT (.var 7) (.var 6)))
  (.seq (.assign 5 (.var 4)) (.seq (.load 7 1 jm1)
  (.seq (.loop ltVT insInner) (.seq (.store 1 (.var 5) (.var 6))
  (.assign 4 (.bin .add (.var 4) (.const 1))))))))))

def insProgB : Mach.BStmt :=
  .seq (mapK (.var 1) (.var 6)) (.seq (.assign 4 (.const 1)) (.loop (.bin .ult (.var 4) (.var 1)) insOuter))

def insCodeO : List (BitVec 32) := compBFO 0 [0, 3] [2] insProgB

/-! ## Expression values -/

theorem ofNat_sub1 {j : Nat} (h1 : 1 ≤ j) (hj : j < 2 ^ 64) :
    BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp; omega

theorem jm1_val {env : Mach.BEnv} {j : Nat} (h5 : env 5 = BitVec.ofNat 64 j) (h1 : 1 ≤ j) (hj : j < 2 ^ 64) :
    jm1.denote env = BitVec.ofNat 64 (j - 1) := by
  simp only [jm1, Mach.BExp.denote, Op.eval, h5]; exact ofNat_sub1 h1 hj

theorem ltVT_val {env : Mach.BEnv} {v t : BitVec 8} (h6 : env 6 = v.setWidth 64) (h7 : env 7 = t.setWidth 64) :
    ltVT.denote env = if v < t then 1 else 0 := by
  simp only [ltVT, Mach.BExp.denote, Op.eval, h6, h7, Proven.bv8_lt]

theorem minE_val {env : Mach.BEnv} {v t : BitVec 8} (h6 : env 6 = v.setWidth 64) (h7 : env 7 = t.setWidth 64) :
    (Mach.BExp.ite ltVT (.var 6) (.var 7)).denote env = (if v < t then v else t).setWidth 64 := by
  have := ltVT_val h6 h7
  simp only [Mach.BExp.denote] at this ⊢
  rw [this, h6, h7]; by_cases h : v < t <;> simp [h]

theorem maxE_val {env : Mach.BEnv} {v t : BitVec 8} (h6 : env 6 = v.setWidth 64) (h7 : env 7 = t.setWidth 64) :
    (Mach.BExp.ite ltVT (.var 7) (.var 6)).denote env = (if v < t then t else v).setWidth 64 := by
  have := ltVT_val h6 h7
  simp only [Mach.BExp.denote] at this ⊢
  rw [this, h6, h7]; by_cases h : v < t <;> simp [h]

theorem getD_get {l : List (BitVec 8)} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-! ## The inner loop: shift right while greater; `pre[0] ≤ key` stops it -/

theorem insInner_exec (xs pre rest : List (BitVec 8)) (key y : BitVec 8) (hs : Proven.Sorted pre)
    (h0 : 0 < pre.length) (hsent : pre.getD 0 0 ≤ key) (hn : pre.length < 2 ^ 63) (σ : Mach.BState)
    (hh : σ.heap = [xs, pre ++ y :: rest]) (h6 : σ.env 6 = key.setWidth 64)
    (h5 : σ.env 5 = BitVec.ofNat 64 pre.length) (h7 : σ.env 7 = (pre.getD (pre.length - 1) 0).setWidth 64) :
    ∃ σ', Mach.BExec (.loop ltVT insInner) σ σ' ∧ σ'.env 1 = σ.env 1 ∧ σ'.env 4 = σ.env 4 ∧
      σ'.env 6 = σ.env 6 ∧ σ'.wheap = σ.wheap ∧ ∃ j, j ≤ pre.length ∧ σ'.env 5 = BitVec.ofNat 64 j ∧
      (∃ y', σ'.heap = [xs, pre.take j ++ y' :: (pre.drop j ++ rest)]) ∧
      (∀ z ∈ pre.take j, z ≤ key) ∧ (∀ z ∈ pre.drop j, key < z) := by
  obtain ⟨σ', hl, hq⟩ := BExec.loop_inv (c := ltVT) (b := insInner)
    (fun τ => τ.env 1 = σ.env 1 ∧ τ.env 4 = σ.env 4 ∧ τ.env 6 = key.setWidth 64 ∧ τ.wheap = σ.wheap ∧
      ∃ j, 1 ≤ j ∧ j ≤ pre.length ∧ τ.env 5 = BitVec.ofNat 64 j ∧
        τ.env 7 = (pre.getD (j - 1) 0).setWidth 64 ∧
        (∃ y', τ.heap = [xs, pre.take j ++ y' :: (pre.drop j ++ rest)]) ∧ ∀ z ∈ pre.drop j, key < z)
    (fun τ => τ.env 1 = σ.env 1 ∧ τ.env 4 = σ.env 4 ∧ τ.env 6 = key.setWidth 64 ∧ τ.wheap = σ.wheap ∧
      ∃ j, j ≤ pre.length ∧ τ.env 5 = BitVec.ofNat 64 j ∧
        (∃ y', τ.heap = [xs, pre.take j ++ y' :: (pre.drop j ++ rest)]) ∧
        (∀ z ∈ pre.take j, z ≤ key) ∧ (∀ z ∈ pre.drop j, key < z))
    (fun τ => (τ.env 5).toNat)
    (fun ⟨env, heap, wheap⟩ ⟨e1, e4, h6, hw, j, hj1, hj, h5, h7, ⟨y', hh⟩, hgt⟩ hc => by
      dsimp only at e1 e4 h6 hw h5 h7 hh hgt hc ⊢
      subst hh
      rw [ltVT_val h6 h7] at hc
      have hlt : key < pre.getD (j - 1) 0 := by
        by_cases hk : key < pre.getD (j - 1) 0
        · exact hk
        · rw [if_neg hk] at hc; exact absurd rfl hc
      have hj2 : 2 ≤ j := by
        refine Classical.byContradiction fun hn => ?_
        rw [show j - 1 = 0 by omega] at hlt
        rw [BitVec.le_def] at hsent; rw [BitVec.lt_def] at hlt; omega
      have hjn : j < 2 ^ 64 := by omega
      have hget : pre.getD (j - 1) 0 = pre[j - 1]'(by omega) := getD_get (by omega)
      have hlen := hole_length (rest := rest) hj y'
      have e5 : (BitVec.ofNat 64 j).toNat = j := toNat_ofNat_lt hjn
      -- after the store and `j := j - 1`
      have hst : (pre.take j ++ y' :: (pre.drop j ++ rest)).set j ((env 7).setWidth 8) =
          pre.take (j - 1) ++ pre[j - 1]'(by omega) :: (pre.drop (j - 1) ++ rest) := by
        rw [hole_set hj, h7, hget, setWidth_setWidth8]; exact hole_shift (by omega) hj
      have hj' : j - 1 ≤ pre.length := by omega
      have hlen' := hole_length (rest := rest) hj' (pre[j - 1]'(by omega))
      have hidx : (jm1.denote (env.set 5 (jm1.denote env))).toNat = j - 1 - 1 := by
        rw [jm1_val (j := j - 1) (by simp [Mach.BEnv.set, jm1_val h5 (by omega) hjn]) (by omega) (by omega)]
        exact toNat_ofNat_lt (by omega)
      refine ⟨_, .seq (.store (b := 1) (by simp) (by simp [Mach.BExp.denote, h5, e5]; omega))
        (.seq .assign (.load (b := 1) (by simp) ?_)), ⟨?_, ?_, ?_, ?_, j - 1, by omega, by omega, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.length_set, List.set_cons_succ,
          List.set_cons_zero, Mach.BExp.denote, h5, e5]
        rw [hidx, hlen]; omega
      all_goals try simp only [Mach.BEnv.set, Mach.BExp.denote, h5, e5, List.getElem_cons_succ, List.getElem_cons_zero,
        List.set_cons_succ, List.set_cons_zero, hst, Nat.reduceEqDiff, ↓reduceIte]
      · simp [e1]
      · simp [e4]
      · simp [h6]
      · exact hw
      · exact jm1_val h5 (by omega) hjn
      · congr 1
        simp only [hidx]
        rw [hole_get (j := j - 1) (by omega) hj', getD_get (by omega)]
      · exact ⟨pre[j - 1]'(by omega), rfl⟩
      · intro z hz
        have e2 : pre.drop (j - 1) = pre[j - 1]'(by omega) :: pre.drop j := by
          rw [List.drop_eq_getElem_cons (i := j - 1) (by omega), Nat.sub_add_cancel (by omega : 1 ≤ j)]
        rw [e2] at hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hget ▸ hlt
        · exact hgt z hz
      · rw [jm1_val h5 (by omega) hjn, toNat_ofNat_lt (by omega)]; omega)
    (fun ⟨env, heap, wheap⟩ ⟨e1, e4, h6, hw, j, hj1, hj, h5, h7, hh, hgt⟩ hc => by
      dsimp only at e1 e4 h6 hw h5 h7 hh hgt hc ⊢
      rw [ltVT_val h6 h7] at hc
      have hle : ¬ key < pre.getD (j - 1) 0 := fun h => by rw [if_pos h] at hc; exact absurd hc (by decide)
      refine ⟨e1, e4, h6, hw, j, hj, h5, hh, fun z hz => ?_, hgt⟩
      have hget : pre.getD (j - 1) 0 = pre[j - 1]'(by omega) := getD_get (by omega)
      have := le_last hs (k := j - 1) (by omega) z (by rw [Nat.sub_add_cancel hj1]; exact hz)
      rw [← hget] at this
      exact BitVec.le_trans this (by rw [BitVec.le_def]; rw [BitVec.lt_def] at hle; omega))
    σ ⟨rfl, rfl, h6, rfl, pre.length, by omega, Nat.le_refl _, h5, h7, ⟨y, by simpa using hh⟩, by simp⟩
  obtain ⟨e1, e4, e6, hw, hq⟩ := hq
  exact ⟨σ', hl, e1, e4, e6.trans h6.symm, hw, hq⟩

end Proven.Mach.Riscv

namespace Proven.Mach.Riscv

/-! ## Single steps on the two-block heap `[xs, L]` -/

theorem BExec.load1 {v : Nat} {i : Mach.BExp} {env : Mach.BEnv} {xs L : List (BitVec 8)} {wh : Mach.WHeap}
    {k : Nat} {x : BitVec 8} (hk : (i.denote env).toNat = k) (hx : L[k]? = some x) :
    Mach.BExec (.load v 1 i) ⟨env, [xs, L], wh⟩ ⟨env.set v (x.setWidth 64), [xs, L], wh⟩ := by
  obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.1 hx
  subst hk
  exact Mach.BExec.load (v := v) (b := 1) (i := i) (σ := ⟨env, [xs, L], wh⟩) (by simp) (by simpa using hk')

theorem BExec.store1 {i e : Mach.BExp} {env : Mach.BEnv} {xs L : List (BitVec 8)} {wh : Mach.WHeap}
    {k : Nat} {u : BitVec 8} (hk : (i.denote env).toNat = k) (hl : k < L.length) (hu : (e.denote env).setWidth 8 = u) :
    Mach.BExec (.store 1 i e) ⟨env, [xs, L], wh⟩ ⟨env, [xs, L.set k u], wh⟩ := by
  subst hk hu
  exact Mach.BExec.store (b := 1) (i := i) (e := e) (σ := ⟨env, [xs, L], wh⟩) (by simp) (by simpa using hl)

theorem BExec.assign1 {v : Nat} {e : Mach.BExp} {env : Mach.BEnv} {H} {wh} {w : BitVec 64}
    (hw : e.denote env = w) : Mach.BExec (.assign v e) ⟨env, H, wh⟩ ⟨env.set v w, H, wh⟩ := hw ▸ .assign

theorem sorted_set0 {a : BitVec 8} {l : List (BitVec 8)} {m : BitVec 8} (hs : Proven.Sorted (a :: l)) (hm : m ≤ a) :
    Proven.Sorted (m :: l) := by
  obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hs
  exact List.pairwise_cons.2 ⟨fun z hz => BitVec.le_trans hm (h1 z hz), h2⟩

/-! ## The outer loop -/

theorem insLoop_exec (xs tl arr0 : List (BitVec 8)) (σ : Mach.BState) (hh : σ.heap = [xs, arr0 ++ tl])
    (h1 : σ.env 1 = BitVec.ofNat 64 arr0.length) (hn : arr0.length < 2 ^ 32) (h4 : σ.env 4 = 1) :
    ∃ σ', Mach.BExec (.loop (.bin .ult (.var 4) (.var 1)) insOuter) σ σ' ∧
      ∃ arr, σ'.heap = [xs, arr ++ tl] ∧ arr.Perm arr0 ∧ Proven.Sorted arr := by
  have hL : (BitVec.ofNat 64 arr0.length).toNat = arr0.length := toNat_ofNat_lt (by omega)
  obtain ⟨σ₁, hl, hq⟩ := BExec.loop_inv (c := .bin .ult (.var 4) (.var 1)) (b := insOuter)
    (fun τ => τ.env 1 = BitVec.ofNat 64 arr0.length ∧ 1 ≤ (τ.env 4).toNat ∧ (τ.env 4).toNat ≤ arr0.length + 1 ∧
      ∃ arr, τ.heap = [xs, arr ++ tl] ∧ arr.length = arr0.length ∧ arr.Perm arr0 ∧
        Proven.Sorted (arr.take (τ.env 4).toNat))
    (fun τ => ∃ arr, τ.heap = [xs, arr ++ tl] ∧ arr.Perm arr0 ∧ Proven.Sorted arr)
    (fun τ => arr0.length + 1 - (τ.env 4).toNat)
    (fun ⟨env, heap, wheap⟩ ⟨h1, hi1, hin, arr, hh, hlen, hp, hs⟩ hc => by
      dsimp only at h1 hi1 hin hh hs ⊢
      simp only [Mach.BExp.denote, ult_ne, h1, hL] at hc
      subst hh
      obtain ⟨i', hi'⟩ : ∃ i', (env 4).toNat = i' + 1 := ⟨(env 4).toNat - 1, by omega⟩
      obtain ⟨a0, arr', rfl⟩ : ∃ a0 arr', arr = a0 :: arr' := by
        cases arr with
        | nil => simp at hlen; omega
        | cons a l => exact ⟨a, l, rfl⟩
      simp only [List.length_cons] at hlen
      rw [hi'] at hs hc
      have hi : i' < arr'.length := by omega
      let x := arr'[i']
      let R := arr'.drop (i' + 1)
      let m := if x < a0 then x else a0
      let k := if x < a0 then a0 else x
      let pre1 := m :: arr'.take i'
      let t := pre1.getD i' 0
      have harr : arr' = arr'.take i' ++ x :: R := by
        rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
      have hpl : (arr'.take i').length = i' := by simp; omega
      have hS : Proven.Sorted (a0 :: arr'.take i') := by simpa using hs
      have hS1 : Proven.Sorted pre1 := sorted_set0 hS (by
        simp only [m]; by_cases hx : x < a0
        · rw [if_pos hx]; exact BitVec.le_of_lt hx
        · rw [if_neg hx]; exact BitVec.le_refl _)
      have hmk : m ≤ k := by
        simp only [m, k]; by_cases hx : x < a0
        · rw [if_pos hx, if_pos hx]; exact BitVec.le_of_lt hx
        · rw [if_neg hx, if_neg hx]; exact BitVec.not_lt.1 hx
      have hL1 : ((a0 :: arr') ++ tl).set 0 m = pre1 ++ x :: (R ++ tl) := by
        conv => lhs; rw [harr]
        simp [pre1]
      have ht : (pre1 ++ x :: (R ++ tl))[i']? = some t := by
        rw [List.getElem?_append_left (by simp [pre1, hpl])]
        simp only [t, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem (by simp [pre1, hpl])]; rfl
      have hn' : arr'.length + 1 < 2 ^ 32 := by omega
      have e4 : env 4 = BitVec.ofNat 64 (i' + 1) := by rw [← hi']; simp
      let env₂ := (env.set 6 (x.setWidth 64)).set 7 (a0.setWidth 64)
      let env₅ := ((env₂.set 6 (k.setWidth 64)).set 5 ((Mach.BExp.var 4).denote (env₂.set 6 (k.setWidth 64)))).set 7
        (t.setWidth 64)
      obtain ⟨σ₆, hex₆, k1, k4, k6, -, j, hj, h5j, ⟨y', hh₆⟩, hle₆, hgt₆⟩ :=
        insInner_exec xs pre1 (R ++ tl) k x hS1 (by simp [pre1]) (by simpa [pre1] using hmk) (by simp [pre1]; omega)
          ⟨env₅, [xs, ((a0 :: arr') ++ tl).set 0 m], wheap⟩ (by rw [hL1]) (by simp [env₅, Mach.BEnv.set])
          (by simp [env₅, env₂, Mach.BEnv.set, Mach.BExp.denote, e4, pre1, hpl])
          (by simp [env₅, Mach.BEnv.set, pre1, hpl, t])
      obtain ⟨env₆, heap₆, wh₆⟩ := σ₆
      dsimp only at k1 k4 k6 h5j hh₆; subst hh₆
      simp only [env₅, env₂, Mach.BEnv.set, Nat.reduceEqDiff, ↓reduceIte] at k1 k4 k6
      have hjl : j ≤ i' + 1 := by simpa [pre1, hpl] using hj
      have hj' : j < (pre1.take j ++ y' :: (pre1.drop j ++ (R ++ tl))).length := by
        rw [hole_length hj]; omega
      have e2 := toNat_inc (show (env 4).toNat < arr0.length by omega) (show arr0.length < 2 ^ 64 by omega)
      have hx1 : ((a0 :: arr') ++ tl)[i' + 1]? = some x := by
        rw [List.cons_append, List.getElem?_cons_succ, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
      have hx0 : ((a0 :: arr') ++ tl)[0]? = some a0 := rfl
      have hk1 : ((Mach.BExp.var 4).denote env).toNat = i' + 1 := hi'
      have hmin : ((Mach.BExp.ite ltVT (.var 6) (.var 7)).denote env₂).setWidth 8 = m := by
        rw [minE_val (v := x) (t := a0) (by simp [env₂, Mach.BEnv.set]) (by simp [env₂, Mach.BEnv.set])]
        exact setWidth_setWidth8 _
      have hmax : (Mach.BExp.ite ltVT (.var 7) (.var 6)).denote env₂ = k.setWidth 64 :=
        maxE_val (by simp [env₂, Mach.BEnv.set]) (by simp [env₂, Mach.BEnv.set])
      have hk5 : (jm1.denote ((env₂.set 6 (k.setWidth 64)).set 5 ((Mach.BExp.var 4).denote (env₂.set 6 (k.setWidth 64))))).toNat = i' := by
        rw [jm1_val (j := i' + 1) (by simp [Mach.BEnv.set, Mach.BExp.denote, env₂, e4]) (by omega) (by omega)]
        exact toNat_ofNat_lt (by omega)
      have hkj : ((Mach.BExp.var 5).denote env₆).toNat = j := by
        simp only [Mach.BExp.denote, h5j]; exact toNat_ofNat_lt (by omega)
      have hkv : ((Mach.BExp.var 6).denote env₆).setWidth 8 = k := by
        simp only [Mach.BExp.denote, k6]; exact setWidth_setWidth8 _
      have e5 : (Mach.BExp.var 4).denote (env₂.set 6 (k.setWidth 64)) = env 4 := by
        simp [Mach.BExp.denote, env₂, Mach.BEnv.set]
      refine ⟨_, .seq (BExec.load1 hk1 hx1) (.seq (BExec.load1 (k := 0) rfl hx0)
        (.seq (BExec.store1 (k := 0) rfl (by simp) hmin) (.seq (BExec.assign1 hmax) (.seq (BExec.assign1 rfl)
        (.seq (BExec.load1 hk5 (by rw [hL1]; exact ht)) (.seq hex₆ (.seq (BExec.store1 hkj hj' hkv)
          (BExec.assign1 rfl)))))))), ?_⟩
      have hset := hole_set (rest := R ++ tl) hj y' k
      have hPl : (pre1.take j ++ k :: pre1.drop j).length = i' + 2 := by simp [pre1, hpl]; omega
      have hRl : R.length = arr'.length - (i' + 1) := by simp [R]
      have hperm : (pre1.take j ++ k :: pre1.drop j ++ R).Perm (a0 :: arr') := by
        have q1 : (pre1.take j ++ k :: pre1.drop j ++ R).Perm (k :: m :: (arr'.take i' ++ R)) := by
          rw [List.append_assoc, List.cons_append]
          refine List.perm_middle.trans ?_
          rw [← List.append_assoc, List.take_append_drop]; rfl
        have q2 : (a0 :: arr').Perm (a0 :: x :: (arr'.take i' ++ R)) := by
          conv => lhs; rw [harr]
          exact List.Perm.cons _ List.perm_middle
        refine q1.trans (List.Perm.trans ?_ q2.symm)
        simp only [k, m]; by_cases hx : x < a0
        · rw [if_pos hx, if_pos hx]
        · rw [if_neg hx, if_neg hx]; exact List.Perm.swap _ _ _
      simp only [Mach.BEnv.set, Nat.reduceEqDiff, ↓reduceIte, Mach.BExp.denote, Op.eval, k4]
      rw [e2, hi']
      refine ⟨⟨by rw [k1, h1], by omega, by omega, pre1.take j ++ k :: pre1.drop j ++ R, ?_, ?_, hperm.trans hp, ?_⟩, by omega⟩
      · rw [hset]; simp
      · simp only [List.length_append, hPl, hRl]; omega
      · rw [List.take_left' hPl]
        exact sorted_insert hS1 hle₆ fun z hz => BitVec.le_of_lt (hgt₆ z hz))
    (fun ⟨env, heap, wheap⟩ ⟨h1, hi1, hin, arr, hh, hlen, hp, hs⟩ hc => by
      dsimp only at h1 hi1 hin hh hs ⊢
      have : ¬ (env 4).toNat < arr0.length := fun hlt =>
        (ult_ne (a := env 4) (b := env 1)).2 (by rw [h1, hL]; exact hlt) hc
      refine ⟨arr, hh, hp, ?_⟩
      rwa [List.take_of_length_le (by omega)] at hs)
    σ ⟨h1, by rw [h4]; decide, by rw [h4]; simp, arr0, hh, rfl, List.Perm.refl _, by
      rw [h4]; cases arr0 <;> simp⟩
  exact ⟨σ₁, hl, hq⟩

/-! ## The whole program, and the machine theorem -/

theorem insProgB_exec (xs out : List (BitVec 8)) (σ : Mach.BState) (hh : σ.heap = [xs, out])
    (h1 : σ.env 1 = BitVec.ofNat 64 xs.length) (hn : xs.length < 2 ^ 32) (hout : xs.length ≤ out.length) :
    ∃ σ', Mach.BExec insProgB σ σ' ∧ σ'.heap = [xs, xs.mergeSort Proven.leB ++ out.drop xs.length] := by
  have hK : ((Mach.BExp.var 1).denote σ.env).toNat = xs.length := by
    simp only [Mach.BExp.denote, h1]; exact toNat_ofNat_lt (by omega)
  obtain ⟨σ₁, hex₁, hh₁, -, k1⟩ := mapK_exec (.var 1) (.var 6) id
    (fun env x he => by simp [Mach.BExp.denote, he, setWidth_setWidth8]) σ xs out hh h1 (by omega)
    (by rw [hK]; omega)
  rw [hK, Nat.min_self, List.map_id, List.take_length] at hh₁
  obtain ⟨σ₂, hex₂, arr, hh₂, hp, hs⟩ := insLoop_exec xs (out.drop xs.length) xs ⟨σ₁.env.set 4 1, σ₁.heap, σ₁.wheap⟩
    hh₁ (by simp [Mach.BEnv.set, k1, h1]) hn (by simp [Mach.BEnv.set])
  refine ⟨σ₂, .seq hex₁ (.seq (BExec.assign' rfl) hex₂), ?_⟩
  rw [hh₂, Proven.sorted_perm_eq hs (Proven.sorted_mergeSort xs) (hp.trans (List.mergeSort_perm xs _).symm)]

theorem insProgB_wf : rvF.wfB 0 [0, 3] [2] insProgB := by
  simp [insProgB, insOuter, insInner, ltVT, jm1, mapK, MachineF.wfB, Mach.BExp.depth, Mach.BExp.vlt, bzOK_iff,
    jmpOK_iff]
  decide +kernel

/-- **Insertion sort, gcc-like inner loop, optimised** (`insProgB` through `compBFO`) in `Implements1` form:
15 bytes of work space (the frame cell saving `gp`, plus alignment) -/
theorem insCodeO_implements1 : Implements1Raw insCodeO (fun x => x.mergeSort leU) (fun _ => 15) := by
  refine implements1_of_execO encRaw encRaw _ 0 (by omega) _ insProgB_wf (fun _ => 0) (fun _ => 15)
    (fun n => by (try dsimp only); omega) _ false ?_
  intro a out tbl env h1 h8 hmax hlt hout hol htl
  simp only [encRaw, List.length_mergeSort] at h1 hlt hout ⊢
  obtain ⟨σ', hex, hh⟩ := insProgB_exec (a.map (·.toBitVec)) out ⟨env, [a.map (·.toBitVec), out], [tbl]⟩ rfl
    (by simpa using h1) (by simpa using hlt) (by simpa using hout)
  simp only [List.length_map] at hh
  refine ⟨σ', _, hex, hh, ?_, ?_, fun h => nomatch h⟩
  · rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp), mergeSort_toBitVec]
  · exact drop_tail _ (by simp)

end Proven.Mach.Riscv
