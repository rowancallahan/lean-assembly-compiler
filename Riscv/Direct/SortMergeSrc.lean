/- Bottom-up merge sort as a `BStmt` program, proved at source level to compute `List.mergeSort`.

Blocks: 0 = input (base `v0`), 1 = scratch (base `v2`), 2 = output (base `v3`); `v1 = n`.
Variables: `v4 = k, v5 = p, v6 = q, v7 = t` (registers), `v8 = x, v9 = y, v10 = mid, v11 = e, v12 = i,
v13 = w, v14 = ww` (slots 0..6).
```
pass(src, dst):  i := 0
  while i < n {
    mid := min(i + w, n); e := min(i + w + w, n); p := i; q := mid; k := i
    while k < e {                                   -- branch-free merge step
      x := src[p < mid ? p : k]; y := src[q < e ? q : k]
      t := (p < mid) & ((q < e & y < x) ^ 1)        -- take the left element?
      dst[k] := t ? x : y; p := p + t; q := q + (t ^ 1); k := k + 1 }
    i := e }
main:  w := 1; pass(in, out); ww := 2
  while ww < n { w := ww; pass(out, scr); w := ww + ww; pass(scr, out); ww := 4 ww }
```
One pass is `MS.runs leB w src 0` (`Proven/SortMergeList.lean`); every pass doubles the sorted chunk
width, so at the end the output is sorted, and a permutation of the input. -/
import Riscv.Direct.Arr2Src
import Riscv.Direct.SortMergeList
import Riscv.Direct.SortIns

set_option linter.unusedVariables false

namespace Proven

open MS

/-! ## The program -/

def ltE (a b : BExp) : BExp := .bin .ult a b
def addE (a b : BExp) : BExp := .bin .add a b
def minE (a b : BExp) : BExp := .ite (ltE a b) a b

def takeE : BExp :=
  .bin .and (ltE (.var 5) (.var 10)) (.bin .xor (.bin .and (ltE (.var 6) (.var 11)) (ltE (.var 9) (.var 8))) (.const 1))

def innerM (src dst : Nat) : BStmt :=
  .seq (.load 8 src (.ite (ltE (.var 5) (.var 10)) (.var 5) (.var 4)))
  (.seq (.load 9 src (.ite (ltE (.var 6) (.var 11)) (.var 6) (.var 4)))
  (.seq (.assign 7 takeE)
  (.seq (.store dst (.var 4) (.ite (.var 7) (.var 8) (.var 9)))
  (.seq (.assign 5 (addE (.var 5) (.var 7)))
  (.seq (.assign 6 (addE (.var 6) (.bin .xor (.var 7) (.const 1))))
  (.assign 4 (addE (.var 4) (.const 1))))))))

def runM (src dst : Nat) : BStmt :=
  .seq (.assign 10 (minE (addE (.var 12) (.var 13)) (.var 1)))
  (.seq (.assign 11 (minE (addE (addE (.var 12) (.var 13)) (.var 13)) (.var 1)))
  (.seq (.assign 5 (.var 12)) (.seq (.assign 6 (.var 10)) (.seq (.assign 4 (.var 12))
  (.seq (.loop (ltE (.var 4) (.var 11)) (innerM src dst)) (.assign 12 (.var 11)))))))

def passM (src dst : Nat) : BStmt :=
  .seq (.assign 12 (.const 0)) (.loop (ltE (.var 12) (.var 1)) (runM src dst))

def mainBody : BStmt :=
  .seq (.assign 13 (.var 14)) (.seq (passM 2 1) (.seq (.assign 13 (addE (.var 14) (.var 14))) (.seq (passM 1 2)
    (.assign 14 (addE (addE (.var 14) (.var 14)) (addE (.var 14) (.var 14)))))))

def msortProg : BStmt :=
  .seq (.assign 13 (.const 1)) (.seq (passM 0 2) (.seq (.assign 14 (.const 2))
    (.loop (ltE (.var 14) (.var 1)) mainBody)))

/-! ## List helpers -/

theorem seg_cons (S : List (BitVec 8)) {a len k j : Nat} (hj : a + k = j) (hk : k < len) (hjl : j < S.length) :
    ((S.drop a).take len).drop k = S[j] :: ((S.drop a).take len).drop (k + 1) := by
  subst hj; rw [List.drop_eq_getElem_cons (by simp; omega)]; simp

theorem seg_nil (S : List (BitVec 8)) {a len k : Nat} (hk : len ≤ k ∨ S.length ≤ a + k) :
    ((S.drop a).take len).drop k = [] := by
  apply List.drop_of_length_le; simp; omega

theorem set_mid {A rest : List (BitVec 8)} {k : Nat} (hk : A.length = k) (hr : rest ≠ []) (x : BitVec 8) :
    (A ++ rest).set k x = A ++ [x] ++ rest.tail := by
  obtain _ | ⟨r, rt⟩ := rest
  · exact absurd rfl hr
  · rw [List.set_append_right _ _ (by omega), hk, Nat.sub_self, List.set_cons_zero]; simp

theorem leB_iff (a b : BitVec 8) : leB a b = true ↔ a ≤ b := by simp [leB]

/-! ## The merge step -/

section
variable (src dst : Nat) (S : List (BitVec 8)) (H : Heap) (Done : List (BitVec 8)) (i w : Nat)

theorem ult8 (a b : BitVec 8) : Op.eval .ult (a.setWidth 64) (b.setWidth 64) = if a < b then 1 else 0 := by
  simp only [Op.eval, bv8_lt]

theorem and01' (p q : Prop) [Decidable p] [Decidable q] :
    Op.eval .and (if p then 1 else 0 : BitVec 64) (if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  simp only [Op.eval]; exact and01 p q

theorem add1a (a : Nat) : BitVec.ofNat 64 a + 1 = BitVec.ofNat 64 (a + 1) := (BitVec.ofNat_add a 1).symm

theorem add1 (a : Nat) : Op.eval .add (BitVec.ofNat 64 a) 1 = BitVec.ofNat 64 (a + 1) := (BitVec.ofNat_add a 1).symm

theorem inner_step (hsd : src ≠ dst) (hs : src < H.length) (hd : dst < H.length) (hS : H[src] = S)
    (hn : S.length < 2 ^ 32) (hi : i < S.length) (hw : 0 < w) (hw' : w < 2 ^ 33) (hDone : Done.length = i)
    (env : BEnv) (p q : Nat) (W rs : List (BitVec 8))
    (hip : i ≤ p) (hpm : p ≤ min (i + w) S.length) (hmq : min (i + w) S.length ≤ q)
    (hqe : q ≤ min (i + w + w) S.length)
    (e10 : env 10 = BitVec.ofNat 64 (min (i + w) S.length)) (e11 : env 11 = BitVec.ofNat 64 (min (i + w + w) S.length))
    (e5 : env 5 = BitVec.ofNat 64 p) (e6 : env 6 = BitVec.ofNat 64 q)
    (e4 : env 4 = BitVec.ofNat 64 (p + q - min (i + w) S.length))
    (hW : W.length = (p - i) + (q - min (i + w) S.length)) (hlen : (Done ++ W ++ rs).length = S.length)
    (hmerge : W ++ (((S.drop i).take w).drop (p - i)).merge (((S.drop (i + w)).take w).drop (q - min (i + w) S.length)) leB
      = ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB)
    (hk : p + q - min (i + w) S.length < min (i + w + w) S.length) :
    ∃ τ, BExec (innerM src dst) ⟨env, H.set dst (Done ++ W ++ rs)⟩ τ ∧
      (τ.env 10 = BitVec.ofNat 64 (min (i + w) S.length) ∧ τ.env 11 = BitVec.ofNat 64 (min (i + w + w) S.length) ∧
      ∃ p q W rs, i ≤ p ∧ p ≤ min (i + w) S.length ∧ min (i + w) S.length ≤ q ∧ q ≤ min (i + w + w) S.length ∧
        τ.env 5 = BitVec.ofNat 64 p ∧ τ.env 6 = BitVec.ofNat 64 q ∧
        τ.env 4 = BitVec.ofNat 64 (p + q - min (i + w) S.length) ∧ τ.heap = H.set dst (Done ++ W ++ rs) ∧
        W.length = (p - i) + (q - min (i + w) S.length) ∧ (Done ++ W ++ rs).length = S.length ∧
        W ++ (((S.drop i).take w).drop (p - i)).merge (((S.drop (i + w)).take w).drop (q - min (i + w) S.length)) leB
          = ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB) ∧
      min (i + w + w) S.length - (τ.env 4).toNat < min (i + w + w) S.length - (env 4).toNat := by
  generalize hmid : min (i + w) S.length = mid at *
  generalize he : min (i + w + w) S.length = e at *
  generalize hk' : p + q - mid = k at *
  have hkn : k < S.length := by omega
  have hHs : (H.set dst (Done ++ W ++ rs))[src]? = some S := by
    rw [List.getElem?_set_ne (Ne.symm hsd), List.getElem?_eq_getElem hs, hS]
  have hHd : (H.set dst (Done ++ W ++ rs))[dst]? = some (Done ++ W ++ rs) := List.getElem?_set_self hd
  have hix : (BExp.denote env (.ite (ltE (.var 5) (.var 10)) (.var 5) (.var 4))).toNat =
      if p < mid then p else k := by
    simp only [BExp.denote, ltE, e5, e10, e4, ult_ofNat (show p < 2 ^ 64 by omega) (show mid < 2 ^ 64 by omega)]
    by_cases h : p < mid <;> simp only [h, if_true, if_false, ite01_eq0, not_true, not_false_eq_true] <;>
      exact toNat_ofNat' (by omega)
  have hixn : (if p < mid then p else k) < S.length := by split <;> omega
  have hiyn : (if q < e then q else k) < S.length := by split <;> omega
  obtain ⟨x, hxv⟩ : ∃ x, S[if p < mid then p else k]? = some x := ⟨_, List.getElem?_eq_getElem hixn⟩
  have hiy : (BExp.denote (env.set 8 (x.setWidth 64)) (.ite (ltE (.var 6) (.var 11)) (.var 6) (.var 4))).toNat =
      if q < e then q else k := by
    simp only [BExp.denote, ltE, BEnv.set, e6, e11, e4, Nat.reduceEqDiff, if_false,
      ult_ofNat (show q < 2 ^ 64 by omega) (show e < 2 ^ 64 by omega)]
    by_cases h : q < e <;> simp only [h, if_true, if_false, ite01_eq0, not_true, not_false_eq_true] <;>
      exact toNat_ofNat' (by omega)
  obtain ⟨y, hyv⟩ : ∃ y, S[if q < e then q else k]? = some y := ⟨_, List.getElem?_eq_getElem hiyn⟩
  have ht : takeE.denote ((env.set 8 (x.setWidth 64)).set 9 (y.setWidth 64)) =
      if p < mid ∧ ¬(q < e ∧ y < x) then 1 else 0 := by
    simp only [takeE, BExp.denote, ltE, BEnv.set, e5, e6, e10, e11, Nat.reduceEqDiff, if_false, if_true,
      ult_ofNat (show q < 2 ^ 64 by omega) (show e < 2 ^ 64 by omega),
      ult_ofNat (show p < 2 ^ 64 by omega) (show mid < 2 ^ 64 by omega), ult8, and01', xor01]
  refine ⟨_, .seq (BExec.load' hHs hix hxv)
    (.seq (BExec.load' hHs hiy hyv) (.seq (BExec.assign' rfl)
    (.seq (BExec.store' (j := k) hHd (by simp only [BExp.denote, BEnv.set, Nat.reduceEqDiff, if_false, e4]; exact toNat_ofNat' (by omega)) (by omega))
    (.seq (BExec.assign' rfl) (.seq (BExec.assign' rfl) (BExec.assign' rfl)))))), ?_⟩
  simp only [BExp.denote, BEnv.set, Nat.reduceEqDiff, if_false, if_true, ht, addE, e4, e5, e6, e10, e11]
  have hlk : (Done ++ W).length = k := by simp; omega
  have hrs : rs ≠ [] := by rintro rfl; simp at hlen; omega
  try rw [List.set_set]
  rw [set_mid hlk hrs]
  by_cases htc : p < mid ∧ ¬(q < e ∧ y < x)
  · have hx : x = S[p] := by rw [if_pos htc.1, List.getElem?_eq_getElem (by omega)] at hxv; exact (Option.some.inj hxv).symm
    simp only [htc, if_true, if_false, ite01_eq0, not_true, add1, Op.eval, BitVec.reduceXOr, BitVec.add_zero]
    refine ⟨⟨trivial, trivial, p + 1, q, W ++ [x], rs.tail, by omega, by omega, hmq, hqe, (by first | rfl | exact (BitVec.ofNat_add _ 1).symm | (simp; done) | (simp; exact (BitVec.ofNat_add _ 1).symm)), (by first | rfl | exact (BitVec.ofNat_add _ 1).symm | (simp; done) | (simp; exact (BitVec.ofNat_add _ 1).symm)),
      by rw [add1a]; congr 1; omega, by simp [setWidth8_64], by simp; omega, by simp at hlen ⊢; omega, ?_⟩,
      by rw [add1a, toNat_ofNat' (by omega), toNat_ofNat' (by omega)]; omega⟩
    rw [← hmerge, seg_cons S (a := i) (len := w) (k := p - i) (j := p) (by omega) (by omega) (by omega),
      show p + 1 - i = p - i + 1 by omega, List.append_assoc, ← hx]
    congr 1
    by_cases hqe' : q < e
    · have hy : y = S[q] := by
        rw [if_pos hqe', List.getElem?_eq_getElem (by omega)] at hyv; exact (Option.some.inj hyv).symm
      rw [seg_cons S (a := i + w) (len := w) (k := q - mid) (j := q) (by omega) (by omega) (by omega), ← hy,
        List.cons_merge_cons_pos]
      · rfl
      · rw [leB_iff]; exact BitVec.not_lt.mp fun h => htc.2 ⟨hqe', h⟩
    · rw [seg_nil S (a := i + w) (len := w) (k := q - mid) (by omega), List.merge_right, List.merge_right]; rfl
  · have hq : q < e := by
      by_cases hpm' : p < mid
      · exact (Classical.not_not.mp fun h => htc ⟨hpm', h⟩).1
      · omega
    have hy : y = S[q] := by rw [if_pos hq, List.getElem?_eq_getElem (by omega)] at hyv; exact (Option.some.inj hyv).symm
    simp only [htc, if_true, if_false, ite01_eq0, not_true, not_false_eq_true, add1, Op.eval, BitVec.reduceXOr,
      BitVec.add_zero]
    refine ⟨⟨trivial, trivial, p, q + 1, W ++ [y], rs.tail, hip, hpm, by omega, by omega, (by first | rfl | exact (BitVec.ofNat_add _ 1).symm | (simp; done) | (simp; exact (BitVec.ofNat_add _ 1).symm)), (by first | rfl | exact (BitVec.ofNat_add _ 1).symm | (simp; done) | (simp; exact (BitVec.ofNat_add _ 1).symm)),
      by rw [add1a]; congr 1; omega, by simp [setWidth8_64], by simp; omega, by simp at hlen ⊢; omega, ?_⟩,
      by rw [add1a, toNat_ofNat' (by omega), toNat_ofNat' (by omega)]; omega⟩
    rw [← hmerge, seg_cons S (a := i + w) (len := w) (k := q - mid) (j := q) (by omega) (by omega) (by omega),
      show q + 1 - mid = q - mid + 1 by omega, List.append_assoc, ← hy]
    congr 1
    by_cases hpm' : p < mid
    · have hx : x = S[p] := by
        rw [if_pos hpm', List.getElem?_eq_getElem (by omega)] at hxv; exact (Option.some.inj hxv).symm
      rw [seg_cons S (a := i) (len := w) (k := p - i) (j := p) (by omega) (by omega) (by omega), ← hx,
        List.cons_merge_cons_neg]
      · rfl
      · rw [leB_iff]; intro hle
        exact htc ⟨hpm', fun h => BitVec.not_lt.mpr hle h.2⟩
    · rw [seg_nil S (a := i) (len := w) (k := p - i) (by omega), List.nil_merge, List.nil_merge]; rfl

/-- the inner loop merges `L = S[i, i+w)` and `R = S[i+w, i+2w)` into `dst[i ..]` -/
theorem merge_inner_exec (hsd : src ≠ dst) (hs : src < H.length) (hd : dst < H.length) (hS : H[src] = S)
    (hn : S.length < 2 ^ 32) (hi : i < S.length) (hw : 0 < w) (hw' : w < 2 ^ 33) (hDone : Done.length = i)
    (σ : BState) (rest : List (BitVec 8)) (hrest : (Done ++ rest).length = S.length)
    (hh : σ.heap = H.set dst (Done ++ rest))
    (h10 : σ.env 10 = BitVec.ofNat 64 (min (i + w) S.length)) (h11 : σ.env 11 = BitVec.ofNat 64 (min (i + w + w) S.length))
    (h5 : σ.env 5 = BitVec.ofNat 64 i) (h6 : σ.env 6 = BitVec.ofNat 64 (min (i + w) S.length))
    (h4 : σ.env 4 = BitVec.ofNat 64 i) :
    ∃ σ', BExec (.loop (ltE (.var 4) (.var 11)) (innerM src dst)) σ σ' ∧ ∃ rest',
      σ'.heap = H.set dst (Done ++ ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB ++ rest') ∧
      (Done ++ ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB ++ rest').length = S.length := by
  let n := S.length
  let mid := min (i + w) n
  let e := min (i + w + w) n
  let L := (S.drop i).take w
  let R := (S.drop (i + w)).take w
  have hmid : mid = min (i + w) n := rfl
  have he : e = min (i + w + w) n := rfl
  have hL : L.length = mid - i := by simp [L, hmid]; omega
  have hR : R.length = e - mid := by simp [R, hmid, he]; omega
  have hS' : ∀ τ : BState, τ.heap = H.set dst (Done ++ rest) ∨ True → True := fun _ _ => trivial
  obtain ⟨σ', hl, hq⟩ := BExec.loop_inv (c := ltE (.var 4) (.var 11)) (b := innerM src dst)
    (fun τ => τ.env 10 = BitVec.ofNat 64 mid ∧ τ.env 11 = BitVec.ofNat 64 e ∧
      ∃ p q W rs, i ≤ p ∧ p ≤ mid ∧ mid ≤ q ∧ q ≤ e ∧ τ.env 5 = BitVec.ofNat 64 p ∧ τ.env 6 = BitVec.ofNat 64 q ∧
        τ.env 4 = BitVec.ofNat 64 (p + q - mid) ∧ τ.heap = H.set dst (Done ++ W ++ rs) ∧
        W.length = (p - i) + (q - mid) ∧ (Done ++ W ++ rs).length = n ∧
        W ++ (L.drop (p - i)).merge (R.drop (q - mid)) leB = L.merge R leB)
    (fun τ => ∃ rest', τ.heap = H.set dst (Done ++ L.merge R leB ++ rest') ∧
      (Done ++ L.merge R leB ++ rest').length = n)
    (fun τ => e - (τ.env 4).toNat)
    (fun ⟨env, heap⟩ ⟨e10, e11, p, q, W, rs, hip, hpm, hmq, hqe, e5, e6, e4, eh, hW, hlen, hmerge⟩ hc => by
      dsimp only at e10 e11 e5 e6 e4 eh hc ⊢
      subst eh
      have hk : p + q - mid < e := by
        simp only [ltE, BExp.denote, e4, e11] at hc
        rw [ult_ofNat (by omega) (by omega)] at hc; by_cases h : p + q - mid < e
        · exact h
        · simp [h] at hc
      exact inner_step src dst S H Done i w hsd hs hd hS hn hi hw hw' hDone env p q W rs hip hpm hmq hqe
        e10 e11 e5 e6 e4 hW hlen hmerge hk)
    (fun τ ⟨e10, e11, p, q, W, rs, hip, hpm, hmq, hqe, e5, e6, e4, eh, hW, hlen, hmerge⟩ hc => by
      have hk : ¬ p + q - mid < e := by
        simp only [ltE, BExp.denote, e4, e11] at hc
        rw [ult_ofNat (by omega) (by omega)] at hc; intro h; simp [h] at hc
      have hp : p - i = L.length := by omega
      have hq : q - mid = R.length := by omega
      rw [hp, hq, List.drop_length, List.drop_length, List.nil_merge, List.append_nil] at hmerge
      exact ⟨rs, by rw [eh, hmerge], by rw [← hmerge]; exact hlen⟩)
    σ ⟨by rw [h10], by rw [h11], i, mid, [], rest, Nat.le_refl _, by omega, Nat.le_refl _, by omega, h5, h6,
      by rw [h4]; congr 1; omega, by rw [hh]; simp, by simp, by simpa using hrest, by simp⟩
  exact ⟨σ', hl, hq⟩

theorem minE_val {env : BEnv} {a b : BExp} {x y : Nat} (ha : a.denote env = BitVec.ofNat 64 x)
    (hb : b.denote env = BitVec.ofNat 64 y) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (minE a b).denote env = BitVec.ofNat 64 (min x y) := by
  simp only [minE, ltE, BExp.denote, ha, hb, ult_ofNat hx hy]
  by_cases h : x < y
  · simp [h]; congr 1; omega
  · simp [h]; congr 1; omega

theorem innerM_assigns (src dst : Nat) : (innerM src dst).assigns = [8, 9, 7, 5, 6, 4] := rfl
theorem passM_assigns (src dst : Nat) : (passM src dst).assigns = [12, 10, 11, 5, 6, 4, 8, 9, 7, 5, 6, 4, 12] := rfl

/-- one pair of runs: `runM` appends `merge L R` to the done prefix of `dst` -/
theorem run_exec (hsd : src ≠ dst) (hs : src < H.length) (hd : dst < H.length) (hS : H[src] = S)
    (hn : S.length < 2 ^ 32) (hi : i < S.length) (hw : 0 < w) (hw' : w < 2 ^ 33) (hDone : Done.length = i)
    (σ : BState) (rest : List (BitVec 8)) (hrest : (Done ++ rest).length = S.length)
    (hh : σ.heap = H.set dst (Done ++ rest)) (h1 : σ.env 1 = BitVec.ofNat 64 S.length)
    (h12 : σ.env 12 = BitVec.ofNat 64 i) (h13 : σ.env 13 = BitVec.ofNat 64 w) :
    ∃ σ', BExec (runM src dst) σ σ' ∧ σ'.env 1 = σ.env 1 ∧ σ'.env 13 = σ.env 13 ∧
      σ'.env 12 = BitVec.ofNat 64 (min (i + w + w) S.length) ∧ ∃ rest',
      σ'.heap = H.set dst (Done ++ ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB ++ rest') ∧
      (Done ++ ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB ++ rest').length = S.length := by
  let M : BExp := minE (addE (.var 12) (.var 13)) (.var 1)
  let E : BExp := minE (addE (addE (.var 12) (.var 13)) (.var 13)) (.var 1)
  have v10 : M.denote σ.env = BitVec.ofNat 64 (min (i + w) S.length) :=
    minE_val (by simp only [addE, BExp.denote, h12, h13, add_ofNat]) (by simp only [BExp.denote, h1]) (by omega) (by omega)
  have v11 : E.denote (σ.asg 10 M).env = BitVec.ofNat 64 (min (i + w + w) S.length) :=
    minE_val (by simp only [addE, BExp.denote, BState.asg_env, Nat.reduceEqDiff, if_false, h12, h13, add_ofNat])
      (by simp only [BExp.denote, BState.asg_env, Nat.reduceEqDiff, if_false, h1]) (by omega) (by omega)
  let σ5 := ((((σ.asg 10 M).asg 11 E).asg 5 (.var 12)).asg 6 (.var 10)).asg 4 (.var 12)
  have g : ∀ j, j ≠ 10 → j ≠ 11 → j ≠ 5 → j ≠ 6 → j ≠ 4 → σ5.env j = σ.env j := fun j a b c d f => by
    simp only [σ5, BState.asg_env, if_neg a, if_neg b, if_neg c, if_neg d, if_neg f]
  obtain ⟨σ6, hex6, rest', hh6, hl6⟩ := merge_inner_exec src dst S H Done i w hsd hs hd hS hn hi hw hw' hDone σ5
    rest hrest (by simpa [σ5] using hh)
    (by simp only [σ5, BState.asg_env, Nat.reduceEqDiff, if_false, if_true]; exact v10)
    (by simp only [σ5, BState.asg_env, Nat.reduceEqDiff, if_false, if_true]; exact v11)
    (by simp only [σ5, BState.asg_env, Nat.reduceEqDiff, if_false, if_true, BExp.denote]; exact h12)
    (by simp only [σ5, BState.asg_env, Nat.reduceEqDiff, if_false, if_true, BExp.denote]; exact v10)
    (by simp only [σ5, BState.asg_env, Nat.reduceEqDiff, if_false, if_true, BExp.denote]; exact h12)
  have k : ∀ j, j ∉ [8, 9, 7, 5, 6, 4] → σ6.env j = σ5.env j := fun j hj => hex6.env_keep (by
    simpa [BStmt.assigns, innerM_assigns] using hj)
  refine ⟨σ6.asg 12 (.var 11), .seq BExec.asg (.seq BExec.asg (.seq BExec.asg (.seq BExec.asg
    (.seq BExec.asg (.seq hex6 BExec.asg))))), ?_, ?_, ?_, rest', hh6, hl6⟩
  · simp only [BState.asg_env, Nat.reduceEqDiff, if_false]
    rw [k 1 (by decide), g 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · simp only [BState.asg_env, Nat.reduceEqDiff, if_false]
    rw [k 13 (by decide), g 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · simp only [BState.asg_env, if_true, BExp.denote]
    rw [k 11 (by decide)]; simp only [σ5, BState.asg_env, Nat.reduceEqDiff, if_false, if_true]; exact v11

theorem runs_min {w : Nat} {S : List (BitVec 8)} {i : Nat} (hw : 0 < w) :
    runs leB w S (min (i + w + w) S.length) = runs leB w S (i + 2 * w) := by
  by_cases h : i + 2 * w ≤ S.length
  · rw [show min (i + w + w) S.length = i + 2 * w by omega]
  · rw [runs_end leB (by omega), runs_end leB (by omega)]

/-- one pass: `dst := runs leB w S 0` -/
theorem pass_exec (hsd : src ≠ dst) (hs : src < H.length) (hd : dst < H.length) (hS : H[src] = S)
    (hD : H[dst].length = S.length) (hn : S.length < 2 ^ 32) (hw : 0 < w) (hw' : w < 2 ^ 33)
    (σ : BState) (hh : σ.heap = H) (h1 : σ.env 1 = BitVec.ofNat 64 S.length) (h13 : σ.env 13 = BitVec.ofNat 64 w) :
    ∃ σ', BExec (passM src dst) σ σ' ∧ σ'.heap = H.set dst (runs leB w S 0) := by
  obtain ⟨σ', hl, hq⟩ := BExec.loop_inv (c := ltE (.var 12) (.var 1)) (b := runM src dst)
    (fun τ => τ.env 1 = BitVec.ofNat 64 S.length ∧ τ.env 13 = BitVec.ofNat 64 w ∧ ∃ i Done rest,
      τ.env 12 = BitVec.ofNat 64 i ∧ i ≤ S.length ∧ τ.heap = H.set dst (Done ++ rest) ∧ Done.length = i ∧
      (Done ++ rest).length = S.length ∧ Done ++ runs leB w S i = runs leB w S 0)
    (fun τ => τ.heap = H.set dst (runs leB w S 0))
    (fun τ => S.length - (τ.env 12).toNat)
    (fun τ ⟨e1, e13, i, Done, rest, e12, hin, eh, hDone, hl, hr⟩ hc => by
      have hi : i < S.length := by
        simp only [ltE, BExp.denote, e12, e1, ult_ofNat (show i < 2 ^ 64 by omega) (show S.length < 2 ^ 64 by omega)] at hc
        exact Classical.byContradiction fun h => by simp [h] at hc
      obtain ⟨σ₁, hex, k1, k13, k12, rest', hh', hl'⟩ :=
        run_exec src dst S H Done i w hsd hs hd hS hn hi hw hw' hDone τ rest hl eh e1 e12 e13
      refine ⟨σ₁, hex, ⟨k1.trans e1, k13.trans e13, _, _, rest', k12, by omega, hh', by simp; omega, hl', ?_⟩, ?_⟩
      · rw [runs_min hw, List.append_assoc, ← runs_step leB hi hw, hr]
      · dsimp only; rw [k12, e12, toNat_ofNat' (by omega), toNat_ofNat' (by omega)]; omega)
    (fun τ ⟨e1, e13, i, Done, rest, e12, hin, eh, hDone, hl, hr⟩ hc => by
      have hi : ¬ i < S.length := by
        simp only [ltE, BExp.denote, e12, e1, ult_ofNat (show i < 2 ^ 64 by omega) (show S.length < 2 ^ 64 by omega)] at hc
        intro h; simp [h] at hc
      have hr0 : rest = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
      rw [runs_end leB (by omega), List.append_nil] at hr
      dsimp only; rw [eh, hr0, List.append_nil, hr])
    ⟨σ.env.set 12 0, σ.heap⟩ ⟨by simp [BEnv.set, h1], by simp [BEnv.set, h13], 0, [], H[dst], by simp [BEnv.set],
      by omega, by rw [hh, List.nil_append, List.set_getElem_self], rfl, by simpa using hD, by simp⟩
  exact ⟨σ', .seq (BExec.assign' rfl) hl, hq⟩

end

/-! ## The whole sort -/

theorem leB_trans : ∀ a b c : BitVec 8, leB a b → leB b c → leB a c := by
  intro a b c h1 h2; simp only [leB, decide_eq_true_eq] at *; exact BitVec.le_trans h1 h2
theorem leB_total : ∀ a b : BitVec 8, leB a b || leB b a := by
  intro a b; simp only [leB, Bool.or_eq_true, decide_eq_true_eq]; exact BitVec.le_total a b

theorem runs_CS0 {w : Nat} (hw : 0 < w) {S : List (BitVec 8)} (h : CS leB w S) : CS leB (2 * w) (runs leB w S 0) := by
  have := runs_CS leB leB_trans leB_total hw h 0; rwa [Nat.zero_mul] at this

theorem pass_keep {src dst : Nat} {σ σ' : BState} (h : BExec (passM src dst) σ σ') {v : Nat}
    (hv : v ∉ [12, 10, 11, 5, 6, 4, 8, 9, 7]) : σ'.env v = σ.env v :=
  h.env_keep fun hm => hv (by
    rw [passM_assigns] at hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; omega)

/-- **The merge sort program computes `List.mergeSort`**: blocks `[xs, scr, out]` with `|scr| = |out| = |xs|`,
`v1 = |xs|`; at the end the output block is `xs.mergeSort leB` (the scratch block holds some list). -/
theorem msortProg_mergeSort (xs scr out : List (BitVec 8)) (σ : BState) (hh : σ.heap = [xs, scr, out])
    (h1 : σ.env 1 = BitVec.ofNat 64 xs.length) (hn : xs.length < 2 ^ 32) (hscr : scr.length = xs.length)
    (hout : out.length = xs.length) :
    ∃ σ', BExec msortProg σ σ' ∧ ∃ scr', σ'.heap = [xs, scr', xs.mergeSort leB] := by
  have hn64 : xs.length < 2 ^ 64 := by omega
  -- first pass: input → output, width 1
  obtain ⟨σ₂, hex₂, hh₂⟩ := pass_exec 0 2 xs [xs, scr, out] 1 (by decide) (by simp) (by simp) rfl (by simpa using hout)
    hn (by decide) (by decide) (σ.asg 13 (.const 1)) hh (by simp [h1]) (by simp [BExp.denote])
  have k1 : σ₂.env 1 = σ.env 1 := by rw [pass_keep hex₂ (by decide)]; simp
  simp only [List.set_cons_succ, List.set_cons_zero] at hh₂
  -- main loop
  obtain ⟨σ', hl, hq⟩ := BExec.loop_inv (c := ltE (.var 14) (.var 1)) (b := mainBody)
    (fun τ => τ.env 1 = BitVec.ofNat 64 xs.length ∧ ∃ ww s o, τ.env 14 = BitVec.ofNat 64 ww ∧ 2 ≤ ww ∧
      ww < 2 ^ 34 ∧ τ.heap = [xs, s, o] ∧ s.length = xs.length ∧ o.length = xs.length ∧ o.Perm xs ∧ CS leB ww o)
    (fun τ => ∃ scr', τ.heap = [xs, scr', xs.mergeSort leB])
    (fun τ => xs.length - (τ.env 14).toNat)
    (fun τ ⟨e1, ww, s, o, e14, hww, hww', eh, hs, ho, hp, hcs⟩ hc => by
      have hlt : ww < xs.length := by
        simp only [ltE, BExp.denote, e14, e1, ult_ofNat (show ww < 2 ^ 64 by omega) hn64] at hc
        exact Classical.byContradiction fun h => by simp [h] at hc
      obtain ⟨τ₂, hex₂, hh₂⟩ := pass_exec 2 1 o [xs, s, o] ww (by decide) (by simp) (by simp) rfl (by simp [hs, ho])
        (by omega) (by omega) (by omega) (τ.asg 13 (.var 14)) eh (by simp [e1, ho]) (by simp [BExp.denote, e14])
      simp only [List.set_cons_succ, List.set_cons_zero] at hh₂
      have k2 : ∀ v ∈ [1, 13, 14], τ₂.env v = (τ.asg 13 (.var 14)).env v := fun v hv => pass_keep hex₂ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; omega)
      have g14 : τ₂.env 14 = BitVec.ofNat 64 ww := by rw [k2 14 (by simp)]; simp [e14]
      have g1 : τ₂.env 1 = BitVec.ofNat 64 xs.length := by rw [k2 1 (by simp)]; simp [e1]
      have hl1 : (runs leB ww o 0).length = xs.length := by rw [runs_length leB (by omega), ho]; rfl
      obtain ⟨τ₄, hex₄, hh₄⟩ := pass_exec 1 2 (runs leB ww o 0) [xs, runs leB ww o 0, o] (ww + ww) (by decide)
        (by simp) (by simp) rfl (by simp [hl1, ho]) (by rw [hl1]; omega) (by omega) (by omega)
        (τ₂.asg 13 (addE (.var 14) (.var 14))) hh₂ (by simp [g1, hl1])
        (by simp only [BState.asg_env, if_true, addE, BExp.denote, g14, add_ofNat])
      simp only [List.set_cons_succ, List.set_cons_zero] at hh₄
      have k4 : ∀ v ∈ [1, 14], τ₄.env v = (τ₂.asg 13 (addE (.var 14) (.var 14))).env v := fun v hv =>
        pass_keep hex₄ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; omega)
      have g14' : τ₄.env 14 = BitVec.ofNat 64 ww := by rw [k4 14 (by simp)]; simp [g14]
      have g1' : τ₄.env 1 = BitVec.ofNat 64 xs.length := by rw [k4 1 (by simp)]; simp [g1]
      refine ⟨τ₄.asg 14 (addE (addE (.var 14) (.var 14)) (addE (.var 14) (.var 14))),
        .seq BExec.asg (.seq hex₂ (.seq BExec.asg (.seq hex₄ BExec.asg))),
        ⟨?_, ww + ww + (ww + ww), runs leB ww o 0, runs leB (ww + ww) (runs leB ww o 0) 0, ?_, by omega, by omega,
          hh₄, hl1, by rw [runs_length leB (by omega), hl1]; rfl, ?_, ?_⟩, ?_⟩
      · simp only [BState.asg_env, Nat.reduceEqDiff, if_false]; exact g1'
      · simp only [BState.asg_env, if_true, addE, BExp.denote, g14', add_ofNat]
      · exact ((runs_perm leB (by omega) _ 0).trans (runs_perm leB (by omega) _ 0)).trans hp
      · have := runs_CS0 (show 0 < ww + ww by omega) (by rw [← Nat.two_mul]; exact runs_CS0 (by omega) hcs)
        rwa [show 2 * (ww + ww) = ww + ww + (ww + ww) by omega] at this
      · show xs.length - (BExp.denote τ₄.env (addE (addE (.var 14) (.var 14)) (addE (.var 14) (.var 14)))).toNat <
          xs.length - (τ.env 14).toNat
        simp only [addE, BExp.denote, g14', add_ofNat, e14]
        rw [toNat_ofNat' (by omega), toNat_ofNat' (by omega)]; omega)
    (fun τ ⟨e1, ww, s, o, e14, hww, hww', eh, hs, ho, hp, hcs⟩ hc => by
      have hge : ¬ ww < xs.length := by
        simp only [ltE, BExp.denote, e14, e1, ult_ofNat (show ww < 2 ^ 64 by omega) hn64] at hc
        intro h; simp [h] at hc
      have hsort := CS_sorted leB hcs (by omega)
      exact ⟨s, by rw [eh, sorted_perm_eq (hsort.imp fun h => (leB_iff _ _).mp h) (sorted_mergeSort xs)
        (hp.trans (List.mergeSort_perm xs leB).symm)]⟩)
    (σ₂.asg 14 (.const 2))
    ⟨by simp only [BState.asg_env, Nat.reduceEqDiff, if_false]; rw [k1, h1], 2, scr, runs leB 1 xs 0,
      by simp [BExp.denote], by decide, by decide, by simpa using hh₂, hscr,
      by rw [runs_length leB (by decide)]; rfl, runs_perm leB (by decide) xs 0, runs_CS0 (by decide) (CS_one leB xs)⟩
  exact ⟨σ', .seq BExec.asg (.seq hex₂ (.seq BExec.asg hl)), hq⟩

end Proven
