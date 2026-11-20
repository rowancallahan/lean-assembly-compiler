/- Bottom-up merge sort with a BRANCHY merge, as a `BStmt` program, proved at source level to compute
`List.mergeSort` (`msortProgB_mergeSort`).  Same blocks, variables and outer loops as `msortProg`
(`Riscv/Direct/SortMergeSrc.lean`); only the merge of two runs differs:
```
  while p < mid ∧ q < e {                       -- both runs nonempty (short-circuit test)
    x := src[p]; y := src[q]
    q := y < x ? q + 1 : q; p := y < x ? p : p + 1  -- take the right element only if strictly smaller
    x := y < x ? y : x; dst[k] := x; k := k + 1 }
  while p < mid { x := src[p]; dst[k] := x; p := p + 1; k := k + 1 }   -- left tail
  while q < e { y := src[q]; dst[k] := y; q := q + 1; k := k + 1 }     -- right tail
```
Each `c ? a : b` with `a` or `b` the destination compiles to a compare-and-branch over one instruction. -/
import Riscv.Direct.SortMergeSrc

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Proven

open MS

/-! ## The program -/

def one : BExp := .const 1
def lt98 : BExp := ltE (.var 9) (.var 8)

def mergeA (src dst : Nat) : BStmt :=
  .seq (.load 8 src (.var 5))
  (.seq (.load 9 src (.var 6))
  (.seq (.assign 6 (.ite lt98 (addE (.var 6) one) (.var 6)))
  (.seq (.assign 5 (.ite lt98 (.var 5) (addE (.var 5) one)))
  (.seq (.assign 8 (.ite lt98 (.var 9) (.var 8)))
  (.seq (.store dst (.var 4) (.var 8))
  (.assign 4 (addE (.var 4) one)))))))

def tailL (src dst : Nat) : BStmt :=
  .seq (.load 8 src (.var 5)) (.seq (.store dst (.var 4) (.var 8))
  (.seq (.assign 5 (addE (.var 5) one)) (.assign 4 (addE (.var 4) one))))

def tailR (src dst : Nat) : BStmt :=
  .seq (.load 9 src (.var 6)) (.seq (.store dst (.var 4) (.var 9))
  (.seq (.assign 6 (addE (.var 6) one)) (.assign 4 (addE (.var 4) one))))

def condA : BExp := .ite (ltE (.var 5) (.var 10)) (ltE (.var 6) (.var 11)) (.const 0)

def mergeB (src dst : Nat) : BStmt :=
  .seq (.loop condA (mergeA src dst)) (.seq (.loop (ltE (.var 5) (.var 10)) (tailL src dst))
    (.loop (ltE (.var 6) (.var 11)) (tailR src dst)))

def runB (src dst : Nat) : BStmt :=
  .seq (.assign 10 (minE (addE (.var 12) (.var 13)) (.var 1)))
  (.seq (.assign 11 (minE (addE (addE (.var 12) (.var 13)) (.var 13)) (.var 1)))
  (.seq (.assign 5 (.var 12)) (.seq (.assign 6 (.var 10)) (.seq (.assign 4 (.var 12))
  (.seq (mergeB src dst) (.assign 12 (.var 11)))))))

def passB (src dst : Nat) : BStmt :=
  .seq (.assign 12 (.const 0)) (.loop (ltE (.var 12) (.var 1)) (runB src dst))

def mainBodyB : BStmt :=
  .seq (.assign 13 (.var 14)) (.seq (passB 2 1) (.seq (.assign 13 (addE (.var 14) (.var 14))) (.seq (passB 1 2)
    (.assign 14 (addE (addE (.var 14) (.var 14)) (addE (.var 14) (.var 14)))))))

def msortProgB : BStmt :=
  .seq (.assign 13 (.const 1)) (.seq (passB 0 2) (.seq (.assign 14 (.const 2))
    (.loop (ltE (.var 14) (.var 1)) mainBodyB)))

/-! ## The merge invariant -/

section
variable (src dst : Nat) (S : List (BitVec 8)) (H : Heap) (Done : List (BitVec 8)) (i w mid e : Nat)

/-- `dst[i, k)` holds `W`, a prefix of `merge L R`, with `L = S[i, i+w)` and `R = S[i+w, i+2w)`;
`W ++ merge (L from p) (R from q) = merge L R`; `X p q` is an extra fact per loop -/
@[reducible] def MI (X : Nat → Nat → Prop) (τ : BState) : Prop :=
  τ.env 10 = BitVec.ofNat 64 mid ∧ τ.env 11 = BitVec.ofNat 64 e ∧
  ∃ p q W rs, i ≤ p ∧ p ≤ mid ∧ mid ≤ q ∧ q ≤ e ∧ τ.env 5 = BitVec.ofNat 64 p ∧ τ.env 6 = BitVec.ofNat 64 q ∧
    τ.env 4 = BitVec.ofNat 64 (p + q - mid) ∧ τ.heap = H.set dst (Done ++ W ++ rs) ∧
    W.length = (p - i) + (q - mid) ∧ (Done ++ W ++ rs).length = S.length ∧
    W ++ (((S.drop i).take w).drop (p - i)).merge (((S.drop (i + w)).take w).drop (q - mid)) leB
      = ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB ∧ X p q

variable {src dst S H Done i w mid e}

theorem heap_write {B : List (BitVec 8)} {W rs : List (BitVec 8)} {k : Nat} (hB : B = Done ++ W ++ rs)
    (hk : (Done ++ W).length = k) (hrs : rs ≠ []) (x : BitVec 8) :
    (H.set dst B).set dst (B.set k x) = H.set dst (Done ++ (W ++ [x]) ++ rs.tail) := by
  subst hB; rw [List.set_set, set_mid hk hrs]; simp

theorem MI_left {X : Nat → Nat → Prop} {env : BEnv} {p q : Nat} {W rs : List (BitVec 8)}
    (hmid : mid = min (i + w) S.length) (he : e = min (i + w + w) S.length) (hDone : Done.length = i)
    (hip : i ≤ p) (hpm : p < mid) (hmq : mid ≤ q) (hqe : q ≤ e) (hW : W.length = (p - i) + (q - mid))
    (hlen : (Done ++ W ++ rs).length = S.length)
    (hmerge : W ++ (((S.drop i).take w).drop (p - i)).merge (((S.drop (i + w)).take w).drop (q - mid)) leB
      = ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB)
    (hle : ∀ h : q < e, leB (S[p]'(by omega)) (S[q]'(by omega)) = true) (hX : X (p + 1) q)
    (e10 : env 10 = BitVec.ofNat 64 mid) (e11 : env 11 = BitVec.ofNat 64 e)
    (e5 : env 5 = BitVec.ofNat 64 (p + 1)) (e6 : env 6 = BitVec.ofNat 64 q)
    (e4 : env 4 = BitVec.ofNat 64 (p + q - mid + 1)) :
    MI dst S H Done i w mid e X
      ⟨env, (H.set dst (Done ++ W ++ rs)).set dst ((Done ++ W ++ rs).set (p + q - mid) (S[p]'(by omega)))⟩ := by
  have hrs : rs ≠ [] := by rintro rfl; simp at hlen; omega
  refine ⟨e10, e11, p + 1, q, W ++ [S[p]'(by omega)], rs.tail, by omega, by omega, hmq, hqe, e5, e6,
    by show env 4 = _; rw [e4]; congr 1; omega, heap_write rfl (by simp; omega) hrs _, by simp; omega,
    by simp at hlen ⊢; omega, ?_, hX⟩
  rw [← hmerge, seg_cons S (a := i) (len := w) (k := p - i) (j := p) (by omega) (by omega) (by omega),
    show p + 1 - i = p - i + 1 by omega, List.append_assoc]
  congr 1
  by_cases hq : q < e
  · rw [seg_cons S (a := i + w) (len := w) (k := q - mid) (j := q) (by omega) (by omega) (by omega),
      List.cons_merge_cons_pos (h := hle hq)]
    rfl
  · rw [seg_nil S (a := i + w) (len := w) (k := q - mid) (by omega), List.merge_right, List.merge_right]; rfl

theorem MI_right {X : Nat → Nat → Prop} {env : BEnv} {p q : Nat} {W rs : List (BitVec 8)}
    (hmid : mid = min (i + w) S.length) (he : e = min (i + w + w) S.length) (hDone : Done.length = i)
    (hip : i ≤ p) (hpm : p ≤ mid) (hmq : mid ≤ q) (hqe : q < e) (hW : W.length = (p - i) + (q - mid))
    (hlen : (Done ++ W ++ rs).length = S.length)
    (hmerge : W ++ (((S.drop i).take w).drop (p - i)).merge (((S.drop (i + w)).take w).drop (q - mid)) leB
      = ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB)
    (hlt : ∀ h : p < mid, leB (S[p]'(by omega)) (S[q]'(by omega)) = false) (hX : X p (q + 1))
    (e10 : env 10 = BitVec.ofNat 64 mid) (e11 : env 11 = BitVec.ofNat 64 e)
    (e5 : env 5 = BitVec.ofNat 64 p) (e6 : env 6 = BitVec.ofNat 64 (q + 1))
    (e4 : env 4 = BitVec.ofNat 64 (p + q - mid + 1)) :
    MI dst S H Done i w mid e X
      ⟨env, (H.set dst (Done ++ W ++ rs)).set dst ((Done ++ W ++ rs).set (p + q - mid) (S[q]'(by omega)))⟩ := by
  have hrs : rs ≠ [] := by rintro rfl; simp at hlen; omega
  refine ⟨e10, e11, p, q + 1, W ++ [S[q]'(by omega)], rs.tail, hip, hpm, by omega, by omega, e5, e6,
    by show env 4 = _; rw [e4]; congr 1; omega, heap_write rfl (by simp; omega) hrs _, by simp; omega,
    by simp at hlen ⊢; omega, ?_, hX⟩
  rw [← hmerge, seg_cons S (a := i + w) (len := w) (k := q - mid) (j := q) (by omega) (by omega) (by omega),
    show q + 1 - mid = q - mid + 1 by omega, List.append_assoc]
  congr 1
  by_cases hp : p < mid
  · rw [seg_cons S (a := i) (len := w) (k := p - i) (j := p) (by omega) (by omega) (by omega),
      List.cons_merge_cons_neg (h := by simp [hlt hp])]
    rfl
  · rw [seg_nil S (a := i) (len := w) (k := p - i) (by omega), List.nil_merge, List.nil_merge]; rfl

theorem heap_src (hsd : src ≠ dst) (hs : src < H.length) (hS : H[src] = S) (B : List (BitVec 8)) :
    (H.set dst B)[src]? = some S := by
  rw [List.getElem?_set_ne (Ne.symm hsd), List.getElem?_eq_getElem hs, hS]

theorem le_of_not_lt8 {a b : BitVec 8} (h : ¬ b < a) : leB a b = true := by
  rw [leB_iff]; exact BitVec.not_lt.mp h

theorem not_le_of_lt8 {a b : BitVec 8} (h : b < a) : leB a b = false := by
  simp only [leB, decide_eq_false_iff_not]; exact BitVec.not_le.mpr h

variable (hsd : src ≠ dst) (hs : src < H.length) (hd : dst < H.length) (hS : H[src] = S)
    (hn : S.length < 2 ^ 32) (hw' : w < 2 ^ 33) (hDone : Done.length = i)
    (hmid : mid = min (i + w) S.length) (he : e = min (i + w + w) S.length)
include hsd hs hd hS hn hw' hDone hmid he

theorem stepA (σ : BState) (hI : MI dst S H Done i w mid e (fun _ _ => True) σ) (hc : condA.denote σ.env ≠ 0) :
    ∃ σ₁, BExec (mergeA src dst) σ σ₁ ∧ MI dst S H Done i w mid e (fun _ _ => True) σ₁ ∧
      e - (σ₁.env 4).toNat < e - (σ.env 4).toNat := by
  obtain ⟨env, heap⟩ := σ
  obtain ⟨e10, e11, p, q, W, rs, hip, hpm, hmq, hqe, e5, e6, e4, eh, hW, hlen, hmerge, -⟩ := hI
  dsimp only at e10 e11 e5 e6 e4 eh hc ⊢
  subst eh
  have hpq : p < mid ∧ q < e := by
    simp only [condA, ltE, BExp.denote, e5, e6, e10, e11, ult_ofNat (show p < 2 ^ 64 by omega)
      (show mid < 2 ^ 64 by omega), ult_ofNat (show q < 2 ^ 64 by omega) (show e < 2 ^ 64 by omega)] at hc
    by_cases h1 : p < mid <;> by_cases h2 : q < e <;> simp [h1, h2] at hc ⊢ <;> exact ⟨h1, h2⟩
  obtain ⟨h1, h2⟩ := hpq
  have hHs := heap_src hsd hs hS (Done ++ W ++ rs)
  have hHd : (H.set dst (Done ++ W ++ rs))[dst]? = some (Done ++ W ++ rs) := List.getElem?_set_self hd
  have j5 : ((BExp.var 5).denote env).toNat = p := by simp only [BExp.denote, e5]; exact toNat_ofNat' (by omega)
  refine ⟨_, .seq (BExec.load' (j := p) hHs j5 (List.getElem?_eq_getElem (by omega)))
    (.seq (BExec.load' (j := q) hHs (by simp only [BExp.denote, BEnv.set, Nat.reduceEqDiff, if_false, e6]; exact toNat_ofNat' (by omega)) (List.getElem?_eq_getElem (by omega)))
    (.seq (BExec.assign' rfl) (.seq (BExec.assign' rfl) (.seq (BExec.assign' rfl)
    (.seq (BExec.store' (j := p + q - mid) hHd (by simp only [BExp.denote, BEnv.set, Nat.reduceEqDiff, if_false, e4]; exact toNat_ofNat' (by omega)) (by omega)) (BExec.assign' rfl)))))), ?_⟩
  simp only [BExp.denote, BEnv.set, lt98, one, addE, ltE, Nat.reduceEqDiff, if_true, if_false, ult8, ite01_eq0,
    e4, e5, e6, e10, e11, add1, add1a]
  by_cases hlt : S[q] < S[p]
  · simp only [hlt, not_true, if_false, if_true, setWidth8_64]
    exact ⟨MI_right hmid he hDone hip (by omega) hmq h2 hW hlen hmerge (fun _ => not_le_of_lt8 hlt) trivial
      (by simp [BEnv.set, e10]) (by simp [BEnv.set, e11]) (by simp [BEnv.set]) (by simp [BEnv.set])
      (by simp [BEnv.set]), by rw [toNat_ofNat' (by omega), toNat_ofNat' (by omega)]; omega⟩
  · simp only [hlt, not_false_eq_true, if_false, if_true, setWidth8_64]
    exact ⟨MI_left hmid he hDone hip h1 hmq (by omega) hW hlen hmerge (fun _ => le_of_not_lt8 hlt) trivial
      (by simp [BEnv.set, e10]) (by simp [BEnv.set, e11]) (by simp [BEnv.set]) (by simp [BEnv.set])
      (by simp [BEnv.set]), by rw [toNat_ofNat' (by omega), toNat_ofNat' (by omega)]; omega⟩


theorem stepL (σ : BState) (hI : MI dst S H Done i w mid e (fun p q => p = mid ∨ q = e) σ)
    (hc : (ltE (.var 5) (.var 10)).denote σ.env ≠ 0) :
    ∃ σ₁, BExec (tailL src dst) σ σ₁ ∧ MI dst S H Done i w mid e (fun p q => p = mid ∨ q = e) σ₁ ∧
      e - (σ₁.env 4).toNat < e - (σ.env 4).toNat := by
  obtain ⟨env, heap⟩ := σ
  obtain ⟨e10, e11, p, q, W, rs, hip, hpm, hmq, hqe, e5, e6, e4, eh, hW, hlen, hmerge, hX⟩ := hI
  dsimp only at e10 e11 e5 e6 e4 eh hc hX ⊢
  subst eh
  have h1 : p < mid := by
    simp only [ltE, BExp.denote, e5, e10, ult_ofNat (show p < 2 ^ 64 by omega) (show mid < 2 ^ 64 by omega)] at hc
    by_cases h1 : p < mid <;> simp [h1] at hc ⊢
  have hHs := heap_src hsd hs hS (Done ++ W ++ rs)
  have hHd : (H.set dst (Done ++ W ++ rs))[dst]? = some (Done ++ W ++ rs) := List.getElem?_set_self hd
  have j5 : ((BExp.var 5).denote env).toNat = p := by simp only [BExp.denote, e5]; exact toNat_ofNat' (by omega)
  refine ⟨_, .seq (BExec.load' (j := p) hHs j5 (List.getElem?_eq_getElem (by omega)))
    (.seq (BExec.store' (j := p + q - mid) hHd (by simp only [BExp.denote, BEnv.set, Nat.reduceEqDiff, if_false, e4]; exact toNat_ofNat' (by omega)) (by omega))
    (.seq (BExec.assign' rfl) (BExec.assign' rfl))), ?_⟩
  simp only [BExp.denote, BEnv.set, one, addE, Nat.reduceEqDiff, if_true, if_false, e4, e5, add1, setWidth8_64]
  exact ⟨MI_left hmid he hDone hip h1 hmq hqe hW hlen hmerge (fun h => absurd h (by omega)) (Or.inr (by omega))
    (by simp [BEnv.set, e10]) (by simp [BEnv.set, e11]) (by simp [BEnv.set]) (by simp [BEnv.set, e6])
    (by simp [BEnv.set]), by rw [toNat_ofNat' (by omega), toNat_ofNat' (by omega)]; omega⟩

theorem stepR (σ : BState) (hI : MI dst S H Done i w mid e (fun p q => p = mid) σ)
    (hc : (ltE (.var 6) (.var 11)).denote σ.env ≠ 0) :
    ∃ σ₁, BExec (tailR src dst) σ σ₁ ∧ MI dst S H Done i w mid e (fun p q => p = mid) σ₁ ∧
      e - (σ₁.env 4).toNat < e - (σ.env 4).toNat := by
  obtain ⟨env, heap⟩ := σ
  obtain ⟨e10, e11, p, q, W, rs, hip, hpm, hmq, hqe, e5, e6, e4, eh, hW, hlen, hmerge, hX⟩ := hI
  dsimp only at e10 e11 e5 e6 e4 eh hc hX ⊢
  subst eh
  have h2 : q < e := by
    simp only [ltE, BExp.denote, e6, e11, ult_ofNat (show q < 2 ^ 64 by omega) (show e < 2 ^ 64 by omega)] at hc
    by_cases h2 : q < e <;> simp [h2] at hc ⊢
  have hHs := heap_src hsd hs hS (Done ++ W ++ rs)
  have hHd : (H.set dst (Done ++ W ++ rs))[dst]? = some (Done ++ W ++ rs) := List.getElem?_set_self hd
  have j6 : ((BExp.var 6).denote env).toNat = q := by simp only [BExp.denote, e6]; exact toNat_ofNat' (by omega)
  refine ⟨_, .seq (BExec.load' (j := q) hHs j6 (List.getElem?_eq_getElem (by omega)))
    (.seq (BExec.store' (j := p + q - mid) hHd (by simp only [BExp.denote, BEnv.set, Nat.reduceEqDiff, if_false, e4]; exact toNat_ofNat' (by omega)) (by omega))
    (.seq (BExec.assign' rfl) (BExec.assign' rfl))), ?_⟩
  simp only [BExp.denote, BEnv.set, one, addE, Nat.reduceEqDiff, if_true, if_false, e4, e6, add1, setWidth8_64]
  exact ⟨MI_right hmid he hDone hip hpm hmq h2 hW hlen hmerge (fun h => absurd h (by omega)) hX
    (by simp [BEnv.set, e10]) (by simp [BEnv.set, e11]) (by simp [BEnv.set, e5]) (by simp [BEnv.set])
    (by simp [BEnv.set]), by rw [toNat_ofNat' (by omega), toNat_ofNat' (by omega)]; omega⟩


theorem MI_weaken {X Y : Nat → Nat → Prop} {τ : BState} (h : MI dst S H Done i w mid e X τ)
    (hXY : ∀ p q, i ≤ p → p ≤ mid → mid ≤ q → q ≤ e → τ.env 5 = BitVec.ofNat 64 p → τ.env 6 = BitVec.ofNat 64 q →
      X p q → Y p q) : MI dst S H Done i w mid e Y τ := by
  obtain ⟨e10, e11, p, q, W, rs, hip, hpm, hmq, hqe, e5, e6, e4, eh, hW, hlen, hmerge, hX⟩ := h
  exact ⟨e10, e11, p, q, W, rs, hip, hpm, hmq, hqe, e5, e6, e4, eh, hW, hlen, hmerge,
    hXY p q hip hpm hmq hqe e5 e6 hX⟩

/-- the three loops merge `L = S[i, i+w)` and `R = S[i+w, i+2w)` into `dst[i ..]` -/
theorem mergeB_exec (hi : i < S.length) (hw : 0 < w) (σ : BState) (rest : List (BitVec 8))
    (hrest : (Done ++ rest).length = S.length) (hh : σ.heap = H.set dst (Done ++ rest))
    (h10 : σ.env 10 = BitVec.ofNat 64 mid) (h11 : σ.env 11 = BitVec.ofNat 64 e)
    (h5 : σ.env 5 = BitVec.ofNat 64 i) (h6 : σ.env 6 = BitVec.ofNat 64 mid) (h4 : σ.env 4 = BitVec.ofNat 64 i) :
    ∃ σ', BExec (mergeB src dst) σ σ' ∧ ∃ rest',
      σ'.heap = H.set dst (Done ++ ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB ++ rest') ∧
      (Done ++ ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB ++ rest').length = S.length := by
  have hL : ((S.drop i).take w).length = mid - i := by simp [hmid]; omega
  have hR : ((S.drop (i + w)).take w).length = e - mid := by simp [hmid, he]; omega
  have b64 : ∀ x, x ≤ e → x < 2 ^ 64 := fun x hx => by omega
  obtain ⟨σ₁, x₁, q₁⟩ := BExec.loop_inv (c := condA) (b := mergeA src dst)
    (MI dst S H Done i w mid e (fun _ _ => True)) (MI dst S H Done i w mid e (fun p q => p = mid ∨ q = e))
    (fun τ => e - (τ.env 4).toNat)
    (stepA hsd hs hd hS hn hw' hDone hmid he)
    (fun τ hI hc => MI_weaken hsd hs hd hS hn hw' hDone hmid he hI fun p q hip hpm hmq hqe e5 e6 _ => by
      simp only [condA, ltE, BExp.denote, e5, e6, hI.1, hI.2.1, ult_ofNat (b64 p (by omega)) (b64 mid (by omega)),
        ult_ofNat (b64 q hqe) (b64 e (Nat.le_refl _))] at hc
      by_cases h1 : p < mid <;> by_cases h2 : q < e <;> simp [h1, h2] at hc <;> omega)
    σ ⟨h10, h11, i, mid, [], rest, Nat.le_refl _, by omega, Nat.le_refl _, by omega, h5, h6,
      by rw [h4]; congr 1; omega, by rw [hh]; simp, by simp, by simpa using hrest, by simp, trivial⟩
  obtain ⟨σ₂, x₂, q₂⟩ := BExec.loop_inv (c := ltE (.var 5) (.var 10)) (b := tailL src dst)
    (MI dst S H Done i w mid e (fun p q => p = mid ∨ q = e)) (MI dst S H Done i w mid e (fun p q => p = mid))
    (fun τ => e - (τ.env 4).toNat)
    (stepL hsd hs hd hS hn hw' hDone hmid he)
    (fun τ hI hc => MI_weaken hsd hs hd hS hn hw' hDone hmid he hI fun p q hip hpm hmq hqe e5 e6 _ => by
      simp only [ltE, BExp.denote, e5, hI.1, ult_ofNat (b64 p (by omega)) (b64 mid (by omega))] at hc
      by_cases h1 : p < mid <;> simp [h1] at hc <;> omega)
    σ₁ q₁
  obtain ⟨σ₃, x₃, q₃⟩ := BExec.loop_inv (c := ltE (.var 6) (.var 11)) (b := tailR src dst)
    (MI dst S H Done i w mid e (fun p q => p = mid))
    (fun τ => ∃ rest', τ.heap = H.set dst (Done ++ ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB ++ rest') ∧
      (Done ++ ((S.drop i).take w).merge ((S.drop (i + w)).take w) leB ++ rest').length = S.length)
    (fun τ => e - (τ.env 4).toNat)
    (stepR hsd hs hd hS hn hw' hDone hmid he)
    (fun τ ⟨e10, e11, p, q, W, rs, hip, hpm, hmq, hqe, e5, e6, e4, eh, hW, hlen, hmerge, hX⟩ hc => by
      have hq : ¬ q < e := by
        simp only [ltE, BExp.denote, e6, e11, ult_ofNat (b64 q hqe) (b64 e (Nat.le_refl _))] at hc
        intro h; simp [h] at hc
      have hp : p - i = ((S.drop i).take w).length := by omega
      have hq' : q - mid = ((S.drop (i + w)).take w).length := by omega
      rw [hp, hq', List.drop_length, List.drop_length, List.nil_merge, List.append_nil] at hmerge
      exact ⟨rs, by rw [eh, hmerge], by rw [← hmerge]; exact hlen⟩)
    σ₂ q₂
  exact ⟨σ₃, .seq x₁ (.seq x₂ x₃), q₃⟩

end

theorem mergeB_assigns (src dst : Nat) : (mergeB src dst).assigns = [8, 9, 6, 5, 8, 4, 8, 5, 4, 9, 6, 4] := rfl
theorem passB_assigns (src dst : Nat) :
    (passB src dst).assigns = [12, 10, 11, 5, 6, 4, 8, 9, 6, 5, 8, 4, 8, 5, 4, 9, 6, 4, 12] := rfl

section
variable (src dst : Nat) (S : List (BitVec 8)) (H : Heap) (Done : List (BitVec 8)) (i w : Nat)

/-- one pair of runs: `runB` appends `merge L R` to the done prefix of `dst` -/
theorem runB_exec (hsd : src ≠ dst) (hs : src < H.length) (hd : dst < H.length) (hS : H[src] = S)
    (hn : S.length < 2 ^ 32) (hi : i < S.length) (hw : 0 < w) (hw' : w < 2 ^ 33) (hDone : Done.length = i)
    (σ : BState) (rest : List (BitVec 8)) (hrest : (Done ++ rest).length = S.length)
    (hh : σ.heap = H.set dst (Done ++ rest)) (h1 : σ.env 1 = BitVec.ofNat 64 S.length)
    (h12 : σ.env 12 = BitVec.ofNat 64 i) (h13 : σ.env 13 = BitVec.ofNat 64 w) :
    ∃ σ', BExec (runB src dst) σ σ' ∧ σ'.env 1 = σ.env 1 ∧ σ'.env 13 = σ.env 13 ∧
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
  obtain ⟨σ6, hex6, rest', hh6, hl6⟩ := mergeB_exec hsd hs hd hS hn hw' hDone rfl rfl hi hw σ5
    rest hrest (by simpa [σ5] using hh)
    (by simp only [σ5, BState.asg_env, Nat.reduceEqDiff, if_false, if_true]; exact v10)
    (by simp only [σ5, BState.asg_env, Nat.reduceEqDiff, if_false, if_true]; exact v11)
    (by simp only [σ5, BState.asg_env, Nat.reduceEqDiff, if_false, if_true, BExp.denote]; exact h12)
    (by simp only [σ5, BState.asg_env, Nat.reduceEqDiff, if_false, if_true, BExp.denote]; exact v10)
    (by simp only [σ5, BState.asg_env, Nat.reduceEqDiff, if_false, if_true, BExp.denote]; exact h12)
  have k : ∀ j, j ∉ [8, 9, 6, 5, 4] → σ6.env j = σ5.env j := fun j hj => hex6.env_keep (by
    simp only [mergeB_assigns, List.mem_cons, List.not_mem_nil, or_false] at hj ⊢; omega)
  refine ⟨σ6.asg 12 (.var 11), .seq BExec.asg (.seq BExec.asg (.seq BExec.asg (.seq BExec.asg
    (.seq BExec.asg (.seq hex6 BExec.asg))))), ?_, ?_, ?_, rest', hh6, hl6⟩
  · simp only [BState.asg_env, Nat.reduceEqDiff, if_false]
    rw [k 1 (by decide), g 1 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · simp only [BState.asg_env, Nat.reduceEqDiff, if_false]
    rw [k 13 (by decide), g 13 (by decide) (by decide) (by decide) (by decide) (by decide)]
  · simp only [BState.asg_env, if_true, BExp.denote]
    rw [k 11 (by decide)]; simp only [σ5, BState.asg_env, Nat.reduceEqDiff, if_false, if_true]; exact v11

/-- one pass: `dst := runs leB w S 0` -/
theorem passB_exec (hsd : src ≠ dst) (hs : src < H.length) (hd : dst < H.length) (hS : H[src] = S)
    (hD : H[dst].length = S.length) (hn : S.length < 2 ^ 32) (hw : 0 < w) (hw' : w < 2 ^ 33)
    (σ : BState) (hh : σ.heap = H) (h1 : σ.env 1 = BitVec.ofNat 64 S.length) (h13 : σ.env 13 = BitVec.ofNat 64 w) :
    ∃ σ', BExec (passB src dst) σ σ' ∧ σ'.heap = H.set dst (runs leB w S 0) := by
  obtain ⟨σ', hl, hq⟩ := BExec.loop_inv (c := ltE (.var 12) (.var 1)) (b := runB src dst)
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
        runB_exec src dst S H Done i w hsd hs hd hS hn hi hw hw' hDone τ rest hl eh e1 e12 e13
      refine ⟨σ₁, hex, ⟨k1.trans e1, k13.trans e13, _, _, rest', k12, by omega, hh', by simp; omega, hl', ?_⟩, ?_⟩
      · rw [runs_min hw, List.append_assoc, ← runs_step leB hi hw, hr]
      · (try dsimp only); rw [k12, e12, toNat_ofNat' (by omega), toNat_ofNat' (by omega)]; omega)
    (fun τ ⟨e1, e13, i, Done, rest, e12, hin, eh, hDone, hl, hr⟩ hc => by
      have hi : ¬ i < S.length := by
        simp only [ltE, BExp.denote, e12, e1, ult_ofNat (show i < 2 ^ 64 by omega) (show S.length < 2 ^ 64 by omega)] at hc
        intro h; simp [h] at hc
      have hr0 : rest = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
      rw [runs_end leB (by omega), List.append_nil] at hr
      (try dsimp only); rw [eh, hr0, List.append_nil, hr])
    ⟨σ.env.set 12 0, σ.heap⟩ ⟨by simp [BEnv.set, h1], by simp [BEnv.set, h13], 0, [], H[dst], by simp [BEnv.set],
      by omega, by rw [hh, List.nil_append, List.set_getElem_self], rfl, by simpa using hD, by simp⟩
  exact ⟨σ', .seq (BExec.assign' rfl) hl, hq⟩

end

theorem passB_keep {src dst : Nat} {σ σ' : BState} (h : BExec (passB src dst) σ σ') {v : Nat}
    (hv : v ∉ [12, 10, 11, 5, 6, 4, 8, 9]) : σ'.env v = σ.env v :=
  h.env_keep fun hm => hv (by
    rw [passB_assigns] at hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; omega)

/-- **The branchy merge sort program computes `List.mergeSort`** (as `msortProg_mergeSort`): blocks `[xs, scr, out]` with `|scr| = |out| = |xs|`,
`v1 = |xs|`; at the end the output block is `xs.mergeSort leB` (the scratch block holds some list). -/
theorem msortProgB_mergeSort (xs scr out : List (BitVec 8)) (σ : BState) (hh : σ.heap = [xs, scr, out])
    (h1 : σ.env 1 = BitVec.ofNat 64 xs.length) (hn : xs.length < 2 ^ 32) (hscr : scr.length = xs.length)
    (hout : out.length = xs.length) :
    ∃ σ', BExec msortProgB σ σ' ∧ ∃ scr', σ'.heap = [xs, scr', xs.mergeSort leB] := by
  have hn64 : xs.length < 2 ^ 64 := by omega
  -- first pass: input → output, width 1
  obtain ⟨σ₂, hex₂, hh₂⟩ := passB_exec 0 2 xs [xs, scr, out] 1 (by decide) (by simp) (by simp) rfl (by simpa using hout)
    hn (by decide) (by decide) (σ.asg 13 (.const 1)) hh (by simp [h1]) (by simp [BExp.denote])
  have k1 : σ₂.env 1 = σ.env 1 := by rw [passB_keep hex₂ (by decide)]; simp
  simp only [List.set_cons_succ, List.set_cons_zero] at hh₂
  -- main loop
  obtain ⟨σ', hl, hq⟩ := BExec.loop_inv (c := ltE (.var 14) (.var 1)) (b := mainBodyB)
    (fun τ => τ.env 1 = BitVec.ofNat 64 xs.length ∧ ∃ ww s o, τ.env 14 = BitVec.ofNat 64 ww ∧ 2 ≤ ww ∧
      ww < 2 ^ 34 ∧ τ.heap = [xs, s, o] ∧ s.length = xs.length ∧ o.length = xs.length ∧ o.Perm xs ∧ CS leB ww o)
    (fun τ => ∃ scr', τ.heap = [xs, scr', xs.mergeSort leB])
    (fun τ => xs.length - (τ.env 14).toNat)
    (fun τ ⟨e1, ww, s, o, e14, hww, hww', eh, hs, ho, hp, hcs⟩ hc => by
      have hlt : ww < xs.length := by
        simp only [ltE, BExp.denote, e14, e1, ult_ofNat (show ww < 2 ^ 64 by omega) hn64] at hc
        exact Classical.byContradiction fun h => by simp [h] at hc
      obtain ⟨τ₂, hex₂, hh₂⟩ := passB_exec 2 1 o [xs, s, o] ww (by decide) (by simp) (by simp) rfl (by simp [hs, ho])
        (by omega) (by omega) (by omega) (τ.asg 13 (.var 14)) eh (by simp [e1, ho]) (by simp [BExp.denote, e14])
      simp only [List.set_cons_succ, List.set_cons_zero] at hh₂
      have k2 : ∀ v ∈ [1, 13, 14], τ₂.env v = (τ.asg 13 (.var 14)).env v := fun v hv => passB_keep hex₂ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; omega)
      have g14 : τ₂.env 14 = BitVec.ofNat 64 ww := by rw [k2 14 (by simp)]; simp [e14]
      have g1 : τ₂.env 1 = BitVec.ofNat 64 xs.length := by rw [k2 1 (by simp)]; simp [e1]
      have hl1 : (runs leB ww o 0).length = xs.length := by rw [runs_length leB (by omega), ho]; rfl
      obtain ⟨τ₄, hex₄, hh₄⟩ := passB_exec 1 2 (runs leB ww o 0) [xs, runs leB ww o 0, o] (ww + ww) (by decide)
        (by simp) (by simp) rfl (by simp [hl1, ho]) (by rw [hl1]; omega) (by omega) (by omega)
        (τ₂.asg 13 (addE (.var 14) (.var 14))) hh₂ (by simp [g1, hl1])
        (by simp only [BState.asg_env, if_true, addE, BExp.denote, g14, add_ofNat])
      simp only [List.set_cons_succ, List.set_cons_zero] at hh₄
      have k4 : ∀ v ∈ [1, 14], τ₄.env v = (τ₂.asg 13 (addE (.var 14) (.var 14))).env v := fun v hv =>
        passB_keep hex₄ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; omega)
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
