/- Nano/V2Self/Proof/Own/OwnP28: the def table across defs: `t[c]` = offset `a ≥ 4096` of `[npw, nres, U, P, R]`. -/
import Nano.V2Self.Proof.Own.OwnP27
namespace OwnP
open C OwnSpec ParSpec

/-- the entries of the defs before (RT's last field, offsets past the 4096-word index) -/
def EntA (ps rs : List (List Nat)) (t : Buf) : Prop :=
  ∀ c < ps.length, ∃ a, 4096 ≤ a ∧ t.getD c 0 = u a ∧ a + 2 + 2 * (ps.getD c []).length + (rs.getD c []).length ≤ t.length ∧
    (ps.getD c []).length < 2 ^ 20 ∧ (rs.getD c []).length < 2 ^ 20 ∧
    t.getD a 0 = u (ps.getD c []).length ∧ t.getD (a + 1) 0 = u (rs.getD c []).length ∧
    (∀ j < (ps.getD c []).length, t.getD (a + 2 + (ps.getD c []).length + j) 0 = u ((ps.getD c []).getD j 0)) ∧
    (∀ j < (rs.getD c []).length, t.getD (a + 2 + 2 * (ps.getD c []).length + j) 0 = u ((rs.getD c []).getD j 0)) ∧
    (∀ k ∈ ps.getD c [], k ≤ 2) ∧ (∀ k ∈ rs.getD c [], k ≤ 1)

def TInv (ps rs : List (List Nat)) (t : Buf) : Prop :=
  ps.length = rs.length ∧ 4096 ≤ t.length ∧ t.length ≤ 4096 + ps.length * 2 ^ 23 ∧ EntA ps rs t

/-- a buffer that keeps `t[0, n)` except index `d` -/
def Keeps (t t' : Buf) (d : Nat) : Prop := t.length ≤ t'.length ∧ ∀ k < t.length, k ≠ d → t'.getD k 0 = t.getD k 0

theorem entA_keep {ps rs : List (List Nat)} {t t' : Buf} (h : EntA ps rs t) (hk : Keeps t t' ps.length)
    (hd : ps.length < 4096) : EntA ps rs t' := by
  intro c hc
  obtain ⟨a, ha, h0, hl, hp, hr, h1, h2, h3, h4, h5, h6⟩ := h c hc
  obtain ⟨hk1, hk2⟩ := hk
  refine ⟨a, ha, by rw [hk2 c (by omega) (by omega)]; exact h0, by omega, hp, hr, by rw [hk2 a (by omega) (by omega)]; exact h1,
    by rw [hk2 (a + 1) (by omega) (by omega)]; exact h2, fun j hj => ?_, fun j hj => ?_, h5, h6⟩
  · rw [hk2 _ (by omega) (by omega)]; exact h3 j hj
  · rw [hk2 _ (by omega) (by omega)]; exact h4 j hj

theorem getD_app_left {l m : Buf} {k : Nat} (h : k < l.length) : (l ++ m).getD k 0 = l.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_right {l m : Buf} {k : Nat} : (l ++ m).getD (l.length + k) 0 = m.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem keeps_app (t m : Buf) (d : Nat) : Keeps t (t ++ m) d := ⟨by simp, fun k hk _ => getD_app_left hk⟩

theorem keeps_set (t : Buf) (d : Nat) (w : UInt64) : Keeps t (t.set d w) d :=
  ⟨by simp, fun k _ hkd => by rw [getD_set, if_neg (by omega)]⟩

theorem keeps_trans {t t1 t2 : Buf} {d : Nat} (h1 : Keeps t t1 d) (h2 : Keeps t1 t2 d) : Keeps t t2 d :=
  ⟨by have := h1.1; have := h2.1; omega, fun k hk hkd => by rw [h2.2 k (by have := h1.1; omega) hkd, h1.2 k hk hkd]⟩

theorem g37_0 (e : UInt64) : g37 (u 0) e = e := rfl

theorem getD_map_range' (y : Buf) {p j : Nat} (hj : j < p) :
    ((List.range' 0 p).map fun q => y.getD q 0).getD j 0 = y.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range', hj]

/-- the table during the verify walk of def `d = |ps|`: its offset and header set, its unused flags appended -/
theorem tab1 {ps rs : List (List Nat)} {t : Buf} (h : TInv ps rs t) (hd : ps.length < 4096) {p r : Nat}
    (hp : p < 2 ^ 20) (hr : r < 2 ^ 20) (f2 : Buf) :
    let t1 := o37 16777216 (bpush (bpush (bset t (u ps.length) (u t.length)) (u p)) (u r)) f2 (u 0) (u p) (u 1)
    t1 = t.set ps.length (u t.length) ++ [u p, u r] ++ ((List.range' 0 p).map fun q => g37 (u 1) (f2.getD q 0)) ∧
    EntA ps rs t1 ∧ t1.length = t.length + 2 + p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e : o37 16777216 (bpush (bpush (bset t (u ps.length) (u t.length)) (u p)) (u r)) f2 (u 0) (u p) (u 1) =
      t.set ps.length (u t.length) ++ [u p, u r] ++ ((List.range' 0 p).map fun q => g37 (u 1) (f2.getD q 0)) := by
    rw [o37_eq _ _ _ 0 p _ (by omega) (by omega) (by omega), bset_u t (by omega)]; simp [bpush]
  refine ⟨e, ?_, by rw [e]; simp; omega⟩
  rw [e]
  have hk : Keeps t (t.set ps.length (u t.length) ++ [u p, u r] ++ ((List.range' 0 p).map fun q => g37 (u 1) (f2.getD q 0)))
      ps.length := by
    rw [List.append_assoc]; exact keeps_trans (keeps_set t _ _) (keeps_app _ _ _)
  exact entA_keep h4 hk hd

/-- after the verify walk: the entry `[p, r, U, P, R]` of def `|ps|` -/
theorem tab2 {ps rs : List (List Nat)} {t : Buf} (h : TInv ps rs t) (hd : ps.length < 4096) {P R : List Nat}
    (hp : P.length < 2 ^ 20) (hr : R.length < 2 ^ 20) (hP2 : ∀ k ∈ P, k ≤ 2) (hR1 : ∀ k ∈ R, k ≤ 1) (f2 f3 v3 : Buf)
    (hf3 : ∀ q < P.length, f3.getD q 0 = u (P.getD q 0)) (hv3 : ∀ j < R.length, v3.getD j 0 = u (R.getD j 0)) :
    TInv (ps ++ [P]) (rs ++ [R]) (o37 16777216 (o37 16777216
      (o37 16777216 (bpush (bpush (bset t (u ps.length) (u t.length)) (u P.length)) (u R.length)) f2 (u 0) (u P.length) (u 1))
      f3 (u 0) (u P.length) (u 0)) v3 (u 0) (u R.length) (u 0)) := by
  obtain ⟨e1, h4, hl1⟩ := tab1 h hd hp hr f2
  have h1 := h.1
  generalize o37 16777216 (bpush (bpush (bset t (u ps.length) (u t.length)) (u P.length)) (u R.length)) f2 (u 0)
    (u P.length) (u 1) = t1 at e1 hl1 h4
  rw [o37_eq _ _ _ 0 _ _ (by omega) (by omega) (by omega), o37_eq _ _ _ 0 _ _ (by omega) (by omega) (by omega)]
  simp only [Nat.sub_zero, g37_0]
  generalize hP' : ((List.range' 0 P.length).map fun q => f3.getD q 0) = P' 
  generalize hR' : ((List.range' 0 R.length).map fun q => v3.getD q 0) = R'
  have lP : P'.length = P.length := by rw [← hP']; simp
  have lR : R'.length = R.length := by rw [← hR']; simp
  have hT := h.2.1
  have hk : Keeps t1 (t1 ++ P' ++ R') ps.length := by rw [List.append_assoc]; exact keeps_app _ _ _
  refine ⟨by simp [h1], by simp; omega, by simp; rw [hl1]; have := h.2.2.1; rw [Nat.add_mul]; omega, fun c hc => ?_⟩
  simp only [List.length_append, List.length_singleton] at hc
  by_cases hcd : c < ps.length
  · obtain ⟨a, ha, rest⟩ := entA_keep h4 hk hd c hcd
    have ep : (ps ++ [P]).getD c [] = ps.getD c [] := by simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hcd]
    have er : (rs ++ [R]).getD c [] = rs.getD c [] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show c < rs.length by omega)]
    rw [ep, er]; exact ⟨a, ha, rest⟩
  · have hc' : c = ps.length := by omega
    subst hc'
    have ep : (ps ++ [P]).getD ps.length [] = P := by simp
    have er : (rs ++ [R]).getD ps.length [] = R := by rw [h1]; simp
    rw [ep, er]
    have g0 : t1.getD ps.length 0 = u t.length := by
      rw [e1, List.append_assoc, getD_app_left (by simp; omega), getD_set, if_pos ⟨rfl, by omega⟩]
    have gL : t1.getD t.length 0 = u P.length := by
      rw [e1, List.append_assoc]
      have := getD_app_right (l := t.set ps.length (u t.length))
        (m := [u P.length, u R.length] ++ ((List.range' 0 P.length).map fun q => g37 (u 1) (f2.getD q 0))) (k := 0)
      simpa using this
    have gL1 : t1.getD (t.length + 1) 0 = u R.length := by
      rw [e1, List.append_assoc]
      have := getD_app_right (l := t.set ps.length (u t.length))
        (m := [u P.length, u R.length] ++ ((List.range' 0 P.length).map fun q => g37 (u 1) (f2.getD q 0))) (k := 1)
      simpa using this
    refine ⟨t.length, h.2.1, ?_, by simp; omega, hp, hr, ?_, ?_, fun j hj => ?_, fun j hj => ?_, hP2, hR1⟩
    · rw [List.append_assoc, getD_app_left (by omega)]; exact g0
    · rw [List.append_assoc, getD_app_left (by omega)]; exact gL
    · rw [List.append_assoc, getD_app_left (by omega)]; exact gL1
    · rw [show t.length + 2 + P.length + j = t1.length + j by omega, List.append_assoc, getD_app_right,
        getD_app_left (by omega), ← hP', getD_map_range' f3 hj]; exact hf3 j hj
    · rw [show t.length + 2 + 2 * P.length + j = (t1 ++ P').length + j by simp; omega, getD_app_right, ← hR',
        getD_map_range' v3 hj]; exact hv3 j hj

end OwnP
