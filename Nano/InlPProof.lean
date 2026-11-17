/- `inlP = inlB` (branch `nano-closeB`): the paged inliner machine (`Nano/InlP.lean`) computes `Nano.U.inlB` whenever
the inliner's table fits its buffer (`inlFits`). -/
import Nano.InlP

set_option linter.unusedSimpArgs false

namespace Nano.IP
open Nano Nano.U

/-! ## bytes -/

theorem ba_get (a : ByteArray) (i : Nat) : a.get! i = (a.data.toList[i]?).getD 0 := by
  cases a with
  | mk d => cases d with
    | mk l => simp [ByteArray.get!]; rfl

theorem arr_get (a : Array Nat) (j : Nat) : a[j]! = (a.toList[j]?).getD 0 := by
  rw [getElem!_def]; simp; rfl

theorem arr_set (a : Array Nat) (i v : Nat) : (a.set! i v).toList = a.toList.set i v := by
  simp [Array.set!]

theorem ba_set (a : ByteArray) (i : Nat) (v : UInt8) : (a.set! i v).data.toList = a.data.toList.set i v := by
  cases a; simp [ByteArray.set!]

theorem size_set (a : ByteArray) (i : Nat) (v : UInt8) : (a.set! i v).size = a.size := by
  cases a; simp [ByteArray.set!, ByteArray.size]

theorem get_set_ne (a : ByteArray) (i j : Nat) (v : UInt8) (h : j ≠ i) : (a.set! i v).get! j = a.get! j := by
  simp [ba_get, ba_set, List.getElem?_set, Ne.symm h]

theorem get_set_eq (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) : (a.set! i v).get! i = v := by
  simp [ba_get, ba_set, List.getElem?_set, h]

theorem set_self (a : ByteArray) (i : Nat) : a.set! i (a.get! i) = a := by
  apply ByteArray.ext; apply Array.ext'; rw [ba_set, ba_get]
  by_cases h : i < a.data.toList.length
  · rw [List.getElem?_eq_getElem h]; simp only [Option.getD_some]; exact List.set_getElem_self _
  · simp [List.set_eq_of_length_le (Nat.le_of_not_lt h)]

theorem aget_set (a : Array Nat) (i j v : Nat) : (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  rw [arr_get, arr_get, arr_set, List.getElem?_set]
  by_cases h : i = j <;> simp [h]
  split <;> simp_all

theorem aset_size (a : Array Nat) (i v : Nat) : (a.set! i v).size = a.size := by simp [Array.set!]

theorem aset_self (a : Array Nat) (i : Nat) : a.set! i a[i]! = a := by
  apply Array.ext'; rw [arr_set, arr_get]
  by_cases h : i < a.toList.length
  · rw [List.getElem?_eq_getElem h]; simp only [Option.getD_some]; exact List.set_getElem_self _
  · simp [List.set_eq_of_length_le (Nat.le_of_not_lt h)]

theorem ba_push (a : ByteArray) (x : UInt8) : (a.push x).data.toList = a.data.toList ++ [x] := by
  cases a with
  | mk d => simp [ByteArray.push]

/-! ## the emit loop -/

/-- the byte the emit loop pushes at `t` -/
def eB (ob : Array Nat) (ls len k t : Nat) : UInt8 :=
  if t < 2 then 0
  else if t < 2 + 20 * k then argB ((t - 2) % 20)
  else if t < 2 + 20 * k + len then UInt8.ofNat ob[BASE + ls + (t - 2 - 20 * k)]!
  else if t == 2 + 20 * k + len then 7
  else if t == 3 + 20 * k + len then 0
  else if t < 36 + 20 * k + len then wrB (t - 4 - 20 * k - len)
  else if t == 36 + 20 * k + len then 12 else 0

theorem em_eq (ob : Array Nat) (ls len k : Nat) : ∀ (n t : Nat) (out : ByteArray), 20 * k + len + 38 - t = n →
    (em out ob t ls len k).data.toList = out.data.toList ++ (List.range' t n).map (eB ob ls len k)
  | 0, t, out, h => by
    rw [em, if_neg (by omega)]; simp
  | n + 1, t, out, h => by
    rw [em, if_pos (by omega), em_eq ob ls len k n (t + 1) _ (by omega), ba_push, List.range'_succ]
    simp [eB]

theorem sArg_get : ∀ s (h : s < sArg.length), sArg[s] = argB s := by decide

theorem serPro_get (k s : Nat) (h : s < (serPro k).length) : (serPro k)[s] = argB (s % 20) := by
  induction k generalizing s with
  | zero => simp [serPro] at h
  | succ k ih =>
    have hl : sArg.length = 20 := rfl
    simp only [serPro] at h ⊢
    by_cases hs : s < 20
    · rw [List.getElem_append_left (by omega)]
      have : s % 20 = s := Nat.mod_eq_of_lt hs
      rw [this]; exact sArg_get s (by rw [hl]; exact hs)
    · rw [List.getElem_append_right (by omega), ih _ (by simp [List.length_append] at h; omega)]
      congr 1; simp [hl]; omega

theorem serPro_length (k : Nat) : (serPro k).length = 20 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [serPro, ih, sArg, mo]; omega

theorem sWr_get (v : Nat) (h : v < sWr.length) : sWr[v] = wrB v := by
  revert v; decide

/-- **the emit loop writes `wrap k last`** when the buffer holds `last` at `ls` -/
theorem em_wrap (out : ByteArray) (ho : out.data.toList = []) (ob : Array Nat) (ls k : Nat) (last : List UInt8)
    (hb : ∀ q (h : q < last.length), ob[BASE + ls + q]! = last[q].toNat) :
    (em out ob 0 ls last.length k).data.toList = wrap k last := by
  rw [em_eq ob ls last.length k _ 0 _ rfl, ho]
  simp only [Nat.sub_zero, List.nil_append]
  show (List.range' 0 (20 * k + last.length + 38)).map (eB ob ls last.length k) = wrap k last
  apply List.ext_getElem
  · simp [wrap, mo, serPro_length, sWr]; omega
  · intro t h1 h2
    simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
    simp only [wrap, mo, List.append_assoc]
    have hP := serPro_length k
    have hW : sWr.length = 32 := rfl
    simp only [List.length_map, List.length_range'] at h1
    unfold eB
    by_cases t0 : t < 2
    · rw [if_pos t0, List.getElem_append_left (by simp; omega)]
      match t, t0 with | 0, _ => rfl | 1, _ => rfl
    rw [if_neg t0, List.getElem_append_right (by simp; omega)]
    simp only [List.length_cons, List.length_nil]
    by_cases t1 : t < 2 + 20 * k
    · rw [if_pos t1, List.getElem_append_left (by omega), serPro_get]
    rw [if_neg t1, List.getElem_append_right (by omega)]
    by_cases t2 : t < 2 + 20 * k + last.length
    · rw [if_pos t2, List.getElem_append_left (by omega), hb (t - 2 - 20 * k) (by omega), UInt8.ofNat_toNat]
      congr 1; omega
    rw [if_neg t2, List.getElem_append_right (by omega)]
    obtain ⟨u, rfl⟩ : ∃ u, t = 2 + 20 * k + last.length + u := ⟨t - (2 + 20 * k + last.length), by omega⟩
    have hu : u < 36 := by omega
    have e : 2 + 20 * k + last.length + u - (0 + 1 + 1) - (serPro k).length - last.length = u := by omega
    simp only [e]
    match u, hu with
    | 0, _ => simp only [beq_iff_eq]; rw [if_pos (by omega)]; rfl
    | 1, _ => simp only [beq_iff_eq]; rw [if_neg (by omega), if_pos (by omega)]; rfl
    | v + 2, hv =>
      simp only [beq_iff_eq]
      rw [if_neg (by omega), if_neg (by omega)]
      show _ = (sWr ++ [12, 0])[v]'(by simp [hW]; omega)
      by_cases t5 : v < 32
      · rw [if_pos (by omega), List.getElem_append_left (by rw [hW]; exact t5), sWr_get]
        congr 1; omega
      · rw [if_neg (by omega), List.getElem_append_right (by rw [hW]; omega)]
        match v, t5, hv with
        | 32, _, _ => rw [if_pos (by omega)]; rfl
        | 33, _, _ => rw [if_neg (by omega)]; rfl
        | w + 34, _, hv => omega

/-! ## steps of the main loop -/

theorem arr_ext (a b : Array Nat) (hs : a.size = b.size) (h : ∀ j, j < a.size → a[j]! = b[j]!) : a = b := by
  apply Array.ext hs
  intro j h1 h2
  have := h j h1
  rw [getElem!_pos a j h1, getElem!_pos b j h2] at this
  exact this

/-- the table and header cells kept -/
theorem keep2 (ob : Array Nat) (A : Nat) (v : Nat) (n : Nat) (hA : 65538 < A) :
    ((ob.set! A v).set! (if n < 65536 then n + 1 else 65537) ob[if n < 65536 then n + 1 else 65537]!).set! HD
      ob[HD]! = ob.set! A v := by
  apply arr_ext
  · simp [aset_size]
  · intro j _
    simp only [aget_set, aset_size, HD]
    repeat' split
    all_goals (first | rfl | omega | (subst_vars; rfl) | simp_all | skip)

theorem mn_end (ob : Array Nat) (src : ByteArray) (i ph m w n hi cp rem cs : Nat)
    (h : ¬ i < src.size) : mn ob src i ph m w n hi cp rem cs = ob := by
  rw [mn, if_neg h]

/-- a copy step -/
theorem mn_copy (ob : Array Nat) (src : ByteArray) (i m w n hi cp rem cs : Nat)
    (h : i < src.size) (hr : 0 < rem) (hw : w < WCAP) : mn ob src i 0 m w n hi cp rem cs =
    mn (ob.set! (BASE + w) ob[BASE + cp]!) src i 0 m (w + 1) n hi (cp + 1) (rem - 1) cs := by
  rw [mn, if_pos h]
  simp only [hr, if_true, hw]
  rw [keep2 _ _ _ _ (by unfold BASE; omega)]

/-- the first byte of a pair, a plain micro-op -/
theorem mn_a (ob : Array Nat) (src : ByteArray) (i m0 w n hi cp cs : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (h13 : b ≠ 13) (h14 : b ≠ 14) (h15 : b ≠ 15) (hw : w < WCAP) :
    mn ob src i 0 m0 w n hi cp 0 cs = mn (ob.set! (BASE + w) b.toNat) src (i + 1) 1 b.toNat (w + 1) n hi cp 0 cs := by
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or, h13, h14, h15]
  rw [keep2 _ _ _ _ (by unfold BASE; omega)]

/-- the first byte of a pair, `13`/`14`/`15` -/
theorem mn_a' (ob : Array Nat) (src : ByteArray) (i m0 w n hi cp cs : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (hm : b = 13 ∨ b = 14 ∨ b = 15) :
    mn ob src i 0 m0 w n hi cp 0 cs = mn ob src (i + 1) 1 b.toNat w n hi cp 0 cs := by
  have hw : (b = 13 ∨ b = 14) ∨ b = 15 := or_assoc.mpr hm
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or]

/-- the second byte, after `13`: close the def -/
theorem mn_b13 (ob : Array Nat) (src : ByteArray) (i w n hi cp cs : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (hw : w < WCAP) :
    mn ob src i 1 13 w n hi cp 0 cs =
    mn (((ob.set! (BASE + w) b.toNat).set! (if n < 65536 then n + 1 else 65537) (w + 1)).set! HD
      (cs * 16777216 + w + 1)) src (i + 1) 0 13 (w + 1) (n + 1) hi cp 0 (w + 1) := by
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or]

/-- the second byte, after `14` -/
theorem mn_b14 (ob : Array Nat) (src : ByteArray) (i w n hi cp cs : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) :
    mn ob src i 1 14 w n hi cp 0 cs = mn ob src (i + 1) 0 14 w n b.toNat cp 0 cs := by
  have hw : True := trivial
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or]

/-- the second byte, after `15`, a def in the table -/
theorem mn_b15 (ob : Array Nat) (src : ByteArray) (i w n hi cp cs a len : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (hj : hi * 256 + b.toNat < n) (ha : ob[hi * 256 + b.toNat]! = a)
    (ha1 : ob[hi * 256 + b.toNat + 1]! = a + len + 1) (haW : a < WCAP) (hlW : len < WCAP) :
    mn ob src i 1 15 w n hi cp 0 cs = mn ob src (i + 1) 0 15 w n hi a len cs := by
  have hw : True := trivial
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or, hj, ha, ha1, haW, show a + len + 1 - 1 - a = len by omega, hlW]

/-- the second byte, after `15`, no such def -/
theorem mn_b15' (ob : Array Nat) (src : ByteArray) (i w n hi cp cs : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (hj : ¬ hi * 256 + b.toNat < n) :
    mn ob src i 1 15 w n hi cp 0 cs = mn ob src (i + 1) 0 15 w n hi cp 0 cs := by
  have hw : True := trivial
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or, hj]

/-- the second byte, after a plain micro-op -/
theorem mn_bx (ob : Array Nat) (src : ByteArray) (i m w n hi cp cs : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (h13 : m ≠ 13) (h14 : m ≠ 14) (h15 : m ≠ 15) (hw : w < WCAP) :
    mn ob src i 1 m w n hi cp 0 cs = mn (ob.set! (BASE + w) b.toNat) src (i + 1) 0 m (w + 1) n hi cp 0 cs := by
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, if_true, aset_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or, h13, h14, h15]
  rw [keep2 _ _ _ _ (by unfold BASE; omega)]

/-! ## the inliner with its final state -/

/-- `inlGo` returning the final table, current code, arity and last body -/
def inlS : List UInt8 → List (List UInt8) → List UInt8 → Nat → Nat → List UInt8 →
    List (List UInt8) × List UInt8 × Nat × List UInt8
  | m :: x :: rest, tab, cur, hi, k, last =>
    if m = 13 then inlS rest (tab ++ [cur]) [] hi x.toNat cur
    else if m = 14 then inlS rest tab cur x.toNat k last
    else if m = 15 then inlS rest tab (cur ++ tab.getD (hi * 256 + x.toNat) []) hi k last
    else inlS rest tab (cur ++ [m, x]) hi k last
  | _, tab, cur, _, k, last => (tab, cur, k, last)

theorem inlGo_inlS : ∀ (xs : List UInt8) (tab : List (List UInt8)) (cur : List UInt8) (hi k : Nat)
    (last : List UInt8), inlGo xs tab cur hi k last =
      wrap (inlS xs tab cur hi k last).2.2.1 (inlS xs tab cur hi k last).2.2.2
  | m :: x :: rest, tab, cur, hi, k, last => by
    rw [inlGo, inlS]
    split
    · exact inlGo_inlS _ _ _ _ _ _
    · split
      · exact inlGo_inlS _ _ _ _ _ _
      · split
        · exact inlGo_inlS _ _ _ _ _ _
        · exact inlGo_inlS _ _ _ _ _ _
  | [], _, _, _, _, _ => rfl
  | [_], _, _, _, _, _ => rfl

/-- the buffer cells the table and the current code use -/
def S (tab : List (List UInt8)) : Nat := (tab.map (·.length + 1)).sum

theorem S_append (tab : List (List UInt8)) (c : List UInt8) : S (tab ++ [c]) = S tab + c.length + 1 := by
  simp [S]; omega

theorem S_take_succ (tab : List (List UInt8)) (j : Nat) (hj : j < tab.length) :
    S (tab.take (j + 1)) = S (tab.take j) + tab[j].length + 1 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, S_append]

theorem S_take_le (tab : List (List UInt8)) (j : Nat) : S (tab.take j) ≤ S tab := by
  unfold S; rw [List.map_take]; generalize List.map _ tab = l
  calc (l.take j).sum ≤ (l.take j).sum + (l.drop j).sum := Nat.le_add_right _ _
    _ = l.sum := by rw [← List.sum_append, List.take_append_drop]

/-- what the inliner has written so far -/
def tot (tab : List (List UInt8)) (cur : List UInt8) : Nat := S tab + cur.length

theorem tot_mono : ∀ (xs : List UInt8) (tab : List (List UInt8)) (cur : List UInt8) (hi k : Nat)
    (last : List UInt8), tot tab cur ≤ tot (inlS xs tab cur hi k last).1 (inlS xs tab cur hi k last).2.1
  | m :: x :: rest, tab, cur, hi, k, last => by
    rw [inlS]
    split
    · have := tot_mono rest (tab ++ [cur]) [] hi x.toNat cur; simp only [tot, S_append] at *; omega
    · split
      · exact tot_mono _ _ _ _ _ _
      · split
        · have := tot_mono rest tab (cur ++ tab.getD (hi * 256 + x.toNat) []) hi k last
          simp only [tot, List.length_append] at *; omega
        · have := tot_mono rest tab (cur ++ [m, x]) hi k last; simp only [tot, List.length_append] at *; omega
  | [], _, _, _, _, _ => Nat.le_refl _
  | [_], _, _, _, _, _ => Nat.le_refl _

/-- **the inliner's table fits the buffer** -/
def inlFits (xs : List UInt8) : Prop :=
  tot (inlS xs [] [] 0 0 []).1 (inlS xs [] [] 0 0 []).2.1 < WCAP

/-! ## the invariant of the main loop -/

/-- the header and the last closed def -/
def Hdr (ob : Array Nat) (cs k : Nat) (last : List UInt8) : Prop :=
  (ob[HD]! = 0 ∧ last = [] ∧ k = 0) ∨
  (∃ ls, ob[HD]! = ls * 16777216 + (ls + last.length) + 1 ∧ ls + last.length < cs ∧ k < 256 ∧
    (∀ q (hq : q < last.length), ob[BASE + ls + q]! = last[q].toNat) ∧ ob[BASE + (ls + last.length)]! = k)

/-- what the emit loop needs -/
def Post (R : Array Nat) (k : Nat) (last : List UInt8) : Prop :=
  R[HD]! % 16777216 - 1 - R[HD]! / 16777216 % 16777216 = last.length ∧
  (if R[HD]! % 16777216 == 0 then 0 else R[BASE + (R[HD]! % 16777216 - 1)]! % 256) = k ∧
  ∀ q (hq : q < last.length), R[BASE + R[HD]! / 16777216 % 16777216 + q]! = last[q].toNat

theorem hdr_post (ob : Array Nat) (cs k : Nat) (last : List UInt8) (h : Hdr ob cs k last) (hcs : cs ≤ WCAP) :
    Post ob k last := by
  rcases h with ⟨h0, rfl, rfl⟩ | ⟨ls, hH, hlt, hk, hb, hkb⟩
  · simp [Post, h0]
  · have e1 : ob[HD]! % 16777216 = ls + last.length + 1 := by rw [hH]; unfold WCAP at hcs; omega
    have e2 : ob[HD]! / 16777216 % 16777216 = ls := by rw [hH]; unfold WCAP at hcs; omega
    refine ⟨by rw [e1, e2]; omega, ?_, by rw [e2]; exact hb⟩
    rw [e1]; simp only [Nat.add_one_sub_one]
    rw [if_neg (by simp), hkb, Nat.mod_eq_of_lt hk]

/-- the main loop's invariant at a pair boundary -/
def Inv (ob : Array Nat) (tab : List (List UInt8)) (cur : List UInt8) (w n cs k : Nat) (last : List UInt8) :
    Prop :=
  ob.size = CAP ∧ n = tab.length ∧ cs = S tab ∧ w = cs + cur.length ∧ w ≤ WCAP ∧
  (∀ j, j ≤ n → j ≤ 65536 → ob[j]! = S (tab.take j)) ∧
  (∀ j (hj : j < tab.length) q (hq : q < tab[j].length), ob[BASE + S (tab.take j) + q]! = tab[j][q].toNat) ∧
  (∀ q (hq : q < cur.length), ob[BASE + cs + q]! = cur[q].toNat) ∧ Hdr ob cs k last

theorem S_take_lt (tab : List (List UInt8)) (j : Nat) (hj : j < tab.length) :
    S (tab.take j) + tab[j].length < S tab := by
  have := S_take_succ tab j hj; have := S_take_le tab (j + 1); omega

/-- cells below `p` are kept by a write at or above `p` -/
theorem get_set_lt (ob : Array Nat) (a p v : Nat) (h : a < p) : (ob.set! p v)[a]! = ob[a]! := by
  rw [aget_set, if_neg (by omega)]

theorem get_set_self (ob : Array Nat) (p v : Nat) (h : p < ob.size) : (ob.set! p v)[p]! = v := by
  rw [aget_set, if_pos ⟨rfl, h⟩]

theorem hdr_mono (ob ob' : Array Nat) (cs cs' k : Nat) (last : List UInt8) (h : Hdr ob cs k last) (hc : cs ≤ cs')
    (hk : ∀ a, a < BASE + cs → ob'[a]! = ob[a]!) : Hdr ob' cs' k last := by
  rcases h with ⟨h0, h1, h2⟩ | ⟨ls, hH, hlt, hk2, hb, hkb⟩
  · left; rw [hk _ (by unfold HD BASE; omega)]; exact ⟨h0, h1, h2⟩
  · right; refine ⟨ls, by rw [hk _ (by unfold HD BASE; omega)]; exact hH, by omega, hk2, fun q hq => ?_, ?_⟩
    · rw [hk _ (by omega)]; exact hb q hq
    · rw [hk _ (by omega)]; exact hkb

/-! ## the source bytes -/

theorem src_cons (src : ByteArray) (i : Nat) (b : UInt8) (r : List UInt8) (h : src.data.toList.drop i = b :: r) :
    i < src.size ∧ src.get! i = b ∧ src.data.toList.drop (i + 1) = r := by
  have h1 : src.data.toList[i]? = some b := by
    have := congrArg (·[0]?) h; simp only [List.getElem?_drop, Nat.add_zero] at this; simpa using this
  have hl : i < src.data.toList.length := by
    rcases Nat.lt_or_ge i src.data.toList.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at h1; cases h1
  refine ⟨by simpa using hl, by rw [ba_get, h1]; rfl, ?_⟩
  rw [← List.tail_drop, h]; rfl

theorem src_nil (src : ByteArray) (i : Nat) (h : src.data.toList.drop i = []) : ¬ i < src.size := by
  rw [List.drop_eq_nil_iff] at h; simpa using h

/-! ## copying a body -/

theorem mn_copyAll : ∀ (c : List UInt8) (ob : Array Nat) (src : ByteArray) (i m w n hi cp cs : Nat),
    i < src.size → w + c.length ≤ WCAP → cp + c.length ≤ w → ob.size = CAP →
    (∀ q (hq : q < c.length), ob[BASE + cp + q]! = c[q].toNat) →
    ∃ ob', ob'.size = CAP ∧ (∀ a, a < BASE + w → ob'[a]! = ob[a]!) ∧
      (∀ q (hq : q < c.length), ob'[BASE + w + q]! = c[q].toNat) ∧
      mn ob src i 0 m w n hi cp c.length cs = mn ob' src i 0 m (w + c.length) n hi (cp + c.length) 0 cs
  | [], ob, src, i, m, w, n, hi, cp, cs, _, _, _, hs, _ =>
    ⟨ob, hs, fun _ _ => rfl, fun q hq => absurd hq (Nat.not_lt_zero _), rfl⟩
  | b :: c, ob, src, i, m, w, n, hi, cp, cs, hi', hw, hcp, hs, hc => by
    simp only [List.length_cons] at hw hcp
    have h0 := hc 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hs1 : (ob.set! (BASE + w) b.toNat).size = CAP := by rw [aset_size, hs]
    obtain ⟨ob', hs', hlo, hc', he⟩ := mn_copyAll c (ob.set! (BASE + w) b.toNat) src i m (w + 1) n hi (cp + 1) cs hi'
      (by omega) (by omega) hs1 (fun q hq => by
        rw [get_set_lt _ _ _ _ (by omega), show BASE + (cp + 1) + q = BASE + cp + (q + 1) by omega,
          hc (q + 1) (by simp; omega)]; simp)
    refine ⟨ob', hs', fun a ha => by rw [hlo a (by omega), get_set_lt _ _ _ _ ha], fun q hq => ?_, ?_⟩
    · cases q with
      | zero =>
        rw [hlo _ (by omega), Nat.add_zero, get_set_self _ _ _ (by rw [hs]; unfold BASE CAP WCAP at *; omega)]; rfl
      | succ q =>
        rw [show BASE + w + (q + 1) = BASE + (w + 1) + q by omega, hc' q (by simp at hq; omega)]; rfl
    · show mn ob src i 0 m w n hi cp (c.length + 1) cs =
        mn ob' src i 0 m (w + (c.length + 1)) n hi (cp + (c.length + 1)) 0 cs
      rw [mn_copy ob src i m w n hi cp (c.length + 1) cs hi' (by omega) (by unfold WCAP at *; omega),
        Nat.add_sub_cancel, h0, he]
      congr 1 <;> omega

/-! ## the main loop simulates `inlS` -/

theorem take_append_le (tab : List (List UInt8)) (c : List UInt8) (j : Nat) (hj : j ≤ tab.length) :
    (tab ++ [c]).take j = tab.take j := by
  rw [List.take_append_of_le_length hj]

/-- writing at or above the current position keeps the invariant's facts below it -/
theorem inv_keep (ob ob' : Array Nat) (tab : List (List UInt8)) (cur : List UInt8) (w n cs k : Nat)
    (last : List UInt8) (h : Inv ob tab cur w n cs k last) (hs : ob'.size = CAP)
    (hk : ∀ a, a < BASE + w → ob'[a]! = ob[a]!) (c : List UInt8)
    (hc : ∀ q (hq : q < c.length), ob'[BASE + w + q]! = c[q].toNat) (hw : w + c.length ≤ WCAP) :
    Inv ob' tab (cur ++ c) (w + c.length) n cs k last := by
  obtain ⟨_, hn, hcs, hw0, _, ht, hb, hcur, hh⟩ := h
  refine ⟨hs, hn, hcs, by simp; omega, hw, fun j h1 h2 => ?_, fun j hj q hq => ?_, fun q hq => ?_,
    hdr_mono ob ob' cs cs k last hh (Nat.le_refl _) fun a ha => hk a (by omega)⟩
  · rw [hk _ (by unfold BASE; omega)]; exact ht j h1 h2
  · have := S_take_lt tab j hj; rw [hk _ (by omega)]; exact hb j hj q hq
  · by_cases hq' : q < cur.length
    · rw [hk _ (by omega), List.getElem_append_left hq']; exact hcur q hq'
    · rw [List.getElem_append_right (by omega), show BASE + cs + q = BASE + w + (q - cur.length) by omega]
      exact hc _ _

theorem tot_lt (rest : List UInt8) (tab : List (List UInt8)) (cur : List UInt8) (hi k : Nat) (last : List UInt8)
    (h : tot (inlS rest tab cur hi k last).1 (inlS rest tab cur hi k last).2.1 < WCAP) : tot tab cur < WCAP :=
  Nat.lt_of_le_of_lt (tot_mono _ _ _ _ _ _) h

theorem inv13 (ob : Array Nat) (tab : List (List UInt8)) (cur : List UInt8) (w n cs k : Nat) (last : List UInt8)
    (b : UInt8) (h : Inv ob tab cur w n cs k last) (hw : w + 1 ≤ WCAP) :
    Inv (((ob.set! (BASE + w) b.toNat).set! (if n < 65536 then n + 1 else 65537) (w + 1)).set! HD
      (cs * 16777216 + w + 1)) (tab ++ [cur]) [] (w + 1) (n + 1) (w + 1) b.toNat cur := by
  obtain ⟨hs, hn, hcs, hw0, _, ht, hbd, hcur, _⟩ := h
  have hsz : ∀ x y z : Nat, (((ob.set! (BASE + w) x).set! (if n < 65536 then n + 1 else 65537) y).set! HD z).size
      = CAP := by intro x y z; simp only [aset_size, hs]
  -- reading the new array
  have rd : ∀ a, a ≠ HD → a ≠ (if n < 65536 then n + 1 else 65537) → a ≠ BASE + w →
      (((ob.set! (BASE + w) b.toNat).set! (if n < 65536 then n + 1 else 65537) (w + 1)).set! HD
        (cs * 16777216 + w + 1))[a]! = ob[a]! := by
    intro a h1 h2 h3; rw [aget_set, if_neg (by omega), aget_set, if_neg (by omega), aget_set, if_neg (by omega)]
  have hS : S (tab ++ [cur]) = w + 1 := by rw [S_append]; omega
  refine ⟨hsz _ _ _, by simp [hn], hS.symm, by simp, hw, fun j h1 h2 => ?_, fun j hj q hq => ?_,
    fun q hq => absurd hq (Nat.not_lt_zero _), Or.inr ⟨cs, ?_, ?_, b.toNat_lt, fun q hq => ?_, ?_⟩⟩
  · by_cases hj : j = n + 1
    · subst hj
      rw [aget_set, if_neg (by unfold HD; omega), aget_set, if_pos ⟨by rw [if_pos (by omega)], by
        rw [aset_size, hs]; split <;> (unfold CAP; omega)⟩, List.take_of_length_le (by simp; omega), hS]
    · rw [rd _ (by unfold HD; omega) (by split <;> omega) (by unfold BASE; omega), take_append_le _ _ _ (by omega)]
      exact ht j (by omega) h2
  · simp only [List.length_append, List.length_cons, List.length_nil] at hj
    by_cases hjn : j < tab.length
    · have := S_take_lt tab j hjn
      have hq2 : q < tab[j].length := by simpa [List.getElem_append_left hjn] using hq
      rw [take_append_le _ _ _ (by omega), rd _ (by unfold HD BASE; omega) (by split <;> (unfold BASE; omega))
        (by omega), hbd j hjn q hq2]
      simp only [List.getElem_append_left hjn]
    · have hj' : j = tab.length := by omega
      subst hj'
      have hq' : q < cur.length := by simpa using hq
      rw [take_append_le _ _ _ (Nat.le_refl _), List.take_of_length_le (Nat.le_refl _), ← hcs,
        rd _ (by unfold HD BASE; omega) (by split <;> (unfold BASE; omega)) (by omega), hcur q hq']
      simp
  · rw [aget_set, if_pos ⟨rfl, by rw [aset_size, aset_size, hs]; unfold HD CAP; omega⟩]; omega
  · omega
  · rw [rd _ (by unfold HD BASE; omega) (by split <;> (unfold BASE; omega)) (by omega)]; exact hcur q hq
  · rw [show cs + cur.length = w by omega, aget_set, if_neg (by unfold HD BASE; omega), aget_set,
      if_neg (by split <;> (unfold BASE; omega)), aget_set, if_pos ⟨rfl, by rw [hs]; unfold CAP BASE WCAP at *; omega⟩]

theorem mn_main : ∀ (rest : List UInt8) (ob : Array Nat) (src : ByteArray) (i m w n hi cp cs : Nat)
    (tab : List (List UInt8)) (cur : List UInt8) (k : Nat) (last : List UInt8),
    src.data.toList.drop i = rest → Inv ob tab cur w n cs k last → hi < 256 →
    tot (inlS rest tab cur hi k last).1 (inlS rest tab cur hi k last).2.1 < WCAP →
    Post (mn ob src i 0 m w n hi cp 0 cs) (inlS rest tab cur hi k last).2.2.1 (inlS rest tab cur hi k last).2.2.2
  | [], ob, src, i, m, w, n, hi, cp, cs, tab, cur, k, last, hr, hI, _, _ => by
    rw [mn_end _ _ _ _ _ _ _ _ _ _ _ (src_nil _ _ hr)]
    exact hdr_post _ _ _ _ hI.2.2.2.2.2.2.2.2 (by obtain ⟨_, _, _, h1, h2, _⟩ := hI; omega)
  | [b], ob, src, i, m, w, n, hi, cp, cs, tab, cur, k, last, hr, hI, _, hf => by
    obtain ⟨hi1, hb, hr'⟩ := src_cons _ _ _ _ hr
    have hn := src_nil _ _ hr'
    have hcs : cs ≤ WCAP := by obtain ⟨_, _, _, h1, h2, _⟩ := hI; omega
    by_cases hm : b = 13 ∨ b = 14 ∨ b = 15
    · rw [mn_a' _ _ _ _ _ _ _ _ _ _ hi1 hb hm, mn_end _ _ _ _ _ _ _ _ _ _ _ hn]
      exact hdr_post _ _ _ _ hI.2.2.2.2.2.2.2.2 hcs
    · have hw : w < WCAP := by
        have := tot_lt _ _ _ _ _ _ hf; obtain ⟨_, _, h1, h2, _⟩ := hI; simp only [tot, inlS] at hf; omega
      rw [mn_a _ _ _ _ _ _ _ _ _ _ hi1 hb (fun e => hm (.inl e)) (fun e => hm (.inr (.inl e)))
        (fun e => hm (.inr (.inr e))) hw, mn_end _ _ _ _ _ _ _ _ _ _ _ hn]
      refine hdr_post _ cs _ _ (hdr_mono ob _ cs cs k last hI.2.2.2.2.2.2.2.2 (Nat.le_refl _) fun a ha => ?_) hcs
      obtain ⟨_, _, _, h1, _⟩ := hI
      exact get_set_lt _ _ _ _ (by omega)
  | m0 :: b :: r, ob, src, i, m, w, n, hi, cp, cs, tab, cur, k, last, hr, hI, hhi, hf => by
    obtain ⟨hi1, hb0, hr1⟩ := src_cons _ _ _ _ hr
    obtain ⟨hi2, hb1, hr2⟩ := src_cons _ _ _ _ hr1
    have hI' := hI
    obtain ⟨hs, hn, hcs, hw0, hwW, ht, hbd, hcur, hh⟩ := hI'
    by_cases h13 : m0 = 13
    · subst h13
      rw [mn_a' _ _ _ _ _ _ _ _ _ _ hi1 hb0 (.inl rfl), show (13 : UInt8).toNat = 13 from rfl]
      have e : inlS (13 :: b :: r) tab cur hi k last = inlS r (tab ++ [cur]) [] hi b.toNat cur := by
        rw [inlS, if_pos rfl]
      rw [e] at hf ⊢
      have := tot_lt _ _ _ _ _ _ hf
      simp only [tot, S_append, List.length_nil] at this
      rw [mn_b13 _ _ _ _ _ _ _ _ _ hi2 hb1 (by omega)]
      exact mn_main r _ src _ 13 (w + 1) (n + 1) hi cp (w + 1) _ _ _ _ hr2
        (inv13 ob tab cur w n cs k last b hI (by omega)) hhi hf
    by_cases h14 : m0 = 14
    · subst h14
      rw [mn_a' _ _ _ _ _ _ _ _ _ _ hi1 hb0 (.inr (.inl rfl)), show (14 : UInt8).toNat = 14 from rfl, mn_b14 _ _ _ _ _ _ _ _ _ hi2 hb1]
      have e : inlS (14 :: b :: r) tab cur hi k last = inlS r tab cur b.toNat k last := by
        rw [inlS, if_neg (by decide), if_pos rfl]
      rw [e] at hf ⊢
      exact mn_main r ob src _ 14 w n b.toNat cp cs _ _ _ _ hr2 hI b.toNat_lt hf
    by_cases h15 : m0 = 15
    · subst h15
      rw [mn_a' _ _ _ _ _ _ _ _ _ _ hi1 hb0 (.inr (.inr rfl)), show (15 : UInt8).toNat = 15 from rfl]
      have e : inlS (15 :: b :: r) tab cur hi k last =
          inlS r tab (cur ++ tab.getD (hi * 256 + b.toNat) []) hi k last := by
        rw [inlS, if_neg (by decide), if_neg (by decide), if_pos rfl]
      rw [e] at hf ⊢
      have hbl := b.toNat_lt
      by_cases hj : hi * 256 + b.toNat < n
      · have hjt : hi * 256 + b.toNat < tab.length := by omega
        have eg : tab.getD (hi * 256 + b.toNat) [] = tab[hi * 256 + b.toNat] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjt]
        rw [eg] at hf ⊢
        have ht1 := tot_lt _ _ _ _ _ _ hf
        simp only [tot, List.length_append] at ht1
        have hlt := S_take_lt tab _ hjt
        rw [mn_b15 ob src _ w n hi cp cs (S (tab.take (hi * 256 + b.toNat))) (tab[hi * 256 + b.toNat]).length b hi2 hb1
          hj (ht _ (by omega) (by omega)) (by rw [ht _ (by omega) (by omega), S_take_succ _ _ hjt])
          (by omega) (by omega)]
        rcases r with _ | ⟨b2, r⟩
        · rw [mn_end _ _ _ _ _ _ _ _ _ _ _ (src_nil _ _ hr2)]
          exact hdr_post _ _ _ _ hh (by omega)
        · obtain ⟨hi3, -, -⟩ := src_cons _ _ _ _ hr2
          obtain ⟨ob', hs', hk', hc', he⟩ := mn_copyAll (tab[hi * 256 + b.toNat]) ob src _ 15 w n hi
            (S (tab.take (hi * 256 + b.toNat))) cs hi3 (by omega) (by omega) hs
            (fun q hq => hbd _ hjt q hq)
          rw [he]
          exact mn_main (b2 :: r) ob' src _ 15 _ n hi _ cs _ _ _ _ hr2
            (inv_keep ob ob' tab cur w n cs k last hI hs' hk' _ hc' (by omega)) hhi hf
      · have eg : tab.getD (hi * 256 + b.toNat) [] = [] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show tab.length ≤ hi * 256 + b.toNat by omega)]
        rw [eg, List.append_nil] at hf ⊢
        rw [mn_b15' _ _ _ _ _ _ _ _ _ hi2 hb1 hj]
        exact mn_main r ob src _ 15 w n hi cp cs _ _ _ _ hr2 hI hhi hf
    · have e : inlS (m0 :: b :: r) tab cur hi k last = inlS r tab (cur ++ [m0, b]) hi k last := by
        rw [inlS, if_neg h13, if_neg h14, if_neg h15]
      rw [e] at hf ⊢
      have ht1 := tot_lt _ _ _ _ _ _ hf
      simp only [tot, List.length_append, List.length_cons, List.length_nil] at ht1
      have n13 : m0.toNat ≠ 13 := fun h => h13 (UInt8.toNat_inj.mp (h.trans rfl))
      have n14 : m0.toNat ≠ 14 := fun h => h14 (UInt8.toNat_inj.mp (h.trans rfl))
      have n15 : m0.toNat ≠ 15 := fun h => h15 (UInt8.toNat_inj.mp (h.trans rfl))
      rw [mn_a _ _ _ _ _ _ _ _ _ _ hi1 hb0 h13 h14 h15 (by omega),
        mn_bx _ _ _ _ _ _ _ _ _ _ hi2 hb1 n13 n14 n15 (by omega)]
      have hs2 : ((ob.set! (BASE + w) m0.toNat).set! (BASE + (w + 1)) b.toNat).size = CAP := by
        simp only [aset_size, hs]
      have hI2 := inv_keep ob ((ob.set! (BASE + w) m0.toNat).set! (BASE + (w + 1)) b.toNat) tab cur w n cs k last hI
        hs2 (fun a ha => by rw [get_set_lt _ _ _ _ (by omega), get_set_lt _ _ _ _ ha]) [m0, b] (fun q hq => by
          match q, hq with
          | 0, _ =>
            simp only [Nat.add_zero]
            rw [get_set_lt _ _ _ _ (by omega), get_set_self _ _ _ (by rw [hs]; unfold CAP BASE WCAP at *; omega)]
            rfl
          | 1, _ =>
            rw [show BASE + w + 1 = BASE + (w + 1) by omega,
              get_set_self _ _ _ (by rw [aset_size, hs]; unfold CAP BASE WCAP at *; omega)]
            rfl) (by simp; omega)
      exact mn_main r _ src _ m0.toNat (w + 1 + 1) n hi cp cs _ _ _ _ hr2 hI2 hhi hf

/-! ## the stage -/

theorem inv0 (sz : Nat) (h : sz = CAP) : Inv (Array.replicate sz 0) [] [] 0 0 0 0 [] := by
  subst h
  have g : ∀ j, (Array.replicate CAP 0)[j]! = 0 := fun j => by
    rw [arr_get]; simp [List.getElem?_replicate]; split <;> rfl
  refine ⟨by simp, rfl, rfl, rfl, by unfold WCAP; omega, fun j h1 _ => ?_, fun j hj => absurd hj (by simp),
    fun q hq => absurd hq (by simp), .inl ⟨g _, rfl, rfl⟩⟩
  rw [g]; simp [S]

/-- the main loop on an input -/
def inlR (xs : ByteArray) : Array Nat := mn (Array.replicate (CAP + 0 * xs.size) 0) xs 0 0 0 0 0 0 0 0 0

theorem inlP_def (xs : ByteArray) : inlP xs = em (xs.extract 0 0) (inlR xs) 0
    ((inlR xs)[HD]! / 16777216 % 16777216) ((inlR xs)[HD]! % 16777216 - 1 - (inlR xs)[HD]! / 16777216 % 16777216)
    (if (inlR xs)[HD]! % 16777216 == 0 then 0 else (inlR xs)[BASE + ((inlR xs)[HD]! % 16777216 - 1)]! % 256) := rfl

theorem extract00 (xs : ByteArray) : (xs.extract 0 0).data.toList = [] := by
  apply List.eq_nil_of_length_eq_zero
  have := @ByteArray.size_extract xs 0 0
  simp only [Array.length_toList]; exact this.trans (by simp)

/-- **the paged inliner computes `inlB`** whenever the inliner's table fits the buffer -/
theorem inlP_eq (x : List UInt8) (h : inlFits x) : (inlP ⟨⟨x⟩⟩).data.toList = inlB x := by
  have hm : Post (inlR ⟨⟨x⟩⟩) (inlS x [] [] 0 0 []).2.2.1 (inlS x [] [] 0 0 []).2.2.2 :=
    mn_main x _ ⟨⟨x⟩⟩ 0 0 0 0 0 0 0 [] [] 0 [] (by simp) (inv0 _ (by simp)) (by decide) h
  rw [inlP_def]
  generalize inlR ⟨⟨x⟩⟩ = R at hm ⊢
  obtain ⟨h1, h2, h3⟩ := hm
  rw [h2, h1, inlB, inlGo_inlS]
  exact em_wrap _ (extract00 _) R _ _ _ h3

end Nano.IP
