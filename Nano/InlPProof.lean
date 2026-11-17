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
def eB (ob : ByteArray) (ls len k t : Nat) : UInt8 :=
  if t < 2 then 0
  else if t < 2 + 20 * k then argB ((t - 2) % 20)
  else if t < 2 + 20 * k + len then ob.get! (ls + (t - 2 - 20 * k))
  else if t == 2 + 20 * k + len then 7
  else if t == 3 + 20 * k + len then 0
  else if t < 36 + 20 * k + len then wrB (t - 4 - 20 * k - len)
  else if t == 36 + 20 * k + len then 12 else 0

theorem em_eq (ob : ByteArray) (ls len k : Nat) : ∀ (n t : Nat) (out : ByteArray), 20 * k + len + 38 - t = n →
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
theorem em_wrap (ob : ByteArray) (ls k : Nat) (last : List UInt8)
    (hb : ∀ q (h : q < last.length), ob.get! (ls + q) = last[q]) :
    (em (ByteArray.mk #[]) ob 0 ls last.length k).data.toList = wrap k last := by
  rw [em_eq ob ls last.length k _ 0 _ rfl]
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
    · rw [if_pos t2, List.getElem_append_left (by omega), hb (t - 2 - 20 * k) (by omega)]
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

theorem mn_end (ob : ByteArray) (st : Array Nat) (src : ByteArray) (i ph m w n hi cp rem cs ls le k : Nat)
    (h : ¬ i < src.size) : mn ob st src i ph m w n hi cp rem cs ls le k =
    ((((((ob.set! WCAP (UInt8.ofNat (ls % 256))).set! (WCAP + 1) (UInt8.ofNat (ls / 256 % 256))).set! (WCAP + 2)
      (UInt8.ofNat (ls / 65536 % 256))).set! (WCAP + 3) (UInt8.ofNat ((le - ls) % 256))).set! (WCAP + 4)
      (UInt8.ofNat ((le - ls) / 256 % 256))).set! (WCAP + 5) (UInt8.ofNat ((le - ls) / 65536 % 256))).set! (WCAP + 6)
      (UInt8.ofNat k) := by
  rw [mn, if_neg h]

/-- a copy step -/
theorem mn_copy (ob : ByteArray) (st : Array Nat) (src : ByteArray) (i m w n hi cp rem cs ls le k : Nat)
    (h : i < src.size) (hr : 0 < rem) (hw : w < WCAP) : mn ob st src i 0 m w n hi cp rem cs ls le k =
    mn (ob.set! w (ob.get! cp)) st src i 0 m (w + 1) n hi (cp + 1) (rem - 1) cs ls le k := by
  rw [mn, if_pos h]
  simp only [hr, if_true, hw, aset_self]

/-- the first byte of a pair, a plain micro-op -/
theorem mn_a (ob : ByteArray) (st : Array Nat) (src : ByteArray) (i m0 w n hi cp cs ls le k : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (h13 : b ≠ 13) (h14 : b ≠ 14) (h15 : b ≠ 15) (hw : w < WCAP) :
    mn ob st src i 0 m0 w n hi cp 0 cs ls le k =
    mn (ob.set! w b) st src (i + 1) 1 b.toNat (w + 1) n hi cp 0 cs ls le k := by
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, h13, h14, h15, hw, aset_self, if_true,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq]

/-- the first byte of a pair, `13`/`14`/`15` -/
theorem mn_a' (ob : ByteArray) (st : Array Nat) (src : ByteArray) (i m0 w n hi cp cs ls le k : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (hm : b = 13 ∨ b = 14 ∨ b = 15) :
    mn ob st src i 0 m0 w n hi cp 0 cs ls le k = mn ob st src (i + 1) 1 b.toNat w n hi cp 0 cs ls le k := by
  have hw : (b = 13 ∨ b = 14) ∨ b = 15 := or_assoc.mpr hm
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, aset_self, if_true, set_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or]

/-- the second byte, after `13`: close the def -/
theorem mn_b13 (ob : ByteArray) (st : Array Nat) (src : ByteArray) (i w n hi cp cs ls le k : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (hw : w < WCAP) :
    mn ob st src i 1 13 w n hi cp 0 cs ls le k =
    mn (ob.set! w b) (st.set! (n + 1) (w + 1)) src (i + 1) 0 13 (w + 1) (n + 1) hi cp 0 (w + 1) cs w b.toNat := by
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, aset_self, if_true, set_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or]

/-- the second byte, after `14` -/
theorem mn_b14 (ob : ByteArray) (st : Array Nat) (src : ByteArray) (i w n hi cp cs ls le k : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) :
    mn ob st src i 1 14 w n hi cp 0 cs ls le k = mn ob st src (i + 1) 0 14 w n b.toNat cp 0 cs ls le k := by
  have hw : True := trivial
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, aset_self, if_true, set_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or]

/-- the second byte, after `15`, a def in the table -/
theorem mn_b15 (ob : ByteArray) (st : Array Nat) (src : ByteArray) (i w n hi cp cs ls le k a len : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (hj : hi * 256 + b.toNat < n) (ha : st[hi * 256 + b.toNat]! = a)
    (ha1 : st[hi * 256 + b.toNat + 1]! = a + len + 1) (haW : a < WCAP) (hlW : len < WCAP) :
    mn ob st src i 1 15 w n hi cp 0 cs ls le k = mn ob st src (i + 1) 0 15 w n hi a len cs ls le k := by
  have hw : True := trivial
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, aset_self, if_true, set_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or, hj, ha, ha1, haW, show a + len + 1 - 1 - a = len by omega, hlW]

/-- the second byte, after `15`, no such def -/
theorem mn_b15' (ob : ByteArray) (st : Array Nat) (src : ByteArray) (i w n hi cp cs ls le k : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (hj : ¬ hi * 256 + b.toNat < n) :
    mn ob st src i 1 15 w n hi cp 0 cs ls le k = mn ob st src (i + 1) 0 15 w n hi cp 0 cs ls le k := by
  have hw : True := trivial
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, aset_self, if_true, set_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or, hj]

/-- the second byte, after a plain micro-op -/
theorem mn_bx (ob : ByteArray) (st : Array Nat) (src : ByteArray) (i m w n hi cp cs ls le k : Nat) (b : UInt8)
    (h : i < src.size) (hb : src.get! i = b) (h13 : m ≠ 13) (h14 : m ≠ 14) (h15 : m ≠ 15) (hw : w < WCAP) :
    mn ob st src i 1 m w n hi cp 0 cs ls le k = mn (ob.set! w b) st src (i + 1) 0 m (w + 1) n hi cp 0 cs ls le k := by
  rw [mn, if_pos h]
  simp (config := { decide := true }) only [Nat.lt_irrefl, if_false, hb, hw, aset_self, if_true, set_self,
    Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.zero_mul, Nat.add_zero, or_false, false_or, and_false,
    false_and, decide_eq_true_eq, and_true, true_and, or_true, true_or, h13, h14, h15]

end Nano.IP
