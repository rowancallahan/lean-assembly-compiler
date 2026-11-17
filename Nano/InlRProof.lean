/- The three inliner stages compute `inlB` (branch nano-final): `ww (inlQ (pr x)) = inlB x` whenever the inliner's
table stays below `2^17 - 1` bytes (`inlFitsR`).  `Q`'s main loop simulates close B's `inlS` (`inlGo` with its final
state) record by record; the invariant is close B's `Inv` with cells packed as `start · 2^17 + length`. -/
import Nano.InlR
import Nano.InlRP
import Nano.InlPProof

set_option linter.unusedSimpArgs false

namespace Nano.IR
open Nano Nano.U Nano.IP

/-! ## `UInt64` cells -/

theorem wget_set (a : Array UInt64) (i j : Nat) (v : UInt64) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  rw [getElem!_def, getElem!_def]
  simp only [Array.set!, Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h; by_cases hs : i < a.size <;> simp [hs]
  · simp [h]

theorem wset_size (a : Array UInt64) (i : Nat) (v : UInt64) : (a.set! i v).size = a.size := by simp [Array.set!]

theorem wset_self (a : Array UInt64) (i : Nat) : a.set! i a[i]! = a := by
  apply Array.ext
  · simp [Array.set!]
  · intro j h1 h2
    have := wget_set a i j a[i]!
    rw [getElem!_pos _ j (by simpa [Array.set!] using h1), getElem!_pos a j h2] at this
    rw [this]; split
    · rename_i h; obtain ⟨rfl, -⟩ := h; rw [getElem!_pos a i h2]
    · rfl

theorem wget_set_ne (a : Array UInt64) (i j : Nat) (v : UInt64) (h : i ≠ j) : (a.set! i v)[j]! = a[j]! := by
  rw [wget_set, if_neg (fun e => h e.1)]

theorem wget_set_eq (a : Array UInt64) (i : Nat) (v : UInt64) (h : i < a.size) : (a.set! i v)[i]! = v := by
  rw [wget_set, if_pos ⟨rfl, h⟩]

/-! ## the emit loop -/

/-- the byte the emit loop writes at `t` -/
def qB (ob : Array UInt64) (ls len t : Nat) : UInt8 := ob[BASE + ls + (if t == 0 then len else t) - 1]!.toUInt8

theorem eq_spec (ob : Array UInt64) (ls len : Nat) : ∀ (n t : Nat) (out : Array UInt8),
    len - t = n → out.size = len →
    (eq out ob t ls len).size = len ∧
      ∀ q, q < len → (eq out ob t ls len)[q]! = if q < t then out[q]! else qB ob ls len q
  | 0, t, out, h, hs => by
    rw [eq, if_neg (by omega)]
    exact ⟨hs, fun q hq => by rw [if_pos (by omega)]⟩
  | n + 1, t, out, h, hs => by
    rw [eq, if_pos (by omega)]
    show (eq (out.set! t (qB ob ls len t)) ob (t + 1) ls len).size = _ ∧ _
    obtain ⟨h1, h2⟩ := eq_spec ob ls len n (t + 1) (out.set! t (qB ob ls len t)) (by omega)
      (by rw [uset_size, hs])
    refine ⟨h1, fun q hq => ?_⟩
    show (eq (out.set! t (qB ob ls len t)) ob (t + 1) ls len)[q]! = _
    rw [h2 q hq, uget_set]
    by_cases hqt : q < t
    · rw [if_pos (Nat.lt_succ_of_lt hqt), if_neg (by omega), if_pos hqt]
    · by_cases hqe : q = t
      · rw [if_pos (by omega), if_pos ⟨hqe.symm, by omega⟩, if_neg hqt, hqe]
      · rw [if_neg (by omega), if_neg hqt]

theorem eq_list (ob : Array UInt64) (ls len : Nat) :
    (eq (Array.replicate len 0) ob 0 ls len).toList = (List.range' 0 len).map (qB ob ls len) := by
  obtain ⟨h1, h2⟩ := eq_spec ob ls len _ 0 (Array.replicate len 0) rfl (by simp)
  apply List.ext_getElem
  · simp [h1]
  · intro q hq _
    have hq' : q < len := by simpa [h1] using hq
    have := h2 q hq'
    rw [if_neg (by omega), getElem!_pos _ q (by rw [h1]; exact hq')] at this
    simp only [Array.getElem_toList, this, List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]

/-- the emit loop on a stored body `last` with its arity byte `k` after it -/
theorem eq_body (ob : Array UInt64) (ls : Nat) (k : UInt8) (last : List UInt8)
    (hb : ∀ q (hq : q < last.length), ob[BASE + ls + q]!.toNat = last[q].toNat)
    (hk : ob[BASE + ls + last.length]!.toNat = k.toNat) :
    (eq (Array.replicate (last.length + 1) 0) ob 0 ls (last.length + 1)).toList = k :: last := by
  rw [eq_list]
  apply List.ext_getElem
  · simp
  · intro q h1 h2
    simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul, qB]
    cases q with
    | zero =>
      simp only [beq_self_eq_true, if_true, List.getElem_cons_zero]
      rw [show BASE + ls + (last.length + 1) - 1 = BASE + ls + last.length by omega]
      apply UInt8.toNat_inj.mp; rw [UInt64.toNat_toUInt8, hk, Nat.mod_eq_of_lt k.toNat_lt_size]
    | succ q =>
      simp only [Nat.succ_ne_zero, beq_iff_eq, if_false, List.getElem_cons_succ]
      rw [show BASE + ls + (q + 1) - 1 = BASE + ls + q by omega]
      have hq : q < last.length := by simp at h1; omega
      apply UInt8.toNat_inj.mp; rw [UInt64.toNat_toUInt8, hb q hq, Nat.mod_eq_of_lt (last[q]).toNat_lt_size]

/-! ## stage `W` -/

theorem ww_suf (xs : List UInt8) : ww xs 3 0 0 = mo 7 0 ++ sWr ++ mo 12 0 := by
  iterate 9 (rw [ww.eq_def]; simp (config := {decide := true}) only [if_true, if_false, Nat.reduceAdd])

theorem ww_body : ∀ (body : List UInt8), ww body 2 0 0 = body ++ mo 7 0 ++ sWr ++ mo 12 0
  | [] => by rw [ww.eq_def]; simp only [show ¬ (2 < 1) by omega, show ¬ (2 < 2) by omega, show 2 < 3 by omega,
      if_true, if_false]; exact ww_suf []
  | b :: t => by
    rw [ww.eq_def]; simp only [show ¬ (2 < 1) by omega, show ¬ (2 < 2) by omega, show 2 < 3 by omega,
      if_true, if_false, ww_body t, List.cons_append]

theorem ww_pro (body : List UInt8) : ∀ k : Nat, ww body 1 k 0 = serPro k ++ ww body 2 0 0
  | 0 => by
    rw [ww.eq_def]; simp only [show ¬ (1 < 1) by omega, show 1 < 2 by omega, show 0 < 1 by omega, if_true,
      if_false]; rfl
  | k + 1 => by
    have e : ∀ q, q ≤ 4 → ww body 1 (k + 1) q = (sArg.drop (4 * q)) ++ ww body 1 k 0 := by
      intro q hq
      induction hq' : 4 - q generalizing q with
      | zero =>
        have : q = 4 := by omega
        subst this
        rw [ww.eq_def]; simp only [show ¬ (1 < 1) by omega, show 1 < 2 by omega, show ¬ (k + 1 < 1) by omega,
          show ¬ (4 < 4) by omega, if_true, if_false, Nat.add_sub_cancel]; rfl
      | succ m ih =>
        rw [ww.eq_def]; simp only [show ¬ (1 < 1) by omega, show 1 < 2 by omega, show ¬ (k + 1 < 1) by omega,
          show q < 4 by omega, if_true, if_false]
        rw [ih (q + 1) (by omega) (by omega)]
        have hq4 : q < 4 := by omega
        rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;> rfl
    rw [e 0 (by omega), ww_pro body k]; simp [serPro, List.append_assoc]

theorem ww_wrap (k : UInt8) (last : List UInt8) : ww (k :: last) 0 0 0 = wrap k.toNat last := by
  rw [ww.eq_def]
  have := k.toNat_lt_size
  simp only [show (0 : Nat) < 1 by omega, if_true, show ¬ (256 ≤ k.toNat) by simp [UInt8.size] at this; omega,
    if_false]
  rw [ww_pro, ww_body]; simp [wrap, mo]

theorem ww_nil : ww [] 0 0 0 = wrap 0 [] := by
  rw [ww.eq_def]; simp only [show (0 : Nat) < 1 by omega, if_true]; rw [ww_suf]; rfl

/-! ## stage `P` -/

theorem u64_lt (hi x : UInt8) (n : UInt64) :
    (hi.toUInt64 * 256 + x.toUInt64 < n) ↔ hi.toNat * 256 + x.toNat < n.toNat := by
  have h1 := hi.toNat_lt_size; have h2 := x.toNat_lt_size
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_mul]
  simp only [UInt8.toNat_toUInt64, UInt64.reduceToNat, UInt8.size] at *
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem pr13 (x : UInt8) (r : List UInt8) (hi : UInt8) (n : UInt64) :
    pr (13 :: x :: r) hi n = (if n < 65536 then [0, 0, x, 2, (n >>> 8).toUInt8, n.toUInt8, 3, 0, 0]
      else [0, 0, x, 3, 0, 0]) ++ pr r hi (n + 1) := by
  rw [pr]; simp only [show ((13 : UInt8) == 13) = true from rfl, if_true]; split <;> rfl

theorem pr14 (x : UInt8) (r : List UInt8) (hi : UInt8) (n : UInt64) : pr (14 :: x :: r) hi n = pr r x n := by
  rw [pr]; rfl

theorem pr15 (x : UInt8) (r : List UInt8) (hi : UInt8) (n : UInt64) :
    pr (15 :: x :: r) hi n = if hi.toUInt64 * 256 + x.toUInt64 < n then [1, hi, x] ++ pr r hi n else pr r hi n := by
  rw [pr]; simp only [show ((15 : UInt8) == 13) = false from rfl, show ((15 : UInt8) == 14) = false from rfl,
    show ((15 : UInt8) == 15) = true from rfl, Bool.false_eq_true, if_false, if_true]; split <;> rfl

theorem prx (m x : UInt8) (r : List UInt8) (hi : UInt8) (n : UInt64) (h13 : m ≠ 13) (h14 : m ≠ 14) (h15 : m ≠ 15) :
    pr (m :: x :: r) hi n = [0, 0, m, 0, 0, x] ++ pr r hi n := by
  rw [pr]; simp [h13, h14, h15]

/-! ## steps of `Q`'s main loop -/

/-- the table cell of a body at `ls` with `len` bytes (with the arity byte) -/
abbrev pkv (ls len : Nat) : Nat := ls * 131072 + len

theorem src3 (src : ByteArray) (i : Nat) (a b c : UInt8) (r : List UInt8)
    (h : src.data.toList.drop i = a :: b :: c :: r) :
    i + 2 < src.size ∧ src.get! i = a ∧ src.get! (i + 1) = b ∧ src.get! (i + 2) = c ∧
      src.data.toList.drop (i + 3) = r := by
  obtain ⟨h1, ha, hr1⟩ := src_cons _ _ _ _ h
  obtain ⟨h2, hb, hr2⟩ := src_cons _ _ _ _ hr1
  obtain ⟨h3, hc, hr3⟩ := src_cons _ _ _ _ hr2
  exact ⟨h3, ha, hb, hc, hr3⟩

theorem mq_end (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) (h : src.data.toList.drop i = []) :
    mq ob src i w cs cp rem = ob := by
  have := src_nil _ _ h
  rw [mq, if_neg (by omega)]

theorem mq_copy (ob : Array UInt64) (src : ByteArray) (i w cs cp rem : Nat) (h : i + 2 < src.size) (hr : 0 < rem) :
    mq ob src i w cs cp rem = mq (ob.set! (BASE + w) ob[BASE + cp]!) src i (w + 1) cs (cp + 1) (rem - 1) := by
  rw [mq, if_pos h]; simp [hr]

theorem mq_emit (ob : Array UInt64) (src : ByteArray) (i w cs cp : Nat) (b : UInt8) (r : List UInt8)
    (h : src.data.toList.drop i = 0 :: 0 :: b :: r) :
    mq ob src i w cs cp 0 = mq (ob.set! (BASE + w) (UInt64.ofNat b.toNat)) src (i + 3) (w + 1) cs cp 0 := by
  obtain ⟨h1, ha, hb, hc, -⟩ := src3 _ _ _ _ _ _ h
  rw [mq, if_pos h1]; simp [ha, hb, hc]

theorem mq_call (ob : Array UInt64) (src : ByteArray) (i w cs cp : Nat) (hi l : UInt8) (r : List UInt8)
    (h : src.data.toList.drop i = 1 :: hi :: l :: r) (ls len : Nat)
    (hc : ob[hi.toNat * 256 + l.toNat]!.toNat = pkv ls (len + 1)) (hl : len + 1 < 131072) (hs : ls < 2 ^ 40) :
    mq ob src i w cs cp 0 = mq ob src (i + 3) w cs ls len := by
  obtain ⟨h1, ha, hb, hc', -⟩ := src3 _ _ _ _ _ _ h
  rw [mq, if_pos h1]
  simp only [ha, hb, hc', Nat.lt_irrefl, decide_false, Bool.false_or, if_false, UInt8.toNat_ofNat]
  simp (config := {decide := true}) only [show (UInt8.toNat 1 == 0) = false from rfl,
    show (UInt8.toNat 1 == 3) = false from rfl, show (UInt8.toNat 1 == 1) = true from rfl, if_true, if_false,
    Bool.false_eq_true, wset_self, hc]
  have e : pkv ls (len + 1) % 4611686018427387904 = pkv ls (len + 1) := Nat.mod_eq_of_lt (by unfold pkv; omega)
  rw [e]; unfold pkv
  congr 1 <;> omega

theorem mq_tab (ob : Array UInt64) (src : ByteArray) (i w cs cp : Nat) (a b : UInt8) (r : List UInt8)
    (h : src.data.toList.drop i = 2 :: a :: b :: r) :
    mq ob src i w cs cp 0 =
      mq (ob.set! (a.toNat * 256 + b.toNat) (UInt64.ofNat (cs * 131072 + (w - cs)))) src (i + 3) w cs cp 0 := by
  obtain ⟨h1, ha, hb, hc, -⟩ := src3 _ _ _ _ _ _ h
  rw [mq, if_pos h1]; simp [ha, hb, hc]

theorem mq_hd (ob : Array UInt64) (src : ByteArray) (i w cs cp : Nat) (r : List UInt8)
    (h : src.data.toList.drop i = 3 :: 0 :: 0 :: r) :
    mq ob src i w cs cp 0 = mq (ob.set! HD (UInt64.ofNat (cs * 131072 + (w - cs)))) src (i + 3) w w cp 0 := by
  obtain ⟨h1, ha, hb, hc, -⟩ := src3 _ _ _ _ _ _ h
  rw [mq, if_pos h1]; simp [ha, hb, hc]

/-! ## the invariant -/

/-- the bound on the inliner's table (cells `BASE …`) -/
abbrev FCAP : Nat := 131071

/-- the header and the last closed def -/
def HdrR (ob : Array UInt64) (cs k : Nat) (last : List UInt8) : Prop :=
  (ob[HD]! = 0 ∧ last = [] ∧ k = 0) ∨
  (∃ ls, ob[HD]!.toNat = pkv ls (last.length + 1) ∧ ls + last.length < cs ∧ k < 256 ∧
    (∀ q (hq : q < last.length), ob[BASE + ls + q]!.toNat = last[q].toNat) ∧ ob[BASE + ls + last.length]!.toNat = k)

/-- the main loop's invariant at a record boundary -/
def InvR (ob : Array UInt64) (tab : List (List UInt8)) (cur : List UInt8) (w cs k : Nat) (last : List UInt8) :
    Prop :=
  ob.size = CAP ∧ cs = S tab ∧ w = cs + cur.length ∧ w ≤ FCAP ∧
  (∀ j, j < tab.length → j < 65536 → ob[j]!.toNat = pkv (S (tab.take j)) (tab[j]!.length + 1)) ∧
  (∀ j (hj : j < tab.length) q (hq : q < tab[j].length), ob[BASE + S (tab.take j) + q]!.toNat = tab[j][q].toNat) ∧
  (∀ q (hq : q < cur.length), ob[BASE + cs + q]!.toNat = cur[q].toNat) ∧ HdrR ob cs k last

theorem hdrR_mono (ob ob' : Array UInt64) (cs cs' k : Nat) (last : List UInt8) (h : HdrR ob cs k last)
    (hc : cs ≤ cs') (hk : ∀ a, a < BASE + cs → ob'[a]! = ob[a]!) : HdrR ob' cs' k last := by
  rcases h with ⟨h0, h1, h2⟩ | ⟨ls, hH, hlt, hk2, hb, hkb⟩
  · left; rw [hk _ (by unfold HD BASE; omega)]; exact ⟨h0, h1, h2⟩
  · right; refine ⟨ls, by rw [hk _ (by unfold HD BASE; omega)]; exact hH, by omega, hk2, fun q hq => ?_, ?_⟩
    · rw [hk _ (by omega)]; exact hb q hq
    · rw [hk _ (by omega)]; exact hkb

/-- writing at or above the current position keeps the invariant's facts below it -/
theorem invR_keep (ob ob' : Array UInt64) (tab : List (List UInt8)) (cur : List UInt8) (w cs k : Nat)
    (last : List UInt8) (h : InvR ob tab cur w cs k last) (hs : ob'.size = CAP)
    (hk : ∀ a, a < BASE + w → ob'[a]! = ob[a]!) (c : List UInt8)
    (hc : ∀ q (hq : q < c.length), ob'[BASE + w + q]!.toNat = c[q].toNat) (hw : w + c.length ≤ FCAP) :
    InvR ob' tab (cur ++ c) (w + c.length) cs k last := by
  obtain ⟨_, hcs, hw0, _, ht, hb, hcur, hh⟩ := h
  refine ⟨hs, hcs, by simp; omega, hw, fun j h1 h2 => ?_, fun j hj q hq => ?_, fun q hq => ?_,
    hdrR_mono ob ob' cs cs k last hh (Nat.le_refl _) fun a ha => hk a (by omega)⟩
  · rw [hk _ (by unfold BASE; omega)]; exact ht j h1 h2
  · have := S_take_lt tab j hj; rw [hk _ (by omega)]; exact hb j hj q hq
  · by_cases hq' : q < cur.length
    · rw [hk _ (by omega), List.getElem_append_left hq']; exact hcur q hq'
    · rw [List.getElem_append_right (by omega), show BASE + cs + q = BASE + w + (q - cur.length) by omega]
      exact hc _ _

theorem u64_ofNat (v : Nat) (h : v < 2 ^ 64) : (UInt64.ofNat v).toNat = v := by
  exact UInt64.toNat_ofNat_of_lt' h

/-- copying a stored body -/
theorem mq_copyAll : ∀ (c : List UInt8) (ob : Array UInt64) (src : ByteArray) (i w cs cp : Nat),
    i + 2 < src.size → w + c.length ≤ FCAP → cp + c.length ≤ w → ob.size = CAP →
    (∀ q (hq : q < c.length), ob[BASE + cp + q]!.toNat = c[q].toNat) →
    ∃ ob', ob'.size = CAP ∧ (∀ a, a < BASE + w → ob'[a]! = ob[a]!) ∧
      (∀ q (hq : q < c.length), ob'[BASE + w + q]!.toNat = c[q].toNat) ∧
      mq ob src i w cs cp c.length = mq ob' src i (w + c.length) cs (cp + c.length) 0
  | [], ob, src, i, w, cs, cp, _, _, _, hs, _ =>
    ⟨ob, hs, fun _ _ => rfl, fun q hq => absurd hq (Nat.not_lt_zero _), rfl⟩
  | b :: c, ob, src, i, w, cs, cp, hi', hw, hcp, hs, hc => by
    simp only [List.length_cons] at hw hcp
    have h0 := hc 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hs1 : (ob.set! (BASE + w) ob[BASE + cp]!).size = CAP := by rw [wset_size, hs]
    obtain ⟨ob', hs', hlo, hc', he⟩ := mq_copyAll c (ob.set! (BASE + w) ob[BASE + cp]!) src i (w + 1) cs (cp + 1) hi'
      (by omega) (by omega) hs1 (fun q hq => by
        rw [wget_set_ne _ _ _ _ (by omega), show BASE + (cp + 1) + q = BASE + cp + (q + 1) by omega,
          hc (q + 1) (by simp; omega)]; simp)
    refine ⟨ob', hs', fun a ha => by rw [hlo a (by omega), wget_set_ne _ _ _ _ (by omega)], fun q hq => ?_, ?_⟩
    · cases q with
      | zero =>
        rw [hlo _ (by omega), Nat.add_zero, wget_set_eq _ _ _ (by rw [hs]; unfold BASE CAP FCAP at *; omega)]
        exact h0
      | succ q =>
        rw [show BASE + w + (q + 1) = BASE + (w + 1) + q by omega, hc' q (by simp at hq; omega)]; rfl
    · show mq ob src i w cs cp (c.length + 1) = mq ob' src i (w + (c.length + 1)) cs (cp + (c.length + 1)) 0
      rw [mq_copy ob src i w cs cp (c.length + 1) hi' (by omega), Nat.add_sub_cancel, he]
      congr 1 <;> omega

theorem nbytes (n : UInt64) (h : n.toNat < 65536) :
    (n >>> 8).toUInt8.toNat * 256 + n.toUInt8.toNat = n.toNat := by
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
    Nat.shiftRight_eq_div_pow]
  omega

/-- closing a def: the arity byte, the table cell (for `n < 65536`), the header -/
theorem inv13R (ob : Array UInt64) (tab : List (List UInt8)) (cur : List UInt8) (w cs k : Nat) (last : List UInt8)
    (b : UInt8) (h : InvR ob tab cur w cs k last) (hw : w + 1 ≤ FCAP) :
    InvR (((fun o : Array UInt64 => if tab.length < 65536 then o.set! tab.length (UInt64.ofNat (pkv cs (w + 1 - cs)))
        else o) (ob.set! (BASE + w) (UInt64.ofNat b.toNat))).set! HD (UInt64.ofNat (pkv cs (w + 1 - cs))))
      (tab ++ [cur]) [] (w + 1) (w + 1) b.toNat cur := by
  obtain ⟨hs, hcs, hw0, _, ht, hbd, hcur, _⟩ := h
  have hbl := b.toNat_lt_size
  simp only [UInt8.size] at hbl
  have hpk : pkv cs (w + 1 - cs) < 2 ^ 64 := by unfold pkv FCAP at *; omega
  generalize hob : ob.set! (BASE + w) (UInt64.ofNat b.toNat) = ob1
  have hs1 : ob1.size = CAP := by rw [← hob, wset_size, hs]
  have r1 : ∀ a, a ≠ BASE + w → ob1[a]! = ob[a]! := fun a ha => by rw [← hob, wget_set_ne _ _ _ _ (Ne.symm ha)]
  have r1' : ob1[BASE + w]!.toNat = b.toNat := by
    rw [← hob, wget_set_eq _ _ _ (by rw [hs]; unfold CAP BASE FCAP at *; omega), u64_ofNat _ (by omega)]
  generalize hob2 : (fun o : Array UInt64 => if tab.length < 65536 then
    o.set! tab.length (UInt64.ofNat (pkv cs (w + 1 - cs))) else o) ob1 = ob2
  have hs2 : ob2.size = CAP := by rw [← hob2]; dsimp only; split <;> simp [wset_size, hs1]
  have r2 : ∀ a, (tab.length < 65536 → a ≠ tab.length) → ob2[a]! = ob1[a]! := fun a ha => by
    rw [← hob2]; dsimp only; split
    · rename_i hl; rw [wget_set_ne _ _ _ _ (Ne.symm (ha hl))]
    · rfl
  have r2' : tab.length < 65536 → ob2[tab.length]!.toNat = pkv cs (w + 1 - cs) := fun hl => by
    rw [← hob2]; dsimp only; rw [if_pos hl, wget_set_eq _ _ _ (by rw [hs1]; unfold CAP; omega), u64_ofNat _ hpk]
  have hs3 : (ob2.set! HD (UInt64.ofNat (pkv cs (w + 1 - cs)))).size = CAP := by rw [wset_size, hs2]
  have r3 : ∀ a, a ≠ HD → (ob2.set! HD (UInt64.ofNat (pkv cs (w + 1 - cs))))[a]! = ob2[a]! := fun a ha => by
    rw [wget_set_ne _ _ _ _ (Ne.symm ha)]
  have hS : S (tab ++ [cur]) = w + 1 := by rw [S_append]; omega
  have rd : ∀ a, a ≠ HD → (tab.length < 65536 → a ≠ tab.length) → a ≠ BASE + w →
      (ob2.set! HD (UInt64.ofNat (pkv cs (w + 1 - cs))))[a]! = ob[a]! := fun a h1 h2 h3 => by
    rw [r3 _ h1, r2 _ h2, r1 _ h3]
  refine ⟨hs3, hS.symm, by simp, hw, fun j h1 h2 => ?_, fun j hj q hq => ?_,
    fun q hq => absurd hq (Nat.not_lt_zero _), Or.inr ⟨cs, ?_, ?_, hbl, fun q hq => ?_, ?_⟩⟩
  · simp only [List.length_append, List.length_cons, List.length_nil] at h1
    by_cases hj : j = tab.length
    · subst hj
      rw [r3 _ (by unfold HD; omega), r2' h2, take_append_le _ _ _ (Nat.le_refl _),
        List.take_of_length_le (Nat.le_refl _), ← hcs]
      have e : (tab ++ [cur])[tab.length]! = cur := by simp [List.getElem!_eq_getElem?_getD]
      rw [e]; unfold pkv; omega
    · rw [rd _ (by unfold HD; omega) (fun _ => hj) (by unfold BASE; omega), take_append_le _ _ _ (by omega)]
      have hj' : j < tab.length := by omega
      rw [ht j hj' h2]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_left hj', List.getElem?_eq_getElem hj']
  · simp only [List.length_append, List.length_cons, List.length_nil] at hj
    by_cases hjn : j < tab.length
    · have := S_take_lt tab j hjn
      have hq2 : q < tab[j].length := by simpa [List.getElem_append_left hjn] using hq
      rw [take_append_le _ _ _ (by omega), rd _ (by unfold HD BASE; omega) (fun _ => by unfold BASE; omega)
        (by omega), hbd j hjn q hq2]
      simp only [List.getElem_append_left hjn]
    · have hj' : j = tab.length := by omega
      subst hj'
      have hq' : q < cur.length := by simpa using hq
      rw [take_append_le _ _ _ (Nat.le_refl _), List.take_of_length_le (Nat.le_refl _), ← hcs,
        rd _ (by unfold HD BASE; omega) (fun _ => by unfold BASE; omega) (by omega), hcur q hq']
      simp
  · rw [wget_set_eq _ _ _ (by rw [hs2]; unfold HD CAP; omega), u64_ofNat _ hpk]; unfold pkv; congr 1; omega
  · omega
  · rw [rd _ (by unfold HD BASE; omega) (fun _ => by unfold BASE; omega) (by omega)]; exact hcur q hq
  · rw [show BASE + cs + cur.length = BASE + w by omega, r3 _ (by unfold HD BASE; omega), r2 _ (fun _ => by unfold BASE; omega), r1']

/-- `P`'s output is empty or starts with a whole record -/
theorem pr_cons3 : ∀ (r : List UInt8) (hi : UInt8) (n : UInt64),
    pr r hi n = [] ∨ ∃ a b c t, pr r hi n = a :: b :: c :: t
  | m :: x :: r, hi, n => by
    by_cases h13 : m = 13
    · subst h13; rw [pr13]; right; split <;> exact ⟨_, _, _, _, rfl⟩
    by_cases h14 : m = 14
    · subst h14; rw [pr14]; exact pr_cons3 r x n
    by_cases h15 : m = 15
    · subst h15; rw [pr15]; split
      · right; exact ⟨_, _, _, _, rfl⟩
      · exact pr_cons3 r hi n
    · rw [prx _ _ _ _ _ h13 h14 h15]; right; exact ⟨_, _, _, _, rfl⟩
  | [], _, _ => by left; simp [pr]
  | [_], _, _ => by left; simp [pr]

/-- no output from `P`: no def is closed -/
theorem inlS_nil : ∀ (r : List UInt8) (hi : UInt8) (n : UInt64) (tab : List (List UInt8)) (cur : List UInt8)
    (h k : Nat) (last : List UInt8), pr r hi n = [] → (inlS r tab cur h k last).2.2 = (k, last)
  | m :: x :: r, hi, n, tab, cur, h, k, last, hp => by
    by_cases h13 : m = 13
    · subst h13; rw [pr13] at hp; split at hp <;> simp at hp
    by_cases h14 : m = 14
    · subst h14; rw [pr14] at hp; rw [inlS, if_neg (by decide), if_pos rfl]; exact inlS_nil r x n _ _ _ _ _ hp
    by_cases h15 : m = 15
    · subst h15; rw [pr15] at hp; split at hp
      · simp at hp
      · rw [inlS, if_neg (by decide), if_neg (by decide), if_pos rfl]; exact inlS_nil r hi n _ _ _ _ _ hp
    · rw [prx _ _ _ _ _ h13 h14 h15] at hp; simp at hp
  | [], _, _, _, _, _, _, _, _ => by simp [inlS]
  | [_], _, _, _, _, _, _, _, _ => by simp [inlS]

theorem len_le_S : ∀ tab : List (List UInt8), tab.length ≤ IP.S tab
  | [] => by simp [IP.S]
  | c :: t => by
    have := len_le_S t
    have e : IP.S (c :: t) = c.length + 1 + IP.S t := by simp [IP.S]
    simp only [List.length_cons]; omega

/-- what the emit loop needs -/
def PostR (R : Array UInt64) (k : Nat) (last : List UInt8) : Prop := ∃ cs, cs ≤ FCAP ∧ HdrR R cs k last

theorem tot_le (rest : List UInt8) (tab : List (List UInt8)) (cur : List UInt8) (hi k : Nat) (last : List UInt8)
    (h : tot (inlS rest tab cur hi k last).1 (inlS rest tab cur hi k last).2.1 ≤ FCAP) : tot tab cur ≤ FCAP :=
  Nat.le_trans (tot_mono _ _ _ _ _ _) h

theorem mq_main : ∀ (rest : List UInt8) (ob : Array UInt64) (src : ByteArray) (i w cs cp : Nat)
    (tab : List (List UInt8)) (cur : List UInt8) (hi : UInt8) (n : UInt64) (k : Nat) (last : List UInt8),
    src.data.toList.drop i = pr rest hi n → n.toNat = tab.length → InvR ob tab cur w cs k last →
    tot (inlS rest tab cur hi.toNat k last).1 (inlS rest tab cur hi.toNat k last).2.1 ≤ FCAP →
    PostR (mq ob src i w cs cp 0) (inlS rest tab cur hi.toNat k last).2.2.1
      (inlS rest tab cur hi.toNat k last).2.2.2
  | rest, ob, src, i, w, cs, cp, tab, cur, hi, n, k, last, hr, hn, hI, hf => by
    have hI' := hI
    obtain ⟨hs, hcs, hw0, hwF, ht, hbd, hcur, hh⟩ := hI'
    by_cases hp : pr rest hi n = []
    · rw [hp] at hr
      rw [mq_end _ _ _ _ _ _ _ hr, inlS_nil rest hi n _ _ _ _ _ hp]
      exact ⟨cs, by omega, hh⟩
    match rest, hp, hr, hf with
    | [], hp, _, _ => exact absurd (by simp [pr]) hp
    | [_], hp, _, _ => exact absurd (by simp [pr]) hp
    | m :: x :: r, _, hr, hf =>
    have hxl := x.toNat_lt_size
    have hil := hi.toNat_lt_size
    simp only [UInt8.size] at hxl hil
    by_cases h13 : m = 13
    · subst h13
      have e : inlS (13 :: x :: r) tab cur hi.toNat k last = inlS r (tab ++ [cur]) [] hi.toNat x.toNat cur := by
        rw [inlS, if_pos rfl]
      rw [e] at hf ⊢
      have ht1 := tot_le _ _ _ _ _ _ hf
      simp only [tot, S_append, List.length_nil] at ht1
      rw [pr13] at hr
      have hn1 : (n + 1).toNat = (tab ++ [cur]).length := by
        have := len_le_S tab
        rw [UInt64.toNat_add, hn]; simp; unfold FCAP at *; omega
      have hI13 := inv13R ob tab cur w cs k last x hI (by omega)
      by_cases hl : n < 65536
      · rw [if_pos hl] at hr
        have hl' : tab.length < 65536 := by rw [← hn]; exact (UInt64.lt_iff_toNat_lt).mp hl
        have d1 := (src3 _ _ _ _ _ _ hr).2.2.2.2
        have d2 := (src3 _ _ _ _ _ _ d1).2.2.2.2
        have d3 := (src3 _ _ _ _ _ _ d2).2.2.2.2
        rw [mq_emit _ _ _ _ _ _ _ _ hr, mq_tab _ _ _ _ _ _ _ _ _ d1, nbytes n (by rw [hn]; exact hl'), hn,
          mq_hd _ _ _ _ _ _ _ d2]
        simp only [if_pos hl'] at hI13
        exact mq_main r _ src _ _ _ cp _ _ hi (n + 1) _ _ d3 hn1 hI13 hf
      · rw [if_neg hl] at hr
        have hl' : ¬ tab.length < 65536 := by rw [← hn]; exact fun h => hl ((UInt64.lt_iff_toNat_lt).mpr h)
        have d1 := (src3 _ _ _ _ _ _ hr).2.2.2.2
        have d2 := (src3 _ _ _ _ _ _ d1).2.2.2.2
        rw [mq_emit _ _ _ _ _ _ _ _ hr, mq_hd _ _ _ _ _ _ _ d1]
        simp only [if_neg hl'] at hI13
        exact mq_main r _ src _ _ _ cp _ _ hi (n + 1) _ _ d2 hn1 hI13 hf
    by_cases h14 : m = 14
    · subst h14
      have e : inlS (14 :: x :: r) tab cur hi.toNat k last = inlS r tab cur x.toNat k last := by
        rw [inlS, if_neg (by decide), if_pos rfl]
      rw [e] at hf ⊢
      rw [pr14] at hr
      exact mq_main r ob src i w cs cp tab cur x n k last hr hn hI hf
    by_cases h15 : m = 15
    · subst h15
      have e : inlS (15 :: x :: r) tab cur hi.toNat k last =
          inlS r tab (cur ++ tab.getD (hi.toNat * 256 + x.toNat) []) hi.toNat k last := by
        rw [inlS, if_neg (by decide), if_neg (by decide), if_pos rfl]
      rw [e] at hf ⊢
      rw [pr15] at hr
      by_cases hj : hi.toUInt64 * 256 + x.toUInt64 < n
      · rw [if_pos hj] at hr
        have hjt : hi.toNat * 256 + x.toNat < tab.length := by rw [← hn]; exact (u64_lt hi x n).mp hj
        have eg : tab.getD (hi.toNat * 256 + x.toNat) [] = tab[hi.toNat * 256 + x.toNat] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjt]
        rw [eg] at hf ⊢
        have ht1 := tot_le _ _ _ _ _ _ hf
        simp only [tot, List.length_append] at ht1
        have hlt := S_take_lt tab _ hjt
        have hcell := ht _ hjt (by omega)
        have e2 : tab[hi.toNat * 256 + x.toNat]! = tab[hi.toNat * 256 + x.toNat] := by
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hjt]
        rw [e2] at hcell
        rw [mq_call ob src i w cs cp hi x _ hr _ _ hcell (by unfold FCAP at *; omega) (by unfold FCAP at *; omega)]
        have hr3 : src.data.toList.drop (i + 3) = pr r hi n := (src3 _ _ _ _ _ _ hr).2.2.2.2
        rcases pr_cons3 r hi n with hp2 | ⟨a, b, c, t, hp2⟩
        · rw [mq_end _ _ _ _ _ _ _ (hr3.trans hp2), inlS_nil r hi n _ _ _ _ _ hp2]
          exact ⟨cs, by omega, hh⟩
        · 
          obtain ⟨hi3, -⟩ := src3 _ _ _ _ _ _ (hr3.trans hp2)
          obtain ⟨ob', hs', hk', hc', he⟩ := mq_copyAll (tab[hi.toNat * 256 + x.toNat]) ob src (i + 3) w cs
            (S (tab.take (hi.toNat * 256 + x.toNat))) hi3 (by omega) (by omega) hs
            (fun q hq => hbd _ hjt q hq)
          rw [he]
          exact mq_main r ob' src _ _ cs _ _ _ hi n _ _ hr3 hn
            (invR_keep ob ob' tab cur w cs k last hI hs' hk' _ hc' (by omega)) hf
      · rw [if_neg hj] at hr
        have hjt : ¬ hi.toNat * 256 + x.toNat < tab.length := by
          rw [← hn]; exact fun h => hj ((u64_lt hi x n).mpr h)
        have eg : tab.getD (hi.toNat * 256 + x.toNat) [] = [] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show tab.length ≤ hi.toNat * 256 + x.toNat by omega)]
        rw [eg, List.append_nil] at hf ⊢
        exact mq_main r ob src i w cs cp tab cur hi n k last hr hn hI hf
    · have e : inlS (m :: x :: r) tab cur hi.toNat k last = inlS r tab (cur ++ [m, x]) hi.toNat k last := by
        rw [inlS, if_neg h13, if_neg h14, if_neg h15]
      rw [e] at hf ⊢
      have ht1 := tot_le _ _ _ _ _ _ hf
      simp only [tot, List.length_append, List.length_cons, List.length_nil] at ht1
      rw [prx _ _ _ _ _ h13 h14 h15] at hr
      have d1 := (src3 _ _ _ _ _ _ hr).2.2.2.2
      have d2 := (src3 _ _ _ _ _ _ d1).2.2.2.2
      rw [mq_emit _ _ _ _ _ _ _ _ hr, mq_emit _ _ _ _ _ _ _ _ d1]
      have hml := m.toNat_lt_size
      simp only [UInt8.size] at hml
      have hs2 : ((ob.set! (BASE + w) (UInt64.ofNat m.toNat)).set! (BASE + (w + 1)) (UInt64.ofNat x.toNat)).size
          = CAP := by simp only [wset_size, hs]
      have hI2 := invR_keep ob ((ob.set! (BASE + w) (UInt64.ofNat m.toNat)).set! (BASE + (w + 1))
        (UInt64.ofNat x.toNat)) tab cur w cs k last hI hs2
        (fun a ha => by rw [wget_set_ne _ _ _ _ (by omega), wget_set_ne _ _ _ _ (by omega)]) [m, x] (fun q hq => by
          match q, hq with
          | 0, _ =>
            simp only [Nat.add_zero]
            rw [wget_set_ne _ _ _ _ (by omega), wget_set_eq _ _ _ (by rw [hs]; unfold CAP BASE FCAP at *; omega),
              u64_ofNat _ (by omega)]
            rfl
          | 1, _ =>
            rw [show BASE + w + 1 = BASE + (w + 1) by omega,
              wget_set_eq _ _ _ (by rw [wset_size, hs]; unfold CAP BASE FCAP at *; omega), u64_ofNat _ (by omega)]
            rfl) (by simp; omega)
      exact mq_main r _ src _ _ cs cp _ _ hi n k last d2 hn hI2 hf
termination_by rest => rest.length

/-! ## the three stages -/

/-- **the inliner's table fits** (all inlined bodies with their arity bytes, and the current body, below `2^17 - 1`
bytes) -/
def inlFitsR (xs : List UInt8) : Prop :=
  tot (inlS xs [] [] 0 0 []).1 (inlS xs [] [] 0 0 []).2.1 ≤ FCAP

theorem invR0 : InvR (Array.replicate CAP 0) [] [] 0 0 0 [] := by
  have g : ∀ j : Nat, (Array.replicate CAP (0 : UInt64))[j]! = 0 := fun j => by
    rw [getElem!_def]; simp only [Array.getElem?_replicate]
    by_cases hj : j < CAP <;> simp [hj]; rfl
  refine ⟨by simp, rfl, rfl, by unfold FCAP; omega, fun j h1 _ => absurd h1 (by simp),
    fun j hj => absurd hj (by simp), fun q hq => absurd hq (by simp), .inl ⟨g _, rfl, rfl⟩⟩

/-- the paged stage's main loop on an input -/
def mqR (xs : ByteArray) : Array UInt64 := mq (Array.replicate (CAP + 0 * xs.size) 0) xs 0 0 0 0 0

theorem inlQ_def (xs : ByteArray) : inlQ xs =
    eq (Array.replicate ((mqR xs)[HD]!.toNat % 4611686018427387904 % 131072) 0) (mqR xs) 0
      ((mqR xs)[HD]!.toNat % 4611686018427387904 / 131072 % 1099511627776)
      ((mqR xs)[HD]!.toNat % 4611686018427387904 % 131072) := rfl

/-- **`W ∘ Q ∘ P = inlB`** whenever the inliner's table fits -/
theorem inlR_eq (x : List UInt8) (h : inlFitsR x) : ww (inlQ ⟨⟨pr x 0 0⟩⟩).toList 0 0 0 = inlB x := by
  have hm : PostR (mqR ⟨⟨pr x 0 0⟩⟩) (inlS x [] [] (0 : UInt8).toNat 0 []).2.2.1
      (inlS x [] [] (0 : UInt8).toNat 0 []).2.2.2 :=
    mq_main x _ ⟨⟨pr x 0 0⟩⟩ 0 0 0 0 [] [] 0 0 0 [] (by simp) rfl (by simpa using invR0) h
  rw [inlQ_def, inlB, inlGo_inlS]
  simp only [UInt8.toNat_zero] at hm
  generalize mqR ⟨⟨pr x 0 0⟩⟩ = R at hm ⊢
  generalize (inlS x [] [] 0 0 []).2.2.1 = k at hm ⊢
  generalize (inlS x [] [] 0 0 []).2.2.2 = last at hm ⊢
  obtain ⟨cs, hcs, hH⟩ := hm
  rcases hH with ⟨h0, rfl, rfl⟩ | ⟨ls, hH, hlt, hk, hb, hkb⟩
  · rw [h0]; simp only [UInt64.toNat_zero, Nat.zero_mod, Nat.zero_div]
    rw [eq, if_neg (by omega)]; exact ww_nil
  · have e1 : R[HD]!.toNat % 4611686018427387904 = pkv ls (last.length + 1) := by
      rw [hH]; unfold pkv FCAP at *; omega
    have e2 : pkv ls (last.length + 1) % 131072 = last.length + 1 := by unfold pkv FCAP at *; omega
    have e3 : pkv ls (last.length + 1) / 131072 % 1099511627776 = ls := by unfold pkv FCAP at *; omega
    rw [e1, e2, e3]
    have hk' : (UInt8.ofNat k).toNat = k := by simp; omega
    rw [eq_body R ls (UInt8.ofNat k) last hb (by rw [hkb, hk']), ww_wrap, hk']

end Nano.IR
