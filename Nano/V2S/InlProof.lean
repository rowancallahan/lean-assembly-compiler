/- Bridge of the nano v2 inliner (Nano/V2/Inl.lean): `inlV_eq : inlV xs = inlB xs` for every input of length
< 2^32. -/
import Nano.V2.Inl

namespace Nano.V2.InlP
open Nano Nano.U Nano.V2

/-! ## list-level meaning of the scanning loops -/

/-- the number of `13` records -/
def c13 : List UInt8 → Nat
  | m :: _ :: r => (if m = 13 then 1 else 0) + c13 r
  | _ => 0

/-- the offset after the `t`-th `13` record -/
def so : List UInt8 → Nat → Nat
  | _, 0 => 0
  | m :: _ :: r, t + 1 => 2 + (if m = 13 then so r t else so r (t + 1))
  | _, _ + 1 => 0

/-- the high-byte register after `k` records -/
def hiS : List UInt8 → Nat → Nat → Nat
  | m :: x :: r, k + 1, h => hiS r k (if m = 14 then x.toNat else h)
  | _, _, h => h

/-- the code of one def from here to its `13` record, appended to `cur` (the inliner's `cur` at that record) -/
def segG : List UInt8 → List (List UInt8) → Nat → List UInt8 → List UInt8
  | m :: x :: r, tab, hi, cur =>
    if m = 13 then cur
    else if m = 14 then segG r tab x.toNat cur
    else if m = 15 then segG r tab hi (cur ++ tab.getD (hi * 256 + x.toNat) [])
    else segG r tab hi (cur ++ [m, x])
  | _, _, _, cur => cur

theorem drop2 (xs : List UInt8) (p : Nat) (h : p + 2 ≤ xs.length) :
    xs.drop p = xs[p] :: xs[p + 1] :: xs.drop (p + 2) := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]; rfl

theorem rdN (xs : List UInt8) (p : Nat) (h : p < xs.length) (hx : xs.length < 2 ^ 32) :
    rd xs p.toUInt64 = xs[p].toUInt64 := by
  unfold rd
  rw [show p.toUInt64.toNat = p by simp; omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem lenLe (xs : List UInt8) (p : Nat) (hx : xs.length < 2 ^ 32) (hp : p ≤ xs.length) :
    (p.toUInt64 + 2 ≤ len xs) ↔ p + 2 ≤ xs.length := by
  unfold len; rw [UInt64.le_iff_toNat_le]; simp; omega

theorem toU_add (p k : Nat) : p.toUInt64 + k.toUInt64 = (p + k).toUInt64 := by simp

theorem beqU (a : UInt8) (k : Nat) (hk : k < 256) : (a.toUInt64 == k.toUInt64) = decide (a.toNat = k) := by
  by_cases h : a.toNat = k
  · have : a.toUInt64 = k.toUInt64 := by apply UInt64.toNat_inj.mp; simp; omega
    simp [this, h]
  · have : a.toUInt64 ≠ k.toUInt64 := fun e => h (by
      have := congrArg UInt64.toNat e; simp at this; omega)
    simp [this, h]

theorem cnt13_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n p c : Nat), p ≤ xs.length →
    xs.length < p + 2 * n → c + (xs.length - p) < 2 ^ 32 →
    cnt13 n xs p.toUInt64 c.toUInt64 = (c + c13 (xs.drop p)).toUInt64
  | 0, p, c, _, h2, _ => by omega
  | n + 1, p, c, h1, h2, h3 => by
    rw [cnt13]
    by_cases hc : p + 2 ≤ xs.length
    · rw [if_pos ((lenLe xs p hx h1).mpr hc), rdN xs p (by omega) hx, drop2 xs p hc, c13]
      have e13 : (13 : UInt64) = (13 : Nat).toUInt64 := rfl
      rw [e13, beqU _ 13 (by decide)]
      have c13le : ∀ l : List UInt8, c13 l ≤ l.length := by
        intro l; induction l using c13.induct <;> simp [c13] <;> split <;> omega
      have := c13le (xs.drop (p + 2)); simp at this
      by_cases hm : xs[p].toNat = 13
      · have hm' : xs[p] = 13 := UInt8.toNat_inj.mp (by simpa using hm)
        rw [if_pos (by simp [hm]), if_pos hm', show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, toU_add,
          show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, toU_add, cnt13_eq xs hx n (p + 2) (c + 1) (by omega)
          (by omega) (by omega)]
        congr 1; omega
      · have hm' : ¬ xs[p] = 13 := fun e => hm (by rw [e]; rfl)
        rw [if_neg (by simp [hm]), if_neg hm', show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, toU_add, cnt13_eq xs hx n (p + 2) c (by omega)
          (by omega) (by omega)]
        congr 1; simp
    · rw [if_neg (fun q => hc ((lenLe xs p hx h1).mp q))]
      rw [show xs.drop p = (xs.drop p) from rfl]
      have : (xs.drop p).length < 2 := by simp; omega
      match hl : xs.drop p, this with
      | [], _ => simp [c13]
      | [_], _ => simp [c13]


/-! ## list lemmas -/

theorem segG_lin : ∀ (l : List UInt8) (tab : List (List UInt8)) (hi : Nat) (cur : List UInt8),
    segG l tab hi cur = cur ++ segG l tab hi []
  | m :: x :: r, tab, hi, cur => by
    unfold segG
    split
    · simp
    · split
      · exact segG_lin r tab _ cur
      · split
        · rw [segG_lin r tab hi, segG_lin r tab hi (_ ++ _)]; simp
        · rw [segG_lin r tab hi, segG_lin r tab hi (_ ++ _)]; simp
  | [], _, _, _ => by simp [segG]
  | [_], _, _, _ => by simp [segG]

theorem inlGo_end : ∀ (l : List UInt8) (tab : List (List UInt8)) (cur : List UInt8) (hi k : Nat) (last : List UInt8),
    c13 l = 0 → inlGo l tab cur hi k last = wrap k last
  | m :: x :: r, tab, cur, hi, k, last, h => by
    unfold c13 at h
    have hm : ¬ m = 13 := fun e => by simp [e] at h
    have hr : c13 r = 0 := by omega
    rw [inlGo, if_neg hm]
    split
    · exact inlGo_end r _ _ _ _ _ hr
    · split <;> exact inlGo_end r _ _ _ _ _ hr
  | [], _, _, _, _, _, _ => by simp [inlGo]
  | [_], _, _, _, _, _, _ => by simp [inlGo]

theorem so_pos : ∀ (l : List UInt8), 0 < c13 l → 2 ≤ so l 1
  | m :: x :: r, h => by unfold so; omega
  | [], h => by simp [c13] at h
  | [_], h => by simp [c13] at h

theorem inlGo_seg : ∀ (l : List UInt8) (tab : List (List UInt8)) (cur : List UInt8) (hi k : Nat) (last : List UInt8),
    0 < c13 l → inlGo l tab cur hi k last =
      inlGo (l.drop (so l 1)) (tab ++ [segG l tab hi cur]) [] (hiS l (so l 1 / 2) hi) (l.getD (so l 1 - 1) 0).toNat
        (segG l tab hi cur)
  | m :: x :: r, tab, cur, hi, k, last, h => by
    by_cases hm : m = 13
    · subst hm; simp [inlGo, so, segG, hiS]
    · unfold c13 at h
      have hr : 0 < c13 r := by simp [hm] at h; omega
      have h2 := so_pos r hr
      have e1 : so (m :: x :: r) 1 = 2 + so r 1 := by simp [so, hm]
      have e2 : (m :: x :: r).drop (2 + so r 1) = r.drop (so r 1) := by
        rw [← List.drop_drop]; rfl
      have e3 : (2 + so r 1) / 2 = so r 1 / 2 + 1 := by omega
      have e4 : (m :: x :: r).getD (2 + so r 1 - 1) 0 = r.getD (so r 1 - 1) 0 := by
        rw [show 2 + so r 1 - 1 = (so r 1 - 1) + 1 + 1 by omega]; rfl
      rw [e1, e2, e3, e4, inlGo, if_neg hm]
      simp only [segG, hiS, if_neg hm]
      split
      · exact inlGo_seg r _ _ _ _ _ hr
      · split <;> exact inlGo_seg r _ _ _ _ _ hr
  | [], _, _, _, _, _, h => by simp [c13] at h
  | [_], _, _, _, _, _, h => by simp [c13] at h

theorem dropcc (m x : UInt8) (r : List UInt8) (k : Nat) : (m :: x :: r).drop (k + 2) = r.drop k := rfl

theorem so_le : ∀ (l : List UInt8) (t : Nat), so l t ≤ l.length
  | _, 0 => by simp [so]
  | m :: x :: r, t + 1 => by
    have := so_le r t; have := so_le r (t + 1)
    simp only [so, List.length_cons]; split <;> omega
  | [], _ + 1 => by simp [so]
  | [_], _ + 1 => by simp [so]

theorem so_even : ∀ (l : List UInt8) (t : Nat), so l t % 2 = 0
  | _, 0 => by simp [so]
  | m :: x :: r, t + 1 => by
    have := so_even r t; have := so_even r (t + 1)
    simp only [so]; split <;> omega
  | [], _ + 1 => by simp [so]
  | [_], _ + 1 => by simp [so]

theorem so_succ : ∀ (l : List UInt8) (t : Nat), t < c13 l → so l (t + 1) = so l t + so (l.drop (so l t)) 1
  | m :: x :: r, 0, _ => by simp [so]
  | m :: x :: r, t + 1, h => by
    unfold c13 at h
    by_cases hm : m = 13
    · simp only [so, hm, if_true] at *
      rw [so_succ r t (by omega)]
      rw [show 2 + so r t = so r t + 2 by omega, dropcc]; omega
    · simp only [so, hm, if_false] at *
      rw [so_succ r (t + 1) (by omega)]
      rw [show 2 + so r (t + 1) = so r (t + 1) + 2 by omega, dropcc]; omega
  | [], _, h => by simp [c13] at h
  | [_], _, h => by simp [c13] at h

theorem c13_so : ∀ (l : List UInt8) (t : Nat), t ≤ c13 l → c13 (l.drop (so l t)) = c13 l - t
  | _, 0, _ => by simp [so]
  | m :: x :: r, t + 1, h => by
    unfold c13 at h
    by_cases hm : m = 13
    · simp only [so, hm, if_true] at h ⊢
      rw [show 2 + so r t = so r t + 2 by omega, dropcc]
      rw [c13_so r t (by omega)]; simp [c13]; omega
    · simp only [so, hm, if_false] at h ⊢
      rw [show 2 + so r (t + 1) = so r (t + 1) + 2 by omega, dropcc]
      rw [c13_so r (t + 1) (by omega)]; simp only [c13]; rw [if_neg hm]; omega
  | [], _ + 1, h => by simp [c13] at h
  | [_], _ + 1, h => by simp [c13] at h

theorem hiS_add : ∀ (l : List UInt8) (a b h : Nat), 2 * a ≤ l.length →
    hiS l (a + b) h = hiS (l.drop (2 * a)) b (hiS l a h)
  | _, 0, b, h, _ => by
    cases b <;> simp [hiS] <;> rfl
  | m :: x :: r, a + 1, b, h, hl => by
    rw [show a + 1 + b = (a + b) + 1 by omega, hiS, hiS, hiS_add r a b _ (by simp at hl; omega)]
    rw [show 2 * (a + 1) = 2 * a + 2 by omega, dropcc]
  | [], _ + 1, _, _, hl => by simp at hl
  | [_], _ + 1, _, _, hl => by simp at hl; omega

theorem hiS_lt : ∀ (l : List UInt8) (k h : Nat), h < 256 → hiS l k h < 256
  | m :: x :: r, k + 1, h, hh => by
    rw [hiS]; apply hiS_lt; split
    · exact x.toNat_lt
    · exact hh
  | [], k, _, hh => by cases k <;> simp [hiS, hh]
  | [_], k, _, hh => by cases k <;> simp [hiS, hh]
  | _ :: _ :: _, 0, _, hh => by simp [hiS, hh]

/-! ## the scanning loops -/

theorem startOf_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n p t : Nat), p ≤ xs.length →
    xs.length < p + 2 * n → t < 2 ^ 32 →
    startOf n xs p.toUInt64 t.toUInt64 = (p + so (xs.drop p) t).toUInt64
  | 0, p, t, h1, h2, _ => by omega
  | n + 1, p, 0, h1, h2, _ => by simp [startOf, so]
  | n + 1, p, t + 1, h1, h2, ht => by
    rw [startOf]
    have hne : ¬ ((t + 1).toUInt64 == 0) = true := by
      simp only [beq_iff_eq]; intro e
      have := congrArg UInt64.toNat e; simp at this; omega
    rw [if_neg hne]
    by_cases hc : p + 2 ≤ xs.length
    · rw [if_pos ((lenLe xs p hx h1).mpr hc), rdN xs p (by omega) hx, drop2 xs p hc]
      have e13 : (13 : UInt64) = (13 : Nat).toUInt64 := rfl
      rw [e13, beqU _ 13 (by decide), show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, toU_add]
      by_cases hm : xs[p].toNat = 13
      · have hm' : xs[p] = 13 := UInt8.toNat_inj.mp (by simpa using hm)
        rw [if_pos (by simp [hm]), show (t + 1).toUInt64 - 1 = t.toUInt64 by simp,
          startOf_eq xs hx n (p + 2) t (by omega) (by omega) (by omega)]
        simp only [so, hm', if_true]; congr 1; omega
      · have hm' : ¬ xs[p] = 13 := fun e => hm (by rw [e]; rfl)
        rw [if_neg (by simp [hm]), startOf_eq xs hx n (p + 2) (t + 1) (by omega) (by omega) (by omega)]
        simp only [so, hm', if_false]; congr 1; omega
    · rw [if_neg (fun q => hc ((lenLe xs p hx h1).mp q))]
      have : (xs.drop p).length < 2 := by simp; omega
      match hl : xs.drop p, this with
      | [], _ => simp [so]
      | [_], _ => simp [so]

theorem hiAt_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n q k h : Nat), q + 2 * k ≤ xs.length →
    k < n → h < 256 →
    hiAt n xs q.toUInt64 (q + 2 * k).toUInt64 h.toUInt64 = (hiS (xs.drop q) k h).toUInt64
  | 0, _, _, _, _, h2, _ => by omega
  | n + 1, q, 0, h, h1, h2, h3 => by
    rw [hiAt, if_neg]
    · cases xs.drop q with
      | nil => simp [hiS]
      | cons a r => cases r <;> simp [hiS]
    · rw [UInt64.le_iff_toNat_le]; simp; omega
  | n + 1, q, k + 1, h, h1, h2, h3 => by
    rw [hiAt, if_pos (by rw [UInt64.le_iff_toNat_le]; simp; omega), rdN xs q (by omega) hx,
      show q.toUInt64 + 1 = (q + 1).toUInt64 by simp, rdN xs (q + 1) (by omega) hx,
      drop2 xs q (by omega), hiS]
    have e14 : (14 : UInt64) = (14 : Nat).toUInt64 := rfl
    rw [e14, beqU _ 14 (by decide), show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, toU_add,
      show q + 2 * (k + 1) = (q + 2) + 2 * k by omega]
    by_cases hm : xs[q].toNat = 14
    · have hm' : xs[q] = 14 := UInt8.toNat_inj.mp (by simpa using hm)
      rw [if_pos (by simp [hm]), if_pos hm', show xs[q + 1].toUInt64 = xs[q + 1].toNat.toUInt64 by simp,
        hiAt_eq xs hx n (q + 2) k _ (by omega) (by omega) xs[q + 1].toNat_lt]; rfl
    · have hm' : ¬ xs[q] = 14 := fun e => hm (by rw [e]; rfl)
      rw [if_neg (by simp [hm]), if_neg hm', hiAt_eq xs hx n (q + 2) k _ (by omega) (by omega) h3]

/-! ## the inlined body -/

/-- the table entries are what `inlBody` computes for their defs -/
def BP (xs : List UInt8) (tab : List (List UInt8)) : Prop :=
  ∀ u (hu : u < tab.length) (f : Nat), (u + 1) * (xs.length + 1) ≤ f → ∀ o,
    inlBody f xs u.toUInt64 (so xs u).toUInt64 (hiS xs (so xs u / 2) 0).toUInt64 o = o ++ tab[u]

theorem startOf0 (xs : List UInt8) (hx : xs.length < 2 ^ 32) (u : Nat) (hu : u < 2 ^ 32) :
    startOf (xs.length + 1) xs 0 u.toUInt64 = (so xs u).toUInt64 := by
  have := startOf_eq xs hx (xs.length + 1) 0 u (by omega) (by omega) hu
  simpa using this

theorem hiAt0 (xs : List UInt8) (hx : xs.length < 2 ^ 32) (u : Nat) :
    hiAt (xs.length + 1) xs 0 (so xs u).toUInt64 0 = (hiS xs (so xs u / 2) 0).toUInt64 := by
  have he := so_even xs u; have hl := so_le xs u
  have := hiAt_eq xs hx (xs.length + 1) 0 (so xs u / 2) 0 (by omega) (by omega) (by decide)
  rw [show 0 + 2 * (so xs u / 2) = so xs u by omega] at this
  simpa using this

theorem split2 (xs : List UInt8) (hx : xs.length < 2 ^ 32) (p : Nat) (hc : p + 2 ≤ xs.length) :
    ∃ a b r, xs.drop p = a :: b :: r ∧ rd xs p.toUInt64 = a.toUInt64 ∧ rd xs (p.toUInt64 + 1) = b.toUInt64 ∧
      xs.drop (p + 2) = r :=
  ⟨xs[p], xs[p + 1], xs.drop (p + 2), drop2 xs p hc, rdN xs p (by omega) hx,
    by rw [show p.toUInt64 + 1 = (p + 1).toUInt64 by simp, rdN xs (p + 1) (by omega) hx]; rfl, rfl⟩

theorem toN (a : UInt8) : a.toUInt64 = a.toNat.toUInt64 := by simp

theorem inlBody_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) (tab : List (List UInt8)) (hb : BP xs tab)
    (htab : tab.length < 2 ^ 32) :
    ∀ (f p hi : Nat) (o : List UInt8), tab.length * (xs.length + 1) + (xs.length - p) / 2 + 1 ≤ f →
    p ≤ xs.length → hi < 256 →
    inlBody f xs tab.length.toUInt64 p.toUInt64 hi.toUInt64 o = segG (xs.drop p) tab hi o
  | 0, _, _, _, hf, _, _ => by omega
  | f + 1, p, hi, o, hf, hp, hh => by
    rw [inlBody]
    by_cases hc : p + 2 ≤ xs.length
    · obtain ⟨a, b, r, hd, ha, hb', hr⟩ := split2 xs hx p hc
      rw [if_pos ((lenLe xs p hx hp).mpr hc), ha, hb', hd, segG]
      simp only []
      have e13 : (13 : UInt64) = (13 : Nat).toUInt64 := rfl
      have e14 : (14 : UInt64) = (14 : Nat).toUInt64 := rfl
      have e15 : (15 : UInt64) = (15 : Nat).toUInt64 := rfl
      rw [e13, e14, e15, beqU _ 13 (by decide), beqU _ 14 (by decide), beqU _ 15 (by decide),
        show (2 : UInt64) = (2 : Nat).toUInt64 from rfl, toU_add]
      have hpx := b.toNat_lt
      have IH := fun hi' o' (hh' : hi' < 256) =>
        inlBody_eq xs hx tab hb htab f (p + 2) hi' o' (by omega) (by omega) hh'
      rw [hr] at IH
      by_cases h13 : a.toNat = 13
      · rw [if_pos (show decide (a.toNat = 13) = true by simp [h13]),
          if_pos (show a = 13 from UInt8.toNat_inj.mp (by simpa using h13))]
      · rw [if_neg (show ¬ decide (a.toNat = 13) = true by simp [h13]),
          if_neg (show ¬ a = 13 from fun e => h13 (by rw [e]; rfl))]
        by_cases h14 : a.toNat = 14
        · rw [if_pos (show decide (a.toNat = 14) = true by simp [h14]),
            if_pos (show a = 14 from UInt8.toNat_inj.mp (by simpa using h14)), toN b, IH _ _ hpx]
        · rw [if_neg (show ¬ decide (a.toNat = 14) = true by simp [h14]),
            if_neg (show ¬ a = 14 from fun e => h14 (by rw [e]; rfl))]
          by_cases h15 : a.toNat = 15
          · rw [if_pos (show decide (a.toNat = 15) = true by simp [h15]),
              if_pos (show a = 15 from UInt8.toNat_inj.mp (by simpa using h15))]
            have et : hi.toUInt64 * 256 + b.toUInt64 = (hi * 256 + b.toNat).toUInt64 := by
              apply UInt64.toNat_inj.mp; simp
            rw [et]
            by_cases hu : hi * 256 + b.toNat < tab.length
            · rw [if_pos (by rw [UInt64.lt_iff_toNat_lt]; simp; omega), startOf0 xs hx _ (by omega),
                hiAt0 xs hx, hb _ hu f (by
                  have : (hi * 256 + b.toNat + 1) * (xs.length + 1) ≤ tab.length * (xs.length + 1) :=
                    Nat.mul_le_mul_right _ hu
                  omega),
                IH _ _ hh]
              simp [hu]
            · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt]; simp; omega), IH _ _ hh,
                List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
              simp
          · rw [if_neg (show ¬ decide (a.toNat = 15) = true by simp [h15]),
              if_neg (show ¬ a = 15 from fun e => h15 (by rw [e]; rfl)), IH _ _ hh]
            simp [put]
    · rw [if_neg (fun q => hc ((lenLe xs p hx hp).mp q))]
      have : (xs.drop p).length < 2 := by simp; omega
      match hl : xs.drop p, this with
      | [], _ => simp [segG]
      | [_], _ => simp [segG]

/-! ## the whole input -/

theorem c13_le : ∀ l : List UInt8, 2 * c13 l ≤ l.length
  | m :: x :: r => by have := c13_le r; simp only [c13, List.length_cons]; split <;> omega
  | [] => by simp [c13]
  | [_] => by simp [c13]

theorem hiS0 (l : List UInt8) (h : Nat) : hiS l 0 h = h := by
  match l with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem getD_drop (l : List UInt8) (p i : Nat) : (l.drop p).getD i 0 = l.getD (p + i) 0 := by
  simp [List.getD_eq_getElem?_getD]

/-- the inliner's state at the start of def `t` -/
theorem inl_main (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ t, t ≤ c13 xs →
    ∃ tab k last, tab.length = t ∧ BP xs tab ∧
      inlB xs = inlGo (xs.drop (so xs t)) tab [] (hiS xs (so xs t / 2) 0) k last ∧
      (t = 0 → k = 0 ∧ last = []) ∧ (0 < t → last = tab.getD (t - 1) [] ∧ k = (xs.getD (so xs t - 1) 0).toNat)
  | 0, _ => ⟨[], 0, [], rfl, fun u hu => absurd hu (by simp), by simp [so, hiS0, inlB], fun _ => ⟨rfl, rfl⟩,
      fun h => absurd h (by omega)⟩
  | t + 1, ht => by
    obtain ⟨tab, k, last, hl, hb, he, -, -⟩ := inl_main xs hx t (by omega)
    subst hl
    have hc := c13_so xs tab.length (by omega)
    have hs := so_succ xs tab.length (by omega)
    have hev := so_even xs tab.length
    have hle := so_le xs tab.length
    have hc2 := c13_le xs
    have hpos := so_pos (xs.drop (so xs tab.length)) (by omega)
    have hev1 := so_even (xs.drop (so xs tab.length)) 1
    have hle1 := so_le (xs.drop (so xs tab.length)) 1
    simp only [List.length_drop] at hle1
    rw [inlGo_seg _ _ _ _ _ _ (by omega)] at he
    refine ⟨tab ++ [segG (xs.drop (so xs tab.length)) tab (hiS xs (so xs tab.length / 2) 0) []], (xs.getD (so xs (tab.length + 1) - 1) 0).toNat,
      segG (xs.drop (so xs tab.length)) tab (hiS xs (so xs tab.length / 2) 0) [], by simp, ?_, ?_,
      fun h => absurd h (by omega), fun _ => ⟨?_, rfl⟩⟩
    · intro u hu f hf o
      by_cases hut : u < tab.length
      · rw [List.getElem_append_left (by omega)]; exact hb u (by omega) f hf o
      · have hut : u = tab.length := by simp at hu; omega
        subst hut
        rw [List.getElem_append_right (by omega)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
        rw [inlBody_eq xs hx tab hb (by omega) f (so xs tab.length) _ o (by
          have : (tab.length + 1) * (xs.length + 1) = tab.length * (xs.length + 1) + (xs.length + 1) :=
            Nat.succ_mul _ _
          omega) hle (hiS_lt _ _ _ (by decide)), segG_lin]
    · rw [he, List.drop_drop, hs, getD_drop,
        show (so xs tab.length + so (List.drop (so xs tab.length) xs) 1) / 2 =
          so xs tab.length / 2 + so (List.drop (so xs tab.length) xs) 1 / 2 by omega,
        hiS_add xs _ _ _ (by omega), show 2 * (so xs tab.length / 2) = so xs tab.length by omega,
        show so xs tab.length + (so (List.drop (so xs tab.length) xs) 1 - 1) =
          so xs tab.length + so (List.drop (so xs tab.length) xs) 1 - 1 by omega]
    · simp

theorem putArg_eq (o : List UInt8) : putArg o = o ++ sArg := by simp [putArg, put2, put, sArg, mo]
theorem putWr_eq (o : List UInt8) : putWr o = o ++ sWr := by simp [putWr, put2, put, sWr, mo]

theorem putPro_eq : ∀ (f k : Nat) (o : List UInt8), k ≤ f → k < 2 ^ 32 → putPro f k.toUInt64 o = o ++ serPro k
  | 0, k, o, h, _ => by
    rw [show k = 0 by omega]; simp [putPro, serPro]
  | f + 1, 0, o, _, _ => by simp [putPro, serPro]
  | f + 1, k + 1, o, h, h2 => by
    have hk : ¬ ((k + 1).toUInt64 == 0) = true := by
      simp only [beq_iff_eq]; intro e; have := congrArg UInt64.toNat e; simp at this
      rw [Nat.mod_eq_of_lt (by omega)] at this; omega
    rw [putPro, if_neg hk,
      show (k + 1).toUInt64 - 1 = k.toUInt64 by simp, putPro_eq f k _ (by omega) (by omega), putArg_eq, serPro]
    simp

theorem subOne (n : Nat) (h1 : 1 ≤ n) : n.toUInt64 - 1 = (n - 1).toUInt64 := by
  have e : n.toUInt64 = (n - 1).toUInt64 + 1 := by
    rw [show (1 : UInt64) = (1 : Nat).toUInt64 from rfl, toU_add, Nat.sub_add_cancel h1]
  rw [e, UInt64.add_sub_cancel]

/-- **the bridge**: the nano v2 inliner is the inliner, on every input of length < 2^32 -/
theorem inlV_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : inlV xs = inlB xs := by
  have hc2 := c13_le xs
  obtain ⟨tab, k, last, hl, hb, he, h0, h1⟩ := inl_main xs hx (c13 xs) (by omega)
  have hJ : cnt13 (xs.length + 1) xs 0 0 = (c13 xs).toUInt64 := by
    have := cnt13_eq xs hx (xs.length + 1) 0 0 (by omega) (by omega) (by omega)
    simpa using this
  rw [he, inlGo_end _ _ _ _ _ _ (by rw [c13_so xs _ (by omega)]; omega)]
  unfold inlV wrap
  simp only [hJ]
  by_cases hz : c13 xs = 0
  · obtain ⟨rfl, rfl⟩ := h0 hz
    rw [hz]
    simp [putPro, put2, put, putWr_eq, serPro, mo]
  · obtain ⟨rfl, rfl⟩ := h1 (by omega)
    have hne : ¬ ((c13 xs).toUInt64 == 0) = true := by
      simp only [beq_iff_eq]; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have hm1 : (c13 xs).toUInt64 - 1 = (c13 xs - 1).toUInt64 := subOne _ (by omega)
    have hs := so_succ xs (c13 xs - 1) (by omega)
    rw [show c13 xs - 1 + 1 = c13 xs by omega] at hs
    have hpos := so_pos (xs.drop (so xs (c13 xs - 1))) (by rw [c13_so xs _ (by omega)]; omega)
    have hle := so_le xs (c13 xs)
    have hk : (so xs (c13 xs)).toUInt64 - 1 = (so xs (c13 xs) - 1).toUInt64 := subOne _ (by omega)
    have hrd : rd xs ((so xs (c13 xs) - 1).toUInt64) = (xs.getD (so xs (c13 xs) - 1) 0).toNat.toUInt64 := by
      rw [rdN xs _ (by omega) hx]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show so xs (c13 xs) - 1 < xs.length by omega)]
    have hb' := hb (c13 xs - 1) (by omega) ((xs.length + 1) * (xs.length + 1)) (Nat.mul_le_mul_right _ (by omega))
    rw [if_neg hne, if_neg hne, hm1, startOf0 xs hx _ (by omega), startOf0 xs hx _ (by omega), hiAt0 xs hx, hk, hrd,
      putPro_eq 256 _ _ (by have := (xs.getD (so xs (c13 xs) - 1) 0).toNat_lt; omega)
        (by have := (xs.getD (so xs (c13 xs) - 1) 0).toNat_lt; omega), hb']
    have hg : tab.getD (c13 xs - 1) [] = tab[c13 xs - 1]'(by omega) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show c13 xs - 1 < tab.length by omega)]
    rw [hg]
    simp [put2, put, putWr_eq, mo]

end Nano.V2.InlP
