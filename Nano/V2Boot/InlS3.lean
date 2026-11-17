/- B₁: the v2 inliner `inlV` (Nano/V2/Inl.lean) in S3 form (Nano/V2Boot/Prelude.lean) and the bridge
`inlVS_eq : inlVS xs = inlV xs` (inputs of length < 2^31, so the fuel `(len+1)^2` is a word). -/
import Nano.V2.Inl
import Nano.V2Boot.Prelude

namespace Nano.V2B
open Nano.V2

/-- `if rd xs p == 13 then c + 1 else c` -/
def inc13 (xs : List UInt8) (p c : UInt64) : UInt64 := if rdS xs p == 13 then c + 1 else c
/-- `if rd xs p == 13 then t - 1 else t` -/
def dec13 (xs : List UInt8) (p t : UInt64) : UInt64 := if rdS xs p == 13 then t - 1 else t
/-- `if rd xs q == 14 then rd xs (q + 1) else h` -/
def hi14 (xs : List UInt8) (q h : UInt64) : UInt64 := if rdS xs q == 14 then rdS xs (q + 1) else h

def cnt13S (f : UInt64) (xs : List UInt8) (p c : UInt64) : UInt64 :=
  if h : f = 0 then c
  else if p + 2 ≤ lenS xs then cnt13S (f - 1) xs (p + 2) (inc13 xs p c) else c
termination_by f.toNat
decreasing_by exact dec_lt h

def startOfS (f : UInt64) (xs : List UInt8) (p t : UInt64) : UInt64 :=
  if h : f = 0 then p
  else if t == 0 then p
  else if p + 2 ≤ lenS xs then startOfS (f - 1) xs (p + 2) (dec13 xs p t) else p
termination_by f.toNat
decreasing_by exact dec_lt h

def hiAtS (f : UInt64) (xs : List UInt8) (q p hh : UInt64) : UInt64 :=
  if h : f = 0 then hh
  else if q + 2 ≤ p then hiAtS (f - 1) xs (q + 2) p (hi14 xs q hh) else hh
termination_by f.toNat
decreasing_by exact dec_lt h

def inlBodyS (f : UInt64) (xs : List UInt8) (j p hi : UInt64) (o : List UInt8) : List UInt8 :=
  if h : f = 0 then o
  else if p + 2 ≤ lenS xs then
    if rdS xs p == 13 then o
    else if rdS xs p == 14 then inlBodyS (f - 1) xs j (p + 2) (rdS xs (p + 1)) o
    else if rdS xs p == 15 then
      if hi * 256 + rdS xs (p + 1) < j then
        inlBodyS (f - 1) xs j (p + 2) hi (inlBodyS (f - 1) xs (hi * 256 + rdS xs (p + 1))
          (startOfS (lenS xs + 1) xs 0 (hi * 256 + rdS xs (p + 1)))
          (hiAtS (lenS xs + 1) xs 0 (startOfS (lenS xs + 1) xs 0 (hi * 256 + rdS xs (p + 1))) 0) o)
      else inlBodyS (f - 1) xs j (p + 2) hi o
    else inlBodyS (f - 1) xs j (p + 2) hi (putR (putR o (rdS xs p)) (rdS xs (p + 1)))
  else o
termination_by f.toNat
decreasing_by all_goals exact dec_lt h

def put2R (o : List UInt8) (m x : UInt64) : List UInt8 := putR (putR o m) x

def putArgR (o : List UInt8) : List UInt8 :=
  put2R (put2R (put2R (put2R (put2R (put2R (put2R (put2R (put2R (put2R o 1 0) 2 6) 2 5) 2 4) 2 3) 2 2) 2 1) 2 0) 3 0) 4 0

def putWrR (o : List UInt8) : List UInt8 :=
  put2R (put2R (put2R (put2R (put2R (put2R (put2R (put2R (put2R (put2R (put2R (put2R (put2R (put2R (put2R (put2R o
    10 0) 11 0) 10 8) 11 1) 10 16) 11 2) 10 24) 11 3) 10 32) 11 4) 10 40) 11 5) 10 48) 11 6) 10 56) 11 7

def putProS (f k : UInt64) (o : List UInt8) : List UInt8 :=
  if h : f = 0 then o else if k == 0 then o else putProS (f - 1) (k - 1) (putArgR o)
termination_by f.toNat
decreasing_by exact dec_lt h

def inlVS (xs : List UInt8) : List UInt8 :=
  let n := lenS xs + 1
  let J := cnt13S n xs 0 0
  let s := startOfS n xs 0 (J - 1)
  let e := startOfS n xs 0 J
  let k := if J == 0 then 0 else rdS xs (e - 1)
  let o := putProS 256 k (put2R [] 0 0)
  let o := if J == 0 then o else inlBodyS (n * n) xs (J - 1) s (hiAtS n xs 0 s 0) o
  (put2R (putWrR (put2R o 7 0)) 12 0).reverse

/-! ## bridge -/

theorem cnt13S_eq (xs : List UInt8) : ∀ (n : Nat) (p c : UInt64), n < 2 ^ 64 →
    cnt13S n.toUInt64 xs p c = cnt13 n xs p c
  | 0, _, _, _ => by rw [cnt13S, dif_pos fuel_zero, cnt13]
  | n + 1, p, c, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    rw [cnt13S, dif_neg h1, cnt13, lenS_eq]
    simp only [inc13, rdS_eq, h2]
    split
    · exact cnt13S_eq xs n _ _ (by omega)
    · rfl

theorem startOfS_eq (xs : List UInt8) : ∀ (n : Nat) (p t : UInt64), n < 2 ^ 64 →
    startOfS n.toUInt64 xs p t = startOf n xs p t
  | 0, _, _, _ => by rw [startOfS, dif_pos fuel_zero, startOf]
  | n + 1, p, t, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    rw [startOfS, dif_neg h1, startOf, lenS_eq]
    simp only [dec13, rdS_eq, h2]
    split
    · rfl
    · split
      · exact startOfS_eq xs n _ _ (by omega)
      · rfl

theorem hiAtS_eq (xs : List UInt8) : ∀ (n : Nat) (q p hh : UInt64), n < 2 ^ 64 →
    hiAtS n.toUInt64 xs q p hh = hiAt n xs q p hh
  | 0, _, _, _, _ => by rw [hiAtS, dif_pos fuel_zero, hiAt]
  | n + 1, q, p, hh, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    rw [hiAtS, dif_neg h1, hiAt]
    simp only [hi14, rdS_eq, h2]
    split
    · exact hiAtS_eq xs n _ _ _ (by omega)
    · rfl

theorem lenS1 (xs : List UInt8) (hx : xs.length < 2 ^ 32) : lenS xs + 1 = (xs.length + 1).toUInt64 := by
  rw [lenS_eq]; unfold len; apply UInt64.toNat_inj.mp; simp

theorem inlBodyS_eq (xs : List UInt8) (hx : xs.length < 2 ^ 32) : ∀ (n : Nat) (j p hi : UInt64) (o : List UInt8),
    n < 2 ^ 64 → inlBodyS n.toUInt64 xs j p hi o.reverse = (inlBody n xs j p hi o).reverse
  | 0, _, _, _, _, _ => by rw [inlBodyS, dif_pos fuel_zero, inlBody]
  | n + 1, j, p, hi, o, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    have ih := inlBodyS_eq xs hx n
    rw [inlBodyS, dif_neg h1, inlBody]
    simp only [lenS1 xs hx, startOfS_eq xs _ _ _ (show xs.length + 1 < 2 ^ 64 by omega),
      hiAtS_eq xs _ _ _ _ (show xs.length + 1 < 2 ^ 64 by omega)]
    rw [lenS_eq]; simp only [rdS_eq, h2]
    split
    · split
      · rfl
      · split
        · exact ih _ _ _ _ (by omega)
        · split
          · split
            · rw [ih _ _ _ _ (by omega), ih _ _ _ _ (by omega)]
            · exact ih _ _ _ _ (by omega)
          · rw [putR_rev, putR_rev]; exact ih _ _ _ _ (by omega)
    · rfl

theorem put2R_rev (o : List UInt8) (m x : UInt64) : put2R o.reverse m x = (put2 o m x).reverse := by
  simp only [put2R, put2, putR_rev]

theorem putArgR_rev (o : List UInt8) : putArgR o.reverse = (putArg o).reverse := by
  simp only [putArgR, putArg, put2R_rev]

theorem putWrR_rev (o : List UInt8) : putWrR o.reverse = (putWr o).reverse := by
  simp only [putWrR, putWr, put2R_rev]

theorem putProS_eq : ∀ (n : Nat) (k : UInt64) (o : List UInt8), n < 2 ^ 64 →
    putProS n.toUInt64 k o.reverse = (putPro n k o).reverse
  | 0, _, _, _ => by rw [putProS, dif_pos fuel_zero, putPro]
  | n + 1, k, o, h => by
    obtain ⟨h1, h2⟩ := fuel_succ n h
    rw [putProS, dif_neg h1, putPro]
    simp only [h2, putArgR_rev]
    split
    · rfl
    · exact putProS_eq n _ _ (by omega)

/-- **the bridge**: the S3 form is the v2 inliner on every input of length < 2^32 -/
theorem inlVS_eq (xs : List UInt8) (hx : xs.length < 2 ^ 31) : inlVS xs = inlV xs := by
  have hx' : xs.length < 2 ^ 32 := by omega
  have hn : xs.length + 1 < 2 ^ 64 := by omega
  have hnn : (xs.length + 1) * (xs.length + 1) < 2 ^ 64 := by
    have : xs.length + 1 ≤ 2 ^ 31 := by omega
    calc (xs.length + 1) * (xs.length + 1) ≤ 2 ^ 31 * 2 ^ 31 := Nat.mul_le_mul this this
      _ < 2 ^ 64 := by decide
  have hm : (xs.length + 1).toUInt64 * (xs.length + 1).toUInt64 = ((xs.length + 1) * (xs.length + 1)).toUInt64 := by
    apply UInt64.toNat_inj.mp; simp
  unfold inlVS inlV
  simp only [lenS1 xs hx', hm, cnt13S_eq xs _ _ _ hn, startOfS_eq xs _ _ _ hn, hiAtS_eq xs _ _ _ _ hn, rdS_eq]
  have e0 : put2R [] 0 0 = (put2 [] 0 0).reverse := put2R_rev [] 0 0
  rw [e0, show (256 : UInt64) = (256 : Nat).toUInt64 from rfl, putProS_eq 256 _ _ (by decide)]
  split
  · rw [put2R_rev, putWrR_rev, put2R_rev, List.reverse_reverse]
  · rw [inlBodyS_eq xs hx' _ _ _ _ _ hnn, put2R_rev, putWrR_rev, put2R_rev, List.reverse_reverse]

end Nano.V2B
