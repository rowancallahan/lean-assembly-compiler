/- The inliner `Nano.U.inlB` in the form the S3 front end accepts, and the bridge `inlBS_eq : inlBS = inlB` (every
input). `Testing/notes/NANO_PARSE_S3.md`.

Differences from the verbatim source: the callee-number registers `hi`, `k` are words (`UInt64`) instead of `Nat`
(`x.toNat` ↦ `x.toUInt64`), the table lookup `tab.getD (hi * 256 + x.toNat) []` ↦ `getW` (word index),
`serPro k` ↦ `serProW` (well-founded on the word). `mo`, `sArg`, `sWr`, the list operations are the originals. -/
import Nano.SerU

namespace Nano.IS
open Nano Nano.U

/-- `tab.getD i.toNat []` with a word index -/
def getW : List (List UInt8) → UInt64 → List UInt8
  | [], _ => []
  | a :: r, i => if i == 0 then a else getW r (i - 1)

theorem getW_eq : ∀ (tab : List (List UInt8)) (i : UInt64), getW tab i = tab.getD i.toNat []
  | [], _ => by simp [getW]
  | a :: r, i => by
    unfold getW
    by_cases h : i = 0
    · subst h; simp
    · have hi : i.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
      rw [if_neg (by simpa using h), getW_eq r (i - 1)]
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
      obtain ⟨n, hn⟩ : ∃ n, i.toNat = n + 1 := ⟨i.toNat - 1, by omega⟩
      simp [hn]

/-- `serPro` on a word -/
def serProW (k : UInt64) : List UInt8 := if h : k = 0 then [] else sArg ++ serProW (k - 1)
termination_by k.toNat
decreasing_by
  have hk : k.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

theorem serProW_eq : ∀ (n : Nat) (k : UInt64), k.toNat = n → serProW k = serPro n
  | 0, k, h => by
    rw [serProW, dif_pos (UInt64.toNat_inj.mp (by simpa using h))]; rfl
  | n + 1, k, h => by
    have hk : k ≠ 0 := fun e => by subst e; simp at h
    rw [serProW, dif_neg hk, serPro, serProW_eq n (k - 1)]
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

/-- `wrap` -/
def wrapS (k : UInt64) (body : List UInt8) : List UInt8 := mo 0 0 ++ serProW k ++ body ++ mo 7 0 ++ sWr ++ mo 12 0

/-- `inlGo` with word registers -/
def inlGoS : List UInt8 → List (List UInt8) → List UInt8 → UInt64 → UInt64 → List UInt8 → List UInt8
  | m :: x :: rest, tab, cur, hi, k, last =>
    if m == 13 then inlGoS rest (tab ++ [cur]) [] hi x.toUInt64 cur
    else if m == 14 then inlGoS rest tab cur x.toUInt64 k last
    else if m == 15 then inlGoS rest tab (cur ++ getW tab (hi * 256 + x.toUInt64)) hi k last
    else inlGoS rest tab (cur ++ [m, x]) hi k last
  | _, _, _, _, k, last => wrapS k last

theorem u8_u64 (x : UInt8) : x.toNat.toUInt64 = x.toUInt64 := by
  apply UInt64.toNat_inj.mp; simp

theorem inlGoS_eq : ∀ (xs : List UInt8) (tab : List (List UInt8)) (cur : List UInt8) (hi k : Nat)
    (last : List UInt8), hi < 256 → k < 256 →
    inlGoS xs tab cur hi.toUInt64 k.toUInt64 last = inlGo xs tab cur hi k last
  | m :: x :: rest, tab, cur, hi, k, last, hhi, hk => by
    have hx := x.toNat_lt
    rw [inlGoS, inlGo]
    by_cases h13 : m = 13
    · simp only [h13, beq_self_eq_true, if_true]
      have := inlGoS_eq rest (tab ++ [cur]) [] hi x.toNat cur hhi hx
      rw [← this, u8_u64]
    · simp only [beq_iff_eq, h13, if_false]
      by_cases h14 : m = 14
      · simp only [h14, if_true]
        have := inlGoS_eq rest tab cur x.toNat k last hx hk
        rw [← this, u8_u64]
      · simp only [h14, if_false]
        by_cases h15 : m = 15
        · simp only [h15, if_true]
          rw [getW_eq, ← inlGoS_eq rest tab _ hi k last hhi hk]
          congr 3
          rw [UInt64.toNat_add, UInt64.toNat_mul]
          simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt8.toNat_toUInt64]
          have : hi % 2 ^ 64 = hi := Nat.mod_eq_of_lt (by omega)
          simp only [UInt64.reduceToNat, this]
          omega
        · simp only [h15, if_false]
          exact inlGoS_eq rest tab _ hi k last hhi hk
  | [], tab, cur, hi, k, last, _, hk => by
    simp only [inlGoS, inlGo, wrapS, wrap]
    rw [serProW_eq k _ (by simp; omega)]
  | [_], tab, cur, hi, k, last, _, hk => by
    simp only [inlGoS, inlGo, wrapS, wrap]
    rw [serProW_eq k _ (by simp; omega)]

/-- **the inliner, S3 form** -/
def inlBS (xs : List UInt8) : List UInt8 := inlGoS xs [] [] 0 0 []

/-- **the bridge**: the S3 form is the inliner, on every input -/
theorem inlBS_eq (xs : List UInt8) : inlBS xs = inlB xs :=
  inlGoS_eq xs [] [] 0 0 [] (by decide) (by decide)

end Nano.IS
