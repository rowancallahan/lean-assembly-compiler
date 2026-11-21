/- The byte/word ends of the J → AArch64 translator `C.e45` (Nano/Codegen/JArm):
`e68` reads Gen's little-endian bytes back into its words (`e68_g40`, the inverse of `C.g40`), and
`e49` writes the words as `JT.wordBytes` (`e49_wordBytes`). -/
import Nano.Codegen.JArm
import Nano.Run.ArmEncOK
import Nano.Run.NatImg
namespace NanoMain
open JT

/-! ## `e68`: bytes → words -/

theorem flat_getD : ∀ (ws : List UInt64) (m j : Nat), m < ws.length → j < 4 →
    (ws.flatMap ArmRA.le4).getD (4 * m + j) 0 = (ArmRA.le4 (ws.getD m 0)).getD j 0
  | [], m, j, h, _ => by simp at h
  | v :: ws, 0, j, _, hj => by
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp [ArmRA.le4]; omega)]; simp
  | v :: ws, m + 1, j, h, hj => by
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp [ArmRA.le4]; omega),
      show 4 * (m + 1) + j - (ArmRA.le4 v).length = 4 * m + j by simp [ArmRA.le4]; omega,
      ← List.getD_eq_getElem?_getD, flat_getD ws m j (by simpa using h) hj]
    simp

theorem flat_len (ws : List UInt64) : (ws.flatMap ArmRA.le4).length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons v ws ih => rw [List.flatMap_cons, List.length_append, ih]; simp [ArmRA.le4]; omega

/-- `e68` from byte `4·m` on: the words from `m` on are pushed (fuel `k` ≥ the words left) -/
theorem e68_gen (ws : List UInt64) (hb : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hl : 4 * ws.length + 4 < 2 ^ 64) :
    ∀ (k m : Nat) (w : Buf), m ≤ ws.length → ws.length ≤ m + k →
      C.e68 k (ws.flatMap ArmRA.le4) (UInt64.ofNat (4 * m)) w = w ++ ws.drop m
  | 0, m, w, h1, h2 => by
    rw [List.drop_of_length_le (by omega)]; simp [C.e68]
  | k + 1, m, w, h1, h2 => by
    simp only [C.e68, len, flat_len]
    have i1 : (UInt64.ofNat (4 * m) + 1).toNat = 4 * m + 1 := by simp; omega
    have i2 : (UInt64.ofNat (4 * m) + 2).toNat = 4 * m + 2 := by simp; omega
    have i3 : (UInt64.ofNat (4 * m) + 3).toNat = 4 * m + 3 := by simp; omega
    by_cases h : m < ws.length
    · have hlt : UInt64.ofNat (4 * m) + 3 < (4 * ws.length).toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, i3]; simp; omega
      have e1 : UInt64.ofNat (4 * m) + 4 = UInt64.ofNat (4 * (m + 1)) := by
        apply UInt64.toNat_inj.1; simp; omega
      have r0 : rd (ws.flatMap ArmRA.le4) (UInt64.ofNat (4 * m)) = ((ArmRA.le4 (ws.getD m 0)).getD 0 0).toUInt64 := by
        unfold rd; rw [show (UInt64.ofNat (4 * m)).toNat = 4 * m + 0 by simp; omega, flat_getD ws m 0 h (by omega)]
      have r1 : rd (ws.flatMap ArmRA.le4) (UInt64.ofNat (4 * m) + 1) = ((ArmRA.le4 (ws.getD m 0)).getD 1 0).toUInt64 := by
        unfold rd; rw [i1, flat_getD ws m 1 h (by omega)]
      have r2 : rd (ws.flatMap ArmRA.le4) (UInt64.ofNat (4 * m) + 2) = ((ArmRA.le4 (ws.getD m 0)).getD 2 0).toUInt64 := by
        unfold rd; rw [i2, flat_getD ws m 2 h (by omega)]
      have r3 : rd (ws.flatMap ArmRA.le4) (UInt64.ofNat (4 * m) + 3) = ((ArmRA.le4 (ws.getD m 0)).getD 3 0).toUInt64 := by
        unfold rd; rw [i3, flat_getD ws m 3 h (by omega)]
      simp only [hlt, ↓reduceIte]
      rw [e1, e68_gen ws hb hl k (m + 1) _ (by omega) (by omega)]
      change _ = w ++ List.drop m ws
      rw [List.drop_eq_getElem_cons h]
      have hw : ws.getD m 0 = ws[m] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      have wb := ArmRA.word_back (ws.getD m 0) (by rw [hw]; exact hb _ (List.getElem_mem h))
      rw [r0, r1, r2, r3, wb, hw]; simp [bpush]
    · have hlt : ¬ UInt64.ofNat (4 * m) + 3 < (4 * ws.length).toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, i3]; simp; omega
      simp only [hlt, ↓reduceIte]; rw [List.drop_of_length_le (by omega)]; simp

/-- **L1**: `e68` (with `e45`'s fuel) inverts Gen's `g40` -/
theorem e68_g40 (c0 : List UInt8) (ws : List UInt64) (hb : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hl : ws.length < 2 ^ 18) :
    C.e68 (len' (C.g40 16777216 c0 ws 0 [])) (C.g40 16777216 c0 ws 0 []) 0 bnew = ws := by
  have e : C.g40 16777216 c0 ws 0 [] = ws.flatMap ArmRA.le4 := by
    have := g40_le4 c0 ws (by omega) 16777216 0 [] (by omega) (by omega)
    simpa using this
  rw [e]
  have := e68_gen ws hb (by omega) (len' (ws.flatMap ArmRA.le4)) 0 bnew (by omega)
    (by simp only [len', flat_len]; omega)
  simpa [bnew] using this

/-! ## `e49`: words → bytes -/

theorem e49_g40 : ∀ (k : Nat) (c : List UInt8) (w : Buf) (i : UInt64) (o : List UInt8),
    C.e49 k c w i o = C.g40 k c w i o
  | 0, c, w, i, o => rfl
  | k + 1, c, w, i, o => by
    simp only [C.e49, C.g40]; split
    · exact e49_g40 k c w _ _
    · rfl

theorem le4_wordBytes (ws : List UInt64) : ws.flatMap ArmRA.le4 = wordBytes (ws.map UInt64.toNat) := by
  unfold wordBytes; rw [List.flatMap_map]; congr 1; funext v
  rw [← le4_wb v.toNat]; congr 1; apply UInt64.toNat_inj.1; simp

/-- `e49` from word `i` on, after `o` (fuel `k` ≥ the words left) -/
theorem e49_gen (c : List UInt8) (w : Buf) (hl : w.length < 2 ^ 64) (k i : Nat) (o : List UInt8)
    (h1 : w.length ≤ i + k) (h2 : i ≤ w.length) :
    C.e49 k c w (UInt64.ofNat i) o = o ++ wordBytes ((w.drop i).map UInt64.toNat) := by
  rw [e49_g40, g40_le4 c w hl k i o h1 h2, le4_wordBytes]

/-- **L6**: `e49` writes the words as `wordBytes` -/
theorem e49_wordBytes (c : List UInt8) (w : Buf) (k : Nat) (hl : w.length < 2 ^ 64) (hk : w.length ≤ k) :
    C.e49 k c w 0 [] = wordBytes (w.map UInt64.toNat) := by
  have := e49_gen c w hl k 0 [] (by omega) (by omega)
  simpa using this

end NanoMain
