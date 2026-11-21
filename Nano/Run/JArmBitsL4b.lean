/- `JArmBits` fields L1 / L6 (bytes ↔ words) and L4 `li` (`C.e56` = `liL`) / `memW` (`C.e57` = `NTm.memW`). -/
import Nano.Run.JArmView
import Nano.Run.JArmBits
namespace JT
open Proven.Top SimW CallProbe ArmEnc C

/-! ## L1 / L6 -/

theorem jab_l1_words : ∀ ws : Buf, ws.length < 2 ^ 32 → (∀ w ∈ ws, w.toNat < 2 ^ 32) →
    e68 (len' (ws.flatMap ArmRA.le4)) (ws.flatMap ArmRA.le4) 0 bnew = ws := by
  intro ws hl hb
  have := NanoMain.e68_gen ws hb (by omega) (len' (ws.flatMap ArmRA.le4)) 0 bnew (by omega)
    (by simp only [len', NanoMain.flat_len]; omega)
  simpa [bnew] using this

theorem jab_l1_len : ∀ ws : Buf, ws.length < 2 ^ 32 → (len (ws.flatMap ArmRA.le4) &&& e_5) = 0 := by
  intro ws hl
  apply ArmRA.u64
  simp only [len, NanoMain.flat_len, e_5, UInt64.toNat_and, Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.reduceToNat,
    ArmRA.and3]
  omega

theorem jab_l6_bytes : ∀ (k : Nat) (c : List UInt8) (w : Buf), w.length ≤ k → w.length < 2 ^ 32 →
    e49 k c w 0 [] = w.flatMap ArmRA.le4 := by
  intro k c w hk hl
  rw [NanoMain.e49_wordBytes c w k (by omega) hk, NanoMain.le4_wordBytes]

/-! ## the word builders -/

private theorem tU {r : Nat} (h : r < 2 ^ 64) : r.toUInt64.toNat = r := CallProbe.toU_toNat _ h

private theorem e52_eq (c d x j : Nat) (hc : c < 2 ^ 32) (hc0 : c % 2 ^ 23 = 0) (hd : d < 32) (hx : x < 65536)
    (hj : j < 4) : e52 c.toUInt64 d.toUInt64 x.toUInt64 j.toUInt64 = (c + j * 2 ^ 21 + x * 2 ^ 5 + d).toUInt64 := by
  apply ArmRA.u64
  unfold e52
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq,
    Nat.reducePow]
  rw [tU (by omega), tU (by omega), tU (by omega), tU (by omega), tU (by omega),
    Nat.mod_eq_of_lt (show j * 2097152 < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show x * 32 < 18446744073709551616 by omega),
    ArmRA.orA (a := c) (b := j * 2097152) 23 (by omega) (by omega),
    ArmRA.orA (b := x * 32) 21 (by omega) (by omega), ArmRA.orA 5 (by omega) (by omega)]

private theorem e50_eq (c d n v : Nat) (hc : c < 2 ^ 32) (hc0 : c % 2 ^ 22 = 0) (hd : d < 32) (hn : n < 32)
    (hv : v < 4096) : e50 c.toUInt64 d.toUInt64 n.toUInt64 v.toUInt64 = (c + v * 2 ^ 10 + n * 2 ^ 5 + d).toUInt64 := by
  apply ArmRA.u64
  unfold e50
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq,
    Nat.reducePow]
  rw [tU (by omega), tU (by omega), tU (by omega), tU (by omega), tU (by omega),
    Nat.mod_eq_of_lt (show v * 1024 < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show n * 32 < 18446744073709551616 by omega),
    ArmRA.orA (a := c) (b := v * 1024) 22 (by omega) (by omega),
    ArmRA.orA (b := n * 32) 10 (by omega) (by omega), ArmRA.orA 5 (by omega) (by omega)]

private theorem e62_eq (c t n : Nat) (f : UInt64) (hc : c < 2 ^ 32) (hc0 : c % 2 ^ 21 = 0) (ht : t < 32) (hn : n < 32) :
    e62 c.toUInt64 t.toUInt64 n.toUInt64 f = (c + f.toNat % 512 * 2 ^ 12 + n * 2 ^ 5 + t).toUInt64 := by
  apply ArmRA.u64
  unfold e62 e_8
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_and, UInt64.reduceToNat, Nat.reduceMod,
    Nat.shiftLeft_eq, Nat.reducePow, Bridge.mask _ 9]
  rw [tU (by omega), tU (by omega), tU (by omega), tU (by omega),
    Nat.mod_eq_of_lt (show f.toNat % 512 * 4096 < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show n * 32 < 18446744073709551616 by omega),
    ArmRA.orA (a := c) (b := f.toNat % 512 * 4096) 21 (by omega) (by omega),
    ArmRA.orA (b := n * 32) 12 (by omega) (by omega), ArmRA.orA 5 (by omega) (by omega)]

/-! ## L4: `li` -/

private theorem beqU (a : UInt64) (n : Nat) (hn : n < 2 ^ 64) : (a == n.toUInt64) = decide (a.toNat = n) := by
  by_cases h : a.toNat = n
  · simp only [h, decide_true]; apply beq_iff_eq.2; apply ArmRA.u64; rw [tU hn, h]
  · simp only [h, decide_false]; apply beq_false_of_ne; intro h'; rw [h', tU hn] at h; exact h rfl

private theorem chk_lt (V j : Nat) : chk V j < 65536 := Nat.mod_lt _ (by decide)

private theorem and7N (v : UInt64) : (v &&& e_7).toNat = v.toNat % 65536 := by
  unfold e_7; simp only [UInt64.toNat_and, UInt64.reduceToNat, Bridge.mask _ 16]

private theorem succU (j : Nat) (hj : j < 4) : j.toUInt64 + 1 = (j + 1).toUInt64 := by
  apply ArmRA.u64; rw [UInt64.toNat_add, tU (by omega), tU (by omega)]; simp; omega

private theorem shr16 {V j : Nat} {v : UInt64} (hv : v.toNat = V / 2 ^ (16 * j)) :
    (v >>> 16).toNat = V / 2 ^ (16 * (j + 1)) := by
  simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, hv]
  rw [Nat.div_div_eq_div_mul, show 16 * (j + 1) = 16 * j + 16 by omega, Nat.pow_add]

private theorem chkN {V j : Nat} {v : UInt64} (hv : v.toNat = V / 2 ^ (16 * j)) :
    (v &&& e_7) = (chk V j).toUInt64 := by
  apply ArmRA.u64; rw [and7N, hv, tU (by have := chk_lt V j; omega)]; rfl

private theorem e55_chain (d V eN : Nat) (hd : d < 32) (he : eN < 65536) :
    ∀ (k j : Nat) (o : Buf) (v : UInt64), j + k ≤ 4 → v.toNat = V / 2 ^ (16 * j) →
      e55 k o d.toUInt64 v j.toUInt64 eN.toUInt64 1 = o ++ (chain d V eN k j).map Nat.toUInt64
  | 0, j, o, v, _, _ => by simp [e55, chain]
  | k + 1, j, o, v, hj, hv => by
    have hc := chk_lt V j
    have ih := fun o => e55_chain d V eN hd he k (j + 1) o (v >>> 16) (by omega) (shr16 hv)
    simp only [e55, chain, chkN hv, beqU _ eN (by omega), tU (show chk V j < 2 ^ 64 by omega), succU j (by omega),
      decide_eq_true_eq]
    by_cases h : chk V j = eN
    · simp only [h, ↓reduceIte]; exact ih o
    · simp only [h, ↓reduceIte, BEq.rfl]
      rw [ih, show (4068474880 : UInt64) = (4068474880 : Nat).toUInt64 from rfl,
        e52_eq _ d (chk V j) j (by omega) (by omega) hd (by omega) (by omega)]
      simp [bpush, ArmEnc.movk]

private theorem e55_walk (d V eN : Nat) (hd : d < 32) (he : eN = 0 ∨ eN = 65535) :
    ∀ (k j : Nat) (o : Buf) (v : UInt64), j + k ≤ 4 → v.toNat = V / 2 ^ (16 * j) →
      e55 k o d.toUInt64 v j.toUInt64 eN.toUInt64 0 = o ++ (walk0 d V eN k j).map Nat.toUInt64
  | 0, j, o, v, _, _ => by simp [e55, walk0]
  | k + 1, j, o, v, hj, hv => by
    have hc := chk_lt V j
    have ih := fun o => e55_walk d V eN hd he k (j + 1) o (v >>> 16) (by omega) (shr16 hv)
    have ic := fun o => e55_chain d V eN hd (by omega) k (j + 1) o (v >>> 16) (by omega) (shr16 hv)
    simp only [e55, walk0, chkN hv, beqU _ eN (by omega), tU (show chk V j < 2 ^ 64 by omega), succU j (by omega),
      decide_eq_true_eq]
    by_cases h : chk V j = eN
    · simp only [h, ↓reduceIte]; exact ih o
    · simp only [h, ↓reduceIte, show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true]
      rcases he with he | he
      · subst he
        simp only [show ((0 : Nat).toUInt64 == 0) = true from rfl, ↓reduceIte]
        rw [ic, show (3531603968 : UInt64) = (3531603968 : Nat).toUInt64 from rfl,
          e52_eq _ d (chk V j) j (by omega) (by omega) hd (by omega) (by omega)]
        simp [bpush, ArmEnc.movzH]
      · subst he
        simp only [show ((65535 : Nat).toUInt64 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
        have e : (65535 : UInt64) - (chk V j).toUInt64 = (65535 - chk V j).toUInt64 := by
          apply ArmRA.u64; rw [UInt64.toNat_sub, tU (by omega), tU (by omega)]; simp; omega
        rw [ic, e, show (2457862144 : UInt64) = (2457862144 : Nat).toUInt64 from rfl,
          e52_eq _ d (65535 - chk V j) j (by omega) (by omega) hd (by omega) (by omega)]
        simp [bpush, ArmEnc.movn]

private theorem e54_cnt (v : UInt64) (eN : Nat) (he : eN < 65536) : (e54 v eN.toUInt64).toNat = cnt v.toNat eN := by
  have h0 : (v &&& e_7) = (chk v.toNat 0).toUInt64 := chkN (j := 0) (by simp)
  have s1 : (v >>> 16).toNat = v.toNat / 2 ^ (16 * 1) := shr16 (j := 0) (by simp)
  have h1 := chkN s1
  have s2 : (v >>> 32).toNat = v.toNat / 2 ^ (16 * 2) := by
    simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  have h2 := chkN s2
  have s3 : (v >>> 48).toNat = v.toNat / 2 ^ (16 * 3) := by
    simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  have h3 := chkN s3
  have c0 := chk_lt v.toNat 0
  have c1 := chk_lt v.toNat 1
  have c2 := chk_lt v.toNat 2
  have c3 := chk_lt v.toNat 3
  have hr : List.range 4 = [0, 1, 2, 3] := by decide
  unfold e54 cnt
  rw [hr, h0, h1, h2, h3]
  simp only [beqU _ eN (show eN < 2 ^ 64 by omega), tU (show chk v.toNat 0 < 2 ^ 64 by omega),
    tU (show chk v.toNat 1 < 2 ^ 64 by omega), tU (show chk v.toNat 2 < 2 ^ 64 by omega),
    tU (show chk v.toNat 3 < 2 ^ 64 by omega), decide_eq_true_eq]
  by_cases a0 : chk v.toNat 0 = eN <;> by_cases a1 : chk v.toNat 1 = eN <;> by_cases a2 : chk v.toNat 2 = eN <;>
    by_cases a3 : chk v.toNat 3 = eN <;> simp [List.filter, a0, a1, a2, a3]

theorem jab_l4_li : ∀ (o : Buf) (d : Nat) (v : UInt64), d < 32 →
    e56 o d.toUInt64 v = o ++ (liL d v.toNat).map Nat.toUInt64 := by
  intro o d v hd
  have hv := v.toNat_lt
  have vv : v = v.toNat.toUInt64 := ArmRA.u64 (by rw [tU (by omega)])
  have e14 : e_14.toNat = 2 ^ 64 - 1 := by decide
  have hs : (e_14 - v).toNat = 2 ^ 64 - 1 - v.toNat := by rw [UInt64.toNat_sub, e14]; omega
  unfold e56 liL
  have g0 := e54_cnt v 0 (by omega)
  have g1 := e54_cnt v 65535 (by omega)
  rw [show (0 : Nat).toUInt64 = 0 from rfl] at g0
  rw [show (65535 : Nat).toUInt64 = 65535 from rfl] at g1
  simp only [UInt64.lt_iff_toNat_lt, hs, g0, g1, UInt64.reduceToNat]
  by_cases h1 : v.toNat < 65536
  · simp only [h1, ↓reduceIte]
    have w := e52_eq 3531603968 d v.toNat 0 (by omega) (by omega) hd h1 (by omega)
    rw [← vv] at w
    rw [show (3531603968 : UInt64) = (3531603968 : Nat).toUInt64 from rfl,
      show (0 : UInt64) = (0 : Nat).toUInt64 from rfl, w]
    simp [bpush, ArmEnc.movz]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : 2 ^ 64 - 1 - v.toNat < 65536
    · simp only [h2, ↓reduceIte]
      have e : e_14 - v = (2 ^ 64 - 1 - v.toNat).toUInt64 := ArmRA.u64 (by rw [hs, tU (by omega)])
      rw [e, show (2457862144 : UInt64) = (2457862144 : Nat).toUInt64 from rfl,
        show (0 : UInt64) = (0 : Nat).toUInt64 from rfl,
        e52_eq 2457862144 d _ 0 (by omega) (by omega) hd h2 (by omega)]
      simp [bpush, ArmEnc.movn]
    · simp only [h2, ↓reduceIte]
      split
      · exact e55_walk d v.toNat 65535 hd (Or.inr rfl) 4 0 o v (by omega) (by simp)
      · exact e55_walk d v.toNat 0 hd (Or.inl rfl) 4 0 o v (by omega) (by simp)

/-! ## L4: `memW` -/

theorem jab_l4_mem : ∀ (o : Buf) (st : Bool) (t n : Nat) (off : Int), t < 32 → n < 32 → -4096 < off → off < 32768 →
    (0 ≤ off → off % 8 = 0) →
    e57 o (if st then 1 else 0) t.toUInt64 n.toUInt64 (iu off) = o ++ (NTm.memW st t n off).map Nat.toUInt64 := by
  intro o st t n off ht hn h1 h2 hal
  have hf : (iu off).toNat = (off % 2 ^ 64).toNat := iu_toNat off
  have hs : ((if st then (1 : UInt64) else 0) == 0) = !st := by cases st <;> rfl
  have k1 : (4181721088 : UInt64) = (4181721088 : Nat).toUInt64 := rfl
  have k2 : (4177526784 : UInt64) = (4177526784 : Nat).toUInt64 := rfl
  have k3 : (4164943872 : UInt64) = (4164943872 : Nat).toUInt64 := rfl
  have k4 : (4160749568 : UInt64) = (4160749568 : Nat).toUInt64 := rfl
  have k5 : (3506438144 : UInt64) = (3506438144 : Nat).toUInt64 := rfl
  have k6 : (16 : UInt64) = (16 : Nat).toUInt64 := rfl
  have k7 : (0 : UInt64) = (0 : Nat).toUInt64 := rfl
  unfold e57 NTm.memW
  simp only [UInt64.lt_iff_toNat_lt, hs]
  by_cases h0 : 0 ≤ off
  · have ha := hal h0
    have c1 : (iu off).toNat < (32768 : UInt64).toNat := by rw [hf]; simp; omega
    have c2 : ((iu off &&& e_3) == 0) = true := by
      apply beq_iff_eq.2; apply ArmRA.u64
      unfold e_3; simp only [UInt64.toNat_and, UInt64.reduceToNat, ArmRA.and7, hf]; omega
    have c3 : off % 8 = 0 ∧ 0 ≤ off ∧ off < 32768 := ⟨ha, h0, h2⟩
    have e : iu off >>> 3 = (off.toNat / 8).toUInt64 := by
      apply ArmRA.u64
      simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, hf]
      rw [tU (by omega)]; omega
    simp only [c1, c2, c3, ↓reduceIte, and_self, e]
    cases st
    · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
      rw [k1, e50_eq _ t n _ (by omega) (by omega) ht hn (by omega)]
      simp [bpush, ArmEnc.ldr]
    · simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true]
      rw [k2, e50_eq _ t n _ (by omega) (by omega) ht hn (by omega)]
      simp [bpush, ArmEnc.str]
  · have c1 : ¬ (iu off).toNat < (32768 : UInt64).toNat := by rw [hf]; simp; omega
    have c3 : ¬ (off % 8 = 0 ∧ 0 ≤ off ∧ off < 32768) := fun h => h0 h.2.1
    have c4 : (iu off + 256).toNat < (256 : UInt64).toNat ↔ (-256 ≤ off ∧ off < 0) := by
      rw [UInt64.toNat_add, hf]; simp; omega
    simp only [c1, c3, c4, ↓reduceIte]
    by_cases h3 : -256 ≤ off ∧ off < 0
    · simp only [h3, and_self, ↓reduceIte]
      have m : (iu off).toNat % 512 = mo off 9 := by rw [hf]; unfold mo; omega
      cases st
      · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
        rw [k3, e62_eq _ t n _ (by omega) (by omega) ht hn, m]
        simp [bpush, ArmEnc.ldur]
      · simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true]
        rw [k4, e62_eq _ t n _ (by omega) (by omega) ht hn, m]
        simp [bpush, ArmEnc.stur]
    · simp only [h3, ↓reduceIte]
      have e : 0 - iu off = ((-off).toNat).toUInt64 := by
        apply ArmRA.u64; rw [UInt64.toNat_sub, hf, tU (by omega)]; simp; omega
      rw [e, k5, k6, e50_eq _ 16 n _ (by omega) (by omega) (by omega) hn (by omega)]
      cases st
      · simp only [Bool.not_false, ↓reduceIte, Bool.false_eq_true]
        rw [k1, k7, e50_eq _ t 16 0 (by omega) (by omega) ht (by omega) (by omega)]
        simp [bpush, ArmEnc.ldr, ArmEnc.subi]
      · simp only [Bool.not_true, ↓reduceIte, Bool.false_eq_true]
        rw [k2, k7, e50_eq _ t 16 0 (by omega) (by omega) ht (by omega) (by omega)]
        simp [bpush, ArmEnc.str, ArmEnc.subi]

end JT
