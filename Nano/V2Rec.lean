/- nano v2, increment 1: the expression generator `Nano.V2.genE` on the record machine (`Nano/StackRec.lean`):
`genE_ok` (with room: the records push `Nano.V2.den e env`) and `genE_fail` (without: the oom flag), copies of v1's
`Nano.R.genE_ok`/`genE_fail` with the new `if` node (`ite_node`, `ite_fail`). -/
import Nano.V2Ops

namespace Nano.V2R
open Proven Nano.R Nano.V2

mutual
/-- variables in scope, argument lists of fewer than 128 entries, no stray `anil`/`acons` -/
def ScE : E → Nat → Bool
  | .num _, _ => true
  | .var i, n => decide (i < n)
  | .add a b, n => ScE a n && ScE b n
  | .sub a b, n => ScE a n && ScE b n
  | .mul a b, n => ScE a n && ScE b n
  | .let_ v b, n => ScE v n && ScE b (n + 1)
  | .call b as, n => ScA as n && ScE b (Nano.V2.cnt as) && decide (Nano.V2.cnt as < 128)
  | .ite _ a b t e, n => ScE a n && ScE b n && ScE t n && ScE e n
  | .bit _ a b, n => ScE a n && ScE b n
  | .sh _ _ a, n => ScE a n
  | .anil, _ => false
  | .acons _ _, _ => false
def ScA : E → Nat → Bool
  | .acons e r, n => ScE e n && ScA r n
  | _, _ => true
end

theorem depE_ge : ∀ (e : E) (d n : Nat), ScE e n = true → d + 1 ≤ Nano.V2.depE d e
  | .num _, d, n, _ => by simp [Nano.V2.depE]
  | .var _, d, n, _ => by simp [Nano.V2.depE]
  | .add a b, d, n, h => by simp only [ScE, Bool.and_eq_true] at h; have := depE_ge a d n h.1; simp only [Nano.V2.depE]; omega
  | .sub a b, d, n, h => by simp only [ScE, Bool.and_eq_true] at h; have := depE_ge a d n h.1; simp only [Nano.V2.depE]; omega
  | .mul a b, d, n, h => by simp only [ScE, Bool.and_eq_true] at h; have := depE_ge a d n h.1; simp only [Nano.V2.depE]; omega
  | .let_ v b, d, n, h => by simp only [ScE, Bool.and_eq_true] at h; have := depE_ge v d n h.1; simp only [Nano.V2.depE]; omega
  | .call b as, d, n, h => by
    simp only [ScE, Bool.and_eq_true] at h; have := depE_ge b (d + Nano.V2.cnt as) _ h.1.2; simp only [Nano.V2.depE]; omega
  | .ite k a b t e, d, n, h => by
    simp only [ScE, Bool.and_eq_true] at h
    have := depE_ge t d n h.1.2; have := depE_ge e d n h.2
    simp only [Nano.V2.depE]; split <;> omega
  | .bit _ a b, d, n, h => by
    simp only [ScE, Bool.and_eq_true] at h; have := depE_ge a d n h.1; simp only [Nano.V2.depE]; omega
  | .sh _ _ a, d, n, h => by simp only [ScE] at h; have := depE_ge a d n h; simp only [Nano.V2.depE]; omega
  | .anil, _, _, h => by simp [ScE] at h
  | .acons _ _, _, _, h => by simp [ScE] at h

theorem genA_cnt : ∀ (as : E) (env : List UInt64), Nano.V2.cnt as = (Nano.V2.denA as env).length
  | .acons _ r, env => by simp [Nano.V2.cnt, Nano.V2.denA, genA_cnt r env]
  | .num _, _ => rfl | .var _, _ => rfl | .add _ _, _ => rfl | .sub _ _, _ => rfl | .mul _ _, _ => rfl
  | .let_ _ _, _ => rfl | .call _ _, _ => rfl | .anil, _ => rfl | .ite _ _ _ _ _, _ => rfl
  | .bit _ _ _, _ => rfl | .sh _ _ _, _ => rfl

variable {P : List UInt8} {T W : Nat}

/-- the comparison operations are well formed from height `h ≥ 2`, with peak `h + 7` at most -/
theorem wf_cmp (k : Cmp) (h : Nat) (hh : 2 ≤ h) : wfOps h (cmpOps k) = true ∧ peakOps h (cmpOps k) ≤ h + 7 := by
  obtain ⟨j, rfl⟩ : ∃ j, h = j + 2 := ⟨h - 2, by omega⟩
  cases k <;> simp [cmpOps, eqOps, ltsOps, ltuOps, wfOps, SOp.wf, SOp.after, peakOps, SOp.peak] <;> (try omega)

theorem wf_sel (h : Nat) (hh : 3 ≤ h) : wfOps h selOps = true ∧ peakOps h selOps = h + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, h = j + 3 := ⟨h - 3, by omega⟩
  simp [selOps, wfOps, SOp.wf, SOp.after, peakOps, SOp.peak]

theorem wf_bit (o : BOp) (h : Nat) (hh : 2 ≤ h) : wfOps h (bitOps o) = true ∧ peakOps h (bitOps o) ≤ h + 7 := by
  obtain ⟨j, rfl⟩ : ∃ j, h = j + 2 := ⟨h - 2, by omega⟩
  cases o <;> simp [bitOps, andOps, xorOps, wfOps, SOp.wf, SOp.after, peakOps, SOp.peak] <;> (try omega)

theorem wf_sh (l : Bool) (k : Nat) (h : Nat) (hh : 1 ≤ h) : wfOps h [shOp l (k % 64)] = true ∧ peakOps h [shOp l (k % 64)] = h := by
  have := Nat.mod_lt k (show 64 > 0 by decide)
  cases l <;> simp [shOp, wfOps, SOp.wf, SOp.after, peakOps, SOp.peak] <;> omega

/-- an expression piece: with room, its records push `v` -/
def Piece (P : List UInt8) (T W : Nat) (code : List UInt8) (vals : List (BitVec 64)) (v : BitVec 64) : Prop :=
  ∀ (s : St) (rest : List UInt8), CodeAt P s.pc (code ++ rest) → Stk s T vals → s.get 12 = BitVec.ofNat 64 W →
    ∃ s', Star P s s' ∧ Stk s' T (vals ++ [v]) ∧ Kept s s' ∧ CodeAt P s'.pc rest

/-- **an `if` node**: X, then A, B, then `c` by the comparison ops, then Y, then `X + c (Y - X)` -/
theorem ite_node (hT2 : T < 2 ^ 64) (hW : W < 2 ^ 64) {X A B Y : List UInt8} {ops : List SOp}
    {vals : List (BitVec 64)} {vx va vb vy c : BitVec 64}
    (hX : Piece P T W X vals vx) (hA : Piece P T W A (vals ++ [vx]) va) (hB : Piece P T W B (vals ++ [vx, va]) vb)
    (hY : Piece P T W Y (vals ++ [vx, c]) vy)
    (hops : runOps ops (vb :: va :: vx :: vals.reverse) = c :: vx :: vals.reverse)
    (hwf : wfOps (vals.length + 3) ops = true) (hfit : W + 8 * peakOps (vals.length + 3) ops ≤ T)
    (hfit2 : W + 8 * (vals.length + 4) ≤ T)
    {s : St} {rest : List UInt8} (h : CodeAt P s.pc (X ++ A ++ B ++ opsCode ops ++ Y ++ opsCode selOps ++ rest))
    (hs : Stk s T vals) (h12 : s.get 12 = BitVec.ofNat 64 W) :
    ∃ s', Star P s s' ∧ Stk s' T (vals ++ [vx + c * (vy - vx)]) ∧ Kept s s' ∧ CodeAt P s'.pc rest := by
  simp only [List.append_assoc] at h
  have k12 : ∀ {a b : St}, Kept a b → a.get 12 = BitVec.ofNat 64 W → b.get 12 = BitVec.ofNat 64 W :=
    fun k e => by rw [k 12 (by decide) (by decide) (by decide)]; exact e
  obtain ⟨s1, x1, st1, k1, c1⟩ := hX s _ h hs h12
  obtain ⟨s2, x2, st2, k2, c2⟩ := hA s1 _ c1 st1 (k12 k1 h12)
  obtain ⟨s3, x3, st3, k3, c3⟩ := hB s2 _ c2 (by simpa using st2) (k12 k2 (k12 k1 h12))
  have e3 : (vals ++ [vx, va] ++ [vb]) = (vb :: va :: vx :: vals.reverse).reverse := by simp
  rw [e3] at st3
  obtain ⟨s4, x4, st4, k4, c4⟩ := ops_ok hT2 hW ops _ s3 _ c3 st3 (k12 k3 (k12 k2 (k12 k1 h12)))
    (by simpa using hwf) (by simpa using hfit)
  rw [hops] at st4
  have h4 := k12 k4 (k12 k3 (k12 k2 (k12 k1 h12)))
  obtain ⟨s5, x5, st5, k5, c5⟩ := hY s4 _ c4 (by simpa using st4) h4
  have e5 : (vals ++ [vx, c] ++ [vy]) = (vy :: c :: vx :: vals.reverse).reverse := by simp
  rw [e5] at st5
  obtain ⟨s6, x6, st6, k6, c6⟩ := ops_ok hT2 hW selOps _ s5 _ c5 st5 (k12 k5 h4)
    (by simp only [List.length_cons, List.length_reverse]; exact (wf_sel _ (by omega)).1)
    (by simp only [List.length_cons, List.length_reverse]; rw [(wf_sel _ (by omega)).2]; omega)
  rw [sel_run] at st6
  exact ⟨s6, x1.trans (x2.trans (x3.trans (x4.trans (x5.trans x6)))), by simpa using st6,
    k1.trans (k2.trans (k3.trans (k4.trans (k5.trans k6)))), c6⟩

/-- two operands, then stack operations -/
theorem ops_node (hT2 : T < 2 ^ 64) (hW : W < 2 ^ 64) {A B : List UInt8} {ops : List SOp} {vals : List (BitVec 64)}
    {va vb r : BitVec 64} (hA : Piece P T W A vals va) (hB : Piece P T W B (vals ++ [va]) vb)
    (hops : runOps ops (vb :: va :: vals.reverse) = r :: vals.reverse)
    (hwf : wfOps (vals.length + 2) ops = true) (hfit : W + 8 * peakOps (vals.length + 2) ops ≤ T)
    {s : St} {rest : List UInt8} (h : CodeAt P s.pc (A ++ B ++ opsCode ops ++ rest)) (hs : Stk s T vals)
    (h12 : s.get 12 = BitVec.ofNat 64 W) :
    ∃ s', Star P s s' ∧ Stk s' T (vals ++ [r]) ∧ Kept s s' ∧ CodeAt P s'.pc rest := by
  simp only [List.append_assoc] at h
  obtain ⟨s1, x1, st1, k1, c1⟩ := hA s _ h hs h12
  obtain ⟨s2, x2, st2, k2, c2⟩ := hB s1 _ c1 st1 (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12)
  have e2 : vals ++ [va] ++ [vb] = (vb :: va :: vals.reverse).reverse := by simp
  rw [e2] at st2
  obtain ⟨s3, x3, st3, k3, c3⟩ := ops_ok hT2 hW ops _ s2 _ c2 st2
    (by rw [k2 12 (by decide) (by decide) (by decide), k1 12 (by decide) (by decide) (by decide)]; exact h12)
    (by simpa using hwf) (by simpa using hfit)
  rw [hops] at st3
  exact ⟨s3, x1.trans (x2.trans x3), by simpa using st3, k1.trans (k2.trans k3), c3⟩

/-- one operand, then stack operations -/
theorem ops1_node (hT2 : T < 2 ^ 64) (hW : W < 2 ^ 64) {A : List UInt8} {ops : List SOp} {vals : List (BitVec 64)}
    {va r : BitVec 64} (hA : Piece P T W A vals va)
    (hops : runOps ops (va :: vals.reverse) = r :: vals.reverse)
    (hwf : wfOps (vals.length + 1) ops = true) (hfit : W + 8 * peakOps (vals.length + 1) ops ≤ T)
    {s : St} {rest : List UInt8} (h : CodeAt P s.pc (A ++ opsCode ops ++ rest)) (hs : Stk s T vals)
    (h12 : s.get 12 = BitVec.ofNat 64 W) :
    ∃ s', Star P s s' ∧ Stk s' T (vals ++ [r]) ∧ Kept s s' ∧ CodeAt P s'.pc rest := by
  simp only [List.append_assoc] at h
  obtain ⟨s1, x1, st1, k1, c1⟩ := hA s _ h hs h12
  have e1 : vals ++ [va] = (va :: vals.reverse).reverse := by simp
  rw [e1] at st1
  obtain ⟨s2, x2, st2, k2, c2⟩ := ops_ok hT2 hW ops _ s1 _ c1 st1
    (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12) (by simpa using hwf) (by simpa using hfit)
  rw [hops] at st2
  exact ⟨s2, x1.trans x2, by simpa using st2, k1.trans k2, c2⟩

theorem toBV_add (a b : UInt64) : (a + b).toBitVec = a.toBitVec + b.toBitVec := rfl

/-- the value of an `if` node from its parts -/
theorem ite_fin {p : Prop} [Decidable p] {q : Bool} (hpq : p ↔ q = true) (vt ve : UInt64) :
    ve.toBitVec + (if p then 1#64 else 0#64) * (vt.toBitVec - ve.toBitVec) = (if q = true then vt else ve).toBitVec := by
  by_cases h : p
  · rw [if_pos h, if_pos (hpq.mp h)]; exact sel_one _ _
  · rw [if_neg h, if_neg (fun e => h (hpq.mpr e))]; simp

/-- the value of a swapped (`<=`) `if` node -/
theorem ite_fin' {p : Prop} [Decidable p] {q : Bool} (hpq : p ↔ q = false) (vt ve : UInt64) :
    vt.toBitVec + (if p then 1#64 else 0#64) * (ve.toBitVec - vt.toBitVec) = (if q = true then vt else ve).toBitVec := by
  by_cases h : p
  · rw [if_pos h, if_neg (by rw [hpq.mp h]; simp)]; exact sel_one _ _
  · have hq : q = true := by
      cases e : q with
      | false => exact absurd (hpq.mpr e) h
      | true => rfl
    rw [if_neg h, if_pos hq]; simp

theorem test_ltu (x y : UInt64) : x.toBitVec.toNat < y.toBitVec.toNat ↔ Cmp.test .ltu x y = true := by
  simp [Cmp.test, UInt64.lt_iff_toNat_lt]
theorem test_leu (x y : UInt64) : y.toBitVec.toNat < x.toBitVec.toNat ↔ Cmp.test .leu x y = false := by
  simp [Cmp.test, UInt64.le_iff_toNat_le]
theorem test_lts (x y : UInt64) : x.toBitVec.slt y.toBitVec = true ↔ Cmp.test .lts x y = true := by
  simp only [Cmp.test, decide_eq_true_iff, Int64.lt_iff_toBitVec_slt, UInt64.toBitVec_toInt64]
theorem test_les (x y : UInt64) : y.toBitVec.slt x.toBitVec = true ↔ Cmp.test .les x y = false := by
  simp only [Cmp.test, decide_eq_false_iff_not, ← Int64.not_lt, Classical.not_not, Int64.lt_iff_toBitVec_slt,
    UInt64.toBitVec_toInt64]
theorem test_eq (x y : UInt64) : x.toBitVec = y.toBitVec ↔ Cmp.test .eq x y = true := by
  simp [Cmp.test, UInt64.toBitVec_inj]

/-- a binary operator node -/
theorem bin_node (k : Nat) (hk : k = 24 ∨ k = 32 ∨ k = 40) (hT2 : T < 2 ^ 64) {a b : E} {sc : List Nat}
    {vals : List (BitVec 64)} {s : St} {rest : List UInt8} {va vb : UInt64}
    (ha : ∀ (s : St) (rest : List UInt8), CodeAt P s.pc (Nano.V2.genE sc vals.length a ++ rest) → Stk s T vals →
      s.get 12 = BitVec.ofNat 64 W →
      ∃ s', Star P s s' ∧ Stk s' T (vals ++ [va.toBitVec]) ∧ Kept s s' ∧ CodeAt P s'.pc rest)
    (hb : ∀ (s : St) (rest : List UInt8), CodeAt P s.pc (Nano.V2.genE sc (vals ++ [va.toBitVec]).length b ++ rest) →
      Stk s T (vals ++ [va.toBitVec]) → s.get 12 = BitVec.ofNat 64 W →
      ∃ s', Star P s s' ∧ Stk s' T (vals ++ [va.toBitVec] ++ [vb.toBitVec]) ∧ Kept s s' ∧ CodeAt P s'.pc rest)
    (h : CodeAt P s.pc (Nano.V2.genE sc vals.length a ++ Nano.V2.genE sc (vals.length + 1) b ++ Nano.binop k.toUInt8 ++ rest))
    (hs : Stk s T vals) (h12 : s.get 12 = BitVec.ofNat 64 W) (hT : 8 * (vals.length + 2) ≤ T) :
    ∃ s', Star P s s' ∧ Stk s' T (vals ++ [opv k va.toBitVec vb.toBitVec]) ∧ Kept s s' ∧ CodeAt P s'.pc rest := by
  simp only [List.append_assoc] at h
  obtain ⟨s1, x1, st1, k1, c1⟩ := ha s _ h hs h12
  obtain ⟨s2, x2, st2, k2, c2⟩ := hb s1 _ (by simpa using c1) st1 (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12)
  obtain ⟨s3, x3, -, st3, k3, c3⟩ := binop_ok hk c2 (vals := vals) (by simpa using st2) hT hT2
  exact ⟨s3, x1.trans (x2.trans x3), st3, k1.trans (k2.trans k3), c3⟩

set_option maxHeartbeats 2000000 in
mutual
/-- **an expression's records push its value** (on the record machine; the stack fits in the work block) -/
theorem genE_ok (hT2 : T < 2 ^ 64) : ∀ (e : E) (sc : List Nat) (env : List UInt64) (vals : List (BitVec 64)) (s : St)
    (rest : List UInt8), CodeAt P s.pc (Nano.V2.genE sc vals.length e ++ rest) → ScE e env.length = true →
    ScOk sc env vals → Stk s T vals → s.get 12 = BitVec.ofNat 64 W → W + 8 * Nano.V2.depE vals.length e ≤ T →
    Nano.V2.depE vals.length e ≤ 256 →
    ∃ s', Star P s s' ∧ Stk s' T (vals ++ [(Nano.V2.den e env).toBitVec]) ∧ Kept s s' ∧ CodeAt P s'.pc rest
  | .num n, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [Nano.V2.genE, List.append_assoc] at h
    obtain ⟨s1, x1, g1, m1, k1, c1⟩ := li_ok h
    obtain ⟨s2, x2, st2, k2, c2⟩ := push_stk c1 (stk_kept hs m1 (k1 31 (by decide)) (k1 12 (by decide)) (k1 2 (by decide)))
      (by rw [k1 12 (by decide)]; exact h12) (by simp only [Nano.V2.depE] at hW; omega) hT2
    exact ⟨s2, x1.trans x2, by rw [g1] at st2; simpa [Nano.V2.den] using st2, fun j a b c => by rw [k2 j a b c, k1 j a], c2⟩
  | .var i, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [Nano.V2.genE, List.append_assoc] at h
    simp only [ScE, decide_eq_true_eq] at hsc
    simp only [Nano.V2.depE] at hW hd
    obtain ⟨hj, hv⟩ := hok i hsc
    obtain ⟨s1, x1, g1, m1, k1, c1⟩ := ldslot_ok h hs hj (by omega) (by omega) hT2
    obtain ⟨s2, x2, st2, k2, c2⟩ := push_stk c1 (stk_kept hs m1 (k1 31 (by decide)) (k1 12 (by decide)) (k1 2 (by decide)))
      (by rw [k1 12 (by decide)]; exact h12) (by omega) hT2
    exact ⟨s2, x1.trans x2, by rw [g1, hv] at st2; simpa [Nano.V2.den] using st2, fun j a b c => by rw [k2 j a b c, k1 j a], c2⟩
  | .add a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.V2.depE] at hW hd
    have := depE_ge b (vals.length + 1) _ hsc.2
    obtain ⟨s', x, st, k, c⟩ := bin_node 24 (by decide) hT2 (va := Nano.V2.den a env) (vb := Nano.V2.den b env)
      (fun s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 (by omega) (by omega))
      (fun s rest h hs h12 => by
        have := genE_ok hT2 b sc env (vals ++ [(Nano.V2.den a env).toBitVec]) s rest h hsc.2 (hok.mono _) hs h12
          (by simp; omega) (by simp; omega)
        simpa using this) (by simpa [Nano.V2.genE] using h) hs h12 (by omega)
    exact ⟨s', x, by rw [toBV_opv24] at st; simpa [Nano.V2.den] using st, k, c⟩
  | .sub a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.V2.depE] at hW hd
    have := depE_ge b (vals.length + 1) _ hsc.2
    obtain ⟨s', x, st, k, c⟩ := bin_node 32 (by decide) hT2 (va := Nano.V2.den a env) (vb := Nano.V2.den b env)
      (fun s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 (by omega) (by omega))
      (fun s rest h hs h12 => by
        have := genE_ok hT2 b sc env (vals ++ [(Nano.V2.den a env).toBitVec]) s rest h hsc.2 (hok.mono _) hs h12
          (by simp; omega) (by simp; omega)
        simpa using this) (by simpa [Nano.V2.genE] using h) hs h12 (by omega)
    exact ⟨s', x, by rw [toBV_opv32] at st; simpa [Nano.V2.den] using st, k, c⟩
  | .mul a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.V2.depE] at hW hd
    have := depE_ge b (vals.length + 1) _ hsc.2
    obtain ⟨s', x, st, k, c⟩ := bin_node 40 (by decide) hT2 (va := Nano.V2.den a env) (vb := Nano.V2.den b env)
      (fun s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 (by omega) (by omega))
      (fun s rest h hs h12 => by
        have := genE_ok hT2 b sc env (vals ++ [(Nano.V2.den a env).toBitVec]) s rest h hsc.2 (hok.mono _) hs h12
          (by simp; omega) (by simp; omega)
        simpa using this) (by simpa [Nano.V2.genE] using h) hs h12 (by omega)
    exact ⟨s', x, by rw [toBV_opv40] at st; simpa [Nano.V2.den] using st, k, c⟩
  | .let_ v b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.V2.depE] at hW hd
    have := depE_ge b (vals.length + 1) _ hsc.2
    simp only [Nano.V2.genE, List.append_assoc] at h
    obtain ⟨s1, x1, st1, k1, c1⟩ := genE_ok hT2 v sc env vals s _ h hsc.1 hok hs h12 (by omega) (by omega)
    obtain ⟨s2, x2, st2, k2, c2⟩ := genE_ok hT2 b (vals.length :: sc) (Nano.V2.den v env :: env)
      (vals ++ [(Nano.V2.den v env).toBitVec]) s1 _ (by simpa using c1) (by simpa using hsc.2) (hok.push _) st1
      (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12) (by simp; omega) (by simp; omega)
    obtain ⟨s3, x3, st3, k3, c3⟩ := tail_ok (k := 1) (mid := [(Nano.V2.den v env).toBitVec]) (by simpa using c2)
      (by simpa using st2) rfl (by decide) (by omega) hT2
    exact ⟨s3, x1.trans (x2.trans x3), by simpa [Nano.V2.den] using st3, k1.trans (k2.trans k3), c3⟩
  | .call b as, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true, decide_eq_true_eq] at hsc; simp only [Nano.V2.depE] at hW hd
    obtain ⟨⟨ha, hb⟩, hc⟩ := hsc
    have := depE_ge b (vals.length + Nano.V2.cnt as) _ hb
    simp only [Nano.V2.genE, List.append_assoc] at h
    obtain ⟨s1, x1, st1, k1, c1, hcnt⟩ := genA_ok hT2 as sc env vals s _ h ha hok hs h12 (by omega) (by omega)
    have hl : ((Nano.V2.denA as env).map UInt64.toBitVec).length = Nano.V2.cnt as := by simp [hcnt]
    obtain ⟨s2, x2, st2, k2, c2⟩ := genE_ok hT2 b (Nano.mkSc (Nano.V2.cnt as) vals.length) (Nano.V2.denA as env).reverse
      (vals ++ (Nano.V2.denA as env).map UInt64.toBitVec) s1 _ (by simpa [hl] using c1) (by simpa [hcnt] using hb)
      (by rw [← hl]; exact ScOk.args _ _ _ (by simp) (fun j h => by simp)) st1
      (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12) (by simp [hl]; omega) (by simp [hl]; omega)
    obtain ⟨s3, x3, st3, k3, c3⟩ := tail_ok (k := Nano.V2.cnt as) (mid := (Nano.V2.denA as env).map UInt64.toBitVec)
      (by simpa using c2) (by simpa using st2) hl hc (by omega) hT2
    exact ⟨s3, x1.trans (x2.trans x3), by simpa [Nano.V2.den] using st3, k1.trans (k2.trans k3), c3⟩
  | .ite k a b t e, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc
    obtain ⟨⟨⟨ha, hb⟩, ht⟩, he⟩ := hsc
    have hW64 : W < 2 ^ 64 := by have := hs.lo; rw [h12] at this; simp at this; omega
    have hw := wf_cmp k (vals.length + 3) (by omega)
    have gt := depE_ge t vals.length _ ht; have ge := depE_ge e vals.length _ he
    have hcode := h; simp only [Nano.V2.genE] at hcode
    simp only [Nano.V2.depE] at hW hd
    cases k with
    | eq =>
      simp only [Cmp.swap, if_false, Bool.false_eq_true] at hcode hW hd
      obtain ⟨s', x, st, kk, c⟩ := ite_node (ops := cmpOps .eq) (vy := (Nano.V2.den t env).toBitVec) hT2 hW64
        (fun s rest h hs h12 => genE_ok hT2 e sc env vals s rest h he hok hs h12 (by omega) (by omega))
        (fun s rest h hs h12 => genE_ok hT2 a sc env (vals ++ [(Nano.V2.den e env).toBitVec]) s rest (by simpa using h) ha (hok.mono _) hs h12
          (by simp; omega) (by simp; omega))
        (fun s rest h hs h12 => by
          have := genE_ok hT2 b sc env (vals ++ [(Nano.V2.den e env).toBitVec, (Nano.V2.den a env).toBitVec]) s rest (by simpa using h) hb (hok.mono _)
            (by simpa using hs) h12 (by simp; omega) (by simp; omega)
          simpa using this)
        (fun s rest h hs h12 => by
          have := genE_ok hT2 t sc env (vals ++ [(Nano.V2.den e env).toBitVec, (if (Nano.V2.den a env).toBitVec = (Nano.V2.den b env).toBitVec then 1#64 else 0#64)]) s rest (by simpa using h) ht (hok.mono _)
            (by simpa using hs) h12 (by simp; omega) (by simp; omega)
          simpa using this)
        (eq_run _ _ _) hw.1 (by omega) (by simp [selOps, peakOps, SOp.peak, SOp.after] at hW; omega)
        hcode hs h12
      refine ⟨s', x, ?_, kk, c⟩
      have := ite_fin (test_eq (Nano.V2.den a env) (Nano.V2.den b env)) (Nano.V2.den t env) (Nano.V2.den e env)
      simp only [Nano.V2.den]; rw [← this]; exact st
    | ltu =>
      simp only [Cmp.swap, if_false, Bool.false_eq_true] at hcode hW hd
      obtain ⟨s', x, st, kk, c⟩ := ite_node (ops := cmpOps .ltu) (vy := (Nano.V2.den t env).toBitVec) hT2 hW64
        (fun s rest h hs h12 => genE_ok hT2 e sc env vals s rest h he hok hs h12 (by omega) (by omega))
        (fun s rest h hs h12 => genE_ok hT2 a sc env (vals ++ [(Nano.V2.den e env).toBitVec]) s rest (by simpa using h) ha (hok.mono _) hs h12
          (by simp; omega) (by simp; omega))
        (fun s rest h hs h12 => by
          have := genE_ok hT2 b sc env (vals ++ [(Nano.V2.den e env).toBitVec, (Nano.V2.den a env).toBitVec]) s rest (by simpa using h) hb (hok.mono _)
            (by simpa using hs) h12 (by simp; omega) (by simp; omega)
          simpa using this)
        (fun s rest h hs h12 => by
          have := genE_ok hT2 t sc env (vals ++ [(Nano.V2.den e env).toBitVec, (if (Nano.V2.den a env).toBitVec.toNat < (Nano.V2.den b env).toBitVec.toNat then 1#64 else 0#64)]) s rest (by simpa using h) ht (hok.mono _)
            (by simpa using hs) h12 (by simp; omega) (by simp; omega)
          simpa using this)
        (ltu_run _ _ _) hw.1 (by omega) (by simp [selOps, peakOps, SOp.peak, SOp.after] at hW; omega)
        hcode hs h12
      refine ⟨s', x, ?_, kk, c⟩
      have := ite_fin (test_ltu (Nano.V2.den a env) (Nano.V2.den b env)) (Nano.V2.den t env) (Nano.V2.den e env)
      simp only [Nano.V2.den]; rw [← this]; exact st
    | lts =>
      simp only [Cmp.swap, if_false, Bool.false_eq_true] at hcode hW hd
      obtain ⟨s', x, st, kk, c⟩ := ite_node (ops := cmpOps .lts) (vy := (Nano.V2.den t env).toBitVec) hT2 hW64
        (fun s rest h hs h12 => genE_ok hT2 e sc env vals s rest h he hok hs h12 (by omega) (by omega))
        (fun s rest h hs h12 => genE_ok hT2 a sc env (vals ++ [(Nano.V2.den e env).toBitVec]) s rest (by simpa using h) ha (hok.mono _) hs h12
          (by simp; omega) (by simp; omega))
        (fun s rest h hs h12 => by
          have := genE_ok hT2 b sc env (vals ++ [(Nano.V2.den e env).toBitVec, (Nano.V2.den a env).toBitVec]) s rest (by simpa using h) hb (hok.mono _)
            (by simpa using hs) h12 (by simp; omega) (by simp; omega)
          simpa using this)
        (fun s rest h hs h12 => by
          have := genE_ok hT2 t sc env (vals ++ [(Nano.V2.den e env).toBitVec, (if (Nano.V2.den a env).toBitVec.slt (Nano.V2.den b env).toBitVec then 1#64 else 0#64)]) s rest (by simpa using h) ht (hok.mono _)
            (by simpa using hs) h12 (by simp; omega) (by simp; omega)
          simpa using this)
        (lts_run _ _ _) hw.1 (by omega) (by simp [selOps, peakOps, SOp.peak, SOp.after] at hW; omega)
        hcode hs h12
      refine ⟨s', x, ?_, kk, c⟩
      have := ite_fin (test_lts (Nano.V2.den a env) (Nano.V2.den b env)) (Nano.V2.den t env) (Nano.V2.den e env)
      simp only [Nano.V2.den]; rw [← this]; exact st
    | leu =>
      simp only [Cmp.swap, if_true] at hcode hW hd
      obtain ⟨s', x, st, kk, c⟩ := ite_node (ops := cmpOps .leu) (vy := (Nano.V2.den e env).toBitVec) hT2 hW64
        (fun s rest h hs h12 => genE_ok hT2 t sc env vals s rest h ht hok hs h12 (by omega) (by omega))
        (fun s rest h hs h12 => genE_ok hT2 b sc env (vals ++ [(Nano.V2.den t env).toBitVec]) s rest (by simpa using h) hb (hok.mono _) hs h12
          (by simp; omega) (by simp; omega))
        (fun s rest h hs h12 => by
          have := genE_ok hT2 a sc env (vals ++ [(Nano.V2.den t env).toBitVec, (Nano.V2.den b env).toBitVec]) s rest (by simpa using h) ha (hok.mono _)
            (by simpa using hs) h12 (by simp; omega) (by simp; omega)
          simpa using this)
        (fun s rest h hs h12 => by
          have := genE_ok hT2 e sc env (vals ++ [(Nano.V2.den t env).toBitVec, (if (Nano.V2.den b env).toBitVec.toNat < (Nano.V2.den a env).toBitVec.toNat then 1#64 else 0#64)]) s rest (by simpa using h) he (hok.mono _)
            (by simpa using hs) h12 (by simp; omega) (by simp; omega)
          simpa using this)
        (ltu_run _ _ _) hw.1 (by omega) (by simp [selOps, peakOps, SOp.peak, SOp.after] at hW; omega)
        hcode hs h12
      refine ⟨s', x, ?_, kk, c⟩
      have := ite_fin' (test_leu (Nano.V2.den a env) (Nano.V2.den b env)) (Nano.V2.den t env) (Nano.V2.den e env)
      simp only [Nano.V2.den]; rw [← this]; exact st
    | les =>
      simp only [Cmp.swap, if_true] at hcode hW hd
      obtain ⟨s', x, st, kk, c⟩ := ite_node (ops := cmpOps .les) (vy := (Nano.V2.den e env).toBitVec) hT2 hW64
        (fun s rest h hs h12 => genE_ok hT2 t sc env vals s rest h ht hok hs h12 (by omega) (by omega))
        (fun s rest h hs h12 => genE_ok hT2 b sc env (vals ++ [(Nano.V2.den t env).toBitVec]) s rest (by simpa using h) hb (hok.mono _) hs h12
          (by simp; omega) (by simp; omega))
        (fun s rest h hs h12 => by
          have := genE_ok hT2 a sc env (vals ++ [(Nano.V2.den t env).toBitVec, (Nano.V2.den b env).toBitVec]) s rest (by simpa using h) ha (hok.mono _)
            (by simpa using hs) h12 (by simp; omega) (by simp; omega)
          simpa using this)
        (fun s rest h hs h12 => by
          have := genE_ok hT2 e sc env (vals ++ [(Nano.V2.den t env).toBitVec, (if (Nano.V2.den b env).toBitVec.slt (Nano.V2.den a env).toBitVec then 1#64 else 0#64)]) s rest (by simpa using h) he (hok.mono _)
            (by simpa using hs) h12 (by simp; omega) (by simp; omega)
          simpa using this)
        (lts_run _ _ _) hw.1 (by omega) (by simp [selOps, peakOps, SOp.peak, SOp.after] at hW; omega)
        hcode hs h12
      refine ⟨s', x, ?_, kk, c⟩
      have := ite_fin' (test_les (Nano.V2.den a env) (Nano.V2.den b env)) (Nano.V2.den t env) (Nano.V2.den e env)
      simp only [Nano.V2.den]; rw [← this]; exact st
  | .bit o a b, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE, Bool.and_eq_true] at hsc; simp only [Nano.V2.depE] at hW hd
    have hW64 : W < 2 ^ 64 := by have := hs.lo; rw [h12] at this; simp at this; omega
    have := depE_ge b (vals.length + 1) _ hsc.2
    have hw := wf_bit o (vals.length + 2) (by omega)
    simp only [Nano.V2.genE] at h
    obtain ⟨s', x, st, kk, c⟩ := ops_node hT2 hW64
      (fun s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc.1 hok hs h12 (by omega) (by omega))
      (fun s rest h hs h12 => by
        have := genE_ok hT2 b sc env (vals ++ [(Nano.V2.den a env).toBitVec]) s rest (by simpa using h) hsc.2
          (hok.mono _) hs h12 (by simp; omega) (by simp; omega)
        simpa using this)
      (bit_run o _ _ _) hw.1 (by omega) h hs h12
    exact ⟨s', x, by simpa [Nano.V2.den] using st, kk, c⟩
  | .sh l k a, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScE] at hsc; simp only [Nano.V2.depE] at hW hd
    have hW64 : W < 2 ^ 64 := by have := hs.lo; rw [h12] at this; simp at this; omega
    have := depE_ge a vals.length _ hsc
    have hw := wf_sh l k (vals.length + 1) (by omega)
    simp only [Nano.V2.genE] at h
    obtain ⟨s', x, st, kk, c⟩ := ops1_node hT2 hW64
      (fun s rest h hs h12 => genE_ok hT2 a sc env vals s rest h hsc hok hs h12 (by omega) (by omega))
      (sh_run l k _ _) hw.1 (by rw [hw.2]; omega) h hs h12
    exact ⟨s', x, by simpa [Nano.V2.den] using st, kk, c⟩
  | .anil, _, _, _, _, _, _, hsc, _, _, _, _, _ => by simp [ScE] at hsc
  | .acons _ _, _, _, _, _, _, _, hsc, _, _, _, _, _ => by simp [ScE] at hsc
/-- an argument list pushes its values -/
theorem genA_ok (hT2 : T < 2 ^ 64) : ∀ (as : E) (sc : List Nat) (env : List UInt64) (vals : List (BitVec 64)) (s : St)
    (rest : List UInt8), CodeAt P s.pc (Nano.V2.genA sc vals.length as ++ rest) → ScA as env.length = true →
    ScOk sc env vals → Stk s T vals → s.get 12 = BitVec.ofNat 64 W → W + 8 * Nano.V2.depA vals.length as ≤ T →
    Nano.V2.depA vals.length as ≤ 256 →
    ∃ s', Star P s s' ∧ Stk s' T (vals ++ (Nano.V2.denA as env).map UInt64.toBitVec) ∧ Kept s s' ∧ CodeAt P s'.pc rest ∧
      Nano.V2.cnt as = (Nano.V2.denA as env).length
  | .acons e r, sc, env, vals, s, rest, h, hsc, hok, hs, h12, hW, hd => by
    simp only [ScA, Bool.and_eq_true] at hsc; simp only [Nano.V2.depA] at hW hd
    simp only [Nano.V2.genA, List.append_assoc] at h
    obtain ⟨s1, x1, st1, k1, c1⟩ := genE_ok hT2 e sc env vals s _ h hsc.1 hok hs h12 (by omega) (by omega)
    obtain ⟨s2, x2, st2, k2, c2, hc2⟩ := genA_ok hT2 r sc env (vals ++ [(Nano.V2.den e env).toBitVec]) s1 _ (by simpa using c1)
      hsc.2 (hok.mono _) st1 (by rw [k1 12 (by decide) (by decide) (by decide)]; exact h12) (by simp; omega)
      (by simp; omega)
    exact ⟨s2, x1.trans x2, by simpa [Nano.V2.denA] using st2, k1.trans k2, c2, by simp [Nano.V2.cnt, Nano.V2.denA, hc2]⟩
  | .num _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [Nano.V2.denA] using hs, fun _ _ _ _ => rfl,
      by simpa [Nano.V2.genA] using h, rfl⟩
  | .var _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [Nano.V2.denA] using hs, fun _ _ _ _ => rfl,
      by simpa [Nano.V2.genA] using h, rfl⟩
  | .add _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [Nano.V2.denA] using hs, fun _ _ _ _ => rfl,
      by simpa [Nano.V2.genA] using h, rfl⟩
  | .sub _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [Nano.V2.denA] using hs, fun _ _ _ _ => rfl,
      by simpa [Nano.V2.genA] using h, rfl⟩
  | .mul _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [Nano.V2.denA] using hs, fun _ _ _ _ => rfl,
      by simpa [Nano.V2.genA] using h, rfl⟩
  | .let_ _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [Nano.V2.denA] using hs, fun _ _ _ _ => rfl,
      by simpa [Nano.V2.genA] using h, rfl⟩
  | .call _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [Nano.V2.denA] using hs, fun _ _ _ _ => rfl,
      by simpa [Nano.V2.genA] using h, rfl⟩
  | .anil, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [Nano.V2.denA] using hs, fun _ _ _ _ => rfl,
      by simpa [Nano.V2.genA] using h, rfl⟩
  | .ite _ _ _ _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [Nano.V2.denA] using hs,
      fun _ _ _ _ => rfl, by simpa [Nano.V2.genA] using h, rfl⟩
  | .bit _ _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [Nano.V2.denA] using hs,
      fun _ _ _ _ => rfl, by simpa [Nano.V2.genA] using h, rfl⟩
  | .sh _ _ _, _, _, vals, s, rest, h, _, _, hs, _, _, _ => ⟨s, .refl _, by simpa [Nano.V2.denA] using hs,
      fun _ _ _ _ => rfl, by simpa [Nano.V2.genA] using h, rfl⟩
end

end Nano.V2R
