/- Astra-11 PROBE 1 (parser): a scoped `let` around a provisional self-call, in Par1 (Nano/V2Self/C/Par1.lean).
Task 12 (`v118`) finishes `let x := v; body`: it restores the binding depth h[4] to the depth saved by task 11 (`v116`),
so `x` goes out of scope, and builds the LET node (tag 5) whose PENDING bit (field 4: "contains a provisional
self-call") is the body's.  A provisional self-call (CONTINUE, pending = 1) inside a let body therefore stays
visible to FINISH, and the binding is dropped.  Heap layout: h[8] operand depth, h[9] node count, operand ids at
d3 + k, node records of 8 words at d5 + 8·id (tag, payload1, payload2, shape, pending, first child, count, next). -/
import Nano.V2Self.C.Par1
import Nano.V2Self.Proof.BufL

namespace ParLet
open BufL C

theorem d3v : d3 = 12352 := rfl
theorem d5v : d5 = 16448 := rfl

/-- operand-stack entries are node ids inside the arena (needed: v2/v5 index the arena with them) -/
def OpsOK (h : Buf) : Prop := ∀ k : UInt64, k.toNat < 4096 → (bget h (12352 + k)).toNat < 16384

theorem toNat_add_small (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; omega

theorem bget_bset_ne (b : Buf) (i j v : UInt64) (h : i.toNat ≠ j.toNat) : bget (bset b i v) j = bget b j :=
  bget_bset_other b i j v h

theorem v2_succ (n : Nat) (h : Buf) (j z c : UInt64) (hc : c ≠ 0) :
    v2 (n + 1) h j z c = v2 n (bset h (16448 + 8 * bget h (12352 + j) + 7) (bget h (12352 + j + 1))) (j + 1) z (c - 1) := by
  simp [v2, hc, d3v, d5v]

/-- the sibling linker writes only arena cells (≥ d5): low cells and the operand stack are unchanged -/
theorem v2_low : ∀ (n : Nat) (h : Buf) (j z c : UInt64), OpsOK h → j.toNat + c.toNat < 4096 →
    (∀ i : UInt64, 1 ≤ i.toNat → (i.toNat < 16448 ∨ i.toNat % 8 ≠ 7) → bget (v2 n h j z c) i = bget h i) ∧ OpsOK (v2 n h j z c)
  | 0, h, j, z, c, ho, hj => by
    simp only [v2]
    refine ⟨fun i i1 _ => bget_bset_ne _ _ _ _ (by simp; omega), fun k hk => ?_⟩
    rw [bget_bset_ne _ _ _ _ (by rw [toNat_add_small _ _ (by simp; omega)]; simp; omega)]; exact ho k hk
  | n + 1, h, j, z, c, ho, hj => by
    by_cases hc : c = 0
    · subst hc; simp [v2]; exact ho
    · rw [v2_succ n h j z c hc]
      have hc1 : 1 ≤ c.toNat := by
        rcases Nat.eq_zero_or_pos c.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hc
        · exact h0
      have hx := ho j (by omega)
      have hxa : (16448 + 8 * bget h (12352 + j) + 7 : UInt64).toNat = 16448 + 8 * (bget h (12352 + j)).toNat + 7 := by
        rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
      have low1 : ∀ i : UInt64, (i.toNat < 16448 ∨ i.toNat % 8 ≠ 7) →
          bget (bset h (16448 + 8 * bget h (12352 + j) + 7) (bget h (12352 + j + 1))) i = bget h i := by
        intro i hi; exact bget_bset_ne _ _ _ _ (by rw [hxa]; omega)
      have o1 : OpsOK (bset h (16448 + 8 * bget h (12352 + j) + 7) (bget h (12352 + j + 1))) := by
        intro k hk; rw [low1 _ (Or.inl (by rw [toNat_add_small _ _ (by simp; omega)]; simp; omega))]; exact ho k hk
      have hj1 : (j + 1).toNat + (c - 1).toNat < 4096 := by
        rw [toNat_add_small _ _ (by simp; omega), UInt64.toNat_sub_of_le _ _ (by simpa using hc1)]; simp; omega
      obtain ⟨l, o⟩ := v2_low n _ (j + 1) z (c - 1) o1 hj1
      exact ⟨fun i i1 i2 => by rw [l i i1 i2, low1 i i2], o⟩

/-- the node-capacity guard of v5 (`h[9] < d13 = 16384`) keeps the 8-word record addresses far below 2^64 -/
theorem zN (z : UInt64) (hz : z < d13) : (8 * z + 7 : UInt64).toNat < 131072 := by
  have h1 := UInt64.lt_iff_toNat_lt.mp hz
  have e : d13.toNat = 16384 := rfl
  rw [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega

/-- the node builder v5 leaves the low cells (status 1–7, 10…, the binding table below the operand stack) alone -/
theorem v5_low (h : Buf) (c a b w t n : UInt64) (ho : OpsOK h) (hN : (bget h 8).toNat ≤ 4096) :
    ∀ i : UInt64, 1 ≤ i.toNat → i.toNat < 12352 → i.toNat ≠ 8 → i.toNat ≠ 9 → bget (v5 h c a b w t n) i = bget h i := by
  intro i i1 i2 i8 i9
  unfold v5
  simp only [d3v, d5v, show d6 = 131072 from rfl, show d4 = 4096 from rfl]
  split
  · split
    · split
      · rename_i hz hn hj
        have hzN : (8 * bget h 9 + 7 : UInt64).toNat < 131072 := zN _ hz
        have h8z : (8 * bget h 9).toNat + 7 < 131072 := by
          rw [UInt64.toNat_add, UInt64.toNat_mul] at hzN; rw [UInt64.toNat_mul]; simp at *; omega
        have c16 : (16448 : UInt64).toNat = 16448 := rfl
        have qe : (16448 + 8 * bget h 9 : UInt64).toNat = 16448 + (8 * bget h 9).toNat :=
          toNat_add_small _ _ (by rw [c16]; omega)
        have q0 : (16448 + 8 * bget h 9 : UInt64).toNat ≥ 16448 := by rw [qe]; omega
        have qk : ∀ k : UInt64, k.toNat ≤ 6 → (16448 + 8 * bget h 9 + k : UInt64).toNat ≥ 16448 := by
          intro k hk; rw [toNat_add_small _ _ (by rw [qe]; omega), qe]; omega
        have hjN : (bget h 8 - n).toNat < 4096 := UInt64.lt_iff_toNat_lt.mp hj
        have hjd : (12352 + (bget h 8 - n) : UInt64).toNat = 12352 + (bget h 8 - n).toNat := toNat_add_small _ _ (by simp; omega)
        rw [bget_bset_ne _ _ _ _ (by simp; omega), bget_bset_ne _ _ _ _ (by simp; omega),
          bget_bset_ne _ _ _ _ (by rw [hjd]; omega)]
        have w7 : ∀ i : UInt64, i.toNat < 16448 → bget (bset (bset (bset (bset (bset (bset (bset h (16448 + 8 * bget h 9) c)
            (16448 + 8 * bget h 9 + 1) a) (16448 + 8 * bget h 9 + 2) b) (16448 + 8 * bget h 9 + 3) w)
            (16448 + 8 * bget h 9 + 4) t) (16448 + 8 * bget h 9 + 5) (bget h (12352 + (bget h 8 - n))))
            (16448 + 8 * bget h 9 + 6) n) i = bget h i := by
          intro i hi
          have q1 := qk 1 (by decide); have q2 := qk 2 (by decide)
          have q3 := qk 3 (by decide); have q4 := qk 4 (by decide); have q5 := qk 5 (by decide); have q6 := qk 6 (by decide)
          rw [bget_bset_ne _ _ _ _ (by omega), bget_bset_ne _ _ _ _ (by omega), bget_bset_ne _ _ _ _ (by omega),
            bget_bset_ne _ _ _ _ (by omega), bget_bset_ne _ _ _ _ (by omega), bget_bset_ne _ _ _ _ (by omega),
            bget_bset_ne _ _ _ _ (by omega)]
        split
        · exact w7 i (by omega)
        · rename_i hn0
          have n0 : n.toNat ≠ 0 := by
            intro h0; apply hn0; simp [UInt64.toNat_inj.mp (show n.toNat = (0:UInt64).toNat by simpa using h0)]
          have hnN : n.toNat ≤ (bget h 8).toNat := by
            have := UInt64.lt_iff_toNat_lt.mp hn
            rw [toNat_add_small _ _ (by simp; omega)] at this; simp at this; omega
          have hb : (bget h 8 - n).toNat + (n - 1).toNat < 4096 := by
            rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hnN),
              UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
          rw [(v2_low 16777216 _ _ _ _ (fun k hk => by
              rw [w7 _ (by rw [toNat_add_small _ _ (by simp; omega)]; simp; omega)]; exact ho k hk)
              hb).1 i i1 (Or.inl (by omega)), w7 i (by omega)]
      · exact bget_bset_ne _ _ _ _ (by simp; omega)
    · exact bget_bset_ne _ _ _ _ (by simp; omega)
  · exact bget_bset_ne _ _ _ _ (by simp; omega)

theorem OpsOK_low' (h h' : Buf) (ho : OpsOK h) (e : ∀ i : UInt64, i.toNat < 16448 → bget h' i = bget h i) :
    OpsOK h' := fun k hk => by
  rw [e _ (by rw [toNat_add_small _ _ (by simp; omega)]; simp; omega)]; exact ho k hk

/-- the node builder's PENDING field: on success, node h[9] gets pending bit `t` (field 4) and tag `c` (field 0) -/
theorem v5_fields (h : Buf) (c a b w t n : UInt64) (ho : OpsOK h) (hN : (bget h 8).toNat ≤ 4096)
    (hl : 147520 ≤ h.length) (hz : bget h 9 < d13) (hn : n < bget h 8 + 1) (hj : bget h 8 - n < 4096) :
    bget (v5 h c a b w t n) (16448 + 8 * bget h 9 + 4) = t ∧ bget (v5 h c a b w t n) (16448 + 8 * bget h 9) = c := by
  unfold v5
  simp only [d3v, d5v, show d6 = 131072 from rfl, show d4 = 4096 from rfl, hz, hn, hj, if_true]
  have hzN : (8 * bget h 9 + 7 : UInt64).toNat < 131072 := zN _ hz
  have h8z : (8 * bget h 9).toNat + 7 < 131072 := by
    rw [UInt64.toNat_add, UInt64.toNat_mul] at hzN; rw [UInt64.toNat_mul]; simp at *; omega
  have c16 : (16448 : UInt64).toNat = 16448 := rfl
  have qe : (16448 + 8 * bget h 9 : UInt64).toNat = 16448 + (8 * bget h 9).toNat :=
    toNat_add_small _ _ (by rw [c16]; omega)
  have m8 : (8 * bget h 9).toNat % 8 = 0 := by rw [UInt64.toNat_mul]; simp
  have qk : ∀ k : UInt64, k.toNat ≤ 6 → (16448 + 8 * bget h 9 + k : UInt64).toNat = 16448 + (8 * bget h 9).toNat + k.toNat := by
    intro k hk; rw [toNat_add_small _ _ (by rw [qe]; omega), qe]
  have q4 := qk 4 (by decide); have q5 := qk 5 (by decide); have q6 := qk 6 (by decide)
  simp only [show (4 : UInt64).toNat = 4 from rfl, show (5 : UInt64).toNat = 5 from rfl, show (6 : UInt64).toNat = 6 from rfl] at q4 q5 q6
  have hjN : (bget h 8 - n).toNat < 4096 := UInt64.lt_iff_toNat_lt.mp hj
  have hjd : (12352 + (bget h 8 - n) : UInt64).toNat = 12352 + (bget h 8 - n).toNat := toNat_add_small _ _ (by simp; omega)
  -- the seven field writes
  generalize hH : bset (bset (bset (bset (bset (bset (bset h (16448 + 8 * bget h 9) c)
      (16448 + 8 * bget h 9 + 1) a) (16448 + 8 * bget h 9 + 2) b) (16448 + 8 * bget h 9 + 3) w)
      (16448 + 8 * bget h 9 + 4) t) (16448 + 8 * bget h 9 + 5) (bget h (12352 + (bget h 8 - n))))
      (16448 + 8 * bget h 9 + 6) n = H
  have L : ∀ (b' : Buf) (i v : UInt64), (bset b' i v).length = b'.length := fun _ _ _ => length_bset _ _ _
  have HL : 147520 ≤ H.length := by rw [← hH]; simp only [L]; exact hl
  have H4 : bget H (16448 + 8 * bget h 9 + 4) = t := by
    rw [← hH, bget_bset_ne _ _ _ _ (by omega), bget_bset_ne _ _ _ _ (by omega)]
    exact bget_bset_same _ _ _ (by simp only [L]; omega)
  have H0 : bget H (16448 + 8 * bget h 9) = c := by
    have q1 := qk 1 (by decide); have q2 := qk 2 (by decide); have q3 := qk 3 (by decide)
    simp only [show (1 : UInt64).toNat = 1 from rfl, show (2 : UInt64).toNat = 2 from rfl,
      show (3 : UInt64).toNat = 3 from rfl] at q1 q2 q3
    rw [← hH]
    repeat rw [bget_bset_ne _ _ _ _ (by omega)]
    exact bget_bset_same _ _ _ (by omega)
  have Hlow : ∀ i : UInt64, i.toNat < 16448 → bget H i = bget h i := by
    intro i hi; rw [← hH]
    have q1 := qk 1 (by decide); have q2 := qk 2 (by decide); have q3 := qk 3 (by decide)
    simp only [show (1 : UInt64).toNat = 1 from rfl, show (2 : UInt64).toNat = 2 from rfl,
      show (3 : UInt64).toNat = 3 from rfl] at q1 q2 q3
    repeat rw [bget_bset_ne _ _ _ _ (by omega)]
  have oH : OpsOK H := OpsOK_low' h H ho Hlow
  constructor
  · rw [bget_bset_ne _ _ _ _ (by simp; omega), bget_bset_ne _ _ _ _ (by simp; omega),
      bget_bset_ne _ _ _ _ (by rw [hjd]; omega)]
    split
    · exact H4
    · rename_i hn0
      have n0 : n.toNat ≠ 0 := by
        intro h0; apply hn0; simp [UInt64.toNat_inj.mp (show n.toNat = (0:UInt64).toNat by simpa using h0)]
      have hnN : n.toNat ≤ (bget h 8).toNat := by
        have := UInt64.lt_iff_toNat_lt.mp hn
        rw [toNat_add_small _ _ (by simp; omega)] at this; simp at this; omega
      have hb : (bget h 8 - n).toNat + (n - 1).toNat < 4096 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hnN),
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
      rw [(v2_low 16777216 H _ _ _ oH hb).1 _ (by omega) (Or.inr (by omega))]; exact H4
  · rw [bget_bset_ne _ _ _ _ (by rw [qe, show (9:UInt64).toNat = 9 from rfl]; omega),
      bget_bset_ne _ _ _ _ (by rw [qe, show (8:UInt64).toNat = 8 from rfl]; omega),
      bget_bset_ne _ _ _ _ (by rw [hjd, qe]; omega)]
    split
    · exact H0
    · rename_i hn0
      have n0 : n.toNat ≠ 0 := by
        intro h0; apply hn0; simp [UInt64.toNat_inj.mp (show n.toNat = (0:UInt64).toNat by simpa using h0)]
      have hnN : n.toNat ≤ (bget h 8).toNat := by
        have := UInt64.lt_iff_toNat_lt.mp hn
        rw [toNat_add_small _ _ (by simp; omega)] at this; simp at this; omega
      have hb : (bget h 8 - n).toNat + (n - 1).toNat < 4096 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hnN),
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
      rw [(v2_low 16777216 H _ _ _ oH hb).1 _ (by omega) (Or.inr (by omega))]; exact H0

theorem OpsOK_low (h h' : Buf) (ho : OpsOK h) (e : ∀ i : UInt64, 12352 ≤ i.toNat → i.toNat < 16448 → bget h' i = bget h i) :
    OpsOK h' := fun k hk => by
  rw [e _ (by rw [toNat_add_small _ _ (by simp; omega)]; simp) (by rw [toNat_add_small _ _ (by simp; omega)]; simp; omega)]
  exact ho k hk

/-- **scope**: after task 12 (`v118`, finish LET) the binding depth h[4] is the depth `b` saved by task 11 before
the binder was installed, so the let-bound name is out of scope (lookups `v7` scan only the first h[4] bindings) -/
theorem v118_scope (h : Buf) (a b : UInt64) (ho : OpsOK h) (hN : (bget h 8).toNat ≤ 4096) (hl : 5 ≤ h.length) :
    bget (v118 h a b) 4 = b := by
  unfold v118 v9
  simp only []
  generalize (if bget h (d5 + 8 * bget h (d3 + bget h 8 - 2) + 3) < 5 then (1 : UInt64)
      else bget h (d7 + 8192 + 3 * (bget h (d5 + 8 * bget h (d3 + bget h 8 - 2) + 3) - 5) + 2)) = v
  have e : ∀ i : UInt64, 12352 ≤ i.toNat → bget (bset (bset h 31 v) 4 b) i = bget h i := by
    intro i hi; rw [bget_bset_ne _ _ _ _ (by simp; omega), bget_bset_ne _ _ _ _ (by simp; omega)]
  have o2 : OpsOK (bset (bset h 31 v) 4 b) := OpsOK_low h _ ho (fun i h1 _ => e i h1)
  have n2 : (bget (bset (bset h 31 v) 4 b) 8).toNat ≤ 4096 := by
    rw [bget_bset_ne _ _ _ _ (by simp), bget_bset_ne _ _ _ _ (by simp)]; exact hN
  rw [v5_low _ _ _ _ _ _ _ o2 n2 4 (by simp) (by simp) (by simp) (by simp)]
  exact bget_bset_same _ _ _ (by simp [bset]; omega)

/-- **pending propagation**: when task 12 succeeds in building the node, the new LET node (id h[9]) has tag 5 and
the body's PENDING bit — a provisional self-call (CONTINUE) in the body stays marked for FINISH (task 80), which
accepts it only in tail position of a fuel def -/
theorem v118_pending (h : Buf) (a b : UInt64) (ho : OpsOK h) (hN : (bget h 8).toNat ≤ 4096) (hl : 147520 ≤ h.length)
    (hz : bget h 9 < d13) (hn : (2 : UInt64) < bget h 8 + 1) (hj : bget h 8 - 2 < 4096) :
    bget (v118 h a b) (16448 + 8 * bget h 9 + 4) = bget h (16448 + 8 * bget h (12352 + bget h 8 - 1) + 4) ∧
    bget (v118 h a b) (16448 + 8 * bget h 9) = 5 := by
  unfold v118 v9
  simp only [d3v, d5v]
  generalize (if bget h (16448 + 8 * bget h (12352 + bget h 8 - 2) + 3) < 5 then (1 : UInt64)
      else bget h (d7 + 8192 + 3 * (bget h (16448 + 8 * bget h (12352 + bget h 8 - 2) + 3) - 5) + 2)) = v
  have e : ∀ i : UInt64, i.toNat ≠ 31 → i.toNat ≠ 4 → bget (bset (bset h 31 v) 4 b) i = bget h i := by
    intro i h1 h2; rw [bget_bset_ne _ _ _ _ (by simp; omega), bget_bset_ne _ _ _ _ (by simp; omega)]
  have o2 : OpsOK (bset (bset h 31 v) 4 b) := OpsOK_low h _ ho (fun i h1 _ => e i (by omega) (by omega))
  have e8 := e 8 (by simp) (by simp); have e9 := e 9 (by simp) (by simp)
  have L : (bset (bset h 31 v) 4 b).length = h.length := by simp [length_bset]
  have := v5_fields (bset (bset h 31 v) 4 b) 5 a (bget (bset h 31 v) 31) (bget h (16448 + 8 * bget h (12352 + bget h 8 - 1) + 3))
    (bget h (16448 + 8 * bget h (12352 + bget h 8 - 1) + 4)) 2 o2 (by rw [e8]; exact hN) (by rw [L]; exact hl)
    (by rw [e9]; exact hz) (by rw [e8]; exact hn) (by rw [e8]; exact hj)
  rw [e9] at this
  exact this

end ParLet
