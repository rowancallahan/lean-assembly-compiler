/- Nano/V2Self/Proof/ParInvOps: the node builder `v5` (pop n operands, link them as siblings by `v2`, push the new node) as an
exact cell-level effect, and its consequence on `OpsRep`.  Box C. -/
import Nano.V2Self.Proof.ParInvRep
namespace ParInv
open C BufL ParSpec

/-! ## Nat-level cell access -/
theorem tn_add (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; omega

theorem tn_mul8 (a : UInt64) (h : a.toNat < 2 ^ 60) : (8 * a).toNat = 8 * a.toNat := by
  rw [UInt64.toNat_mul]; simp; omega

theorem bget_bset' (b : Buf) (i j v : UInt64) (h : i.toNat ≠ j.toNat) : bget (bset b i v) j = bget b j :=
  bget_bset_other b i j v h

theorem bget_bset_eq (b : Buf) (i j v : UInt64) (h : i.toNat = j.toNat) (hl : i.toNat < b.length) : bget (bset b i v) j = v := by
  rw [bget_bset]; simp [h, show j.toNat < b.length by omega]

/-- the operand id at stack position `k` -/
def opAt (h : Buf) (k : Nat) : UInt64 := bget h (d3 + k.toUInt64)

theorem d3k (k : Nat) (hk : k < 4096) : (d3 + k.toUInt64).toNat = 12352 + k := by
  rw [tn_add _ _ (by simp [d3v]; omega)]; simp [d3v]; omega

theorem recNext (u : UInt64) (hu : u.toNat < 16384) : (d5 + 8 * u + 7).toNat = 16448 + 8 * u.toNat + 7 := by
  rw [tn_add _ _ (by rw [tn_add _ _ (by rw [tn_mul8 _ (by omega)]; simp [d5v]; omega)]; rw [tn_mul8 _ (by omega)]; simp [d5v]; omega),
    tn_add _ _ (by rw [tn_mul8 _ (by omega)]; simp [d5v]; omega), tn_mul8 _ (by omega)]; simp [d5v]

theorem recK (u k : UInt64) (hu : u.toNat < 16384) (hk : k.toNat < 8) : (d5 + 8 * u + k).toNat = 16448 + 8 * u.toNat + k.toNat := by
  rw [tn_add _ _ (by rw [tn_add _ _ (by rw [tn_mul8 _ (by omega)]; simp [d5v]; omega)]; rw [tn_mul8 _ (by omega)]; simp [d5v]; omega),
    tn_add _ _ (by rw [tn_mul8 _ (by omega)]; simp [d5v]; omega), tn_mul8 _ (by omega)]; simp [d5v]

/-! ## v2: sibling linking -/
/-- `v2 N h j z c` sets next(op[j+k]) := op[j+k+1] for k < c and nothing else (operand ids in the arena, the written ids distinct) -/
theorem v2_eff : ∀ (N : Nat) (h : Buf) (j : Nat) (z c : UInt64), c.toNat < N → j + c.toNat < 4096 → 16448 + 8 * 16384 ≤ h.length →
    (∀ k, k ≤ c.toNat → (opAt h (j + k)).toNat < 16384) →
    ((List.range c.toNat).map fun k => (opAt h (j + k)).toNat).Nodup →
    (v2 N h j.toUInt64 z c).length = h.length ∧
    (∀ i : UInt64, (∀ k, k < c.toNat → i.toNat ≠ 16448 + 8 * (opAt h (j + k)).toNat + 7) → bget (v2 N h j.toUInt64 z c) i = bget h i) ∧
    (∀ k, k < c.toNat → bget (v2 N h j.toUInt64 z c) (d5 + 8 * opAt h (j + k) + 7) = opAt h (j + k + 1))
  | 0, h, j, z, c, hc, hj, hl, ho, hd => absurd hc (by omega)
  | N + 1, h, j, z, c, hc, hj, hl, ho, hd => by
    by_cases c0 : c = 0
    · subst c0; simp [v2]
    · have c1 : 1 ≤ c.toNat := by
        rcases Nat.eq_zero_or_pos c.toNat with e | e
        · exact absurd (UInt64.toNat_inj.mp (by simpa using e)) c0
        · exact e
      have e1 : (j.toUInt64 + 1) = (j + 1).toUInt64 := by simp
      have ec : (c - 1).toNat = c.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
      have hx := ho 0 (by omega)
      simp only [Nat.add_zero] at hx
      have wa : (d5 + 8 * opAt h j + 7).toNat = 16448 + 8 * (opAt h j).toNat + 7 := recNext _ hx
      have hv : v2 (N + 1) h j.toUInt64 z c = v2 N (bset h (d5 + 8 * opAt h j + 7) (opAt h (j + 1))) (j + 1).toUInt64 z (c - 1) := by
        simp only [v2, c0, beq_iff_eq, if_false, opAt, e1]
        congr 2
        simp [UInt64.add_assoc]
      obtain ⟨h1, h1d⟩ : ∃ h1, h1 = bset h (d5 + 8 * opAt h j + 7) (opAt h (j + 1)) := ⟨_, rfl⟩
      rw [← h1d] at hv
      have l1 : h1.length = h.length := by rw [h1d]; exact length_bset _ _ _
      have o1 : ∀ k, k < 4096 → opAt h1 k = opAt h k := by
        intro k hk; simp only [opAt]; rw [h1d, bget_bset' _ _ _ _ (by rw [wa, d3k k hk]; omega)]
      have ho1 : ∀ k, k ≤ (c - 1).toNat → (opAt h1 (j + 1 + k)).toNat < 16384 := by
        intro k hk; rw [o1 _ (by omega), show j + 1 + k = j + (k + 1) by omega]; exact ho _ (by omega)
      have hdl : (List.range c.toNat).map (fun k => (opAt h (j + k)).toNat) =
          (opAt h j).toNat :: (List.range (c.toNat - 1)).map (fun k => (opAt h (j + 1 + k)).toNat) := by
        rw [show c.toNat = c.toNat - 1 + 1 by omega, List.range_succ_eq_map]; simp [Nat.add_comm, Nat.add_left_comm]
      rw [hdl, List.nodup_cons] at hd
      have hd1 : ((List.range (c - 1).toNat).map fun k => (opAt h1 (j + 1 + k)).toNat).Nodup := by
        rw [ec]
        have : (List.range (c.toNat - 1)).map (fun k => (opAt h1 (j + 1 + k)).toNat) =
            (List.range (c.toNat - 1)).map (fun k => (opAt h (j + 1 + k)).toNat) := by
          apply List.map_congr_left; intro k hk; simp at hk; rw [o1 _ (by omega)]
        rw [this]; exact hd.2
      obtain ⟨L, U, W⟩ := v2_eff N h1 (j + 1) z (c - 1) (by omega) (by omega) (by rw [l1]; exact hl) ho1 hd1
      rw [hv]
      refine ⟨by rw [L, l1], ?_, ?_⟩
      · intro i hi
        rw [U i (fun k hk => by rw [o1 _ (by omega), show j + 1 + k = j + (k + 1) by omega]; exact hi _ (by omega)),
          h1d, bget_bset' _ _ _ _ (by rw [wa]; have := hi 0 (by omega); simp at this; omega)]
      · intro k hk
        rcases Nat.eq_zero_or_pos k with k0 | k0
        · subst k0
          simp only [Nat.add_zero]
          rw [U _ (fun k' hk' => by
              rw [wa, o1 _ (by omega)]
              intro e
              apply hd.1
              simp only [List.mem_map, List.mem_range]
              refine ⟨k', by omega, ?_⟩
              omega)]
          rw [h1d]; exact bget_bset_eq _ _ _ _ rfl (by rw [wa]; omega)
        · have := W (k - 1) (by omega)
          rw [o1 _ (by omega), o1 _ (by omega), show j + 1 + (k - 1) = j + k by omega,
            show j + k + 1 = j + 1 + (k - 1) + 1 by omega] at this
          rw [show j + k + 1 = j + 1 + (k - 1) + 1 by omega]
          exact this

/-! ## v5: the node builder -/
/-- `v5 h c a b w t n` (guards passing): node z = h[9] gets fields (c, a, b, w, t, first = op[J], n) with J = h[8] − n, the popped
operands op[J..J+n-1] are linked as siblings, op[J] := z, h[8] := J + 1, h[9] := z + 1; no other cell changes -/
theorem v5_eff (h : Buf) (c a b w t n : UInt64) (hl : 147520 ≤ h.length) (hz : (bget h 9).toNat < 16384)
    (hm : (bget h 8).toNat ≤ 4096) (hn : n.toNat ≤ (bget h 8).toNat) (hJ : (bget h 8).toNat - n.toNat < 4096)
    (hb : ∀ i, i < n.toNat → (opAt h ((bget h 8).toNat - n.toNat + i)).toNat < (bget h 9).toNat)
    (hd : ((List.range n.toNat).map fun i => (opAt h ((bget h 8).toNat - n.toNat + i)).toNat).Nodup) :
    let J := (bget h 8).toNat - n.toNat
    let z := bget h 9
    let h' := v5 h c a b w t n
    h'.length = h.length ∧
    fld h' z 0 = c ∧ fld h' z 1 = a ∧ fld h' z 2 = b ∧ fld h' z 3 = w ∧ fld h' z 4 = t ∧ fld h' z 5 = opAt h J ∧ fld h' z 6 = n ∧
    (∀ i, i + 1 < n.toNat → fld h' (opAt h (J + i)) 7 = opAt h (J + i + 1)) ∧
    opAt h' J = z ∧ bget h' 8 = J.toUInt64 + 1 ∧ bget h' 9 = z + 1 ∧
    (∀ i : UInt64, i.toNat ≠ 8 → i.toNat ≠ 9 → i.toNat ≠ 12352 + J →
      (i.toNat < 16448 + 8 * z.toNat ∨ 16448 + 8 * z.toNat + 7 ≤ i.toNat) →
      (∀ k, k + 1 < n.toNat → i.toNat ≠ 16448 + 8 * (opAt h (J + k)).toNat + 7) → bget h' i = bget h i) := by
  intro J z h'
  have hz' : z.toNat < 16384 := hz
  have hb' : ∀ i, i < n.toNat → (opAt h (J + i)).toNat < z.toNat := hb
  have hJ' : J < 4096 := hJ
  have g1 : bget h 9 < d13 := UInt64.lt_iff_toNat_lt.mpr (by simp [show d13.toNat = 16384 from rfl]; omega)
  have g2 : n < bget h 8 + 1 := UInt64.lt_iff_toNat_lt.mpr (by rw [tn_add _ _ (by simp; omega)]; simp; omega)
  have ej : bget h 8 - n = J.toUInt64 := by
    apply UInt64.toNat_inj.mp; rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hn)]; simp; omega
  have g3 : bget h 8 - n < d4 := by rw [ej]; exact UInt64.lt_iff_toNat_lt.mpr (by simp [show d4.toNat = 4096 from rfl]; omega)
  have eq : ∀ k : UInt64, k.toNat < 8 → (d5 + 8 * z + k).toNat = 16448 + 8 * z.toNat + k.toNat := fun k hk => recK z k hz hk
  have ed : (d3 + J.toUInt64).toNat = 12352 + J := d3k J hJ
  -- the 7 field writes
  obtain ⟨H1, e1⟩ : ∃ H1, H1 = bset (bset (bset (bset (bset (bset (bset h (d5 + 8 * z) c) (d5 + 8 * z + 1) a) (d5 + 8 * z + 2) b)
      (d5 + 8 * z + 3) w) (d5 + 8 * z + 4) t) (d5 + 8 * z + 5) (opAt h J)) (d5 + 8 * z + 6) n := ⟨_, rfl⟩
  have q0 : (d5 + 8 * z).toNat = 16448 + 8 * z.toNat := by have := eq 0 (by decide); simpa using this
  have L1 : H1.length = h.length := by rw [e1]; simp [length_bset]
  have U1 : ∀ i : UInt64, (i.toNat < 16448 + 8 * z.toNat ∨ 16448 + 8 * z.toNat + 7 ≤ i.toNat) → bget H1 i = bget h i := by
    intro i hi
    rw [e1]
    repeat rw [bget_bset' _ _ _ _ (by first | rw [q0]; omega | rw [eq _ (by decide)]; simp; omega)]
  have F1 : ∀ k : UInt64, k.toNat < 7 → fld H1 z k = [c, a, b, w, t, opAt h J, n].getD k.toNat 0 := by
    intro k hk
    have hk' : k.toNat = 0 ∨ k.toNat = 1 ∨ k.toNat = 2 ∨ k.toNat = 3 ∨ k.toNat = 4 ∨ k.toNat = 5 ∨ k.toNat = 6 := by omega
    have ek := eq k (by omega)
    simp only [fld]; rw [e1]
    rcases hk' with e | e | e | e | e | e | e <;> simp only [e, List.getD_cons_succ, List.getD_cons_zero] <;>
      repeat (first
        | rw [bget_bset_eq _ _ _ _ (by first | rw [q0, ek]; omega | rw [ek, eq _ (by decide)]; simp; omega)
            (by (try simp only [length_bset]); first | rw [q0]; omega | rw [eq _ (by decide)]; simp; omega)]
        | rw [bget_bset' _ _ _ _ (by first | rw [q0, ek]; omega | rw [ek, eq _ (by decide)]; simp; omega)])
  have O1 : ∀ k, k < 4096 → opAt H1 k = opAt h k := fun k hk => U1 _ (Or.inl (by rw [d3k k hk]; omega))
  -- the sibling links
  obtain ⟨H2, e2⟩ : ∃ H2, H2 = (if n == 0 then H1 else v2 16777216 H1 J.toUInt64 z (n - 1)) := ⟨_, rfl⟩
  have P2 : H2.length = h.length ∧
      (∀ i : UInt64, (∀ k, k + 1 < n.toNat → i.toNat ≠ 16448 + 8 * (opAt h (J + k)).toNat + 7) → bget H2 i = bget H1 i) ∧
      (∀ k, k + 1 < n.toNat → bget H2 (d5 + 8 * opAt h (J + k) + 7) = opAt h (J + k + 1)) := by
    by_cases n0 : n = 0
    · subst n0; simp [e2, L1]
    · have n1 : 1 ≤ n.toNat := by
        rcases Nat.eq_zero_or_pos n.toNat with e | e
        · exact absurd (UInt64.toNat_inj.mp (by simpa using e)) n0
        · exact e
      have en : (n - 1).toNat = n.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
      have hd' : ((List.range (n - 1).toNat).map fun k => (opAt H1 (J + k)).toNat).Nodup := by
        rw [en]
        have : (List.range (n.toNat - 1)).map (fun k => (opAt H1 (J + k)).toNat) =
            ((List.range n.toNat).map fun i => (opAt h ((bget h 8).toNat - n.toNat + i)).toNat).take (n.toNat - 1) := by
          rw [← List.map_take, List.take_range]; simp only [Nat.min_eq_left (Nat.sub_le _ _)]
          apply List.map_congr_left; intro k hk; simp at hk; rw [O1 _ (by omega)]
        rw [this]; exact hd.sublist (List.take_sublist _ _)
      obtain ⟨L, U, W⟩ := v2_eff 16777216 H1 J z (n - 1) (by rw [en]; omega) (by rw [en]; omega) (by rw [L1]; omega)
        (fun k hk => by rw [en] at hk; rw [O1 _ (by omega)]; have := hb' k (by omega); omega) hd'
      have e2' : H2 = v2 16777216 H1 J.toUInt64 z (n - 1) := by rw [e2]; simp [n0]
      rw [e2']
      refine ⟨by rw [L, L1], fun i hi => U i (fun k hk => by rw [en] at hk; rw [O1 _ (by omega)]; exact hi k (by omega)),
        fun k hk => ?_⟩
      have := W k (by rw [en]; omega)
      rw [O1 _ (by omega), O1 _ (by omega)] at this; exact this
  obtain ⟨L2, U2, W2⟩ := P2
  have hv : h' = bset (bset (bset H2 (d3 + J.toUInt64) z) 8 (J.toUInt64 + 1)) 9 (z + 1) := by
    show v5 h c a b w t n = _
    unfold v5
    have g3' : J.toUInt64 < d4 := by rw [← ej]; exact g3
    simp only [g1, g2, ej, g3', if_true, e2, e1]
    rfl
  have l2 : 147520 ≤ H2.length := by omega
  have top : ∀ i : UInt64, i.toNat ≠ 8 → i.toNat ≠ 9 → i.toNat ≠ 12352 + J → bget h' i = bget H2 i := by
    intro i a1 a2 a3
    rw [hv, bget_bset' _ _ _ _ (by simp; omega), bget_bset' _ _ _ _ (by simp; omega), bget_bset' _ _ _ _ (by rw [ed]; omega)]
  have fz : ∀ k : UInt64, k.toNat < 7 → fld h' z k = [c, a, b, w, t, opAt h J, n].getD k.toNat 0 := by
    intro k hk
    have ek := eq k (by omega)
    simp only [fld] at F1 ⊢
    rw [top _ (by omega) (by omega) (by omega), U2 _ (fun k' hk' => by have := hb' k' (by omega); omega)]
    exact F1 k hk
  refine ⟨by rw [hv]; simp only [length_bset]; exact L2, fz 0 (by decide), fz 1 (by decide), fz 2 (by decide), fz 3 (by decide),
    fz 4 (by decide), fz 5 (by decide), fz 6 (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hx := hb' i (by omega)
    simp only [fld]
    rw [top _ (by rw [recNext _ (by omega)]; omega) (by rw [recNext _ (by omega)]; omega) (by rw [recNext _ (by omega)]; omega)]
    exact W2 i hi
  · simp only [opAt]
    rw [hv, bget_bset' _ _ _ _ (by rw [ed]; have : (9:UInt64).toNat = 9 := rfl; omega),
      bget_bset' _ _ _ _ (by rw [ed]; have : (8:UInt64).toNat = 8 := rfl; omega)]
    exact bget_bset_eq _ _ _ _ rfl (by rw [ed]; omega)
  · rw [hv, bget_bset' _ _ _ _ (by simp)]
    exact bget_bset_eq _ _ _ _ rfl (by simp only [length_bset]; simp; omega)
  · rw [hv]; exact bget_bset_eq _ _ _ _ rfl (by simp only [length_bset]; simp; omega)
  · intro i a1 a2 a3 a4 a5
    rw [top i a1 a2 a3, U2 i a5, U1 i a4]

end ParInv
