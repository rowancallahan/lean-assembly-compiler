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

theorem d3k (k : Nat) (hk : k < 4096) : (d3 + k.toUInt64).toNat = 12352 + k := by
  rw [tn_add _ _ (by simp [d3v]; omega)]; simp [d3v]; omega

theorem recNext (u : UInt64) (hu : u.toNat < 16384) : (d5 + 8 * u + 7).toNat = 16448 + 8 * u.toNat + 7 := by
  rw [tn_add _ _ (by rw [tn_add _ _ (by rw [tn_mul8 _ (by omega)]; simp [d5v]; omega)]; rw [tn_mul8 _ (by omega)]; simp [d5v]; omega),
    tn_add _ _ (by rw [tn_mul8 _ (by omega)]; simp [d5v]; omega), tn_mul8 _ (by omega)]; simp [d5v]

theorem recK (u k : UInt64) (hu : u.toNat < 16384) (hk : k.toNat < 8) : (d5 + 8 * u + k).toNat = 16448 + 8 * u.toNat + k.toNat := by
  rw [tn_add _ _ (by rw [tn_add _ _ (by rw [tn_mul8 _ (by omega)]; simp [d5v]; omega)]; rw [tn_mul8 _ (by omega)]; simp [d5v]; omega),
    tn_add _ _ (by rw [tn_mul8 _ (by omega)]; simp [d5v]; omega), tn_mul8 _ (by omega)]; simp [d5v]

theorem drop_bset0 (h : Buf) (i v : UInt64) (hi : i.toNat < 184384) : (bset h i v).drop 184384 = h.drop 184384 := by
  simp only [bset]; exact List.drop_set_of_lt hi

/-! ## v2: sibling linking -/
/-- `v2 N h j z c` sets next(op[j+k]) := op[j+k+1] for k < c and nothing else (operand ids in the arena, the written ids distinct) -/
theorem v2_eff : ∀ (N : Nat) (h : Buf) (j : Nat) (z c : UInt64), c.toNat < N → j + c.toNat < 4096 → 16448 + 8 * 16384 ≤ h.length →
    (∀ k, k ≤ c.toNat → (opAt h (j + k)).toNat < 16384) →
    ((List.range c.toNat).map fun k => (opAt h (j + k)).toNat).Nodup →
    (v2 N h j.toUInt64 z c).length = h.length ∧
    (∀ i : UInt64, (∀ k, k < c.toNat → i.toNat ≠ 16448 + 8 * (opAt h (j + k)).toNat + 7) → bget (v2 N h j.toUInt64 z c) i = bget h i) ∧
    (∀ k, k < c.toNat → bget (v2 N h j.toUInt64 z c) (d5 + 8 * opAt h (j + k) + 7) = opAt h (j + k + 1)) ∧
    (v2 N h j.toUInt64 z c).drop 184384 = h.drop 184384
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
      obtain ⟨L, U, W, D⟩ := v2_eff N h1 (j + 1) z (c - 1) (by omega) (by omega) (by rw [l1]; exact hl) ho1 hd1
      rw [hv]
      refine ⟨by rw [L, l1], ?_, ?_, by rw [D, h1d, drop_bset0 _ _ _ (by rw [wa]; omega)]⟩
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
      (∀ k, k + 1 < n.toNat → i.toNat ≠ 16448 + 8 * (opAt h (J + k)).toNat + 7) → bget h' i = bget h i) ∧
    h'.drop 184384 = h.drop 184384 := by
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
      (∀ k, k + 1 < n.toNat → bget H2 (d5 + 8 * opAt h (J + k) + 7) = opAt h (J + k + 1)) ∧
      H2.drop 184384 = H1.drop 184384 := by
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
      obtain ⟨L, U, W, D⟩ := v2_eff 16777216 H1 J z (n - 1) (by rw [en]; omega) (by rw [en]; omega) (by rw [L1]; omega)
        (fun k hk => by rw [en] at hk; rw [O1 _ (by omega)]; have := hb' k (by omega); omega) hd'
      have e2' : H2 = v2 16777216 H1 J.toUInt64 z (n - 1) := by rw [e2]; simp [n0]
      rw [e2']
      refine ⟨by rw [L, L1], fun i hi => U i (fun k hk => by rw [en] at hk; rw [O1 _ (by omega)]; exact hi k (by omega)),
        fun k hk => ?_, D⟩
      have := W k (by rw [en]; omega)
      rw [O1 _ (by omega), O1 _ (by omega)] at this; exact this
  obtain ⟨L2, U2, W2, D2⟩ := P2
  have D1 : H1.drop 184384 = h.drop 184384 := by
    rw [e1]
    repeat rw [drop_bset0 _ _ _ (by first | rw [q0]; omega | rw [eq _ (by decide)]; simp; omega)]
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
    fz 4 (by decide), fz 5 (by decide), fz 6 (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rw [hv, drop_bset0 _ _ _ (by decide), drop_bset0 _ _ _ (by decide), drop_bset0 _ _ _ (by rw [ed]; omega), D2, D1]

/-! ## list helpers -/
theorem mem_getD_flat {α : Type} : ∀ (L : List (List α)) (i : Nat) (x : α), x ∈ L.getD i [] → x ∈ L.flatten
  | [], i, x, hx => by simp at hx
  | a :: L, 0, x, hx => by simp at hx; simp [hx]
  | a :: L, i + 1, x, hx => by simp only [List.getD_cons_succ] at hx; simp only [List.flatten_cons, List.mem_append]; exact Or.inr (mem_getD_flat L i x hx)

theorem flat_disj {α : Type} : ∀ (L : List (List α)), L.flatten.Nodup → ∀ i j, i < j → ∀ x, x ∈ L.getD i [] → x ∈ L.getD j [] → False
  | [], _, _, _, _, _, hx, _ => by simp at hx
  | a :: L, hn, 0, j + 1, _, x, hx, hy => by
    rw [List.flatten_cons, List.nodup_append] at hn
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hx hy
    exact hn.2.2 x hx x (mem_getD_flat L j x hy) rfl
  | a :: L, hn, i + 1, j + 1, hij, x, hx, hy => by
    rw [List.flatten_cons, List.nodup_append] at hn
    simp only [List.getD_cons_succ] at hx hy
    exact flat_disj L hn.2.1 i j (by omega) x hx hy

theorem getD_eq {α : Type} (l : List α) (i : Nat) (d : α) (hi : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem nodup_getD {α : Type} : ∀ (L : List (List α)) (i : Nat), L.flatten.Nodup → (L.getD i []).Nodup
  | [], i, _ => by simp
  | a :: L, 0, hn => by rw [List.flatten_cons, List.nodup_append] at hn; simpa using hn.1
  | a :: L, i + 1, hn => by rw [List.flatten_cons, List.nodup_append] at hn; simpa using nodup_getD L i hn.2.1

theorem getD_rev_take {α : Type} (L : List (List α)) (n r : Nat) (hn : n ≤ L.length) (hr : r < n) :
    (L.take n).reverse.getD r [] = L.getD (n - 1 - r) [] := by
  rw [getD_eq _ _ _ (by simp; omega), getD_eq _ _ _ (by omega), List.getElem_reverse, List.getElem_take]
  congr 1; simp; omega

theorem getD_drop {α : Type} (L : List (List α)) (n i : Nat) : (L.drop n).getD i [] = L.getD (n + i) [] := by
  simp [List.getD_eq_getElem?_getD]

/-! ## child chains of Layer-2 trees -/
theorem kidsR_chain (h : Buf) : ∀ (ns : List ParRun.RN) (f : Nat → UInt64) (Is : Nat → List UInt64),
    (∀ i, i + 1 < ns.length → fld h (f i) 7 = f (i + 1)) →
    (∀ i (hi : i < ns.length), RNRep h (f i) (ns[i]'hi) (Is i)) →
    KidsR h (f 0) ns ((List.range ns.length).map Is).flatten
  | [], _, _, _, _ => by simp; exact .nil
  | n :: ns, f, Is, hk, hv => by
    have ih := kidsR_chain h ns (fun i => f (i + 1)) (fun i => Is (i + 1))
      (fun i hi => hk (i + 1) (by simp; omega)) (fun i hi => hv (i + 1) (by simp; omega))
    have nx : KidsR h (fld h (f 0) 7) ns ((List.range ns.length).map fun i => Is (i + 1)).flatten := by
      cases ns with
      | nil => simp; exact .nil
      | cons _ _ => rw [hk 0 (by simp)]; exact ih
    have e : (List.range (n :: ns).length).map Is = Is 0 :: (List.range ns.length).map fun i => Is (i + 1) := by
      simp [List.range_succ_eq_map]
    rw [e, List.flatten_cons]
    exact .cons (hv 0 (by simp)) nx

theorem nodup_flat_range (Is : Nat → List UInt64) : ∀ (m : Nat), (∀ i, i < m → (Is i).Nodup) →
    (∀ i j, i < m → j < m → i ≠ j → ∀ v, v ∈ Is i → v ∉ Is j) → ((List.range m).map Is).flatten.Nodup
  | 0, _, _ => by simp
  | m + 1, hn, hd => by
    rw [List.range_succ, List.map_append, List.flatten_append, List.nodup_append]
    refine ⟨nodup_flat_range Is m (fun i hi => hn i (by omega)) (fun i j hi hj => hd i j (by omega) (by omega)), by simpa using hn m (by omega), ?_⟩
    intro a ha b hb e
    subst e
    simp only [List.mem_flatten, List.mem_map, List.mem_range] at ha
    obtain ⟨l, ⟨i, hi, rfl⟩, hl⟩ := ha
    simp at hb
    exact hd i m (by omega) (by omega) (by omega) a hl hb

theorem mem_flat_range {Is : Nat → List UInt64} {m : Nat} {v : UInt64} (h : v ∈ ((List.range m).map Is).flatten) :
    ∃ i, i < m ∧ v ∈ Is i := by
  simp only [List.mem_flatten, List.mem_map, List.mem_range] at h
  obtain ⟨l, ⟨i, hi, rfl⟩, hl⟩ := h
  exact ⟨i, hi, hl⟩

/-! ## B's `mkNode` is `v5` -/
open ParRun in
/-- **node builder**: `v5` with the fields of a Layer-2 node realises `mkNode` on the arena representation -/
theorem arena_v5 (h : Buf) (arena vals : List RN) (n : Nat) (t A B : Nat) (sh : Option Sh) (p : Bool) (w : UInt64)
    (hA : ArenaRep h arena vals) (hn : n ≤ vals.length) (hl : 147520 ≤ h.length) (hz : arena.length < 16384)
    (hJ : vals.length - n < 4096) (hw : ShOpt h w sh) (ht : t < 2 ^ 64) (ha : A < 2 ^ 64) (hb : B < 2 ^ 64) :
    let nd := RN.mk t A B sh p (vals.take n).reverse
    let h' := v5 h t.toUInt64 A.toUInt64 B.toUInt64 w (if p then 1 else 0) n.toUInt64
    h'.length = h.length ∧ ShTabAgree h h' ∧ ArenaRep h' (arena ++ [nd]) (nd :: vals.drop n) ∧
    (∀ i : UInt64, i.toNat < 12352 → i.toNat ≠ 8 → i.toNat ≠ 9 → bget h' i = bget h i) ∧
    (∀ i : UInt64, 147520 ≤ i.toNat → bget h' i = bget h i) ∧ h'.drop 184384 = h.drop 184384 := by
  intro nd h'
  obtain ⟨h9, hal, h8, hvl, I, hI, hR, hD, hX⟩ := hA
  have en : n.toUInt64.toNat = n := by simp; omega
  have J := vals.length - n
  have hb9 : (bget h 9).toNat < 16384 := by omega
  have hroots : ∀ i, i < n → (opAt h (vals.length - n + i)).toNat < arena.length := by
    intro i hi
    obtain ⟨hr, _, _⟩ := hR (n - 1 - i) (by omega)
    rw [show vals.length - 1 - (n - 1 - i) = vals.length - n + i by omega] at hr; exact hr
  have E := v5_eff h t.toUInt64 A.toUInt64 B.toUInt64 w (if p then 1 else 0) n.toUInt64 hl hb9 (by omega) (by rw [en]; omega)
    (by rw [en]; omega) (fun i hi => by rw [en, h8]; rw [en] at hi; have := hroots i hi; omega)
    (by
      rw [en, h8]; unfold List.Nodup; rw [List.pairwise_iff_getElem]
      intro r1 r2 h1 h2 h12
      simp only [List.length_map, List.length_range] at h1 h2
      simp only [List.getElem_map, List.getElem_range]
      intro e
      have := hD (vals.length - n + r1) (vals.length - n + r2) (by omega) (by omega) (UInt64.toNat_inj.mp e)
      omega)
  simp only [en] at E
  rw [h8] at E
  obtain ⟨EL, F0, F1, F2, F3, F4, F5, F6, Elink, Eop, E8, E9, EU, ED⟩ := E
  -- abbreviations
  have zN : (bget h 9) = arena.length.toUInt64 := UInt64.toNat_inj.mp (by rw [h9]; simp; omega)
  have rootAt : ∀ i (hi : i < n), ∃ hr : (opAt h (vals.length - n + i)).toNat < arena.length,
      arena[(opAt h (vals.length - n + i)).toNat]'hr = vals[n - 1 - i]'(by omega) ∧
      ∀ u, u < arena.length → opAt h (vals.length - n + i) ∈ I u → (opAt h (vals.length - n + i)).toNat = u := by
    intro i hi
    have := hR (n - 1 - i) (by omega)
    rw [show vals.length - 1 - (n - 1 - i) = vals.length - n + i by omega] at this; exact this
  -- a record below the old arena size that is no popped root keeps all fields; any record keeps fields 0..6
  have keep : ∀ v : UInt64, v.toNat < arena.length → ∀ k : UInt64, k.toNat < 8 →
      (k.toNat = 7 → ∀ i, i + 1 < n → v ≠ opAt h (vals.length - n + i)) → fld h' v k = fld h v k := by
    intro v hv k hk h7
    simp only [fld]
    have r := recK v k (by omega) hk
    refine EU _ (by rw [r]; omega) (by rw [r]; omega) (by rw [r]; omega) (by rw [r, h9]; omega) ?_
    intro i hi e
    rw [r] at e
    exact h7 (by omega) i hi (UInt64.toNat_inj.mp (by omega))
  -- an arena node's own records: the frame
  have arenaFrame : ∀ u (hu : u < arena.length), RNRep h' u.toUInt64 (arena[u]'hu) (I u) := by
    intro u hu
    obtain ⟨r, nd, bnd⟩ := hI u hu
    obtain ⟨tl, et⟩ := r.head
    refine r.frame (fun k hk => keep _ (by simp; omega) k (by omega) (fun e => by omega)) (fun v hv k hk => ?_) ?_
    · rw [et] at hv nd
      have vb := bnd v (by rw [et]; exact List.mem_cons_of_mem _ hv)
      refine keep v vb k hk (fun _ i hi e => ?_)
      obtain ⟨hr, _, hu'⟩ := rootAt i (by omega)
      rw [← e] at hu'
      have := hu' u hu (by rw [et]; exact List.mem_cons_of_mem _ hv)
      have : v = u.toUInt64 := UInt64.toNat_inj.mp (by simp; omega)
      rw [this] at hv
      exact (List.nodup_cons.mp nd).1 hv
    · intro i hi1 hi2
      exact EU i (by omega) (by omega) (by omega) (Or.inr (by rw [h9]; omega)) (fun k hk => by
        have := (rootAt k (by omega)).1; omega)
  have shtab : ShTabAgree h h' := fun i hi1 hi2 => EU i (by omega) (by omega) (by omega) (Or.inr (by rw [h9]; omega)) (fun k hk => by
    have := (rootAt k (by omega)).1; omega)
  -- the popped roots, bottom first, as children of the new node
  have kidRep : ∀ i (hi : i < n), RNRep h' (opAt h (vals.length - n + i)) (((vals.take n).reverse)[i]'(by simp; omega))
      (I (opAt h (vals.length - n + i)).toNat) := by
    intro i hi
    obtain ⟨hr, ea, _⟩ := rootAt i hi
    have := arenaFrame _ hr
    simp only [UInt64.ofNat_toNat] at this
    rw [ea] at this
    rw [List.getElem_reverse, List.getElem_take]
    simpa [show n - 1 - i = (vals.take n).length - 1 - i by simp; omega] using this
  let ids := ((List.range n).map fun i => I (opAt h (vals.length - n + i)).toNat).flatten
  have idsB : ∀ v ∈ ids, v.toNat < arena.length := by
    intro v hv
    obtain ⟨i, hi, hv⟩ := mem_flat_range hv
    exact (hI _ (rootAt i hi).1).2.2 v hv
  have newRep : RNRep h' (bget h 9) nd (bget h 9 :: ids) := by
    have K := kidsR_chain h' (vals.take n).reverse (fun i => opAt h (vals.length - n + i)) (fun i => I (opAt h (vals.length - n + i)).toNat)
      (fun i hi => by simp at hi; have := Elink i (by omega); simpa using this)
      (fun i hi => kidRep i (by simp at hi; omega))
    simp only [List.length_reverse, List.length_take, Nat.min_eq_left hn, Nat.add_zero] at K
    refine .mk F0 F1 F2 (by rw [F3]; exact hw.frame shtab) F4 (by rw [F6]; simp [Nat.min_eq_left hn]) ht (fun _ _ => ⟨ha, hb⟩) (by rw [F5]; exact K)
  have newNodup : (bget h 9 :: ids).Nodup := by
    refine List.nodup_cons.mpr ⟨fun hm => by have := idsB _ hm; omega, ?_⟩
    refine nodup_flat_range _ n (fun i hi => (hI _ (rootAt i hi).1).2.1) (fun i j hi hj hij v h1 h2 => ?_)
    exact hX (vals.length - n + i) (vals.length - n + j) (by omega) (by omega) (by omega) v h1 h2
  -- kept operand positions
  have opKeep : ∀ q, q < vals.length - n → opAt h' q = opAt h q := by
    intro q hq
    simp only [opAt]
    refine EU _ (by rw [d3k q (by omega)]; omega) (by rw [d3k q (by omega)]; omega) (by rw [d3k q (by omega)]; omega)
      (Or.inl (by rw [d3k q (by omega), h9]; omega)) (fun k hk => by rw [d3k q (by omega)]; have := (rootAt k (by omega)).1; omega)
  have oldRoot : ∀ q (hq : q < vals.length - n), ∃ hr : (opAt h q).toNat < arena.length,
      arena[(opAt h q).toNat]'hr = vals[n + (vals.length - n - 1 - q)]'(by omega) ∧
      ∀ u, u < arena.length → opAt h q ∈ I u → (opAt h q).toNat = u := by
    intro q hq
    have := hR (n + (vals.length - n - 1 - q)) (by omega)
    rw [show vals.length - 1 - (n + (vals.length - n - 1 - q)) = q by omega] at this; exact this
  have selfMem : ∀ q (hq : q < vals.length), opAt h q ∈ I (opAt h q).toNat := by
    intro q hq
    have := hR (vals.length - 1 - q) (by omega)
    rw [show vals.length - 1 - (vals.length - 1 - q) = q by omega] at this
    obtain ⟨hr, _, _⟩ := this
    have := (hI _ hr).1.mem
    simpa using this
  let I' : Nat → List UInt64 := fun u => if u < arena.length then I u else bget h 9 :: ids
  have hz9 : (bget h 9).toNat = arena.length := h9
  have ez : (opAt h' (vals.length - n)) = bget h 9 := Eop
  refine ⟨EL, shtab, ⟨?_, by simp; omega, ?_, by simp; omega, I', ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [E9, tn_add _ _ (by simp; omega)]; simp; omega
  · rw [E8, tn_add _ _ (by simp; omega)]; simp; omega
  · intro u hu
    simp only [List.length_append, List.length_cons, List.length_nil] at hu
    by_cases hua : u < arena.length
    · simp only [I', hua, if_true]
      rw [List.getElem_append_left hua]
      exact ⟨arenaFrame u hua, (hI u hua).2.1, fun v hv => by have := (hI u hua).2.2 v hv; simp; omega⟩
    · have ue : u = arena.length := by omega
      subst ue
      simp only [I', Nat.lt_irrefl, if_false]
      rw [List.getElem_append_right (by omega)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      rw [← zN]
      refine ⟨newRep, newNodup, fun v hv => ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil]
      rcases List.mem_cons.mp hv with e | e
      · rw [e]; omega
      · have := idsB v e; omega
  · intro k hk
    simp only [List.length_cons, List.length_drop] at hk ⊢
    cases k with
    | zero =>
      simp only [Nat.sub_zero, Nat.add_sub_cancel]
      simp only [ez]
      refine ⟨by simp; omega, ?_, fun u hu hm => ?_⟩
      · simp only [List.getElem_cons_zero]
        rw [List.getElem_append_right (by omega)]; simp [hz9]
      · by_cases hua : u < arena.length
        · simp only [I', hua, if_true] at hm; have := (hI u hua).2.2 _ hm; omega
        · simp at hu; omega
    | succ k =>
      have pq : vals.length - n + 1 - 1 - (k + 1) = vals.length - n - 1 - k := by omega
      have ok := opKeep (vals.length - n - 1 - k) (by omega)
      simp only [pq, ok]
      obtain ⟨hr, ea, hu⟩ := oldRoot (vals.length - n - 1 - k) (by omega)
      refine ⟨by simp; omega, ?_, fun u hu' hm => ?_⟩
      · rw [List.getElem_append_left hr, ea]
        simp only [List.getElem_cons_succ, List.getElem_drop]
        congr 1; omega
      · by_cases hua : u < arena.length
        · simp only [I', hua, if_true] at hm; exact hu u hua hm
        · simp only [I', hua, if_false] at hm
          rcases List.mem_cons.mp hm with e | e
          · rw [e] at hr; omega
          · obtain ⟨i, hi, hv⟩ := mem_flat_range e
            exact absurd hv (hX (vals.length - n - 1 - k) (vals.length - n + i) (by omega) (by omega) (by omega) _
              (selfMem _ (by omega)))
  · intro k1 k2 h1 h2 e
    simp only [List.length_cons, List.length_drop] at h1 h2
    rcases Nat.lt_or_ge k1 (vals.length - n) with c1 | c1 <;> rcases Nat.lt_or_ge k2 (vals.length - n) with c2 | c2
    · rw [opKeep _ c1, opKeep _ c2] at e; exact hD k1 k2 (by omega) (by omega) e
    · rw [opKeep _ c1, show k2 = vals.length - n by omega, ez] at e
      have := (oldRoot k1 c1).1; rw [e] at this; omega
    · rw [opKeep _ c2, show k1 = vals.length - n by omega, ez] at e
      have := (oldRoot k2 c2).1; rw [← e] at this; omega
    · omega
  · intro k1 k2 h1 h2 h12 v hv1 hv2
    simp only [List.length_cons, List.length_drop] at h1 h2
    have side : ∀ q, q < vals.length - n → v ∈ I (opAt h q).toNat → v ∉ I' (opAt h' (vals.length - n)).toNat := by
      intro q hq hv hv'
      rw [ez, hz9] at hv'
      simp only [I', Nat.lt_irrefl, if_false] at hv'
      rcases List.mem_cons.mp hv' with e | e
      · have := (hI _ (oldRoot q hq).1).2.2 v hv; rw [e] at this; omega
      · obtain ⟨i, hi, hv3⟩ := mem_flat_range e
        exact hX q (vals.length - n + i) (by omega) (by omega) (by omega) v hv hv3
    have low : ∀ q (hq : q < vals.length - n), I' (opAt h' q).toNat = I (opAt h q).toNat := by
      intro q hq; rw [opKeep q hq]; simp [I', (oldRoot q hq).1]
    rcases Nat.lt_or_ge k1 (vals.length - n) with c1 | c1 <;> rcases Nat.lt_or_ge k2 (vals.length - n) with c2 | c2
    · rw [low _ c1] at hv1; rw [low _ c2] at hv2; exact hX k1 k2 (by omega) (by omega) h12 v hv1 hv2
    · rw [low _ c1] at hv1; rw [show k2 = vals.length - n by omega] at hv2; exact side k1 c1 hv1 hv2
    · rw [low _ c2] at hv2; rw [show k1 = vals.length - n by omega] at hv1; exact side k2 c2 hv2 hv1
    · omega
  · intro i a1 a2 a3
    exact EU i a2 a3 (by omega) (Or.inl (by rw [h9]; omega)) (fun k hk => by have := (rootAt k (by omega)).1; omega)
  · intro i a1
    exact EU i (by omega) (by omega) (by omega) (Or.inr (by rw [h9]; omega)) (fun k hk => by have := (rootAt k (by omega)).1; omega)
  · exact ED

end ParInv
