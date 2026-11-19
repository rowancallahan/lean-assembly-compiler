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

/-! ## frame lemmas for the type side -/
theorem shapeRow (c : UInt64) (h1 : 5 ≤ c.toNat) (h2 : c.toNat < 5 + 8192) (k : UInt64) (hk : k.toNat < 3) :
    (d7 + 8192 + 3 * (c - 5) + k).toNat = 155712 + 3 * (c.toNat - 5) + k.toNat := by
  have e5 : (c - 5).toNat = c.toNat - 5 := by rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  have e3 : (3 * (c - 5)).toNat = 3 * (c.toNat - 5) := by
    rw [UInt64.toNat_mul, e5, show (3 : UInt64).toNat = 3 from rfl]; exact Nat.mod_eq_of_lt (by omega)
  have a1 : (d7 + 8192 : UInt64).toNat = 155712 := rfl
  have a2 : (d7 + 8192 + 3 * (c - 5)).toNat = 155712 + 3 * (c.toNat - 5) := by rw [tn_add _ _ (by rw [a1, e3]; omega), a1, e3]
  rw [tn_add _ _ (by rw [a2]; omega), a2]

/-- the shape table region `[155712, 155712 + 3·8192)` -/
def ShTabAgree (h h' : Buf) : Prop := ∀ i : UInt64, 155712 ≤ i.toNat → i.toNat < 155712 + 3 * 8192 → bget h' i = bget h i

theorem ShapeCode.frame {h h' : Buf} {c : UInt64} {s : Sh} (r : ShapeCode h c s) (e : ShTabAgree h h') : ShapeCode h' c s := by
  induction r with
  | uw => exact .uw
  | bf => exact .bf
  | ls => exact .ls
  | nt => exact .nt
  | pr h1 h2 hl hr _ _ il ir =>
    have r0 := shapeRow _ h1 h2 0 (by decide)
    have r1 := shapeRow _ h1 h2 1 (by decide)
    simp only [UInt64.add_zero, show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl, Nat.add_zero] at r0 r1
    exact .pr h1 h2 (by rw [e _ (by omega) (by omega)]; exact hl) (by rw [e _ (by omega) (by omega)]; exact hr) il ir

theorem TyRep.frame {h h' : Buf} {res u : UInt64} {ty : Ty} (r : TyRep h res u ty)
    (e0 : ∀ k : UInt64, k.toNat < 7 → fld h' u k = fld h u k) (e : ShTabAgree h h') : TyRep h' res u ty := by
  have i0 := e0 0 (by decide); have i2 := e0 2 (by decide); have i3 := e0 3 (by decide)
  have ii : InpLoc h' u ↔ InpLoc h u := by simp only [InpLoc, i0, i2]
  cases ty with
  | s s => exact ⟨by rw [i3]; exact r.1.frame e, by rw [i0]; exact r.2.1, by rw [ii]; exact r.2.2⟩
  | lit => exact ⟨by rw [i3]; exact r.1, by rw [ii]; exact r.2⟩
  | inp => exact ⟨ii.mpr r.1, by rw [i3]; exact r.2⟩
  | bot => exact ⟨by rw [i3]; exact r.1, by rw [i0]; exact r.2.1, by rw [ii]; exact r.2.2⟩

theorem ValRep.frame {h h' : Buf} {res u : UInt64} {v : Nd × Ty} {ids : List UInt64} (r : ValRep h res u v ids)
    (e0 : ∀ k : UInt64, k.toNat < 7 → fld h' u k = fld h u k) (e : RecAgree h h' ids.tail) (es : ShTabAgree h h') :
    ValRep h' res u v ids :=
  ⟨r.1.frame e0 e, r.2.1.frame e0 es, by rw [e0 4 (by decide)]; exact r.2.2⟩

/-! ## popped operands become the new node's child chain -/
/-- the visible children (input locals dropped), bottom first -/
def visible (vs : List (Nd × Ty)) : List Nd := (vs.filter fun v => decide (v.2 ≠ .inp)).map (·.1)

theorem NodeRep.inp_ids {h : Buf} {u : UInt64} {nd : Nd} {ids : List UInt64} (r : NodeRep h u nd ids) (hi : InpLoc h u) : ids = [u] := by
  cases r with
  | loc => rfl
  | _ => rename_i a _; simp_all [InpLoc]

theorem TyRep.inp_iff {h : Buf} {res u : UInt64} {ty : Ty} (r : TyRep h res u ty) : InpLoc h u ↔ ty = .inp := by
  cases ty with
  | inp => exact ⟨fun _ => rfl, fun _ => r.1⟩
  | s s => exact ⟨fun x => absurd x r.2.2, fun x => by cases x⟩
  | lit => exact ⟨fun x => absurd x r.2, fun x => by cases x⟩
  | bot => exact ⟨fun x => absurd x r.2.2, fun x => by cases x⟩

theorem kids_chain (h : Buf) (res : UInt64) : ∀ (vs : List (Nd × Ty)) (idss : List (List UInt64)) (f : Nat → UInt64) (k0 : Nat),
    idss.length = vs.length →
    (∀ i, i + 1 < vs.length → fld h (f (k0 + i)) 7 = f (k0 + i + 1)) →
    (∀ i (hi : i < vs.length), ValRep h res (f (k0 + i)) (vs[i]'hi) (idss.getD i [])) →
    Kids h (f k0) vs.length (visible vs) idss.flatten
  | [], [], _, _, _, _, _ => .nil
  | v :: vs, ids :: idss, f, k0, hL, hk, hv => by
    have hL' : idss.length = vs.length := by simpa using hL
    have ih := kids_chain h res vs idss f (k0 + 1) hL'
      (fun i hi => by have := hk (i + 1) (by simp; omega); rw [show k0 + (i + 1) = k0 + 1 + i by omega] at this; exact this)
      (fun i hi => by have := hv (i + 1) (by simp; omega); rw [show k0 + (i + 1) = k0 + 1 + i by omega] at this; simpa using this)
    have nx : Kids h (fld h (f k0) 7) vs.length (visible vs) idss.flatten := by
      cases vs with
      | nil => cases idss with
        | nil => exact .nil
        | cons _ _ => simp at hL'
      | cons _ _ => have := hk 0 (by simp); simp only [Nat.add_zero] at this; rw [this]; exact ih
    have v0 := hv 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero, List.getD_cons_zero] at v0
    by_cases hi : v.2 = .inp
    · have il : InpLoc h (f k0) := (v0.2.1.inp_iff).mpr hi
      have e := v0.1.inp_ids il
      have : visible (v :: vs) = visible vs := by simp [visible, hi]
      rw [this, List.flatten_cons, e]
      exact .skip il nx
    · have il : ¬ InpLoc h (f k0) := fun x => hi ((v0.2.1.inp_iff).mp x)
      have : visible (v :: vs) = v.1 :: visible vs := by simp [visible, hi]
      rw [this, List.flatten_cons]
      exact .cons v0.1 il nx
  | [], _ :: _, _, _, hL, _, _ => by simp at hL
  | _ :: _, [], _, _, hL, _, _ => by simp at hL

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

theorem NodeRep.head {h : Buf} {u : UInt64} {nd : Nd} {ids : List UInt64} (r : NodeRep h u nd ids) : ∃ t, ids = u :: t := by
  cases r <;> exact ⟨_, rfl⟩

/-! ## OPS / REDUCE: v5 over the operand-stack representation -/
/-- the hypotheses of `v5_eff`, from the operand-stack representation (top `pre` popped) -/
theorem ops_v5_hyps (h : Buf) (res : UInt64) (pre vals : List (Nd × Ty)) (hO : OpsRep h res (pre ++ vals)) :
    let n := pre.length.toUInt64
    (bget h 8).toNat ≤ 4096 ∧ n.toNat ≤ (bget h 8).toNat ∧ (bget h 8).toNat - n.toNat = vals.length ∧ n.toNat = pre.length ∧
    (∀ i, i < n.toNat → (opAt h ((bget h 8).toNat - n.toNat + i)).toNat < (bget h 9).toNat) ∧
    ((List.range n.toNat).map fun i => (opAt h ((bget h 8).toNat - n.toNat + i)).toNat).Nodup := by
  intro n
  obtain ⟨h8, hm, h9, idss, hL, hnd, hbel, hv⟩ := hO
  simp only [List.length_append] at h8 hm hL hv
  have en : n.toNat = pre.length := by simp [n]; omega
  have root : ∀ i (hi : i < pre.length + vals.length), opAt h (pre.length + vals.length - 1 - i) ∈ idss.getD i [] :=
    fun i hi => (hv i (by simpa using hi)).1.mem
  have idx : ∀ r, r < pre.length → (bget h 8).toNat - n.toNat + r = pre.length + vals.length - 1 - (pre.length - 1 - r) := by
    intro r hr; omega
  refine ⟨by omega, by omega, by omega, en, fun r hr => ?_, ?_⟩
  · rw [idx r (by omega)]
    have := hbel _ (mem_getD_flat _ _ _ (root (pre.length - 1 - r) (by omega)))
    exact UInt64.lt_iff_toNat_lt.mp this
  · unfold List.Nodup
    rw [List.pairwise_iff_getElem]
    intro r1 r2 h1 h2 h12
    simp only [List.length_map, List.length_range] at h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [idx r1 (by omega), idx r2 (by omega)]
    intro e
    have e' := UInt64.toNat_inj.mp e
    exact flat_disj idss hnd (pre.length - 1 - r2) (pre.length - 1 - r1) (by omega) _
      (root _ (by omega)) (by rw [← e']; exact root _ (by omega))

/-- **OPS/REDUCE**: `v5` pops `pre` (top first) and pushes node z = h[9]: the popped operands form z's child chain (input locals
skipped), and any representation of z on top of the untouched rest gives the new operand-stack representation -/
theorem ops_reduce (h : Buf) (res c a b w t : UInt64) (pre vals : List (Nd × Ty)) (hO : OpsRep h res (pre ++ vals))
    (hl : 147520 ≤ h.length) (hz : (bget h 9).toNat < 16384) (hJ : vals.length < 4096) :
    let z := bget h 9
    let h' := v5 h c a b w t pre.length.toUInt64
    ShTabAgree h h' ∧
    ∃ ids, Kids h' (fld h' z 5) pre.length (visible pre.reverse) ids ∧ (∀ v ∈ ids, v < z) ∧
      ∀ v, ValRep h' res z v (z :: ids) → OpsRep h' res (v :: vals) := by
  intro z h'
  obtain ⟨hm, hn, hJv, en, hb, hd⟩ := ops_v5_hyps h res pre vals hO
  have E := v5_eff h c a b w t pre.length.toUInt64 hl hz hm hn (by omega) hb hd
  have hJv' : (bget h 8).toNat - pre.length = vals.length := by omega
  simp only [en] at E
  simp only [hJv'] at E
  obtain ⟨EL, _, _, _, _, _, E5, _, Elink, Eop, E8, E9, EU⟩ := E
  obtain ⟨h8, _, h9, idss, hL, hnd, hbel, hv⟩ := hO
  simp only [List.length_append] at h8 hL hv
  have hz' : z.toNat < 16384 := hz
  have zz : z.toNat = (bget h 9).toNat := rfl
  have root : ∀ i (hi : i < pre.length + vals.length), opAt h (pre.length + vals.length - 1 - i) ∈ idss.getD i [] :=
    fun i hi => (hv i (by simpa using hi)).1.mem
  have below : ∀ v ∈ idss.flatten, v.toNat < z.toNat := fun v hv => UInt64.lt_iff_toNat_lt.mp (hbel v hv)
  -- a record of the old operand trees is unchanged except possibly a popped root's next field
  have keep : ∀ (v : UInt64), v ∈ idss.flatten → ∀ k : UInt64, k.toNat < 8 →
      (k.toNat = 7 → ∀ k', k' + 1 < pre.length → v ≠ opAt h (vals.length + k')) → fld h' v k = fld h v k := by
    intro v hv k hk h7
    have vz := below v hv
    simp only [fld]
    have r := recK v k (by omega) hk
    refine EU _ (by rw [r]; omega) (by rw [r]; omega) (by rw [r]; omega) (by rw [r]; omega) ?_
    intro k' hk' e
    rw [r] at e
    have hk7 : k.toNat = 7 := by omega
    exact h7 hk7 k' hk' (UInt64.toNat_inj.mp (by omega))
  have nL : pre.length ≤ idss.length := by omega
  -- entries: the popped ones (i < n) and the kept ones (n ≤ i)
  have notPopped : ∀ i v, i < pre.length + vals.length → v ∈ idss.getD i [] → ∀ k', k' + 1 < pre.length →
      (i ≥ pre.length ∨ v ≠ opAt h (pre.length + vals.length - 1 - i)) → v ≠ opAt h (vals.length + k') := by
    intro i v hi hv k' hk' hc e
    have hr := root (pre.length - 1 - k') (by omega)
    rw [show pre.length + vals.length - 1 - (pre.length - 1 - k') = vals.length + k' by omega] at hr
    rcases Nat.lt_trichotomy i (pre.length - 1 - k') with c1 | c1 | c1
    · exact flat_disj idss hnd _ _ c1 v hv (e ▸ hr)
    · subst c1
      rcases hc with c2 | c2
      · omega
      · exact c2 (by rw [show pre.length + vals.length - 1 - (pre.length - 1 - k') = vals.length + k' by omega]; exact e)
    · exact flat_disj idss hnd _ _ c1 v (e ▸ hr) hv
  have shtab : ShTabAgree h h' := fun i hi1 hi2 => EU i (by omega) (by omega) (by omega) (Or.inr (by omega)) (fun k hk => by
      have := below _ (mem_getD_flat _ _ _ (root (pre.length - 1 - k) (by omega)))
      rw [show pre.length + vals.length - 1 - (pre.length - 1 - k) = vals.length + k by omega] at this
      omega)
  -- frame for one old entry, given the new position of its root is unchanged
  have frameEntry : ∀ i (hi : i < pre.length + vals.length),
      ValRep h' res (opAt h (pre.length + vals.length - 1 - i)) ((pre ++ vals)[i]'(by simpa using hi)) (idss.getD i []) := by
    intro i hi
    have V := hv i (by simpa using hi)
    obtain ⟨t, et⟩ := V.1.head
    have nd := nodup_getD idss i hnd
    rw [et] at nd
    have hu : opAt h (pre.length + vals.length - 1 - i) ∈ idss.flatten := mem_getD_flat _ _ _ (root i hi)
    refine V.frame (fun k hk => keep _ hu k (by omega) (fun e => by omega)) (fun v hvt k hk => ?_) ?_
    · rw [et] at hvt
      have hvm : v ∈ idss.getD i [] := by rw [et]; exact List.mem_cons_of_mem _ hvt
      refine keep v (mem_getD_flat _ _ _ hvm) k hk (fun _ k' hk' => notPopped i v hi hvm k' hk' (Or.inr ?_))
      intro e; rw [e] at hvt; exact (List.nodup_cons.mp nd).1 hvt
    · exact shtab
  refine ⟨shtab, ((idss.take pre.length).reverse).flatten, ?_, ?_, ?_⟩
  · -- the child chain
    have K := kids_chain h' res pre.reverse ((idss.take pre.length).reverse) (fun k => opAt h k) vals.length
      (by simp; omega) (fun i hi => by simp at hi; exact Elink i hi) (fun r hr => by
        simp only [List.length_reverse] at hr
        rw [getD_rev_take _ _ _ nL hr]
        have := frameEntry (pre.length - 1 - r) (by omega)
        rw [show pre.length + vals.length - 1 - (pre.length - 1 - r) = vals.length + r by omega] at this
        rw [List.getElem_reverse]
        rw [List.getElem_append_left (by omega)] at this
        exact this)
    simp only [List.length_reverse] at K
    rw [E5]; exact K
  · intro v hv
    rw [List.mem_flatten] at hv
    obtain ⟨l, hl1, hl2⟩ := hv
    rw [List.mem_reverse] at hl1
    have : v ∈ idss.flatten := List.mem_flatten.mpr ⟨l, List.mem_of_mem_take hl1, hl2⟩
    exact UInt64.lt_iff_toNat_lt.mpr (below v this)
  · intro v V
    have perm : (((idss.take pre.length).reverse).flatten ++ (idss.drop pre.length).flatten).Perm idss.flatten := by
      have := (List.Perm.flatten (List.reverse_perm (idss.take pre.length))).append_right (idss.drop pre.length).flatten
      rw [← List.flatten_append, ← List.flatten_append, List.take_append_drop] at this
      rw [List.flatten_append] at this
      exact this
    refine ⟨?_, by simp; omega, ?_, (z :: ((idss.take pre.length).reverse).flatten) :: idss.drop pre.length, by simp; omega, ?_, ?_, ?_⟩
    · rw [E8]; simp; omega
    · rw [E9, tn_add _ _ (by simp; omega)]; simp; omega
    · rw [List.flatten_cons, List.cons_append, List.nodup_cons]
      refine ⟨fun hm => ?_, perm.nodup_iff.mpr hnd⟩
      have := below z (perm.subset hm); omega
    · intro x hx
      rw [E9]
      rw [List.flatten_cons, List.cons_append, List.mem_cons] at hx
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [tn_add _ _ (by simp; omega)]
      have e1 : (1 : UInt64).toNat = 1 := rfl
      rcases hx with hx | hx
      · subst hx; omega
      · have := below x (perm.subset hx); omega
    · intro i hi
      cases i with
      | zero => simpa [opAt] using (show ValRep h' res (opAt h' vals.length) v (z :: ((idss.take pre.length).reverse).flatten) by rw [Eop]; exact V)
      | succ i =>
        simp only [List.length_cons] at hi
        have F := frameEntry (pre.length + i) (by omega)
        rw [List.getElem_append_right (by omega)] at F
        simp only [List.getElem_cons_succ, List.getD_cons_succ, getD_drop]
        have eo : bget h' (d3 + (vals.length + 1 - 1 - (i + 1)).toUInt64) = opAt h (pre.length + vals.length - 1 - (pre.length + i)) := by
          rw [show pre.length + vals.length - 1 - (pre.length + i) = vals.length + 1 - 1 - (i + 1) by omega]
          apply EU <;> (try rw [d3k _ (by omega)]) <;> (try omega)
        rw [show (v :: vals).length - 1 - (i + 1) = vals.length + 1 - 1 - (i + 1) by simp, eo]
        simpa using F

end ParInv
