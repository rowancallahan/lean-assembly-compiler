/- Nano/V2Self/Proof/ParInvMkPair: task 42 `mkPair` (v107: two settled operands → pair interning v10, then a tuple node v5).
Also: status 0 is absorbing for `v2` / `v5` (their writes never hit cell 0). -/
import Nano.V2Self.Proof.ParInvPair
import Nano.V2Self.Proof.ParInvIte
namespace ParInv
open C BufL ParSpec ParRun

theorem stat0' (h : Buf) : bget (bset h 0 0) 0 = 0 := by
  rw [bget_bset]; by_cases hl : 0 < h.length <;> simp [hl, bget, List.getD]

theorem v2_stat : ∀ (N : Nat) (h : Buf) (j z c : UInt64), bget h 0 = 0 → bget (v2 N h j z c) 0 = 0
  | 0, h, j, z, c, h0 => stat0' h
  | N + 1, h, j, z, c, h0 => by
    rw [v2]
    by_cases c0 : c = 0
    · simp [c0, h0]
    · simp only [c0, beq_iff_eq, if_false]
      apply v2_stat N _ _ _ _
      rw [bget_bset' _ _ _ _ ?_, h0]
      generalize bget h (d3 + j) = x
      simp only [d5, d3, d1, d2, d4, UInt64.toNat_add, UInt64.toNat_mul]
      simp; omega

theorem v5_stat (h : Buf) (c a b w t n : UInt64) (h0 : bget h 0 = 0) : bget (v5 h c a b w t n) 0 = 0 := by
  unfold v5
  by_cases g1 : bget h 9 < d13
  · by_cases g2 : n < bget h 8 + 1
    · by_cases g3 : bget h 8 - n < d4
      · simp only [g1, g2, g3, if_true]
        have z1 := UInt64.lt_iff_toNat_lt.mp g1
        have j1 := UInt64.lt_iff_toNat_lt.mp g3
        simp only [d13, d4, show (16384 : UInt64).toNat = 16384 from rfl, show (4096 : UInt64).toNat = 4096 from rfl] at z1 j1
        have ne : ∀ k : UInt64, k.toNat < 7 → (d5 + 8 * bget h 9 + k).toNat ≠ (0 : UInt64).toNat := by
          intro k hk; simp only [d5, d3, d1, d2, d4, UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
        have nj : (d3 + (bget h 8 - n)).toNat ≠ (0 : UInt64).toNat := by
          simp only [d3, d1, d2, UInt64.toNat_add]; simp; omega
        rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ nj]
        have hb : ∀ g : Buf, bget g 0 = 0 → bget (if n == 0 then g else v2 16777216 g (bget h 8 - n) (bget h 9) (n - 1)) 0 = 0 := by
          intro g g0; split
          · exact g0
          · exact v2_stat _ _ _ _ _ g0
        apply hb
        rw [bget_bset' _ _ _ _ (ne 6 (by decide)), bget_bset' _ _ _ _ (ne 5 (by decide)), bget_bset' _ _ _ _ (ne 4 (by decide)),
          bget_bset' _ _ _ _ (ne 3 (by decide)), bget_bset' _ _ _ _ (ne 2 (by decide)), bget_bset' _ _ _ _ (ne 1 (by decide)),
          bget_bset' _ _ _ _ (by simpa using ne 0 (by decide)), h0]
      · simp only [g1, g2, g3, if_true, if_false]; exact stat0' h
    · simp only [g1, g2, if_true, if_false]; exact stat0' h
  · simp only [g1, if_false]; exact stat0' h

/-! ## task 42: `mkPair` (v107) -/
theorem h_mkPair {h ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st (.mkPair :: fs))
    (hnf : fs.all (fun f => !f.isFlat)) (hv2 : 2 ≤ st.vals.length) (hsv : ∀ x ∈ st.vals, x.sh.isSome) (hs : bget (step h) 0 ≠ 0) :
    ∃ k st', stepF .mkPair st = some (k, st') ∧ Rep (step h) ts st' (k ++ fs) := by
  obtain ⟨E, _, R1⟩ := rep_pop r (by simp [inDefF, Frame.isDefs])
  generalize (taskAt h fs.length).a = a at E
  generalize (taskAt h fs.length).b = b at E
  generalize hh : bset h 5 fs.length.toUInt64 = h1 at E R1
  obtain ⟨hn7, hl, har⟩ := rep_bounds R1
  have rA := R1.2.2.2.2.2.2.2.1
  have h8le : (bget h1 8).toNat ≤ 4096 := by rw [rA.2.2.1]; exact rA.2.2.2.1
  generalize e2 : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 2) + 3) = cX
  generalize e1 : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 1) + 3) = cY
  generalize p2 : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 2) + 4) = pX
  generalize p1 : bget h1 (d5 + 8 * bget h1 (d3 + bget h1 8 - 1) + 4) = pY
  have ev : step h = (if pX == 0 then if pY == 0 then
      v5 (v10 16777216 h1 cX cY 0) 6 2 0 (bget (v10 16777216 h1 cX cY 0) 25) 0 2 else bset h1 0 0 else bset h1 0 0) := by
    rw [E]; simp only [Frame.code, v96, v107, e2, e1, p2, p1]; simp
  rw [ev] at hs ⊢
  obtain ⟨vy, vx, rest, evs⟩ : ∃ vy vx rest, st.vals = vy :: vx :: rest := by
    match hv : st.vals with
    | vy :: vx :: rest => exact ⟨vy, vx, rest, rfl⟩
    | [] => simp [hv] at hv2
    | [_] => simp [hv] at hv2
  have lk : ∀ k, k < 2 → k < st.vals.length := fun k hk => by rw [evs]; simp; omega
  have fk : ∀ k (hk : k < 2), ∃ ids, RNRep h1 (bget h1 (d3 + bget h1 8 - (k + 1).toUInt64)) (st.vals[k]'(lk k hk)) ids := by
    intro k hk; rw [opCell rA.2.2.1 rA.2.2.2.1 k (lk k hk)]; exact val_rep rA k (lk k hk)
  obtain ⟨_, rY⟩ := fk 0 (by decide); obtain ⟨_, rX⟩ := fk 1 (by decide)
  have fY := rY.fields; have fX := rX.fields
  simp only [fld, show ((0 : Nat) + 1).toUInt64 = 1 from rfl, show ((1 : Nat) + 1).toUInt64 = 2 from rfl] at fY fX
  rw [e1, p1] at fY; rw [e2, p2] at fX
  simp only [evs, List.getElem_cons_zero, List.getElem_cons_succ] at fY fX
  obtain ⟨l, hxl⟩ := Option.isSome_iff_exists.mp (hsv vx (by rw [evs]; simp))
  obtain ⟨rr, hyr⟩ := Option.isSome_iff_exists.mp (hsv vy (by rw [evs]; simp))
  have sX := fX.2.2.2.1; have sY := fY.2.2.2.1
  rw [hxl] at sX; rw [hyr] at sY
  simp only [ShOpt] at sX sY
  have dead : bget (bset h1 0 0) 0 = 0 := stat0' h1
  cases hpx : vx.pend
  · cases hpy : vy.pend
    · have zx : pX = 0 := by rw [fX.2.2.2.2, hpx]; rfl
      have zy : pY = 0 := by rw [fY.2.2.2.2, hpy]; rfl
      simp only [zx, zy, beq_self_eq_true, if_true] at hs ⊢
      have hs2 : bget (v10 16777216 h1 cX cY 0) 0 ≠ 0 := fun z => hs (v5_stat _ _ _ _ _ _ _ z)
      obtain ⟨nl, nr, R2⟩ := rep_intern R1 cX cY l rr sX sY hs2
      have w2 : ShOpt (v10 16777216 h1 cX cY 0) (bget (v10 16777216 h1 cX cY 0) 25) (some (.p l rr)) :=
        R2.2.2.2.2.2.2.2.2.1 _ rfl
      obtain ⟨st', em, R3⟩ := rep_v5g R2 hnf 2 6 2 0 (some (.p l rr)) false _ w2 (by decide) (fun _ _ => ⟨by decide, by decide⟩)
        (by decide) hs
      refine ⟨[], st', ?_, by simpa using R3⟩
      simp only [stepF, evs, hxl, hyr, hpx, hpy, Bool.or_false, Bool.false_eq_true, if_false, nl, nr, or_self]
      rw [show (vy :: vx :: rest) = st.vals from evs.symm, em]; rfl
    · have zy : pY = 1 := by rw [fY.2.2.2.2, hpy]; rfl
      have zx : pX = 0 := by rw [fX.2.2.2.2, hpx]; rfl
      simp only [zx, zy, beq_self_eq_true, if_true] at hs; exact absurd dead (by simpa using hs)
  · have zx : pX = 1 := by rw [fX.2.2.2.2, hpx]; rfl
    simp only [zx] at hs; exact absurd dead (by simpa using hs)

end ParInv
