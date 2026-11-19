/- Nano/V2Self/Proof/ParInvHdr: def-header tasks 70 / 73 / 74 / 75 on box C's Rep (parser lead).  Generic `rep_cur`: the current
def row's fields +1..+4, +6 and `k` parameter codes appended at h[27] represent a new current row `cur'`. -/
import Nano.V2Self.Proof.ParInvFinish
namespace ParInv
open C BufL ParSpec ParRun

/-- `rowRep_frame'` with agreement only on the row's own parameter cells -/
theorem rowRep_frame'' {h h' : Buf} {j : Nat} {d : DefR} (hj : j < 512) (r : RowRep h j d)
    (c : ∀ k : UInt64, k.toNat < 8 → bget h' (d7 + 8 * j.toUInt64 + k) = bget h (d7 + 8 * j.toUInt64 + k))
    (cc : ∀ i : Nat, i < d.params.length → bget h' (d7 + 4096 + bget h (d7 + 8 * j.toUInt64 + 5) + i.toUInt64) =
      bget h (d7 + 4096 + bget h (d7 + 8 * j.toUInt64 + 5) + i.toUInt64))
    (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') : RowRep h' j d := by
  have c0 := c 0 (by decide); simp only [UInt64.add_zero] at c0
  obtain ⟨a0, a1, a2, a3, a4, a6, a5, ap⟩ := r
  refine ⟨by rw [c0]; exact nameAt_frame et (by omega) a0, by rw [c 1 (by decide)]; exact a1, by rw [c 2 (by decide)]; exact a2,
    by rw [c 3 (by decide)]; exact a3.frame es, by rw [c 4 (by decide)]; exact a4, by rw [c 6 (by decide)]; exact a6,
    by rw [c 5 (by decide)]; exact a5, fun i hi => ?_⟩
  rw [c 5 (by decide), cc i hi]
  exact (ap i hi).frame es

/-- **current-row update**: Rep is kept when only the current row's fields +1..+4, +6, the parameter-code cells
[h27, h27 + k) and h[27] change and they represent `cur'` (same name and start, `k` more parameters) -/
theorem rep_cur {h h' ts : Buf} {st : St} {fs : List Frame} (r : Rep h ts st fs) (hD : inDefF fs = true) (cur' : DefR) (k : Nat)
    (hname : cur'.name = st.cur.name) (hpre : ∀ i (hi : i < st.cur.params.length), ∃ hi' : i < cur'.params.length, cur'.params[i] = st.cur.params[i])
    (hk : cur'.params.length = st.cur.params.length + k) (hJ : (bget h 27).toNat + k ≤ 4096) (hl : h'.length = h.length)
    (ed : h'.drop 184384 = h.drop 184384)
    (e : ∀ i : UInt64, i.toNat ≠ 27 →
      (i.toNat < 147520 + 8 * st.defs.length + 1 ∨ 147520 + 8 * st.defs.length + 7 ≤ i.toNat ∨ i.toNat = 147520 + 8 * st.defs.length + 5) →
      (i.toNat < 151616 + (bget h 27).toNat ∨ 151616 + (bget h 27).toNat + k ≤ i.toNat) → bget h' i = bget h i)
    (e27 : (bget h' 27).toNat = (bget h 27).toNat + k)
    (r1 : bget h' (d7 + 8 * st.defs.length.toUInt64 + 1) = cur'.npw.toUInt64)
    (r2 : (bget h' (d7 + 8 * st.defs.length.toUInt64 + 2)).toNat = cur'.nni)
    (r3 : ShOpt h' (bget h' (d7 + 8 * st.defs.length.toUInt64 + 3)) cur'.res)
    (r4 : bget h' (d7 + 8 * st.defs.length.toUInt64 + 4) = b01 cur'.loop)
    (r6 : (bget h' (d7 + 8 * st.defs.length.toUInt64 + 6)).toNat = cur'.params.length)
    (hc : ∀ i (hi : i < k), ShapeCode h' (bget h' (d7 + 4096 + (bget h 27) + i.toUInt64)) (cur'.params[st.cur.params.length + i]'(by omega))) :
    Rep h' ts { st with cur := cur' } fs := by
  obtain ⟨hn, hlen, har⟩ := rep_bounds r
  obtain ⟨rT, rts, r0, r3', r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := r
  rw [hD] at rD
  obtain ⟨d12, dlt, d27, drows, dcur, dz, d0, dsr⟩ := rD
  simp only [if_true] at dcur
  obtain ⟨⟨c0, c1, c2, c3, c4, c6, c5, cc⟩, cs⟩ := dcur
  have big : ∀ i : UInt64, 155712 ≤ i.toNat → bget h' i = bget h i := fun i hi => e i (by omega) (by omega) (by omega)
  have low : ∀ i : UInt64, i.toNat < 147520 → i.toNat ≠ 27 → bget h' i = bget h i := fun i hi a => e i a (by omega) (by omega)
  have et : TokAgree h h' := ⟨low 7 (by decide) (by decide), fun i hi => big i (by omega)⟩
  have es : ShTabAgree h h' := fun i a _ => big i a
  have rowc : ∀ k' : UInt64, k'.toNat < 8 → (d7 + 8 * st.defs.length.toUInt64 + k').toNat = 147520 + 8 * st.defs.length + k'.toNat :=
    fun k' hk' => defCell _ dlt k' hk'
  have rc5 : (d7 + 8 * st.defs.length.toUInt64 + 5).toNat = 147520 + 8 * st.defs.length + 5 := rowc 5 (by decide)
  have rc0 : (d7 + 8 * st.defs.length.toUInt64 + 0).toNat = 147520 + 8 * st.defs.length := rowc 0 (by decide)
  have c5' : bget h' (d7 + 8 * st.defs.length.toUInt64 + 5) = bget h (d7 + 8 * st.defs.length.toUInt64 + 5) :=
    e _ (by rw [rc5]; omega) (Or.inr (Or.inr rc5)) (Or.inl (by rw [rc5]; omega))
  have c0' : bget h' (d7 + 8 * st.defs.length.toUInt64) = bget h (d7 + 8 * st.defs.length.toUInt64) := by
    have := e (d7 + 8 * st.defs.length.toUInt64 + 0) (by rw [rc0]; omega) (Or.inl (by rw [rc0]; omega))
      (Or.inl (by rw [rc0]; omega))
    simpa using this
  refine ⟨tokensAt_frame rT et rts, rts, by rw [low 0 (by decide) (by decide)]; exact r0,
    by rw [low 3 (by decide) (by decide)]; exact tokAt_frame et hn r3', by rw [low 11 (by decide) (by decide)]; exact r11,
    binds_frame rB (low 4 (by decide) (by decide)) (fun i a _ => big i (by omega)) et hn es, ?_,
    arena_frame rA (low 8 (by decide) (by decide)) (low 9 (by decide) (by decide)) (fun i a b => low i b (by omega)) es,
    fun s hs => by rw [low 25 (by decide) (by decide)]; exact (r25 s hs).frame es,
    fun x hx hne => by rw [low 29 (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 x hx hne),
    by rw [low 30 (by decide) (by decide)]; exact r30, by rw [low 32 (by decide) (by decide)]; exact r32, out_frame rO ed,
    tasks_frame rK (low 5 (by decide) (by decide)) (fun i a b => low i (by have := rK.2.1; omega) (by omega)) et hn es
      (fun i a b => low i b (by omega)) har⟩
  show DefsRep h' { st with cur := cur' } (inDefF fs)
  rw [hD]
  refine ⟨by rw [low 12 (by decide) (by decide)]; exact d12, dlt, by rw [e27]; omega, fun j hj => ?_, ?_, fun j h1 h2 => ?_, ?_, ?_⟩
  · have hj : j < st.defs.length := hj
    obtain ⟨rr, rs⟩ := drows j hj
    have a5 := rr.2.2.2.2.2.2.1
    refine ⟨rowRep_frame'' (by omega) rr (fun k' hk' => e _ (by rw [defCell j (by omega) k' hk']; omega)
        (Or.inl (by rw [defCell j (by omega) k' hk']; omega)) (Or.inl (by rw [defCell j (by omega) k' hk']; omega)))
        (fun i (hi : i < (st.defs[j]'hj).params.length) => by
          have pc := parCell (bget h (d7 + 8 * j.toUInt64 + 5)) i (by omega)
          exact e _ (by rw [pc]; omega) (Or.inr (Or.inl (by rw [pc]; omega))) (Or.inl (by rw [pc]; omega))) et hn es, ?_⟩
    rw [e _ (by rw [defCell j (by omega) 5 (by decide)]; simp; omega) (Or.inl (by rw [defCell j (by omega) 5 (by decide)]; simp; omega))
      (Or.inl (by rw [defCell j (by omega) 5 (by decide)]; simp; omega)), e27]
    exact Nat.le_trans rs (Nat.le_add_right _ _)
  · simp only [if_true]
    refine ⟨⟨by rw [c0', hname]; exact nameAt_frame et (by omega) c0, r1, r2, r3, r4, r6, by rw [c5', hk]; omega, fun i hi => ?_⟩, ?_⟩
    · have hi : i < cur'.params.length := hi
      rw [c5']
      by_cases hio : i < st.cur.params.length
      · obtain ⟨hi', heq⟩ := hpre i hio
        have pc := parCell (bget h (d7 + 8 * st.defs.length.toUInt64 + 5)) i (by omega)
        rw [heq, e _ (by rw [pc]; omega) (Or.inr (Or.inl (by rw [pc]; omega))) (Or.inl (by rw [pc]; omega))]
        exact (cc i hio).frame es
      · have hi2 : i - st.cur.params.length < k := by omega
        have := hc (i - st.cur.params.length) hi2
        have ea : d7 + 4096 + bget h (d7 + 8 * st.defs.length.toUInt64 + 5) + i.toUInt64 =
            d7 + 4096 + bget h 27 + (i - st.cur.params.length).toUInt64 := by
          apply UInt64.toNat_inj.mp
          rw [parCell _ _ (by omega), parCell _ _ (by omega)]; omega
        rw [ea]
        have ei : st.cur.params.length + (i - st.cur.params.length) = i := by omega
        simp only [ei] at this
        exact this
    · rw [c5', hk, e27]; omega
  · have h1 : st.defs.length < j := h1
    exact fun k' hk' => by
      rw [e _ (by rw [defCell j h2 k' hk']; omega) (Or.inr (Or.inl (by rw [defCell j h2 k' hk']; omega)))
        (Or.inl (by rw [defCell j h2 k' hk']; omega))]
      exact dz j h1 h2 k' hk'
  · intro i hi1 hi2
    rw [e27] at hi1
    have eidx : (d7 + 4096 + i.toUInt64).toNat = 151616 + i := by
      rw [UInt64.toNat_add]; simp [Nat.toUInt64, show (d7 + 4096 : UInt64).toNat = 151616 from rfl]; omega
    rw [e _ (by rw [eidx]; omega) (Or.inr (Or.inl (by rw [eidx]; omega))) (Or.inr (by rw [eidx]; omega))]
    exact d0 i (by omega) hi2

  · refine ⟨by rw [low 26 (by decide) (by decide)]; exact dsr.1, fun k' h1 h2 => ?_, fun k' hk' => ?_⟩
    · rw [low 26 (by decide) (by decide)] at h1
      have ek : (d7 + 8192 + 3 * k'.toUInt64).toNat = 155712 + 3 * k' := by
        rw [UInt64.toNat_add, UInt64.toNat_mul, show (d7 + 8192 : UInt64).toNat = 155712 from rfl]; simp; omega
      rw [big _ (by omega)]; exact dsr.2.1 k' h1 h2
    · rw [low 26 (by decide) (by decide)] at hk'
      obtain ⟨l, r, sa, sb, sw⟩ := dsr.2.2 k' hk'
      have cq : ∀ q : UInt64, q.toNat < 3 → bget h' (d7 + 8192 + 3 * k'.toUInt64 + q) = bget h (d7 + 8192 + 3 * k'.toUInt64 + q) :=
        fun q hq => big _ (by have := dsr.1; rw [shRowK k' (by omega) q hq]; omega)
      have cq0 := cq 0 (by decide); simp only [UInt64.add_zero] at cq0
      exact ⟨l, r, by rw [cq0]; exact sa.frame es, by rw [cq 1 (by decide)]; exact sb.frame es, by rw [cq 2 (by decide)]; exact sw⟩
end ParInv
