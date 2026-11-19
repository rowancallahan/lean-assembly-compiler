/- Nano/V2Self/Proof/ParInvAssign: Layer 3, pieces for task 68 `assign` (v133), box G.
`v201_eq`: the scan for an earlier INPUT-flagged binding = `(binds.take i).any Bd.inp`. -/
import Nano.V2Self.Proof.ParInvGroup
namespace ParInv
open C BufL ParSpec ParRun

theorem v201_eq {h : Buf} {bs : List Bd} (hB : BindsRep h bs) :
    ∀ (i n : Nat), i ≤ bs.length → i < n → v201 n h i.toUInt64 = if (bs.take i).any Bd.inp then 1 else 0
  | 0, n + 1, _, _ => by rw [v201]; simp
  | i + 1, n + 1, hi, hn => by
    obtain ⟨_, bl, brows⟩ := hB
    have hne : ((i + 1).toUInt64 == 0) = false := by
      rw [beq_eq_false_iff_ne]; intro e; have := congrArg UInt64.toNat e; simp at this; omega
    have e1 : (i + 1).toUInt64 - 1 = i.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    obtain ⟨_, _, _, a3⟩ := brows i (by omega)
    rw [v201]; simp only [hne, e1, a3]
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some, List.any_append]
    cases hin : (bs[i]'(by omega)).inp with
    | true => simp [b01, hin]
    | false =>
      simp only [b01, Bool.false_eq_true, if_false, List.any_cons, List.any_nil, hin, Bool.or_false]
      have := v201_eq ⟨‹_›, bl, brows⟩ i n (by omega) (by omega)
      simpa using this

/-- the heap after v133's writes: binding row (slot, code, input flag), scratch 31, slot counter h[11], the parameter code cell
at h[27], h[27] + 1, and the current def row's non-input count (+2) and parameter count (+6) -/
def asgHeap (g : Buf) (a wv n1 z : UInt64) : Buf :=
  bset (bset (bset (bset (bset (bset (bset (bset (bset g (d9 + 4 * a + 1) (bget g 11)) (d9 + 4 * a + 2) wv) (d9 + 4 * a + 3) n1) 31 z)
    11 (bget g 11 + z - z * n1)) ((d7 + 4096) + bget g 27) wv) 27 (bget g 27 + 1))
    (d7 + 8 * bget g 12 + 2) (bget g (d7 + 8 * bget g 12 + 2) + 1 - n1)) (d7 + 8 * bget g 12 + 2 + 4) (bget g (d7 + 8 * bget g 12 + 2 + 4) + 1)

theorem v133_eq (g : Buf) (a b : UInt64) (i0 D J : Nat) (ha : a = i0.toUInt64) (hi0 : i0 < 1024) (h12 : bget g 12 = D.toUInt64)
    (hD : D < 512) (h27 : bget g 27 = J.toUInt64) (hJ : J < 4096) (hl : 184384 ≤ g.length) (hne : a ≠ bget g 4)
    (hw4 : bget g 25 ≠ 4) (hwb : (bget g 25).toNat < 5 + 8192)
    (hgd : (if bget g 25 = 3 then (if b = 1 then (0 : UInt64) else (if v201 16777216 g a = 0 then 1 else 0)) else 0) ≠ 1) :
    v133 g a b = v1 (asgHeap g a (bget g 25)
        (if (if bget g 25 = 3 then (if b = 1 then v201 16777216 g a else 1) else 1) = 0 then 1 else 0)
        (if bget g 25 < 5 then 1 else bget g ((d7 + 8192) + 3 * (bget g 25 - 5) + 2))) 68 (a + 1) b := by
  have r1 := rowCell i0 hi0 1 (by decide); have r2 := rowCell i0 hi0 2 (by decide); have r3 := rowCell i0 hi0 3 (by decide)
  have cr2 := defCell D hD 2 (by decide); have cr6 := defCell D hD 6 (by decide)
  simp only [show (1 : UInt64).toNat = 1 from rfl, show (2 : UInt64).toNat = 2 from rfl, show (3 : UInt64).toNat = 3 from rfl,
    show (6 : UInt64).toNat = 6 from rfl] at r1 r2 r3 cr2 cr6
  rw [← ha] at r1 r2 r3
  rw [← h12] at cr2 cr6
  have e6 : d7 + 8 * bget g 12 + 2 + 4 = d7 + 8 * bget g 12 + 6 := by rw [UInt64.add_assoc]; rfl
  have pc : ((d7 + 4096) + bget g 27).toNat = 151616 + J := by
    rw [h27, UInt64.toNat_add, show (d7 + 4096 : UInt64).toNat = 151616 from rfl]; simp; omega
  have j4 : bget g 27 < 4096 := by rw [h27, UInt64.lt_iff_toNat_lt]; simp; omega
  have u11 : (11 : UInt64).toNat = 11 := rfl
  have u12 : (12 : UInt64).toNat = 12 := rfl
  have u27 : (27 : UInt64).toNat = 27 := rfl
  have u31 : (31 : UInt64).toNat = 31 := rfl
  -- reads through the three binding-row writes
  have A : ∀ (x1 x2 x3 j : UInt64), (j.toNat < 180288 ∨ 184384 ≤ j.toNat) →
      bget (bset (bset (bset g (d9 + 4 * a + 1) x1) (d9 + 4 * a + 2) x2) (d9 + 4 * a + 3) x3) j = bget g j := fun x1 x2 x3 j hj => by
    rw [bget_bset' _ _ _ _ (by rw [r3]; omega), bget_bset' _ _ _ _ (by rw [r2]; omega), bget_bset' _ _ _ _ (by rw [r1]; omega)]
  have LA : ∀ (x1 x2 x3 : UInt64), (bset (bset (bset g (d9 + 4 * a + 1) x1) (d9 + 4 * a + 2) x2) (d9 + 4 * a + 3) x3).length = g.length :=
    fun _ _ _ => by simp only [length_bset]
  have B31 : ∀ (X : Buf) (z : UInt64), 31 < X.length → bget (bset X 31 z) 31 = z := fun X z h => bget_bset_same _ _ _ h
  have B11 : ∀ (x1 x2 x3 z : UInt64),
      bget (bset (bset (bset (bset g (d9 + 4 * a + 1) x1) (d9 + 4 * a + 2) x2) (d9 + 4 * a + 3) x3) 31 z) 11 = bget g 11 :=
    fun x1 x2 x3 z => by rw [bget_bset' _ _ _ _ (by decide), A _ _ _ _ (Or.inl (by decide))]
  have B27 : ∀ (x1 x2 x3 z v : UInt64),
      bget (bset (bset (bset (bset (bset g (d9 + 4 * a + 1) x1) (d9 + 4 * a + 2) x2) (d9 + 4 * a + 3) x3) 31 z) 11 v) 27 = bget g 27 :=
    fun x1 x2 x3 z v => by rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide), A _ _ _ _ (Or.inl (by decide))]
  have C : ∀ (x1 x2 x3 z v pv jv j : UInt64), j.toNat < 147520 + 8 * 512 → j.toNat ≠ 11 → j.toNat ≠ 27 → j.toNat ≠ 31 →
      bget (bset (bset (bset (bset (bset (bset (bset g (d9 + 4 * a + 1) x1) (d9 + 4 * a + 2) x2) (d9 + 4 * a + 3) x3) 31 z) 11 v)
        ((d7 + 4096) + bget g 27) pv) 27 jv) j = bget g j := fun x1 x2 x3 z v pv jv j h1 h2 h3 h4 => by
    rw [bget_bset' _ _ _ _ (by rw [u27]; omega), bget_bset' _ _ _ _ (by rw [pc]; omega), bget_bset' _ _ _ _ (by rw [u11]; omega),
      bget_bset' _ _ _ _ (by rw [u31]; omega), A _ _ _ _ (Or.inl (by omega))]
  have C6 : ∀ (x1 x2 x3 z v pv jv cv : UInt64),
      bget (bset (bset (bset (bset (bset (bset (bset (bset g (d9 + 4 * a + 1) x1) (d9 + 4 * a + 2) x2) (d9 + 4 * a + 3) x3) 31 z) 11 v)
        ((d7 + 4096) + bget g 27) pv) 27 jv) (d7 + 8 * bget g 12 + 2) cv) (d7 + 8 * bget g 12 + 2 + 4) = bget g (d7 + 8 * bget g 12 + 2 + 4) :=
    fun x1 x2 x3 z v pv jv cv => by
      rw [bget_bset' _ _ _ _ (by rw [e6, cr2, cr6]; omega), C _ _ _ _ _ _ _ _ (by rw [e6, cr6]; omega) (by rw [e6, cr6]; omega)
        (by rw [e6, cr6]; omega) (by rw [e6, cr6]; omega)]
  have B31' : ∀ (x1 x2 x3 z : UInt64),
      bget (bset (bset (bset (bset g (d9 + 4 * a + 1) x1) (d9 + 4 * a + 2) x2) (d9 + 4 * a + 3) x3) 31 z) 31 = z :=
    fun x1 x2 x3 z => B31 _ z (by rw [LA]; omega)
  have C12 : ∀ (x1 x2 x3 z v pv jv : UInt64),
      bget (bset (bset (bset (bset (bset (bset (bset g (d9 + 4 * a + 1) x1) (d9 + 4 * a + 2) x2) (d9 + 4 * a + 3) x3) 31 z) 11 v)
        ((d7 + 4096) + bget g 27) pv) 27 jv) 12 = bget g 12 :=
    fun x1 x2 x3 z v pv jv => C x1 x2 x3 z v pv jv 12 (by decide) (by decide) (by decide) (by decide)
  have CCR : ∀ (x1 x2 x3 z v pv jv : UInt64),
      bget (bset (bset (bset (bset (bset (bset (bset g (d9 + 4 * a + 1) x1) (d9 + 4 * a + 2) x2) (d9 + 4 * a + 3) x3) 31 z) 11 v)
        ((d7 + 4096) + bget g 27) pv) 27 jv) (d7 + 8 * bget g 12 + 2) = bget g (d7 + 8 * bget g 12 + 2) :=
    fun x1 x2 x3 z v pv jv => C x1 x2 x3 z v pv jv _ (by rw [cr2]; omega) (by rw [cr2]; omega) (by rw [cr2]; omega) (by rw [cr2]; omega)
  unfold v133 v9 asgHeap
  simp only [beq_iff_eq, hne, hw4, k0, k1, if_false, hgd]
  by_cases h5 : bget g 25 < 5
  · simp only [h5, if_true]
    simp only [B11, B27, j4, if_true, B31', C12, CCR, C6]
  · have h5' : 5 ≤ (bget g 25).toNat := by
      rcases Nat.lt_or_ge (bget g 25).toNat 5 with h | h
      · exact absurd (UInt64.lt_iff_toNat_lt.mpr h) h5
      · exact h
    have sr := shapeRow (bget g 25) h5' hwb 2 (by decide)
    simp only [h5, if_false]
    rw [A _ _ _ _ (Or.inl (by rw [sr]; simp; omega))]
    simp only [B11, B27, j4, if_true, B31', C12, CCR, C6]

end ParInv
