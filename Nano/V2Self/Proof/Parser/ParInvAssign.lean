/- Nano/V2Self/Proof/Parser/ParInvAssign: Layer 3, pieces for task 68 `assign` (v133), box G.
`v201_eq`: the scan for an earlier INPUT-flagged binding = `(binds.take i).any Bd.inp`. -/
import Nano.V2Self.Proof.Parser.ParInvGroup
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
    (hgd : (if bget g 25 = 3 then (if b = 1 then (0 : UInt64) else (if v201 16777216 g a = 0 then 1 else 0)) else 0) ≠ 1)
    (hcap : ¬ (1048575 : UInt64) < bget g 11 + (if bget g 25 < 5 then 1 else bget g ((d7 + 8192) + 3 * (bget g 25 - 5) + 2)) - (if bget g 25 < 5 then 1 else bget g ((d7 + 8192) + 3 * (bget g 25 - 5) + 2)) * (if (if bget g 25 = 3 then (if b = 1 then v201 16777216 g a else 1) else 1) = 0 then 1 else 0)) :
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
    have hc := hcap; simp only [h5, if_true] at hc; rw [if_neg hc]
  · have h5' : 5 ≤ (bget g 25).toNat := by
      rcases Nat.lt_or_ge (bget g 25).toNat 5 with h | h
      · exact absurd (UInt64.lt_iff_toNat_lt.mpr h) h5
      · exact h
    have sr := shapeRow (bget g 25) h5' hwb 2 (by decide)
    simp only [h5, if_false]
    rw [A _ _ _ _ (Or.inl (by rw [sr]; simp; omega))]
    simp only [B11, B27, j4, if_true, B31', C12, CCR, C6]
    have hc := hcap; simp only [h5, if_false] at hc; rw [if_neg hc]

theorem v133_cap (g : Buf) (a b : UInt64) (i0 D J : Nat) (ha : a = i0.toUInt64) (hi0 : i0 < 1024) (h12 : bget g 12 = D.toUInt64)
    (hD : D < 512) (h27 : bget g 27 = J.toUInt64) (hJ : J < 4096) (hl : 184384 ≤ g.length) (hne : a ≠ bget g 4)
    (hw4 : bget g 25 ≠ 4) (hwb : (bget g 25).toNat < 5 + 8192)
    (hgd : (if bget g 25 = 3 then (if b = 1 then (0 : UInt64) else (if v201 16777216 g a = 0 then 1 else 0)) else 0) ≠ 1)
    (hcap : (1048575 : UInt64) < bget g 11 + (if bget g 25 < 5 then 1 else bget g ((d7 + 8192) + 3 * (bget g 25 - 5) + 2)) - (if bget g 25 < 5 then 1 else bget g ((d7 + 8192) + 3 * (bget g 25 - 5) + 2)) * (if (if bget g 25 = 3 then (if b = 1 then v201 16777216 g a else 1) else 1) = 0 then 1 else 0)) :
    bget (v133 g a b) 0 = 0 := by
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
  unfold v133 v9
  simp only [beq_iff_eq, hne, hw4, k0, k1, if_false, hgd]
  by_cases h5 : bget g 25 < 5
  · simp only [h5, if_true]
    simp only [B11, B27, j4, if_true, B31', C12, CCR, C6]
    have hc := hcap; simp only [h5, if_true] at hc; rw [if_pos hc]; exact status_bset0 _
  · have h5' : 5 ≤ (bget g 25).toNat := by
      rcases Nat.lt_or_ge (bget g 25).toNat 5 with h | h
      · exact absurd (UInt64.lt_iff_toNat_lt.mpr h) h5
      · exact h
    have sr := shapeRow (bget g 25) h5' hwb 2 (by decide)
    simp only [h5, if_false]
    rw [A _ _ _ _ (Or.inl (by rw [sr]; simp; omega))]
    simp only [B11, B27, j4, if_true, B31', C12, CCR, C6]
    have hc := hcap; simp only [h5, if_false] at hc; rw [if_pos hc]; exact status_bset0 _

/-- the cells of `asgHeap` -/
theorem asg_eff (g : Buf) (a wv n1 z : UInt64) (i0 D J : Nat) (ha : a = i0.toUInt64) (hi0 : i0 < 1024) (h12 : bget g 12 = D.toUInt64)
    (hD : D < 512) (h27 : bget g 27 = J.toUInt64) (hJ : J < 4096) (hl : 184384 ≤ g.length) :
    ∀ G, G = asgHeap g a wv n1 z →
    G.length = g.length ∧ bget G (d9 + 4 * a + 1) = bget g 11 ∧ bget G (d9 + 4 * a + 2) = wv ∧ bget G (d9 + 4 * a + 3) = n1 ∧
    bget G 11 = bget g 11 + z - z * n1 ∧ bget G ((d7 + 4096) + bget g 27) = wv ∧ bget G 27 = bget g 27 + 1 ∧
    bget G (d7 + 8 * bget g 12 + 2) = bget g (d7 + 8 * bget g 12 + 2) + 1 - n1 ∧
    bget G (d7 + 8 * bget g 12 + 6) = bget g (d7 + 8 * bget g 12 + 6) + 1 ∧
    (∀ j : UInt64, j.toNat ≠ 11 → j.toNat ≠ 27 → j.toNat ≠ 31 → j.toNat ≠ 151616 + J → j.toNat ≠ 147520 + 8 * D + 2 →
      j.toNat ≠ 147520 + 8 * D + 6 → (j.toNat < 180288 + 4 * i0 + 1 ∨ 180288 + 4 * i0 + 4 ≤ j.toNat) → bget G j = bget g j) ∧
    G.drop 184384 = g.drop 184384 := by
  intro G hG
  subst hG
  have r1 := rowCell i0 hi0 1 (by decide); have r2 := rowCell i0 hi0 2 (by decide); have r3 := rowCell i0 hi0 3 (by decide)
  have cr2 := defCell D hD 2 (by decide); have cr6 := defCell D hD 6 (by decide)
  simp only [show (1 : UInt64).toNat = 1 from rfl, show (2 : UInt64).toNat = 2 from rfl, show (3 : UInt64).toNat = 3 from rfl,
    show (6 : UInt64).toNat = 6 from rfl] at r1 r2 r3 cr2 cr6
  rw [← ha] at r1 r2 r3
  rw [← h12] at cr2 cr6
  have e6 : d7 + 8 * bget g 12 + 2 + 4 = d7 + 8 * bget g 12 + 6 := by rw [UInt64.add_assoc]; rfl
  have pc : ((d7 + 4096) + bget g 27).toNat = 151616 + J := by
    rw [h27, UInt64.toNat_add, show (d7 + 4096 : UInt64).toNat = 151616 from rfl]; simp; omega
  have u11 : (11 : UInt64).toNat = 11 := rfl
  have u27 : (27 : UInt64).toNat = 27 := rfl
  have u31 : (31 : UInt64).toNat = 31 := rfl
  unfold asgHeap
  rw [e6]
  refine ⟨by simp only [length_bset], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bget_bset' _ _ _ _ (by rw [cr6, r1]; omega), bget_bset' _ _ _ _ (by rw [cr2, r1]; omega), bget_bset' _ _ _ _ (by rw [u27, r1]; omega), bget_bset' _ _ _ _ (by rw [pc, r1]; omega), bget_bset' _ _ _ _ (by rw [u11, r1]; omega), bget_bset' _ _ _ _ (by rw [u31, r1]; omega), bget_bset' _ _ _ _ (by rw [r3, r1]; omega), bget_bset' _ _ _ _ (by rw [r2, r1]; omega), bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [r1]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [cr6, r2]; omega), bget_bset' _ _ _ _ (by rw [cr2, r2]; omega), bget_bset' _ _ _ _ (by rw [u27, r2]; omega), bget_bset' _ _ _ _ (by rw [pc, r2]; omega), bget_bset' _ _ _ _ (by rw [u11, r2]; omega), bget_bset' _ _ _ _ (by rw [u31, r2]; omega), bget_bset' _ _ _ _ (by rw [r3, r2]; omega), bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [r2]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [cr6, r3]; omega), bget_bset' _ _ _ _ (by rw [cr2, r3]; omega), bget_bset' _ _ _ _ (by rw [u27, r3]; omega), bget_bset' _ _ _ _ (by rw [pc, r3]; omega), bget_bset' _ _ _ _ (by rw [u11, r3]; omega), bget_bset' _ _ _ _ (by rw [u31, r3]; omega), bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [r3]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [cr6, u11]; omega), bget_bset' _ _ _ _ (by rw [cr2, u11]; omega), bget_bset' _ _ _ _ (by rw [u27, u11]; omega), bget_bset' _ _ _ _ (by rw [pc, u11]; omega), bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [u11]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [cr6, pc]; omega), bget_bset' _ _ _ _ (by rw [cr2, pc]; omega), bget_bset' _ _ _ _ (by rw [u27, pc]; omega), bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [pc]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [cr6, u27]; omega), bget_bset' _ _ _ _ (by rw [cr2, u27]; omega), bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [u27]; omega)]
  · rw [bget_bset' _ _ _ _ (by rw [cr6, cr2]; omega), bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [cr2]; omega)]
  · rw [bget_bset_same _ _ _ (by (try simp only [length_bset]); rw [cr6]; omega)]
  · intro j j11 j27 j31 jpc jc2 jc6 jrow
    rw [bget_bset' _ _ _ _ (by rw [cr6]; omega), bget_bset' _ _ _ _ (by rw [cr2]; omega), bget_bset' _ _ _ _ (by rw [u27]; omega), bget_bset' _ _ _ _ (by rw [pc]; omega), bget_bset' _ _ _ _ (by rw [u11]; omega), bget_bset' _ _ _ _ (by rw [u31]; omega), bget_bset' _ _ _ _ (by rw [r3]; omega), bget_bset' _ _ _ _ (by rw [r2]; omega), bget_bset' _ _ _ _ (by rw [r1]; omega)]
  · rw [drop_bset0 _ _ _ (by rw [cr6]; omega), drop_bset0 _ _ _ (by rw [cr2]; omega), drop_bset0 _ _ _ (by decide),
      drop_bset0 _ _ _ (by rw [pc]; omega), drop_bset0 _ _ _ (by decide), drop_bset0 _ _ _ (by decide),
      drop_bset0 _ _ _ (by rw [r3]; omega), drop_bset0 _ _ _ (by rw [r2]; omega), drop_bset0 _ _ _ (by rw [r1]; omega)]

/-- a def row survives when its 8 cells and its parameter-code cells are unchanged -/
theorem row_frame' {h h' : Buf} {j : Nat} {d : DefR} (r : RowRep h j d)
    (c : ∀ k : UInt64, k.toNat < 8 → bget h' (d7 + 8 * j.toUInt64 + k) = bget h (d7 + 8 * j.toUInt64 + k))
    (cp : ∀ i, i < d.params.length → bget h' (d7 + 4096 + bget h (d7 + 8 * j.toUInt64 + 5) + i.toUInt64) =
      bget h (d7 + 4096 + bget h (d7 + 8 * j.toUInt64 + 5) + i.toUInt64))
    (et : TokAgree h h') (hn : (bget h 7).toNat < 2 ^ 32) (es : ShTabAgree h h') : RowRep h' j d := by
  have c0 := c 0 (by decide); simp only [UInt64.add_zero] at c0
  obtain ⟨a0, a1, a2, a3, a4, a6, a5, ap⟩ := r
  refine ⟨by rw [c0]; exact nameAt_frame et (by omega) a0, by rw [c 1 (by decide)]; exact a1, by rw [c 2 (by decide)]; exact a2,
    by rw [c 3 (by decide)]; exact a3.frame es, by rw [c 4 (by decide)]; exact a4, by rw [c 6 (by decide)]; exact a6,
    by rw [c 5 (by decide)]; exact a5, fun i hi => ?_⟩
  rw [c 5 (by decide), cp i hi]
  exact (ap i hi).frame es

/-- **Rep after v133's writes**: binding `i0` typed (slot = nx, code, input flag), nx advanced by the width unless it is the
input, the current row extended by the parameter code -/
theorem rep_asg {g ts : Buf} {st : St} {fs : List Frame} (R : Rep g ts st fs) (hD : inDefF fs = true) (i0 : Nat)
    (hi : i0 < st.binds.length) (w : Sh) (hty : st.ty = some w) (n1 : Bool) (hnni : st.cur.nni < 2 ^ 63)
    (hJ : (bget g 27).toNat < 4096) :
    Rep (asgHeap g i0.toUInt64 (bget g 25) (b01 n1) w.width.toUInt64) ts
      { st with binds := st.binds.set i0 ⟨(st.binds[i0]'hi).name, st.nx, some w, n1⟩,
                nx := if n1 then st.nx else st.nx + w.width,
                cur := { st.cur with params := st.cur.params ++ [w], nni := if n1 then st.cur.nni else st.cur.nni + 1 } } fs := by
  obtain ⟨hn7, hl, har⟩ := rep_bounds R
  obtain ⟨rT, rts, r0, r3, r11, rB, rD, rA, r25, r29, r30, r32, rO, rK⟩ := R
  rw [hD] at rD
  obtain ⟨b4, bl, brows⟩ := rB
  obtain ⟨d12, dl, d27, drows, dcur, dzero, dz0, ⟨ds26, dsz, dsd⟩, dH⟩ := rD
  simp only [if_true] at dH
  simp only [if_true] at dcur
  obtain ⟨⟨⟨k0, k1, k2, k3, k4, k6, k5, kp⟩, kJ⟩, dl'⟩ := dcur
  have i1024 : i0 < 1024 := by omega
  have h12 : bget g 12 = st.defs.length.toUInt64 := by rw [← d12]; simp
  have h27 : bget g 27 = (bget g 27).toNat.toUInt64 := by simp
  obtain ⟨L, e1, e2, e3, e11, epc, e27, ec2, ec6, U, Dr⟩ :=
    asg_eff g i0.toUInt64 (bget g 25) (b01 n1) w.width.toUInt64 i0 st.defs.length (bget g 27).toNat rfl i1024 h12 dl' h27 hJ hl _ rfl
  generalize asgHeap g i0.toUInt64 (bget g 25) (b01 n1) w.width.toUInt64 = G at L e1 e2 e3 e11 epc e27 ec2 ec6 U Dr ⊢
  rw [h12] at ec2 ec6
  have sc := r25 w hty
  -- cells outside the def table / binding rows and the three scalars
  have cS : ∀ j : UInt64, j.toNat < 64 → j.toNat ≠ 11 → j.toNat ≠ 27 → j.toNat ≠ 31 → bget G j = bget g j :=
    fun j a b c d => U j b c d (by omega) (by omega) (by omega) (Or.inl (by omega))
  have cLo : ∀ j : UInt64, 64 ≤ j.toNat → j.toNat < 147520 → bget G j = bget g j :=
    fun j a b => U j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  have cHi : ∀ j : UInt64, 184384 ≤ j.toNat → bget G j = bget g j :=
    fun j a => U j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inr (by omega))
  have cSh : ∀ j : UInt64, 155712 ≤ j.toNat → j.toNat < 180288 → bget G j = bget g j :=
    fun j a b => U j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  have et : TokAgree g G := ⟨cS 7 (by decide) (by decide) (by decide) (by decide), fun j hj => cHi j hj⟩
  have es : ShTabAgree g G := fun j a b => cSh j a (by omega)
  have scG : ShapeCode G (bget g 25) w := sc.frame es
  refine ⟨tokensAt_frame rT et rts, rts, by rw [cS 0 (by decide) (by decide) (by decide) (by decide)]; exact r0,
    by rw [cS 3 (by decide) (by decide) (by decide) (by decide)]; exact tokAt_frame et hn7 r3, ?_, ?_, ?_,
    arena_frame rA (cS 8 (by decide) (by decide) (by decide) (by decide)) (cS 9 (by decide) (by decide) (by decide) (by decide))
      (fun j a b => cLo j (by omega) b) es,
    fun s' hs' => by rw [cS 25 (by decide) (by decide) (by decide) (by decide)]; exact (r25 s' hs').frame es,
    fun y hy => by rw [cS 29 (by decide) (by decide) (by decide) (by decide)]; exact nameAt_frame et (by omega) (r29 y hy),
    by rw [cS 30 (by decide) (by decide) (by decide) (by decide)]; exact r30,
    by rw [cS 32 (by decide) (by decide) (by decide) (by decide)]; exact r32, out_frame rO Dr,
    tasks_frame rK (cS 5 (by decide) (by decide) (by decide) (by decide)) (fun j a b => cLo j a (by have := rK.2.1; omega)) et hn7 es
      (fun j a b => cLo j (by omega) b) har⟩
  · -- h[11]
    rw [e11, r11]
    cases n1 with
    | true => simp [b01]
    | false => simp [b01]
  · -- bindings
    have cRow : ∀ i, i < 1024 → ∀ k : UInt64, k.toNat < 4 → (i ≠ i0 ∨ k.toNat = 0) →
        bget G (d9 + 4 * i.toUInt64 + k) = bget g (d9 + 4 * i.toUInt64 + k) := fun i hi' k hk hne => by
      have c := rowCell i hi' k hk
      exact U _ (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega)
        (by rw [c]; omega)
    refine ⟨by rw [cS 4 (by decide) (by decide) (by decide) (by decide)]; simpa using b4, by simpa using bl, fun i hi' => ?_⟩
    have hi2 : i < st.binds.length := by simpa using hi'
    dsimp only
    by_cases hii : i = i0
    · subst hii
      obtain ⟨a0, _, _, _⟩ := brows i hi2
      have c0 := cRow i i1024 0 (by decide) (Or.inr rfl); simp only [UInt64.add_zero] at c0
      simp only [List.getElem_set_self]
      exact ⟨by rw [c0]; exact nameAt_frame et (by omega) a0, by rw [e1]; exact r11, by rw [e2]; exact scG, e3⟩
    · obtain ⟨a0, a1, a2, a3⟩ := brows i hi2
      have c := fun k hk => cRow i (by omega) k hk (Or.inl hii)
      have c0 := c 0 (by decide); simp only [UInt64.add_zero] at c0
      simp only [List.getElem_set_ne (Ne.symm hii)]
      exact ⟨by rw [c0]; exact nameAt_frame et (by omega) a0, by rw [c 1 (by decide)]; exact a1,
        by rw [c 2 (by decide)]; exact a2.frame es, by rw [c 3 (by decide)]; exact a3⟩
  · -- def table
    rw [hD]
    unfold DefsRep
    dsimp only
    have cDef : ∀ j, j < 512 → ∀ k : UInt64, k.toNat < 8 → (j ≠ st.defs.length ∨ (k.toNat ≠ 2 ∧ k.toNat ≠ 6)) →
        bget G (d7 + 8 * j.toUInt64 + k) = bget g (d7 + 8 * j.toUInt64 + k) := fun j hj k hk hne => by
      have c := defCell j hj k hk
      exact U _ (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega)
        (Or.inl (by rw [c]; omega))
    have cPar : ∀ (sv : UInt64) (i : Nat), sv.toNat + i < 4096 → sv.toNat + i ≠ (bget g 27).toNat →
        bget G (d7 + 4096 + sv + i.toUInt64) = bget g (d7 + 4096 + sv + i.toUInt64) := fun sv i h1 h2 => by
      have c := parCell sv i h1
      exact U _ (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega)
        (Or.inl (by rw [c]; omega))
    have e27n : (bget G 27).toNat = (bget g 27).toNat + 1 := by rw [e27, tn_add _ _ (by simp; omega)]; rfl
    refine ⟨by rw [cS 12 (by decide) (by decide) (by decide) (by decide)]; exact d12, dl, by rw [e27n]; omega, fun j hj => ?_, ?_,
      fun j h1 h2 k hk => by rw [cDef j h2 k hk (Or.inl (by omega))]; exact dzero j h1 h2 k hk,
      fun i h1 h2 => by
        rw [e27n] at h1
        have c := parCell0 i h2
        rw [U _ (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega) (by rw [c]; omega)
          (Or.inl (by rw [c]; omega))]
        exact dz0 i (by omega) h2,
      ⟨by rw [cS 26 (by decide) (by decide) (by decide) (by decide)]; exact ds26,
      fun k h1 h2 => by
        rw [cS 26 (by decide) (by decide) (by decide) (by decide)] at h1
        have c := shRow0 k h2
        rw [cSh _ (by rw [c]; omega) (by rw [c]; omega)]; exact dsz k h1 h2,
      fun k hk => by
        rw [cS 26 (by decide) (by decide) (by decide) (by decide)] at hk
        obtain ⟨l, r, sa, sb, sw⟩ := dsd k hk
        have cq : ∀ q : UInt64, q.toNat < 3 → bget G (d7 + 8192 + 3 * k.toUInt64 + q) = bget g (d7 + 8192 + 3 * k.toUInt64 + q) :=
          fun q hq => cSh _ (by rw [shRowK k (by omega) q hq]; omega) (by rw [shRowK k (by omega) q hq]; omega)
        have cq0 := cq 0 (by decide); simp only [UInt64.add_zero] at cq0
        exact ⟨l, r, by rw [cq0]; exact sa.frame es, by rw [cq 1 (by decide)]; exact sb.frame es, by rw [cq 2 (by decide)]; exact sw⟩⟩,
      by
        simp only [if_true]
        have rn : ∀ s : St, s.defs = st.defs → s.cur.name = st.cur.name → (rows s).map DefR.name = (rows st).map DefR.name :=
          fun s a b => rows_names a b
        rw [rn _ (by rfl) (by rfl)]
        exact hashRep_frame (by simp [rows]; omega) dH (fun j a _ => cHi j a) (fun i hi => by
          have c := cDef i hi 7 (by decide) (Or.inr ⟨by decide, by decide⟩)
          simpa using c)⟩
    · have hb := (drows j hj).2
      refine ⟨row_frame' (drows j hj).1 (fun k hk => cDef j (by omega) k hk (Or.inl (by omega)))
        (fun i hi' => cPar _ i (by omega) (by omega)) et hn7 es, ?_⟩
      rw [cDef j (by omega) 5 (by decide) (Or.inl (by omega)), e27n]; omega
    · simp only [if_true]
      have c := fun k hk hne => cDef st.defs.length dl' k hk (Or.inr hne)
      have c0 := c 0 (by decide) (by decide); simp only [UInt64.add_zero] at c0
      have c5 := c 5 (by decide) (by decide)
      refine ⟨⟨⟨by rw [c0]; exact nameAt_frame et (by omega) k0, by rw [c 1 (by decide) (by decide)]; exact k1, ?_,
        by rw [c 3 (by decide) (by decide)]; exact k3.frame es, by rw [c 4 (by decide) (by decide)]; exact k4, ?_, ?_, ?_⟩, ?_⟩, dl'⟩
      · rw [ec2]
        cases n1 with
        | true => simpa [b01] using k2
        | false =>
          simp only [b01, Bool.false_eq_true, if_false, UInt64.sub_zero]
          rw [tn_add _ _ (by rw [k2]; simp; omega), k2]; rfl
      · rw [ec6, tn_add _ _ (by rw [k6]; simp; omega), k6]; simp
      · rw [c5]; simp only [List.length_append, List.length_singleton]; omega
      · intro idx hidx
        simp only [List.length_append, List.length_singleton] at hidx
        rw [c5]
        by_cases hlt : idx < st.cur.params.length
        · rw [cPar _ idx (by omega) (by omega)]
          simp only [List.getElem_append_left hlt]
          exact (kp idx hlt).frame es
        · have hid : idx = st.cur.params.length := by omega
          subst hid
          have ecell : d7 + 4096 + bget g (d7 + 8 * st.defs.length.toUInt64 + 5) + st.cur.params.length.toUInt64 =
              d7 + 4096 + bget g 27 := by
            rw [UInt64.add_assoc]; congr 1
            apply UInt64.toNat_inj.mp
            have lenU : (st.cur.params.length.toUInt64).toNat = st.cur.params.length := by simp; omega
            rw [tn_add _ _ (by rw [lenU]; omega), lenU]; omega
          rw [ecell, epc]
          simpa using scG
      · rw [c5, e27n]; simp only [List.length_append, List.length_singleton]; omega

theorem ShapeCode.bound {h : Buf} {c : UInt64} {s : Sh} (r : ShapeCode h c s) : c.toNat < 5 + 8192 := by
  cases r <;> first | decide | assumption

theorem ShapeCode.ls_code {h : Buf} {c : UInt64} (r : ShapeCode h c .ls) : c = 3 := by
  cases r; rfl

/-- the parameter-code area is full: task 68 fails -/
theorem v133_full (g : Buf) (a b : UInt64) (i0 : Nat) (ha : a = i0.toUInt64) (hi0 : i0 < 1024) (hl : 184384 ≤ g.length)
    (hne : a ≠ bget g 4) (hJ : ¬ bget g 27 < 4096) : bget (v133 g a b) 0 = 0 := by
  have r1 := rowCell i0 hi0 1 (by decide); have r2 := rowCell i0 hi0 2 (by decide); have r3 := rowCell i0 hi0 3 (by decide)
  simp only [show (1 : UInt64).toNat = 1 from rfl, show (2 : UInt64).toNat = 2 from rfl, show (3 : UInt64).toNat = 3 from rfl] at r1 r2 r3
  rw [← ha] at r1 r2 r3
  have B27 : ∀ (x1 x2 x3 z v : UInt64),
      bget (bset (bset (bset (bset (bset g (d9 + 4 * a + 1) x1) (d9 + 4 * a + 2) x2) (d9 + 4 * a + 3) x3) 31 z) 11 v) 27 = bget g 27 :=
    fun x1 x2 x3 z v => by
      rw [bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by decide), bget_bset' _ _ _ _ (by rw [r3, show (27 : UInt64).toNat = 27 from rfl]; omega),
        bget_bset' _ _ _ _ (by rw [r2, show (27 : UInt64).toNat = 27 from rfl]; omega), bget_bset' _ _ _ _ (by rw [r1, show (27 : UInt64).toNat = 27 from rfl]; omega)]
  unfold v133 v9
  simp only [beq_iff_eq, hne, if_false, k0, k1]
  by_cases c4 : bget g 25 = 4
  · simp only [c4, if_true]; exact stat0 _ (by omega)
  simp only [c4, if_false]
  by_cases cg : (if bget g 25 = 3 then (if b = 1 then (0 : UInt64) else (if v201 16777216 g a = 0 then 1 else 0)) else 0) = 1
  · simp only [cg, if_true]; exact stat0 _ (by omega)
  simp only [cg, if_false]
  apply ite0 _ _ _ (status_bset0 _)
  simp only [B27, hJ, if_false]
  exact v1_zero _ _ _ _ (stat0 _ (by simp only [length_bset]; omega))

/-! ## task 68: `assign i sz` (v133) -/
theorem h_assign {h ts : Buf} {st : St} {i0 sz : Nat} {fs : List Frame} (r : Rep h ts st (.assign i0 sz :: fs))
    (hD : inDefF fs = true) (hia : i0 ≤ st.binds.length) (hty : st.ty.isSome) (hnni : st.cur.nni < 2 ^ 63)
    (hn20 : st.nx < 2 ^ 20) (hty20 : cw st.ty < 2 ^ 20) (hs : bget (step h) 0 ≠ 0) :
    ∃ fr st', stepF (.assign i0 sz) st = some (fr, st') ∧ Rep (step h) ts st' (fr ++ fs) := by
  obtain ⟨E, ⟨ea, eb⟩, R1⟩ := rep_pop r rfl
  simp only [Frame.code] at E
  generalize (taskAt h fs.length).a = a at E ea
  generalize (taskAt h fs.length).b = b at E eb
  generalize bset h 5 fs.length.toUInt64 = g at E R1
  obtain ⟨hn, hl, har⟩ := rep_bounds R1
  have rB := R1.2.2.2.2.2.1
  have b4 := rB.1; have bl := rB.2.1
  have ev : step h = v133 g a b := by rw [E]; simp [v96]
  rw [ev] at hs ⊢
  have ha : a = i0.toUInt64 := by rw [← ea]; simp
  by_cases ceq : a = bget g 4
  · have hlen : i0 = st.binds.length := by rw [← ea, ceq, b4]
    have e0 : v133 g a b = g := by unfold v133; simp [ceq]
    rw [e0]
    exact ⟨[], st, by simp [stepF, hlen], R1⟩
  have hne : i0 ≠ st.binds.length := fun e => ceq (by apply UInt64.toNat_inj.mp; rw [ea, b4, e])
  have hilt : i0 < st.binds.length := by omega
  have i1024 : i0 < 1024 := by omega
  have hJ : bget g 27 < 4096 := by
    by_cases hJ : bget g 27 < 4096
    · exact hJ
    · exact absurd (v133_full g a b i0 ha i1024 hl ceq hJ) hs
  have hJ' := UInt64.lt_iff_toNat_lt.mp hJ
  simp only [show (4096 : UInt64).toNat = 4096 from rfl] at hJ'
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hty
  have sc := R1.2.2.2.2.2.2.2.2.1 w hw
  have rD : DefsRep g st true := hD ▸ R1.2.2.2.2.2.2.1
  have h12 : bget g 12 = st.defs.length.toUInt64 := by rw [← rD.1]; simp
  have dead : ∀ X : Buf, X.length = g.length → bget X 0 ≠ 0 → X ≠ bset g 0 0 := fun X _ hx e => hx (by rw [e]; exact stat0 _ (by omega))
  by_cases c4 : bget g 25 = 4
  · exfalso; apply hs; unfold v133; simp only [beq_iff_eq, ceq, if_false, c4, if_true]; exact stat0 _ (by omega)
  by_cases cg : (if bget g 25 = 3 then (if b = 1 then (0 : UInt64) else (if v201 16777216 g a = 0 then 1 else 0)) else 0) = 1
  · exfalso; apply hs; unfold v133; simp only [beq_iff_eq, ceq, if_false, c4, k0, k1, cg, if_true]; exact stat0 _ (by omega)
  have dlt : st.defs.length < 512 := by have := rD.2.2.2.2.1; simp only [if_true] at this; exact this.2
  by_cases hcp : (1048575 : UInt64) < bget g 11 + (if bget g 25 < 5 then 1 else bget g ((d7 + 8192) + 3 * (bget g 25 - 5) + 2)) - (if bget g 25 < 5 then 1 else bget g ((d7 + 8192) + 3 * (bget g 25 - 5) + 2)) * (if (if bget g 25 = 3 then (if b = 1 then v201 16777216 g a else 1) else 1) = 0 then 1 else 0)
  · exact absurd (v133_cap g a b i0 st.defs.length (bget g 27).toNat ha i1024 h12 dlt (by simp) hJ' hl ceq c4 sc.bound cg hcp) hs
  rw [v133_eq g a b i0 st.defs.length (bget g 27).toNat ha i1024 h12 dlt (by simp) hJ' hl ceq c4 sc.bound cg hcp] at hs ⊢
  -- decode the machine's flags
  have hw3 : bget g 25 = 3 ↔ w = .ls := ⟨fun e => ShapeCode.det (e ▸ sc) .ls, fun e => (e ▸ sc).ls_code⟩
  have hb1 : b = 1 ↔ sz = 1 := ⟨fun e => by rw [← eb, e]; rfl, fun e => UInt64.toNat_inj.mp (by rw [eb, e]; rfl)⟩
  have hv := v201_eq rB i0 16777216 hia (by omega)
  rw [← ha] at hv
  have hwnt : w ≠ .nt := fun e => c4 (e ▸ sc).nt_code
  have en1 : (if (if bget g 25 = 3 then (if b = 1 then v201 16777216 g a else 1) else 1) = 0 then (1 : UInt64) else 0) =
      b01 (w == .ls && sz == 1 && !((st.binds.take i0).any Bd.inp)) := by
    rw [hv]
    by_cases q1 : w = .ls <;> by_cases q2 : sz = 1 <;> cases q3 : (st.binds.take i0).any Bd.inp <;>
      simp [hw3, hb1, q1, q2, b01]
  have hgj : ¬ (w = .ls ∧ sz ≠ 1 ∧ (!((st.binds.take i0).any Bd.inp)) = true) := by
    rintro ⟨q1, q2, q3⟩
    apply cg
    rw [hv]
    simp only [Bool.not_eq_true'] at q3
    simp [hw3, hb1, q1, q2, q3]
  have ez : (if bget g 25 < 5 then 1 else bget g ((d7 + 8192) + 3 * (bget g 25 - 5) + 2)) = w.width.toUInt64 :=
    v9_cw (o := some w) sc
  have r11 : bget g 11 = st.nx.toUInt64 := R1.2.2.2.2.1
  have hw20 : w.width < 2 ^ 20 := by rw [hw] at hty20; exact hty20
  have capN : ¬ 2 ^ 20 ≤ (if (w == .ls && sz == 1 && !((st.binds.take i0).any Bd.inp)) = true then st.nx
      else st.nx + w.width) := by
    rw [en1, ez, r11] at hcp
    cases hn1 : (w == .ls && sz == 1 && !((st.binds.take i0).any Bd.inp))
    · simp only [hn1, b01, Bool.false_eq_true, if_false] at hcp ⊢
      intro hle; apply hcp
      rw [UInt64.lt_iff_toNat_lt, show (1048575 : UInt64).toNat = 1048575 from rfl]
      simp [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show st.nx < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show w.width < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show st.nx + w.width < 2 ^ 64 by omega)]
      omega
    · simp only [if_true]; omega
  rw [en1, ez, ha] at hs ⊢
  have R2 := rep_asg R1 hD i0 hilt w hw (w == .ls && sz == 1 && !((st.binds.take i0).any Bd.inp)) hnni hJ'
  have ea1 : (i0.toUInt64 + 1).toNat = i0 + 1 := by rw [tn_add _ _ (by simp; omega)]; simp; omega
  have R3 := rep_push (.assign (i0 + 1) sz) (i0.toUInt64 + 1) b R2 rfl ⟨ea1, eb⟩ hs
  refine ⟨[.assign (i0 + 1) sz], _, ?_, R3⟩
  simp only [stepF, if_neg hne, hw, List.getElem?_eq_getElem hilt, if_neg hwnt, if_neg hgj, capN, if_false, ↓reduceIte]

end ParInv
