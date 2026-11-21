/- Nano/Parser/ParInvHash: the hashed def lookup `v8` (bucket hash `v84`, chain walk `v83`).
Rows are chained per bucket: the bucket cell `d9 + d10 + b` holds the newest row (1-based) of bucket `b`, slot 7 of row `i`
the next older row of the same bucket (`HashRep`).  `v8_lookup`: the walk finds the same row as the linear scan `idxOf`
(rows of other buckets cannot match: equal spellings hash alike). -/
import Nano.Parser.ParInv
namespace ParInv
open C BufL

/-- `v84`'s value on a spelling -/
def hashL : List UInt64 → UInt64 → UInt64
  | [], s => s
  | c :: t, s => hashL t (s * 33 + c)

/-- the bucket of a spelling (as in `v8` / `v127`) -/
def bkt (nm : List UInt64) : UInt64 := hashL nm 0 &&& 1023

/-- the bucket of a spelling written with `Nat` bytes (`DefR.name`) -/
def bktN (x : List Nat) : UInt64 := bkt (x.map Nat.toUInt64)

/-- the newest row (1-based) below `m` with property `p`, 0 if none -/
def topR (p : Nat → Prop) [DecidablePred p] : Nat → Nat
  | 0 => 0
  | m + 1 => if p m then m + 1 else topR p m

/-- the bucket chains of the rows with spellings `ns` (bottom first) -/
def HashRep (h : Buf) (ns : List (List Nat)) : Prop :=
  (∀ b : UInt64, b.toNat < 1024 → bget h (d9 + d10 + b) = (topR (fun i => bktN (ns.getD i []) = b) ns.length).toUInt64) ∧
  ∀ i, i < ns.length → bget h (d7 + 8 * i.toUInt64 + 7) = (topR (fun k => bktN (ns.getD k []) = bktN (ns.getD i [])) i).toUInt64

theorem topR_le (p : Nat → Prop) [DecidablePred p] : ∀ m, topR p m ≤ m
  | 0 => Nat.le_refl _
  | m + 1 => by
    simp only [topR]; split
    · omega
    · exact Nat.le_succ_of_le (topR_le p m)

theorem topR_zero (p : Nat → Prop) [DecidablePred p] : ∀ m, topR p m = 0 → ∀ i, i < m → ¬ p i
  | 0, _, i, hi => absurd hi (by omega)
  | m + 1, e, i, hi => by
    simp only [topR] at e
    split at e
    · omega
    · rename_i hm
      by_cases q : i = m
      · subst q; exact hm
      · exact topR_zero p m e i (by omega)

theorem topR_succ (p : Nat → Prop) [DecidablePred p] : ∀ m k, topR p m = k + 1 →
    k < m ∧ p k ∧ topR p k = topR p k ∧ ∀ i, k < i → i < m → ¬ p i
  | 0, k, e => by simp [topR] at e
  | m + 1, k, e => by
    simp only [topR] at e
    split at e
    · rename_i hm
      have : k = m := by omega
      subst this
      exact ⟨by omega, hm, rfl, fun i a b => absurd b (by omega)⟩
    · rename_i hm
      obtain ⟨a, b, _, d⟩ := topR_succ p m k e
      refine ⟨by omega, b, rfl, fun i i1 i2 => ?_⟩
      by_cases q : i = m
      · subst q; exact hm
      · exact d i i1 (by omega)

theorem topR_snoc_self (p : Nat → Prop) [DecidablePred p] (m : Nat) (hm : p m) : topR p (m + 1) = m + 1 := by
  simp [topR, hm]

theorem topR_snoc_other (p : Nat → Prop) [DecidablePred p] (m : Nat) (hm : ¬ p m) : topR p (m + 1) = topR p m := by
  simp [topR, hm]

theorem topR_congr (p q : Nat → Prop) [DecidablePred p] [DecidablePred q] : ∀ m, (∀ i, i < m → (p i ↔ q i)) → topR p m = topR q m
  | 0, _ => rfl
  | m + 1, e => by
    simp only [topR]
    rw [topR_congr p q m (fun i hi => e i (by omega))]
    by_cases hp : p m
    · simp [hp, (e m (by omega)).mp hp]
    · simp [hp, show ¬ q m from fun x => hp ((e m (by omega)).mpr x)]

/-- `idxOf` skips rows that do not match -/
theorem idxOf_skip (tab : List (UInt64 × List UInt64)) (nx : List UInt64) (a : Nat) :
    ∀ b, a ≤ b → (∀ i, a ≤ i → i < b → (tab.getD i (0, [])).2 ≠ nx) → idxOf tab nx b = idxOf tab nx a
  | 0, hab, _ => by
    have : a = 0 := by omega
    subst this; rfl
  | b + 1, hab, e => by
    by_cases q : a = b + 1
    · subst q; rfl
    · simp only [idxOf, if_neg (e b (by omega) (by omega))]
      exact idxOf_skip tab nx a b (by omega) (fun i i1 i2 => e i i1 (by omega))

theorem idxOf_none (tab : List (UInt64 × List UInt64)) (nx : List UInt64) (b : Nat)
    (e : ∀ i, i < b → (tab.getD i (0, [])).2 ≠ nx) : idxOf tab nx b = 0 :=
  (idxOf_skip tab nx 0 b (by omega) (fun i _ i2 => e i i2)).trans rfl

/-- **`v84` = `hashL`** on a spelling in the token region -/
theorem v84_hash : ∀ (l : List UInt64) (n : Nat) (h : Buf) (a s : UInt64), l.length + 1 ≤ n → NameSeq h a l → v84 n h a s = hashL l s
  | [], n + 1, h, a, s, _, e => by
    simp only [NameSeq] at e
    simp [v84, e, hashL]
  | c :: t, n + 1, h, a, s, hn, e => by
    simp only [NameSeq] at e
    obtain ⟨e1, e2, e3⟩ := e
    simp only [v84, e1, beq_self_eq_true, if_true, e2, hashL]
    exact v84_hash t n h (a + 2) (s * 33 + c) (by simp at hn; omega) e3

theorem bkt_lt (nm : List UInt64) : (bkt nm).toNat < 1024 := by
  unfold bkt
  have : hashL nm 0 &&& 1023 ≤ 1023 := UInt64.and_le_right
  rw [UInt64.le_iff_toNat_le] at this
  have : (1023 : UInt64).toNat = 1023 := rfl
  omega

/-- the chain facts the walk needs (slot 7 of every row of the bucket `B` below the row count) -/
def ChainAt (h : Buf) (tab : List (UInt64 × List UInt64)) (B : UInt64) : Prop :=
  ∀ i, i < tab.length → bkt (tab.getD i (0, [])).2 = B →
    bget h (d7 + 8 * i.toUInt64 + 7) = (topR (fun k => bkt (tab.getD k (0, [])).2 = B) i).toUInt64

theorem chainAt_same {r : Nat} {h h' : Buf} (s : Same r h h') (hr : r < 147520) {tab : List (UInt64 × List UInt64)} {B : UInt64}
    (hl : tab.length < 2 ^ 20) (c : ChainAt h tab B) : ChainAt h' tab B := fun i hi hb => by
  have q : (d7 + 8 * i.toUInt64 + 7).toNat = 147520 + 8 * i + 7 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, d7v]; simp [UInt64.toNat_ofNat']; omega
  rw [s.2 _ (by rw [q]; omega) (by rw [q]; omega)]; exact c i hi hb

theorem row_cell (i : Nat) (hi : i < 2 ^ 20) : (d7 + 8 * i.toUInt64).toNat = 147520 + 8 * i := by
  rw [UInt64.toNat_add, UInt64.toNat_mul, d7v]; simp [UInt64.toNat_ofNat']; omega

/-- **the chain walk**: started at the newest row below `m` of the name's bucket, `v83` finds the last match among the first
`min j m` rows; only the scratch cells h[22], h[31] change -/
theorem v83_walk (tab : List (UInt64 × List UInt64)) (x : UInt64) (nx : List UInt64) (jn : Nat) (j : UInt64) (hj : j.toNat = jn) :
    ∀ (n m : Nat) (h : Buf), m ≤ tab.length → tab.length < 2 ^ 20 → m + 1 ≤ n →
      31 < h.length → (bget h 7).toNat < 2 ^ 40 → DefTabRep h tab → ChainAt h tab (bkt nx) → NameOK h x nx → nx.length < 2 ^ 24 →
      Same 22 h (v83 n h j x (topR (fun k => bkt (tab.getD k (0, [])).2 = bkt nx) m).toUInt64) ∧
      bget (v83 n h j x (topR (fun k => bkt (tab.getD k (0, [])).2 = bkt nx) m).toUInt64) 22 = (idxOf tab nx (min jn m)).toUInt64
  | n + 1, m, h, hm, hl, hn, h31, h7, tr, ch, nm, nl => by
    generalize hc : topR (fun k => bkt (tab.getD k (0, [])).2 = bkt nx) m = c
    have l22 : (22 : UInt64).toNat < h.length := by show 22 < h.length; omega
    have l31 : (31 : UInt64).toNat < h.length := h31
    -- rows of other buckets never match
    have nomt : ∀ i, bkt (tab.getD i (0, [])).2 ≠ bkt nx → (tab.getD i (0, [])).2 ≠ nx := fun i a b => a (by rw [b])
    cases c with
    | zero =>
      have z := topR_zero _ m hc
      simp only [v83, show ((0 : Nat).toUInt64 == 0) = true from rfl, if_true]
      refine ⟨same_bset 22 h 22 0 (Or.inl rfl), ?_⟩
      rw [bget_bset_same _ _ _ l22, idxOf_none tab nx _ (fun i hi => nomt i (z i (by omega)))]; rfl
    | succ k =>
      obtain ⟨hk, pk, _, gap⟩ := topR_succ _ m k hc
      have hk20 : k < 2 ^ 20 := by omega
      have cne : ((k + 1).toUInt64 == 0) = false := by
        have : (k + 1).toUInt64 ≠ 0 := fun e => by
          have := congrArg UInt64.toNat e; simp [UInt64.toNat_ofNat'] at this; omega
        simpa using this
      have csub : (k + 1).toUInt64 - 1 = k.toUInt64 := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp [UInt64.toNat_ofNat']; omega)]
        simp [UInt64.toNat_ofNat']; omega
      have tk := tr k (by omega)
      have getD : tab.getD k (0, []) = tab[k]'(by omega) := by simp [List.getD, show k < tab.length by omega]
      have nxt : bget h (d7 + 8 * k.toUInt64 + 7) = (topR (fun i => bkt (tab.getD i (0, [])).2 = bkt nx) k).toUInt64 :=
        ch k (by omega) pk
      -- the rows strictly between k and m do not match
      have skipm : idxOf tab nx (min jn m) = idxOf tab nx (min jn (k + 1)) :=
        idxOf_skip tab nx _ _ (by omega) (fun i i1 i2 => nomt i (gap i (by omega) (by omega)))
      by_cases jc : j < (k + 1).toUInt64
      · have jk : jn ≤ k := by rw [UInt64.lt_iff_toNat_lt] at jc; simp [UInt64.toNat_ofNat'] at jc; omega
        have stp : v83 (n + 1) h j x (k + 1).toUInt64 = v83 n h j x (topR (fun i => bkt (tab.getD i (0, [])).2 = bkt nx) k).toUInt64 := by
          simp only [v83, cne, Bool.false_eq_true, if_false, jc, if_true, csub, nxt]
        rw [stp]
        have ih := v83_walk tab x nx jn j hj n k h (by omega) hl (by omega) h31 h7 tr ch nm nl
        refine ⟨ih.1, ?_⟩
        rw [ih.2, skipm, show min jn (k + 1) = jn by omega, show min jn k = jn by omega]
      · have jk : k < jn := by rw [UInt64.lt_iff_toNat_lt] at jc; simp [UInt64.toNat_ofNat'] at jc; omega
        obtain ⟨t1, t2, t3⟩ := tk
        obtain ⟨n1, n2, n3⟩ := nm
        obtain ⟨u1, u2, u3⟩ := t2
        have p1 : (x + 1).toNat = x.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
        have q1 : ((tab[k]'(by omega)).1 + 1).toNat = (tab[k]'(by omega)).1.toNat + 1 := by
          rw [UInt64.toNat_add]; simp; omega
        have eq85 := v85_name (tab[k]'(by omega)).2 nx 16777216 h ((tab[k]'(by omega)).1 + 1) (x + 1) (by omega) u2 n2
          (by rw [q1]; omega) (by rw [p1]; omega)
        have hcell : bget h (d7 + 8 * k.toUInt64) = (tab[k]'(by omega)).1 := t1
        by_cases hq : (tab[k]'(by omega)).2 = nx
        · have stp : v83 (n + 1) h j x (k + 1).toUInt64 = bset (bset h 31 1) 22 (k + 1).toUInt64 := by
            simp only [v83, cne, Bool.false_eq_true, if_false, jc, csub, hcell, eq85, if_pos hq]
            rw [bget_bset_same _ _ _ l31]; rfl
          rw [stp]
          refine ⟨(same_bset 22 h 31 1 (Or.inr rfl)).trans (same_bset 22 _ 22 _ (Or.inl rfl)), ?_⟩
          rw [bget_bset_same _ _ _ (by simpa [bset] using l22), skipm, show min jn (k + 1) = k + 1 by omega]
          simp only [idxOf, getD, hq, if_true]
        · have stp : v83 (n + 1) h j x (k + 1).toUInt64 =
              v83 n (bset h 31 0) j x (topR (fun i => bkt (tab.getD i (0, [])).2 = bkt nx) k).toUInt64 := by
            simp only [v83, cne, Bool.false_eq_true, if_false, jc, csub, hcell, eq85, if_neg hq]
            rw [bget_bset_same _ _ _ l31]
            have : ((0 : UInt64) == 1) = false := by decide
            simp only [this, Bool.false_eq_true, if_false]
            rw [bget_bset_other _ _ _ _ (by
              have := row_cell k hk20
              rw [UInt64.toNat_add, this]; simp; omega), nxt]
          rw [stp]
          have s1 := same_bset 22 h 31 0 (Or.inr rfl)
          have ih := v83_walk tab x nx jn j hj n k (bset h 31 0) (by omega) hl (by omega) (by simpa [bset] using h31)
            (by rw [s1.2 7 (by decide) (by decide)]; exact h7)
            (defTabRep_same s1 ⟨by omega, by omega⟩ h7 hl tr) (chainAt_same s1 (by omega) hl ch)
            (nameOK_same s1 ⟨by omega, by omega⟩ h7 ⟨n1, n2, n3⟩) nl
          refine ⟨s1.trans ih.1, ?_⟩
          rw [ih.2, skipm, show min jn (k + 1) = k + 1 by omega, show min jn k = k by omega]
          simp only [idxOf, getD, hq, if_false]

/-- **v8 = innermost-def lookup** among the first `j` of the rows `tab`, through the name's bucket chain; only the scratch
cells h[22], h[31] change -/
theorem v8_lookup (tab : List (UInt64 × List UInt64)) (x : UInt64) (nx : List UInt64) (jn : Nat) (h : Buf) (j : UInt64)
    (hj : j.toNat = jn) (hjt : jn ≤ tab.length) (hl : tab.length < 2 ^ 20) (h31 : 31 < h.length) (h7 : (bget h 7).toNat < 2 ^ 40)
    (tr : DefTabRep h tab) (hb : bget h (d9 + d10 + bkt nx) = (topR (fun k => bkt (tab.getD k (0, [])).2 = bkt nx) tab.length).toUInt64)
    (ch : ChainAt h tab (bkt nx)) (nm : NameOK h x nx) (nl : nx.length < 2 ^ 24) :
    Same 22 h (v8 h j x) ∧ bget (v8 h j x) 22 = (idxOf tab nx jn).toUInt64 := by
  have e : v8 h j x = v83 16777216 h j x (topR (fun k => bkt (tab.getD k (0, [])).2 = bkt nx) tab.length).toUInt64 := by
    unfold v8
    rw [v84_hash nx 16777216 h (x + 1) 0 (by omega) nm.2.1, ← hb]; rfl
  rw [e]
  have w := v83_walk tab x nx jn j hj 16777216 tab.length h (Nat.le_refl _) hl (by omega) h31 h7 tr ch nm nl
  rwa [show min jn tab.length = jn by omega] at w

/-! ## the bucket chains as part of `DefsRep` -/
theorem bktCell (b : UInt64) (hb : b.toNat < 1024) : (d9 + d10 + b).toNat = 184384 + b.toNat := by
  rw [UInt64.toNat_add, show (d9 + d10 : UInt64).toNat = 184384 from rfl]; omega

theorem slot7Cell (i : Nat) (hi : i < 512) : (d7 + 8 * i.toUInt64 + 7).toNat = 147520 + 8 * i + 7 := by
  rw [UInt64.toNat_add, row_cell i (by omega)]; simp; omega

theorem bktN_map (l : List UInt64) : bktN (l.map UInt64.toNat) = bkt l := by
  simp [bktN, List.map_map, Function.comp_def]

/-- `HashRep` reads the bucket cells and slot 7 of the rows only -/
theorem hashRep_frame {h h' : Buf} {ns : List (List Nat)} (hl : ns.length ≤ 512) (r : HashRep h ns)
    (eb : ∀ i : UInt64, 184384 ≤ i.toNat → i.toNat < 185408 → bget h' i = bget h i)
    (e7 : ∀ i, i < 512 → bget h' (d7 + 8 * i.toUInt64 + 7) = bget h (d7 + 8 * i.toUInt64 + 7)) : HashRep h' ns :=
  ⟨fun b hb => by rw [eb _ (by rw [bktCell b hb]; omega) (by rw [bktCell b hb]; omega)]; exact r.1 b hb,
   fun i hi => by rw [e7 i (by omega)]; exact r.2 i hi⟩

/-- no rows: all buckets empty -/
theorem hashRep_nil {h : Buf} (z : ∀ i : UInt64, 184384 ≤ i.toNat → i.toNat < 185408 → bget h i = 0) : HashRep h [] :=
  ⟨fun b hb => by rw [z _ (by rw [bktCell b hb]; omega) (by rw [bktCell b hb]; omega)]; rfl, fun i hi => absurd hi (by simp)⟩

/-- **registering a row**: its slot 7 takes the old head of its bucket, the bucket cell the new row -/
theorem hashRep_snoc {h h' : Buf} {ns : List (List Nat)} (x : List Nat) (hl : ns.length < 512) (r : HashRep h ns)
    (eb : ∀ b : UInt64, b.toNat < 1024 → b ≠ bktN x → bget h' (d9 + d10 + b) = bget h (d9 + d10 + b))
    (enew : bget h' (d9 + d10 + bktN x) = (ns.length + 1).toUInt64)
    (e7 : ∀ i, i < ns.length → bget h' (d7 + 8 * i.toUInt64 + 7) = bget h (d7 + 8 * i.toUInt64 + 7))
    (e7new : bget h' (d7 + 8 * ns.length.toUInt64 + 7) = bget h (d9 + d10 + bktN x)) : HashRep h' (ns ++ [x]) := by
  have gl : ∀ k, k < ns.length → (ns ++ [x]).getD k [] = ns.getD k [] := fun k hk => by
    simp [List.getD, List.getElem?_append_left hk]
  have gx : (ns ++ [x]).getD ns.length [] = x := by simp [List.getD]
  have tc : ∀ (p : List Nat → Prop) [DecidablePred p], ∀ m, m ≤ ns.length →
      topR (fun k => p ((ns ++ [x]).getD k [])) m = topR (fun k => p (ns.getD k [])) m :=
    fun p _ m hm => topR_congr _ _ m (fun k hk => by rw [gl k (by omega)])
  refine ⟨fun b hb => ?_, fun i hi => ?_⟩
  · rw [List.length_append, List.length_singleton]
    by_cases q : bktN x = b
    · subst q
      rw [topR_snoc_self _ ns.length (by rw [gx]), enew]
    · rw [topR_snoc_other _ ns.length (by rw [gx]; exact q), tc (fun l => bktN l = b) ns.length (Nat.le_refl _),
        eb b hb (Ne.symm q), r.1 b hb]
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases q : i = ns.length
    · subst q
      rw [e7new, gx, tc (fun l => bktN l = bktN x) ns.length (Nat.le_refl _), r.1 (bktN x) (bkt_lt _)]
    · rw [e7 i (by omega), r.2 i (by omega), gl i (by omega), tc (fun l => bktN l = bktN (ns.getD i [])) i (by omega)]

/-- the hypotheses of `v8_lookup` from the bucket chains of the same rows -/
theorem hash_ok {h : Buf} {ns : List (List Nat)} {tab : List (UInt64 × List UInt64)} (r : HashRep h ns) (hl : tab.length = ns.length)
    (hn : ∀ i (hi : i < tab.length) (hi' : i < ns.length), (tab[i].2).map UInt64.toNat = ns[i]'hi') (nx : List UInt64) :
    bget h (d9 + d10 + bkt nx) = (topR (fun k => bkt (tab.getD k (0, [])).2 = bkt nx) tab.length).toUInt64 ∧ ChainAt h tab (bkt nx) := by
  have g : ∀ k, k < tab.length → bkt (tab.getD k (0, [])).2 = bktN (ns.getD k []) := fun k hk => by
    have e := hn k hk (by omega)
    simp only [List.getD, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (show k < ns.length by omega), Option.getD_some]
    rw [← e, bktN_map]
  have tc : ∀ (B : UInt64) m, m ≤ tab.length →
      topR (fun k => bkt (tab.getD k (0, [])).2 = B) m = topR (fun k => bktN (ns.getD k []) = B) m :=
    fun B m hm => topR_congr _ _ m (fun k hk => by rw [g k (by omega)])
  refine ⟨by rw [tc _ _ (Nat.le_refl _), hl, r.1 _ (bkt_lt nx)], fun i hi hb => ?_⟩
  rw [tc _ i (by omega), r.2 i (by omega), ← g i hi, hb]

end ParInv
