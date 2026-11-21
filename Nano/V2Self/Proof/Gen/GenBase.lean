/- GenRef, part 0 (source-independent): Gen's state `GS`, the item stack `Stk`, the fixup list `Fx`, append-only
emitters (`em`, `PI`), the per-def context `Cx`, the invariant between items `Inv`, and the buffer / register-file
lemmas the item proofs use.  Nothing here mentions Gen's dispatch (g36/g37) or its encoders. -/
import Nano.V2Self.Proof.Machine.ExprExact
import Nano.V2Self.Proof.Gen.Fixup
import Nano.V2Self.Proof.Machine.CallExact
namespace GenRef
open C CallProbe

structure GS where
  x : Buf
  r : Buf
  o : Buf
  k : Buf
  t : Buf
  f : Buf

def live (s : GS) : Prop := bget s.r 5 ≠ 1 ∧ bget s.r 4 ≠ 1 ∧ ¬ 16777215 < bsize s.o ∧ bget s.r 6 ≠ 0 ∧ 5 ≤ s.r.length

def err (s : GS) : Prop := bget s.r 4 = 1

/-- the code is too big: g39 errs at its next iteration (bsize o is exact below 2^62) -/
def big (s : GS) : Prop := 2 ^ 24 ≤ s.o.length ∧ s.o.length < 2 ^ 62

abbrev Item := UInt64 × UInt64 × UInt64

def Stk (k : Buf) (L : List Item) : Prop :=
  3 * L.length ≤ k.length ∧ ∀ j (e : Item), L[j]? = some e →
    k.getD (3 * j) 0 = e.1 ∧ k.getD (3 * j + 1) 0 = e.2.1 ∧ k.getD (3 * j + 2) 0 = e.2.2

def Fx (f : Buf) (F : List UInt64) : Prop := F.length ≤ f.length ∧ ∀ j < F.length, f.getD j 0 = F.getD j 0

theorem getD_set (l : Buf) (i j : Nat) (v : UInt64) : (l.set i v).getD j 0 = if i = j ∧ i < l.length then v else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h; by_cases h2 : i < l.length <;> simp [h2]
  · simp [h]

theorem g17_get (k : Buf) (j : UInt64) (v : UInt64) (hj : j.toNat ≤ k.length) (hk : k.length < 2 ^ 64) (i : Nat) :
    (g17 k j v).getD i 0 = if i = j.toNat then v else k.getD i 0 := by
  unfold g17
  by_cases h : j < bsize k
  · have h' : j.toNat < k.length := by
      have := UInt64.lt_iff_toNat_lt.mp h; simp [bsize] at this; omega
    simp only [h, if_true, bset, getD_set]
    by_cases hi : i = j.toNat
    · simp [hi, h']
    · simp [hi, Ne.symm hi]
  · have h' : j.toNat = k.length := by
      have : ¬ j.toNat < (bsize k).toNat := fun h2 => h (UInt64.lt_iff_toNat_lt.mpr h2)
      have hb : (bsize k).toNat = k.length := by simp [bsize]; omega
      omega
    simp only [h, if_false, bpush, List.getD_eq_getElem?_getD, List.getElem?_append]
    by_cases hi : i = j.toNat
    · subst hi; simp [h']
    · by_cases hl : i < k.length
      · simp [hl, hi]
      · have : k.length < i := by omega
        simp [hl, hi, List.getElem?_eq_none (by simp; omega : [v].length ≤ i - k.length)]

theorem g17_len (k : Buf) (j v : UInt64) (hj : j.toNat ≤ k.length) (hk : k.length < 2 ^ 64) : (g17 k j v).length = max k.length (j.toNat + 1) := by
  unfold g17
  by_cases h : j < bsize k
  · have h' : j.toNat < k.length := by
      have := UInt64.lt_iff_toNat_lt.mp h; simp [bsize] at this; omega
    simp [h, bset]; omega
  · have h' : j.toNat = k.length := by
      have : ¬ j.toNat < (bsize k).toNat := fun h2 => h (UInt64.lt_iff_toNat_lt.mpr h2)
      have hb : (bsize k).toNat = k.length := by simp [bsize]; omega
      omega
    simp [h, bpush]; omega

/-- the words an append-only emitter adds at code position h -/
def em (F : Buf → Buf) (h : Nat) : List UInt64 := (F (List.replicate h 0)).drop h

def PI (F : Buf → Buf) : Prop := ∀ o : Buf, F o = o ++ em F o.length

theorem pi_bpush (v : UInt64) : PI (fun o => bpush o v) := by intro o; simp [em, bpush]

theorem pi_comp {F G : Buf → Buf} (hF : PI F) (hG : PI G) : PI (fun o => G (F o)) := by
  intro o
  have e1 := hF o; have e2 := hG (F o)
  have e3 := hF (List.replicate o.length 0); have e4 := hG (F (List.replicate o.length 0))
  simp only [em] at *
  rw [e2, e1, e4, e3]; simp [List.append_assoc]

theorem u_toNat (n : Nat) (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by simp [Nat.toUInt64]; omega

theorem u3 (n j : Nat) (h : 3 * n + j < 2 ^ 64) : (n.toUInt64 * 3 + j.toUInt64).toNat = 3 * n + j := by
  simp [Nat.toUInt64, UInt64.toNat_add, UInt64.toNat_mul]; omega

/-- push an item -/
theorem stk_push (k : Buf) (L : List Item) (c a b : UInt64) (hs : Stk k L) (hk : k.length < 2 ^ 62) (hL : L.length < 2 ^ 60) :
    Stk (g18 k L.length.toUInt64 c a b) (L ++ [(c, a, b)]) ∧
    (g18 k L.length.toUInt64 c a b).length = max k.length (3 * L.length + 3) := by
  obtain ⟨h3, hL'⟩ := hs
  have e0 : (L.length.toUInt64 * 3).toNat = 3 * L.length := by
    have := u3 L.length 0 (by omega); simpa using this
  have e1 : (L.length.toUInt64 * 3 + 1).toNat = 3 * L.length + 1 := u3 L.length 1 (by omega)
  have e2 : (L.length.toUInt64 * 3 + 2).toNat = 3 * L.length + 2 := u3 L.length 2 (by omega)
  have l1 := g17_len k (L.length.toUInt64 * 3) c (by omega) (by omega)
  have l2 := g17_len (g17 k (L.length.toUInt64 * 3) c) (L.length.toUInt64 * 3 + 1) a (by omega) (by omega)
  have l3 := g17_len (g17 (g17 k (L.length.toUInt64 * 3) c) (L.length.toUInt64 * 3 + 1) a) (L.length.toUInt64 * 3 + 2) b
    (by omega) (by omega)
  rw [e0] at l1; rw [e1, l1] at l2; rw [e2, l2] at l3
  have hlen : (g18 k L.length.toUInt64 c a b).length = max k.length (3 * L.length + 3) := by
    unfold g18; rw [l3]; omega
  refine ⟨⟨by rw [hlen]; simp; omega, fun j e hj => ?_⟩, hlen⟩
  unfold g18
  rw [g17_get _ _ _ (by omega) (by omega), g17_get _ _ _ (by omega) (by omega), g17_get _ _ _ (by omega) (by omega),
    g17_get _ _ _ (by omega) (by omega), g17_get _ _ _ (by omega) (by omega), g17_get _ _ _ (by omega) (by omega),
    g17_get _ _ _ (by omega) (by omega), g17_get _ _ _ (by omega) (by omega), g17_get _ _ _ (by omega) (by omega)]
  rw [e0, e1, e2]
  rw [List.getElem?_append] at hj
  by_cases hjl : j < L.length
  · simp only [hjl, if_true] at hj
    obtain ⟨q1, q2, q3⟩ := hL' j e hj
    refine ⟨?_, ?_, ?_⟩ <;> simp only [show ¬ 3 * j = 3 * L.length + 2 by omega, show ¬ 3 * j = 3 * L.length + 1 by omega,
      show ¬ 3 * j = 3 * L.length by omega, show ¬ 3 * j + 1 = 3 * L.length + 2 by omega, show ¬ 3 * j + 1 = 3 * L.length + 1 by omega,
      show ¬ 3 * j + 1 = 3 * L.length by omega, show ¬ 3 * j + 2 = 3 * L.length + 2 by omega, show ¬ 3 * j + 2 = 3 * L.length + 1 by omega,
      show ¬ 3 * j + 2 = 3 * L.length by omega, if_false] <;> assumption
  · simp only [hjl, if_false] at hj
    have hjj : j = L.length := by
      rcases Nat.lt_or_ge j (L.length + 1) with h | h
      · omega
      · simp [List.getElem?_eq_none (by simp; omega : [(c, a, b)].length ≤ j - L.length)] at hj
    subst hjj
    simp at hj; subst hj
    simp

/-- drop the top item -/
theorem stk_pop {k : Buf} {L : List Item} {e : Item} (hs : Stk k (L ++ [e])) : Stk k L :=
  ⟨by have := hs.1; simp at this; omega, fun j e' hj => hs.2 j e' (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]; exact hj)⟩

/-- the top item's fields -/
theorem stk_top {k : Buf} {L : List Item} {e : Item} (hs : Stk k (L ++ [e])) :
    k.getD (3 * L.length) 0 = e.1 ∧ k.getD (3 * L.length + 1) 0 = e.2.1 ∧ k.getD (3 * L.length + 2) 0 = e.2.2 :=
  hs.2 L.length e (by simp)

/-- patch field a of item j -/
theorem stk_set {k : Buf} {L : List Item} (hs : Stk k L) (j : Nat) (e : Item) (hj : L[j]? = some e) (v : UInt64) :
    Stk (k.set (3 * j + 1) v) (L.set j (e.1, v, e.2.2)) := by
  have hjl := (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨by simp; exact hs.1, fun i e' hi => ?_⟩
  simp only [getD_set]
  rw [List.getElem?_set] at hi
  by_cases hij : j = i
  · subst hij
    simp [hjl] at hi; subst hi
    obtain ⟨q1, q2, q3⟩ := hs.2 j e hj
    have : 3 * j + 1 < k.length := by have := hs.1; omega
    simp only [List.getD_eq_getElem?_getD] at q1 q3
    simp [this, q1, q3]
  · simp only [hij, if_false] at hi
    obtain ⟨q1, q2, q3⟩ := hs.2 i e' hi
    refine ⟨?_, ?_, ?_⟩
    · rw [if_neg (by omega)]; exact q1
    · rw [if_neg (by omega)]; exact q2
    · rw [if_neg (by omega)]; exact q3

/-- Gen's per-def constants: the AST, npw, nslots, κ, the def-start table -/
structure Cx where
  X : Buf
  p : UInt64
  ns : UInt64
  u : UInt64
  T : Buf
  q : UInt64

def tg (X : Buf) (i : Nat) : UInt64 := X.getD i 0

/-- a slot range is inside the frame (g43 = 0) -/
def SlotOk (K : Cx) (s w : UInt64) : Prop := w ≠ 0 ∧ s < 251 ∧ w < 251 ∧ ¬ K.ns < s + w

/-- Gen's state is in def context K with pending items L and recorded exits F -/
structure Inv (K : Cx) (s : GS) (L : List Item) (F : List UInt64) : Prop where
  x : s.x = K.X
  t : s.t = K.T
  rl : s.r.length = 10
  r1 : bget s.r 1 = K.p
  r2 : bget s.r 2 = K.q
  r7 : bget s.r 7 = K.ns
  r9 : bget s.r 9 = K.u
  r4 : bget s.r 4 ≠ 1
  r5 : bget s.r 5 ≠ 1
  r6 : bget s.r 6 = L.length.toUInt64
  stk : Stk s.k L
  kl : s.k.length < 2 ^ 62
  Ll : L.length < 2 ^ 60
  fx : Fx s.f F
  r8 : bget s.r 8 = F.length.toUInt64
  fl : s.f.length ≤ 65536
  ol : s.o.length < 2 ^ 24

theorem bget_set (r : Buf) (j : UInt64) (v : UInt64) (i : UInt64) (hj : j.toNat < r.length) :
    bget (bset r j v) i = if j = i then v else bget r i := by
  rw [BufL.bget_bset]
  by_cases h : j = i
  · subst h; simp [hj]
  · have : j.toNat ≠ i.toNat := fun e => h (UInt64.toNat_inj.mp e)
    simp [h, this]

theorem live_of {K s L F} (hI : Inv K s L F) (hL : L ≠ []) : live s := by
  refine ⟨hI.r5, hI.r4, ?_, ?_, by rw [hI.rl]; omega⟩
  · have := hI.ol
    intro h
    have h2 := UInt64.lt_iff_toNat_lt.mp h
    simp only [bsize] at h2
    rw [u_toNat _ (by omega)] at h2; simp at h2; omega
  rw [hI.r6]; intro h
  have h1 := congrArg UInt64.toNat h
  rw [u_toNat L.length (by have := hI.Ll; omega)] at h1
  exact hL (List.length_eq_zero_iff.mp h1)

theorem rget (r : Buf) (hr : r.length = 10) (j i : UInt64) (v : UInt64) (hj : j.toNat < 10) :
    bget (bset r j v) i = if j = i then v else bget r i := bget_set r j v i (by omega)

/-- the register file after an item sets r[6] (the visit's first write): length, r[0] (the cursor), r[6] -/
theorem r6_get {K s L F} (hI : Inv K s L F) {i : Nat} (hr0 : bget s.r 0 = i.toUInt64) (n : UInt64) :
    (bset s.r 6 n).length = 10 ∧ bget (bset s.r 6 n) 0 = i.toUInt64 ∧ bget (bset s.r 6 n) 6 = n :=
  ⟨by rw [BufL.length_bset]; exact hI.rl, by rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0],
    by rw [rget _ hI.rl 6 6 _ (by decide), if_pos rfl]⟩

/-- rebuild Inv after an item that writes only r[0], r[6], k and o -/
theorem inv_mk {K s L0 F} (hI : Inv K s L0 F) (r' k' o' : Buf) (L' : List Item)
    (hr : ∀ j : UInt64, j ≠ 0 → j ≠ 6 → bget r' j = bget s.r j) (hrl : r'.length = 10)
    (h6 : bget r' 6 = L'.length.toUInt64) (hk : Stk k' L') (hkl : k'.length < 2 ^ 62) (hLl : L'.length < 2 ^ 60)
    (ho : o'.length < 2 ^ 24) : Inv K ⟨s.x, r', o', k', s.t, s.f⟩ L' F where
  x := hI.x
  t := hI.t
  rl := hrl
  r1 := by rw [hr 1 (by decide) (by decide)]; exact hI.r1
  r2 := by rw [hr 2 (by decide) (by decide)]; exact hI.r2
  r7 := by rw [hr 7 (by decide) (by decide)]; exact hI.r7
  r9 := by rw [hr 9 (by decide) (by decide)]; exact hI.r9
  r4 := by rw [hr 4 (by decide) (by decide)]; exact hI.r4
  r5 := by rw [hr 5 (by decide) (by decide)]; exact hI.r5
  r6 := h6
  stk := hk
  kl := hkl
  Ll := hLl
  fx := hI.fx
  r8 := by rw [hr 8 (by decide) (by decide)]; exact hI.r8
  fl := hI.fl
  ol := ho

theorem r06 (r : Buf) (hr : r.length = 10) (a b : UInt64) :
    (bset (bset r 6 a) 0 b).length = 10 ∧ bget (bset (bset r 6 a) 0 b) 6 = a ∧ bget (bset (bset r 6 a) 0 b) 0 = b ∧
    ∀ j : UInt64, j ≠ 0 → j ≠ 6 → bget (bset (bset r 6 a) 0 b) j = bget r j := by
  have l1 : (bset r 6 a).length = 10 := by rw [BufL.length_bset]; exact hr
  refine ⟨by rw [BufL.length_bset]; exact l1, ?_, ?_, fun j h0 h6 => ?_⟩
  · rw [rget _ l1 0 6 b (by decide), if_neg (by decide), rget _ hr 6 6 a (by decide), if_pos rfl]
  · rw [rget _ l1 0 0 b (by decide), if_pos rfl]
  · rw [rget _ l1 0 j b (by decide), if_neg (Ne.symm h0), rget _ hr 6 j a (by decide), if_neg (Ne.symm h6)]

theorem tg_u (X : Buf) (i : Nat) (hi : i < 2 ^ 64) : bget X i.toUInt64 = tg X i := by
  simp [bget, tg, u_toNat i hi]

theorem tg_u1 (X : Buf) (i j : Nat) (hi : i + j < 2 ^ 64) : bget X (i.toUInt64 + j.toUInt64) = tg X (i + j) := by
  rw [← tg_u X (i + j) hi]; congr 1; simp [Nat.toUInt64, UInt64.ofNat_add]

theorem u_add (i j : Nat) : i.toUInt64 + j.toUInt64 = (i + j).toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]

theorem em_le (F : Buf → Buf) (h c : Nat) (hF : ∀ o : Buf, (F o).length ≤ o.length + c) : (em F h).length ≤ c := by
  have := hF (List.replicate h 0); simp [em] at *; omega

theorem g43_ok (r : Buf) (s w ns : UInt64) (h7 : bget r 7 = ns) :
    g43 r s w = (if w ≠ 0 ∧ s < 251 ∧ w < 251 ∧ ¬ ns < s + w then 0 else 1) := by
  unfold g43; rw [h7]
  by_cases h1 : w = 0
  · simp [h1, g_1]
  · by_cases h2 : s < 251
    · by_cases h3 : w < 251
      · by_cases h4 : ns < s + w <;> simp [h1, h2, h3, h4, g_1, g_0]
      · simp [h1, h2, h3, g_1]
    · simp [h1, h2, g_1]

theorem g16_err (r : Buf) (hr : r.length = 10) : bget (g16 r) 4 = 1 := by
  unfold g16; rw [rget _ hr 4 4 _ (by decide), if_pos rfl]; rfl

/-- the top item of an Inv state, as g37 reads it -/
theorem top_item {K s L F} {e : Item} (hI : Inv K s (L ++ [e]) F) :
    bget s.r 6 - 1 = L.length.toUInt64 ∧ bget s.k ((bget s.r 6 - 1) * 3) = e.1 ∧
    bget s.k ((bget s.r 6 - 1) * 3 + 1) = e.2.1 ∧ bget s.k ((bget s.r 6 - 1) * 3 + 2) = e.2.2 := by
  have hL := hI.Ll; simp at hL
  obtain ⟨t0, t1, t2⟩ := stk_top hI.stk
  have hn : bget s.r 6 - 1 = L.length.toUInt64 := by
    apply UInt64.toNat.inj; rw [hI.r6]; simp [Nat.toUInt64]
  refine ⟨hn, ?_, ?_, ?_⟩ <;> rw [hn] <;> simp only [bget]
  · rw [show (L.length.toUInt64 * 3).toNat = 3 * L.length by simp [Nat.toUInt64]; omega, t0]
  · rw [show (L.length.toUInt64 * 3 + 1).toNat = 3 * L.length + 1 by simp [Nat.toUInt64]; omega, t1]
  · rw [show (L.length.toUInt64 * 3 + 2).toNat = 3 * L.length + 2 by simp [Nat.toUInt64]; omega, t2]

theorem stk_push3 (k : Buf) (L : List Item) (a b c : Item) (hs : Stk k L) (hk : k.length < 2 ^ 62) (hL : L.length + 3 < 2 ^ 60) :
    Stk (g18 (g18 (g18 k L.length.toUInt64 a.1 a.2.1 a.2.2) (L.length.toUInt64 + 1) b.1 b.2.1 b.2.2)
      (L.length.toUInt64 + 2) c.1 c.2.1 c.2.2) (L ++ [a, b, c]) ∧
    (g18 (g18 (g18 k L.length.toUInt64 a.1 a.2.1 a.2.2) (L.length.toUInt64 + 1) b.1 b.2.1 b.2.2)
      (L.length.toUInt64 + 2) c.1 c.2.1 c.2.2).length < 2 ^ 62 := by
  obtain ⟨s1, l1⟩ := stk_push k L a.1 a.2.1 a.2.2 hs hk (by omega)
  have e1 : L.length.toUInt64 + 1 = (L ++ [(a.1, a.2.1, a.2.2)]).length.toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]
  obtain ⟨s2, l2⟩ := stk_push _ _ b.1 b.2.1 b.2.2 s1 (by rw [l1]; omega) (by simp; omega)
  have e2 : L.length.toUInt64 + 2 = (L ++ [(a.1, a.2.1, a.2.2)] ++ [(b.1, b.2.1, b.2.2)]).length.toUInt64 := by
    simp [Nat.toUInt64, UInt64.ofNat_add]
  rw [← e1] at s2 l2
  obtain ⟨s3, l3⟩ := stk_push _ _ c.1 c.2.1 c.2.2 s2 (by rw [l2, l1]; simp; omega) (by simp; omega)
  rw [← e2] at s3 l3
  refine ⟨by simpa using s3, by rw [l3, l2, l1]; simp; omega⟩

theorem rset2 (r : Buf) (hr : r.length = 10) (j1 j2 v1 v2 : UInt64) (h1 : j1.toNat < 10) (h2 : j2.toNat < 10) (j : UInt64) :
    bget (bset (bset r j1 v1) j2 v2) j = if j2 = j then v2 else if j1 = j then v1 else bget r j := by
  have l1 : (bset r j1 v1).length = 10 := by rw [BufL.length_bset]; exact hr
  rw [rget _ l1 j2 j v2 h2, rget _ hr j1 j v1 h1]

theorem len2 (r : Buf) (hr : r.length = 10) (j1 j2 v1 v2 : UInt64) : (bset (bset r j1 v1) j2 v2).length = 10 := by
  rw [BufL.length_bset, BufL.length_bset]; exact hr

theorem set_mid (A B : Buf) (x v : UInt64) : (A ++ x :: B).set A.length v = A ++ v :: B := by
  simp [List.set_append_right]

theorem r6set (r : Buf) (hr : r.length = 10) (v : UInt64) :
    (bset r 6 v).length = 10 ∧ bget (bset r 6 v) 6 = v ∧ ∀ j : UInt64, j ≠ 6 → bget (bset r 6 v) j = bget r j := by
  refine ⟨by rw [BufL.length_bset]; exact hr, by rw [rget _ hr 6 6 _ (by decide), if_pos rfl], fun j hj => ?_⟩
  rw [rget _ hr 6 j _ (by decide), if_neg (Ne.symm hj)]

/-- push an item at an index given as a UInt64 equal to the stack length -/
theorem stk_push_at (k : Buf) (L : List Item) (n c a b : UInt64) (hn : n = L.length.toUInt64) (hs : Stk k L)
    (hk : k.length < 2 ^ 62) (hL : L.length + 1 < 2 ^ 60) :
    Stk (g18 k n c a b) (L ++ [(c, a, b)]) ∧ (g18 k n c a b).length < 2 ^ 62 := by
  subst hn
  obtain ⟨h1, h2⟩ := stk_push k L c a b hs hk (by omega)
  exact ⟨h1, by rw [h2]; omega⟩

/-- seven pushes (IF) -/
theorem stk_push7 (k : Buf) (L : List Item) (e0 e1 e2 e3 e4 e5 e6 : Item) (hs : Stk k L) (hk : k.length < 2 ^ 62)
    (hL : L.length + 7 < 2 ^ 60) :
    Stk (g18 (g18 (g18 (g18 (g18 (g18 (g18 k L.length.toUInt64 e0.1 e0.2.1 e0.2.2) (L.length.toUInt64 + 1) e1.1 e1.2.1 e1.2.2)
      (L.length.toUInt64 + 2) e2.1 e2.2.1 e2.2.2) (L.length.toUInt64 + 3) e3.1 e3.2.1 e3.2.2) (L.length.toUInt64 + 4) e4.1 e4.2.1 e4.2.2)
      (L.length.toUInt64 + 5) e5.1 e5.2.1 e5.2.2) (L.length.toUInt64 + 6) e6.1 e6.2.1 e6.2.2) (L ++ [e0, e1, e2, e3, e4, e5, e6]) ∧
    (g18 (g18 (g18 (g18 (g18 (g18 (g18 k L.length.toUInt64 e0.1 e0.2.1 e0.2.2) (L.length.toUInt64 + 1) e1.1 e1.2.1 e1.2.2)
      (L.length.toUInt64 + 2) e2.1 e2.2.1 e2.2.2) (L.length.toUInt64 + 3) e3.1 e3.2.1 e3.2.2) (L.length.toUInt64 + 4) e4.1 e4.2.1 e4.2.2)
      (L.length.toUInt64 + 5) e5.1 e5.2.1 e5.2.2) (L.length.toUInt64 + 6) e6.1 e6.2.1 e6.2.2).length < 2 ^ 62 := by
  have q (j : Nat) (M : List Item) (hM : M.length = L.length + j) : L.length.toUInt64 + j.toUInt64 = M.length.toUInt64 := by
    rw [hM]; simp [Nat.toUInt64, UInt64.ofNat_add]
  obtain ⟨s0, l0⟩ := stk_push_at k L _ e0.1 e0.2.1 e0.2.2 rfl hs hk (by omega)
  obtain ⟨s1, l1⟩ := stk_push_at _ _ _ e1.1 e1.2.1 e1.2.2 (q 1 _ (by simp)) s0 l0 (by simp; omega)
  obtain ⟨s2, l2⟩ := stk_push_at _ _ _ e2.1 e2.2.1 e2.2.2 (q 2 _ (by simp)) s1 l1 (by simp; omega)
  obtain ⟨s3, l3⟩ := stk_push_at _ _ _ e3.1 e3.2.1 e3.2.2 (q 3 _ (by simp)) s2 l2 (by simp; omega)
  obtain ⟨s4, l4⟩ := stk_push_at _ _ _ e4.1 e4.2.1 e4.2.2 (q 4 _ (by simp)) s3 l3 (by simp; omega)
  obtain ⟨s5, l5⟩ := stk_push_at _ _ _ e5.1 e5.2.1 e5.2.2 (q 5 _ (by simp)) s4 l4 (by simp; omega)
  obtain ⟨s6, l6⟩ := stk_push_at _ _ _ e6.1 e6.2.1 e6.2.2 (q 6 _ (by simp)) s5 l5 (by simp; omega)
  exact ⟨by simpa using s6, l6⟩

theorem bset_mid (A B : Buf) (x v : UInt64) (p : UInt64) (hp : p.toNat = A.length) :
    bset (A ++ x :: B) p v = A ++ v :: B := by simp only [bset, hp]; exact set_mid A B x v

theorem bsize_u (o : Buf) : bsize o = o.length.toUInt64 := rfl

theorem ulen (l : Buf) (n : Nat) (h : l.length = n) : bsize l = n.toUInt64 := by rw [bsize_u, h]

theorem stk_g27 : ∀ (F : Nat) (k : Buf) (L : List Item) (q : Nat), q ≤ F → Stk k L → k.length < 2 ^ 62 →
    L.length + q < 2 ^ 60 →
    Stk (g27 F k L.length.toUInt64 q.toUInt64) (L ++ List.replicate q (1, 0, 0)) ∧
    (g27 F k L.length.toUInt64 q.toUInt64).length < 2 ^ 62
  | F, k, L, 0, _, hs, hk, _ => by cases F <;> simp [g27, hs, hk]
  | F + 1, k, L, q + 1, hq, hs, hk, hL => by
    have hne : ¬ ((q + 1).toUInt64 == 0) = true := by
      simp [Nat.toUInt64, UInt64.ofNat_add]; intro h; have := congrArg UInt64.toNat h; simp at this; omega
    obtain ⟨s1, l1⟩ := stk_push k L 1 0 0 hs hk (by omega)
    have e1 : L.length.toUInt64 + 1 = (L ++ [(1, 0, 0)]).length.toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]
    have e2 : (q + 1).toUInt64 - 1 = q.toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]
    simp only [g27, hne, if_false, Bool.false_eq_true, e1, e2]
    obtain ⟨s2, l2⟩ := stk_g27 F _ _ q (by omega) s1 (by rw [l1]; omega) (by simp; omega)
    refine ⟨?_, l2⟩
    have : L ++ [(1, 0, 0)] ++ List.replicate q ((1 : UInt64), (0 : UInt64), (0 : UInt64)) = L ++ List.replicate (q + 1) (1, 0, 0) := by
      simp [List.replicate_succ]
    rw [← this]; exact s2
  | 0, k, L, q + 1, hq, _, _, _ => absurd hq (by omega)

theorem u_small (q : UInt64) (h : q < 251) : q.toNat < 251 ∧ q.toNat.toUInt64 = q := by
  refine ⟨UInt64.lt_iff_toNat_lt.mp h, by simp [Nat.toUInt64]⟩

theorem g33_lt (p : UInt64) : g33 p < 4 := by
  unfold g33
  repeat (first | split | decide)

/-- g36's tag normalization and operator-range flag -/
def nt (c0 : UInt64) : UInt64 := if c0 < 7 then c0 else if c0 == 7 then 999 else if c0 < 12 then c0 - 1 else 999

def rngA (c b : UInt64) : UInt64 :=
  if c == 3 then (if b - 1 < 8 then g_1 else g_0) else if c == 4 then (if b - 1 < 2 then g_1 else g_0)
  else if c == 8 then (if b - 1 < 9 then g_1 else g_0) else g_1

theorem nt_toNat (t : UInt64) : (nt t).toNat =
    if t.toNat < 7 then t.toNat else if t.toNat = 7 then 999 else if t.toNat < 12 then t.toNat - 1 else 999 := by
  unfold nt
  by_cases h1 : t < 7
  · have : t.toNat < 7 := UInt64.lt_iff_toNat_lt.mp h1
    rw [if_pos h1, if_pos this]
  · have : ¬ t.toNat < 7 := fun h => h1 (UInt64.lt_iff_toNat_lt.mpr h)
    rw [if_neg h1, if_neg this]
    by_cases h2 : (t == 7) = true
    · have : t.toNat = 7 := by simp at h2; subst h2; rfl
      rw [if_pos h2, if_pos this]; rfl
    · have : ¬ t.toNat = 7 := fun h => h2 (by simp; exact UInt64.toNat.inj h)
      rw [if_neg h2, if_neg this]
      by_cases h3 : t < 12
      · have h3' : t.toNat < 12 := UInt64.lt_iff_toNat_lt.mp h3
        rw [if_pos h3, if_pos h3', UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
      · have : ¬ t.toNat < 12 := fun h => h3 (UInt64.lt_iff_toNat_lt.mpr h)
        rw [if_neg h3, if_neg this]; rfl

/-- the tags that g36 visits as values in tail mode -/
theorem nt_tail (t : UInt64) (h4 : t ≠ 4) (h5 : t ≠ 5) (h11 : t ≠ 11) : nt t ≠ 4 ∧ nt t ≠ 5 ∧ nt t ≠ 10 := by
  have e := nt_toNat t
  have n4 : t.toNat ≠ 4 := fun h => h4 (UInt64.toNat.inj (by rw [h]; rfl))
  have n5 : t.toNat ≠ 5 := fun h => h5 (UInt64.toNat.inj (by rw [h]; rfl))
  have n11 : t.toNat ≠ 11 := fun h => h11 (UInt64.toNat.inj (by rw [h]; rfl))
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> (rw [h] at e; simp at e; split at e <;> (try split at e) <;> (try split at e) <;> omega)

theorem fx_push (f : Buf) (F : List UInt64) (v : UInt64) (hF : Fx f F) (hl : F.length ≤ 65535) (hf : f.length ≤ 65536) :
    Fx (g17 f F.length.toUInt64 v) (F ++ [v]) ∧ (g17 f F.length.toUInt64 v).length ≤ 65536 := by
  have hu : F.length.toUInt64.toNat = F.length := u_toNat _ (by omega)
  have hle : F.length.toUInt64.toNat ≤ f.length := by rw [hu]; exact hF.1
  refine ⟨⟨?_, fun j hj => ?_⟩, ?_⟩
  · rw [g17_len _ _ _ hle (by omega), hu]; simp; omega
  · rw [g17_get _ _ _ hle (by omega), hu]
    by_cases hjF : j = F.length
    · subst hjF; simp
    · rw [if_neg hjF]; simp at hj
      rw [hF.2 j (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j < F.length)]
  · rw [g17_len _ _ _ hle (by omega), hu]; omega

/-- rebuild Inv after an item that writes r[0], r[6], r[8], k, o and f -/
theorem inv_mk2 {K s L0 F} (hI : Inv K s L0 F) (r' k' o' f' : Buf) (L' : List Item) (F' : List UInt64)
    (hr : ∀ j : UInt64, j ≠ 0 → j ≠ 6 → j ≠ 8 → bget r' j = bget s.r j) (hrl : r'.length = 10)
    (h6 : bget r' 6 = L'.length.toUInt64) (hk : Stk k' L') (hkl : k'.length < 2 ^ 62) (hLl : L'.length < 2 ^ 60)
    (hfx : Fx f' F') (h8 : bget r' 8 = F'.length.toUInt64) (hfl : f'.length ≤ 65536)
    (ho : o'.length < 2 ^ 24) : Inv K ⟨s.x, r', o', k', s.t, f'⟩ L' F' where
  x := hI.x
  t := hI.t
  rl := hrl
  r1 := by rw [hr 1 (by decide) (by decide) (by decide)]; exact hI.r1
  r2 := by rw [hr 2 (by decide) (by decide) (by decide)]; exact hI.r2
  r7 := by rw [hr 7 (by decide) (by decide) (by decide)]; exact hI.r7
  r9 := by rw [hr 9 (by decide) (by decide) (by decide)]; exact hI.r9
  r4 := by rw [hr 4 (by decide) (by decide) (by decide)]; exact hI.r4
  r5 := by rw [hr 5 (by decide) (by decide) (by decide)]; exact hI.r5
  r6 := h6
  stk := hk
  kl := hkl
  Ll := hLl
  fx := hfx
  r8 := h8
  fl := hfl
  ol := ho

/-- rebuild Inv after an item that writes r[0], r[3], r[6], k and o -/
theorem inv_mk3 {K s L0 F} (hI : Inv K s L0 F) (r' k' o' : Buf) (L' : List Item)
    (hr : ∀ j : UInt64, j ≠ 0 → j ≠ 3 → j ≠ 6 → bget r' j = bget s.r j) (hrl : r'.length = 10)
    (h6 : bget r' 6 = L'.length.toUInt64) (hk : Stk k' L') (hkl : k'.length < 2 ^ 62) (hLl : L'.length < 2 ^ 60)
    (ho : o'.length < 2 ^ 24) : Inv K ⟨s.x, r', o', k', s.t, s.f⟩ L' F where
  x := hI.x
  t := hI.t
  rl := hrl
  r1 := by rw [hr 1 (by decide) (by decide) (by decide)]; exact hI.r1
  r2 := by rw [hr 2 (by decide) (by decide) (by decide)]; exact hI.r2
  r7 := by rw [hr 7 (by decide) (by decide) (by decide)]; exact hI.r7
  r9 := by rw [hr 9 (by decide) (by decide) (by decide)]; exact hI.r9
  r4 := by rw [hr 4 (by decide) (by decide) (by decide)]; exact hI.r4
  r5 := by rw [hr 5 (by decide) (by decide) (by decide)]; exact hI.r5
  r6 := h6
  stk := hk
  kl := hkl
  Ll := hLl
  fx := hI.fx
  r8 := by rw [hr 8 (by decide) (by decide) (by decide)]; exact hI.r8
  fl := hI.fl
  ol := ho

theorem nt_val (t : UInt64) (v : Nat) (hv : 1 ≤ v ∧ v ≤ 9) (h : nt t = v.toUInt64) :
    t = (if v < 7 then v else v + 1).toUInt64 := by
  have e := nt_toNat t
  rw [h, u_toNat _ (by omega)] at e
  apply UInt64.toNat.inj
  rw [u_toNat _ (by split <;> omega)]
  split at e <;> (try split at e) <;> (try split at e) <;> split <;> omega

theorem tg_lt (X : Buf) (i : Nat) (h : tg X i ≠ 0) : i < X.length := by
  rcases Nat.lt_or_ge i X.length with h1 | h1
  · exact h1
  · exact absurd (by simp [tg, List.getD_eq_getElem?_getD, List.getElem?_eq_none h1]) h

end GenRef
