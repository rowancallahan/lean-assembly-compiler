/- The g39 work-item invariant (Astra-11, Gen soundness on success), part 1: the state, the step, `Reach`, the item
stack and the fixup list as abstract lists.  Gen's main loop `g39` runs `g37` (one work item) while the stop flags are
clear and items are pending; `Reach s P` = after finitely many items, with every intermediate state live, P holds or
the error flag is set (then g39 returns at once and g42 outputs []).  Items are triples (tag, a, b) stored at
k[3j..3j+2]; stale words above the count are ignored (`Stk`).  Fixups likewise (`Fx`, count = r[8]). -/
import Nano.V2Self.Proof.ExprExact
import Nano.V2Self.Proof.Fixup
import Nano.V2Self.Proof.CallExact
namespace GenRef
open C CallProbe

structure GS where
  x : Buf
  r : Buf
  o : Buf
  k : Buf
  t : Buf
  f : Buf

/-- one work item (g39's `bget r 6 ≠ 0` branch) -/
def st (s : GS) : GS :=
  match g37 s.x s.r s.o s.k s.t s.f with
  | (r1, (o1, (k1, f1))) => ⟨s.x, r1, o1, k1, s.t, f1⟩

def live (s : GS) : Prop := bget s.r 5 ≠ 1 ∧ bget s.r 4 ≠ 1 ∧ bget s.r 6 ≠ 0
def err (s : GS) : Prop := bget s.r 4 = 1
/-- the code is too big: code only grows, and g42 outputs [] above 2^24 words -/
def big (s : GS) : Prop := 2 ^ 32 ≤ s.o.length

/-- `it m s` = m work items from s -/
def it : Nat → GS → GS
  | 0, s => s
  | n + 1, s => it n (st s)

theorem it_add : ∀ (n m : Nat) (s : GS), it (n + m) s = it n (it m s)
  | n, 0, s => rfl
  | n, m + 1, s => by rw [show n + (m + 1) = (n + m) + 1 by omega]; simp only [it]; exact it_add n m (st s)

def Reach (s : GS) (P : GS → Prop) : Prop :=
  ∃ m, (∀ j < m, live (it j s)) ∧ (P (it m s) ∨ err (it m s) ∨ big (it m s))

theorem Reach.done {s : GS} {P : GS → Prop} (h : P s) : Reach s P := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inl h⟩

theorem Reach.error {s : GS} {P : GS → Prop} (h : err s) : Reach s P := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inr (.inl h)⟩

theorem Reach.toobig {s : GS} {P : GS → Prop} (h : big s) : Reach s P := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inr (.inr h)⟩

theorem Reach.step {s : GS} {P : GS → Prop} (hl : live s) (h : Reach (st s) P) : Reach s P := by
  obtain ⟨m, hm, hp⟩ := h
  refine ⟨m + 1, fun j hj => ?_, hp⟩
  rcases j with _ | j
  · exact hl
  · exact hm j (by omega)

theorem Reach.bind {s : GS} {P Q : GS → Prop} (h : Reach s P) (hq : ∀ s', P s' → Reach s' Q) : Reach s Q := by
  obtain ⟨m, hm, hp⟩ := h
  rcases hp with hp | he
  · obtain ⟨n, hn, hq⟩ := hq _ hp
    refine ⟨n + m, fun j hj => ?_, by rw [it_add]; exact hq⟩
    by_cases hjm : j < m
    · exact hm j hjm
    · have := hn (j - m) (by omega)
      rw [← it_add] at this
      rwa [show j - m + m = j by omega] at this
  · exact ⟨m, hm, .inr he⟩

theorem Reach.mono {s : GS} {P Q : GS → Prop} (h : Reach s P) (hq : ∀ s', P s' → Q s') : Reach s Q :=
  h.bind fun s' hp => .done (hq s' hp)

/-! ## the item stack and the fixup list -/

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
theorem pi_g21 : PI g21 := by intro o; simp [em, g21, bpush, bsize]
theorem pi_g22 (d) : PI (fun o => g22 o d) := by intro o; simp [em, g22, bpush, bsize]
theorem pi_g23 (d v) : PI (fun o => g23 o d v) := by intro o; unfold g23; split <;> simp [em, bpush]
theorem pi_g31 (p) : PI (fun o => g31 o p) := by intro o; simp [em, g31, g30, bpush]
theorem pi_comp {F G : Buf → Buf} (hF : PI F) (hG : PI G) : PI (fun o => G (F o)) := by
  intro o
  have e1 := hF o; have e2 := hG (F o)
  have e3 := hF (List.replicate o.length 0); have e4 := hG (F (List.replicate o.length 0))
  simp only [em] at *
  rw [e2, e1, e4, e3]; simp [List.append_assoc]
theorem pi_g32 (p u : UInt64) : PI (fun o => g32 o p u) := by
  intro o
  by_cases h1 : p = 1; · subst h1; simp [em, g32, g22, bpush, bsize]
  by_cases h3 : p = 3; · subst h3; simp [em, g32, g22, bpush, bsize]
  by_cases h2 : p = 2; · subst h2; simp [em, g32, bpush]
  by_cases h5 : p = 5
  · subst h5
    have q1 : PI (fun o => bpush (bpush (bpush o (g1 0 0 6 6 30)) (g4 7 31 6 8)) (g13 0 (bsize o + 2) 1)) := by
      intro o; simp [em, bpush, bsize]
    have q2 : PI (fun o => bpush (bpush (bpush o (g12 0 5 0)) (g12 7 5 8)) (g10 30 6 0)) := by intro o; simp [em, bpush]
    have := pi_comp (pi_comp (pi_comp (pi_comp (pi_comp (pi_bpush (g10 5 30 0)) (pi_g23 6 ((u + 2) <<< 3))) q1)
      (pi_g23 7 u)) q2) pi_g21
    exact this o
  by_cases h6 : p = 6; · subst h6; simp [em, g32, bpush]
  by_cases h7 : p = 7; · subst h7; simp [em, g32, g30, bpush]
  by_cases h8 : p = 8; · subst h8; simp [em, g32, bpush]
  simp [em, g32, g30, bpush, bsize, h1, h2, h3, h5, h6, h7, h8]

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


/-! ## the reference: what Gen emits for a node, as a big-step relation over code words

`CG K d i h c i' E`: the node at AST word i, visited in value mode with d items below its visit item, emits the words c
starting at code word h, ends at AST word i', and records the exit placeholders E (absolute word indices, in f order).
`CT K hd …`: the same in tail mode (a loop arm; hd = the loop head).  `CGs K d i h n …`: n consecutive value nodes
(PAIR / CALL / PRIM operands), the first visited at depth d + n − 1.  Jumps are final (patched) words; exit
placeholders stay 0 until ENDDEF. -/

/-- Gen's per-def constants: the AST, npw, nslots, κ, the def-start table -/
structure Cx where
  X : Buf
  p : UInt64
  ns : UInt64
  u : UInt64
  T : Buf
  q : UInt64

def tg (X : Buf) (i : Nat) : UInt64 := X.getD i 0
/-- `jal rd` from word a to word b -/
def jw (rd : UInt64) (a b : Nat) : UInt64 := g13 rd a.toUInt64 b.toUInt64
/-- a slot range is inside the frame (g43 = 0) -/
def SlotOk (K : Cx) (s w : UInt64) : Prop := w ≠ 0 ∧ s < 251 ∧ w < 251 ∧ ¬ K.ns < s + w
/-- IF's compare + branch -/
def ifHd (cmp : UInt64) : List UInt64 := [g11 6 31 0, g11 5 31 8, g10 31 31 16, if cmp == 1 then g4 0 5 6 8 else g4 6 5 6 8]
/-- LOOP's head: t0 := fuel; beq t0, x0, +8; (placeholder → the step arm) -/
def lpHd (p : UInt64) : List UInt64 := [g11 5 8 (g24 p 0), g4 0 5 0 8]
/-- LOOP's decrement (item 11) -/
def lpDec (p : UInt64) : List UInt64 := [g10 5 5 g_901, g12 5 8 (g24 p 0)]

mutual
inductive CG (K : Cx) : Nat → Nat → Nat → List UInt64 → Nat → List Nat → Prop
  | const {d i h} : tg K.X i = 1 → CG K d i h (em (fun o => g21 (g23 o 5 (tg K.X (i + 1)))) h) (i + 2) []
  | local {d i h} : tg K.X i = 2 → SlotOk K (tg K.X (i + 1)) (tg K.X (i + 2)) →
      CG K d i h (em (g25 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) h) (i + 3) []
  | bin {d i h ca cb i1 i2 Ea Eb} : tg K.X i = 3 → tg K.X (i + 1) - 1 < 8 →
      CG K (d + 2) (i + 2) h ca i1 Ea → CG K (d + 1) i1 (h + ca.length) cb i2 Eb →
      CG K d i h (ca ++ cb ++ em (fun o => g31 o (tg K.X (i + 1))) (h + ca.length + cb.length)) i2 (Ea ++ Eb)
  | ite {d i h ca cb ct ce i1 i2 i3 i4 Ea Eb Et Ee} : tg K.X i = 4 → tg K.X (i + 1) - 1 < 2 →
      CG K (d + 6) (i + 2) h ca i1 Ea → CG K (d + 5) i1 (h + ca.length) cb i2 Eb →
      CG K (d + 3) i2 (h + ca.length + cb.length + 5) ct i3 Et →
      CG K (d + 1) i3 (h + ca.length + cb.length + 5 + ct.length + 1) ce i4 Ee →
      CG K d i h (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
        [jw 0 (h + ca.length + cb.length + 4) (h + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
        [jw 0 (h + ca.length + cb.length + 5 + ct.length) (h + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce)
        i4 (Ea ++ Eb ++ Et ++ Ee)
  | lett {d i h cv cb i1 i2 Ev Eb} : tg K.X i = 5 → SlotOk K (tg K.X (i + 1)) (tg K.X (i + 2)) →
      CG K (d + 2) (i + 3) h cv i1 Ev →
      CG K d i1 (h + cv.length + (em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (h + cv.length)).length) cb i2 Eb →
      CG K d i h (cv ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (h + cv.length) ++ cb) i2 (Ev ++ Eb)
  | pair {d i h c i' E} : tg K.X i = 6 → tg K.X (i + 1) < 251 →
      CGs K d (i + 2) h (tg K.X (i + 1)).toNat c i' E → CG K d i h c i' E
  | call {d i h c i' E} : tg K.X i = 8 → tg K.X (i + 2) < 251 → tg K.X (i + 1) < bsize K.T →
      CGs K (d + 1) (i + 3) h (tg K.X (i + 2)).toNat c i' E →
      CG K d i h (c ++ [g13 1 (h + c.length).toUInt64 (bget K.T (tg K.X (i + 1)))]) i' E
  | prim {d i h c i' E} : tg K.X i = 9 → tg K.X (i + 1) - 1 < 9 →
      CGs K (d + 1) (i + 2) h (g33 (tg K.X (i + 1))).toNat c i' E →
      CG K d i h (c ++ em (fun o => g32 o (tg K.X (i + 1)) K.u) (h + c.length)) i' E
  | loop {i h cz cs i1 i2 Ez Es} : tg K.X i = 10 →
      CT K h 3 (i + 1) (h + 3) cz i1 Ez →
      CT K h 1 i1 (h + 3 + cz.length + 2) cs i2 Es →
      CG K 1 i h (lpHd K.p ++ [jw 0 (h + 2) (h + 3 + cz.length)] ++ cz ++ lpDec K.p ++ cs) i2 (Ez ++ Es)
inductive CT (K : Cx) : Nat → Nat → Nat → Nat → List UInt64 → Nat → List Nat → Prop
  /-- a value node in tail position: value, then an exit placeholder -/
  | val {hd d i h c i' E} : tg K.X i ≠ 4 → tg K.X i ≠ 5 → tg K.X i ≠ 11 →
      CG K (d + 1) i h c i' E → CT K hd d i h (c ++ [0]) i' (E ++ [h + c.length])
  | cont {hd d i h c i'} : tg K.X i = 11 →
      CG K (d + 1) (i + 1) h c i' [] →
      CT K hd d i h (c ++ em (g26 256 K.p 1 (K.p - 1)) (h + c.length) ++
        [jw 0 (h + c.length + (em (g26 256 K.p 1 (K.p - 1)) (h + c.length)).length) hd]) i' []
  | ite {hd d i h ca cb ct ce i1 i2 i3 i4 Ea Eb Et Ee} : tg K.X i = 4 → tg K.X (i + 1) - 1 < 2 →
      CG K (d + 6) (i + 2) h ca i1 Ea → CG K (d + 5) i1 (h + ca.length) cb i2 Eb →
      CT K hd (d + 3) i2 (h + ca.length + cb.length + 5) ct i3 Et →
      CT K hd (d + 1) i3 (h + ca.length + cb.length + 5 + ct.length + 1) ce i4 Ee →
      CT K hd d i h (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
        [jw 0 (h + ca.length + cb.length + 4) (h + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
        [jw 0 (h + ca.length + cb.length + 5 + ct.length) (h + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce)
        i4 (Ea ++ Eb ++ Et ++ Ee)
  | lett {hd d i h cv cb i1 i2 Ev Eb} : tg K.X i = 5 → SlotOk K (tg K.X (i + 1)) (tg K.X (i + 2)) →
      CG K (d + 2) (i + 3) h cv i1 Ev →
      CT K hd d i1 (h + cv.length + (em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (h + cv.length)).length) cb i2 Eb →
      CT K hd d i h (cv ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (h + cv.length) ++ cb) i2 (Ev ++ Eb)
inductive CGs (K : Cx) : Nat → Nat → Nat → Nat → List UInt64 → Nat → List Nat → Prop
  | nil {d i h} : CGs K d i h 0 [] i []
  | cons {d i h n c cs i1 i2 E Es} : CG K (d + n) i h c i1 E → CGs K d i1 (h + c.length) n cs i2 Es →
      CGs K d i h (n + 1) (c ++ cs) i2 (E ++ Es)
end


/-! ## the invariant between items -/

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
  ol : s.o.length < 2 ^ 32

theorem bget_set (r : Buf) (j : UInt64) (v : UInt64) (i : UInt64) (hj : j.toNat < r.length) :
    bget (bset r j v) i = if j = i then v else bget r i := by
  rw [BufL.bget_bset]
  by_cases h : j = i
  · subst h; simp [hj]
  · have : j.toNat ≠ i.toNat := fun e => h (UInt64.toNat_inj.mp e)
    simp [h, this]

theorem bk (k : Buf) (n j : Nat) (h : 3 * n + j < 2 ^ 64) : bget k (n.toUInt64 * 3 + j.toUInt64) = k.getD (3 * n + j) 0 := by
  simp only [bget]; rw [u3 n j h]

theorem bk0 (k : Buf) (n : Nat) (h : 3 * n < 2 ^ 64) : bget k (n.toUInt64 * 3) = k.getD (3 * n) 0 := by
  have := bk k n 0 (by omega); simpa using this

theorem pred_u (n : Nat) (h : n + 1 < 2 ^ 64) : (n + 1).toUInt64 - 1 = n.toUInt64 := by
  apply UInt64.toNat.inj; simp [Nat.toUInt64]

/-- g37 on a visit item (unfolding with `extract_lets`: zeta-reducing Gen's lets blows up the term) -/
theorem g37_visit (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 1) :
    g37 x r o k t f = (match g36 x (g15 r 6 (bget r 6 - 1)) o k (bget k ((bget r 6 - 1) * 3 + 1)) with
      | (r2, (o2, k2)) => (r2, (o2, (k2, f)))) := by
  unfold g37
  extract_lets n c z y r1
  have hc' : (c == 1) = true := by simp [c, n, hc]
  rw [if_pos hc']

/-- popping a visit item: `st` is g36 on the popped register file -/
theorem st_visit {K s L F} {m : UInt64} (hI : Inv K s (L ++ [(1, m, 0)]) F) :
    st s = (match g36 s.x (bset s.r 6 L.length.toUInt64) s.o s.k m with
      | (r2, (o2, k2)) => ⟨s.x, r2, o2, k2, s.t, s.f⟩) := by
  have hL := hI.Ll; simp at hL
  obtain ⟨t0, t1, t2⟩ := stk_top hI.stk
  have hn : bget s.r 6 - 1 = L.length.toUInt64 := by
    apply UInt64.toNat.inj; rw [hI.r6]; simp [Nat.toUInt64]
  have e0 : bget s.k (L.length.toUInt64 * 3) = 1 := by
    simp only [bget]; rw [show (L.length.toUInt64 * 3).toNat = 3 * L.length by simp [Nat.toUInt64]; omega, t0]
  have e1 : bget s.k (L.length.toUInt64 * 3 + 1) = m := by
    simp only [bget]; rw [show (L.length.toUInt64 * 3 + 1).toNat = 3 * L.length + 1 by simp [Nat.toUInt64]; omega, t1]
  unfold st
  rw [g37_visit _ _ _ _ _ _ (by rw [hn, e0]), hn, e1]
  rfl


/-- the value-visit postcondition: the node at i emitted c (CG), the item is gone, cursor at i' -/
def VPost (K : Cx) (s0 : GS) (L : List Item) (F : List UInt64) (d i : Nat) (s' : GS) : Prop :=
  ∃ c i' E, CG K d i s0.o.length c i' E ∧ Inv K s' L (F ++ E.map Nat.toUInt64) ∧ s'.o = s0.o ++ c ∧
    bget s'.r 0 = i'.toUInt64 ∧ i < i' ∧ (2 ≤ d → E = [] ∧ bget s'.r 3 = bget s0.r 3)

theorem g36_const (x r o k : Buf) (hc : bget x (bget r 0) = 1) :
    g36 x r o k 0 = (g15 r 0 (bget r 0 + 2), (g21 (g23 o 5 (bget x (bget r 0 + 1))), k)) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 1 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc, g_1]
  rw [if_neg (by simp [ha]), if_neg (by decide), if_pos (by simp [hc])]

theorem live_of {K s L F} (hI : Inv K s L F) (hL : L ≠ []) : live s := by
  refine ⟨hI.r5, hI.r4, ?_⟩
  rw [hI.r6]; intro h
  have h1 := congrArg UInt64.toNat h
  rw [u_toNat L.length (by have := hI.Ll; omega)] at h1
  exact hL (List.length_eq_zero_iff.mp h1)

theorem rget (r : Buf) (hr : r.length = 10) (j i : UInt64) (v : UInt64) (hj : j.toNat < 10) :
    bget (bset r j v) i = if j = i then v else bget r i := bget_set r j v i (by omega)


/-- rebuild Inv after an item that writes only r[0], r[6], k and o -/
theorem inv_mk {K s L0 F} (hI : Inv K s L0 F) (r' k' o' : Buf) (L' : List Item)
    (hr : ∀ j : UInt64, j ≠ 0 → j ≠ 6 → bget r' j = bget s.r j) (hrl : r'.length = 10)
    (h6 : bget r' 6 = L'.length.toUInt64) (hk : Stk k' L') (hkl : k'.length < 2 ^ 62) (hLl : L'.length < 2 ^ 60)
    (ho : o'.length < 2 ^ 32) : Inv K ⟨s.x, r', o', k', s.t, s.f⟩ L' F where
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

theorem pi_const (v : UInt64) : PI (fun o => g21 (g23 o 5 v)) := pi_comp (pi_g23 5 v) pi_g21

/-- CONST -/
theorem v_const {K s L F d i} (hI : Inv K s (L ++ [(1, 0, 0)]) F) (hr0 : bget s.r 0 = i.toUInt64) (hi : i < 2 ^ 31)
    (ht : tg K.X i = 1) : Reach s (VPost K s L F d i) := by
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  have hl6 : (bset s.r 6 L.length.toUInt64).length = 10 := by rw [BufL.length_bset]; exact hI.rl
  have h0 : bget (bset s.r 6 L.length.toUInt64) 0 = i.toUInt64 := by
    rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have hx : bget s.x i.toUInt64 = 1 := by rw [hI.x, tg_u _ _ (by omega), ht]
  rw [g36_const _ _ _ _ (by rw [h0]; exact hx), h0]
  dsimp only
  have hv : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  have e : g21 (g23 s.o 5 (tg K.X (i + 1))) = s.o ++ em (fun o => g21 (g23 o 5 (tg K.X (i + 1)))) s.o.length :=
    pi_const _ s.o
  rw [hv, e]
  by_cases hb : 2 ^ 32 ≤ (s.o ++ em (fun o => g21 (g23 o 5 (tg K.X (i + 1)))) s.o.length).length
  · exact Reach.toobig hb
  obtain ⟨q1, q2, q3, q4⟩ := r06 s.r hI.rl L.length.toUInt64 (i.toUInt64 + 2)
  refine Reach.done ⟨_, i + 2, [], .const ht, ?_, rfl, ?_, by omega, fun _ => ⟨rfl, ?_⟩⟩
  · simp only [List.map_nil, List.append_nil]
    exact inv_mk hI _ _ _ L q4 q1 q2 (stk_pop hI.stk) hI.kl (by have := hI.Ll; simp at this; omega) (by omega)
  · simp only [g15]; rw [q3]; simp [Nat.toUInt64, UInt64.ofNat_add]
  · simp only [g15]; rw [q4 3 (by decide) (by decide)]


theorem pi_g25 : ∀ (n : Nat) (p s w : UInt64), PI (g25 n p s w)
  | 0, p, s, w => fun o => by simp [g25, em]
  | n + 1, p, s, w => by
    by_cases hw : (w == 0) = true
    · intro o; simp [g25, hw, em]
    · have := pi_comp (pi_comp (pi_bpush (g11 5 8 (g24 p s))) pi_g21) (pi_g25 n p (s + 1) (w - 1))
      intro o; have e := this o; simp only [g25, hw, if_false, Bool.false_eq_true] at e ⊢; exact e

theorem pi_g26 : ∀ (n : Nat) (p s w : UInt64), PI (g26 n p s w)
  | 0, p, s, w => fun o => by simp [g26, em]
  | n + 1, p, s, w => by
    by_cases hw : (w == 0) = true
    · intro o; simp [g26, hw, em]
    · have := pi_comp (pi_comp (pi_comp (pi_bpush (g11 5 31 0)) (pi_bpush (g10 31 31 8)))
        (pi_bpush (g12 5 8 (g24 p (s + w - 1))))) (pi_g26 n p s (w - 1))
      intro o; have e := this o; simp only [g26, hw, if_false, Bool.false_eq_true] at e ⊢; exact e

theorem g36_local (x r o k : Buf) (hc : bget x (bget r 0) = 2) :
    g36 x r o k 0 = (if g43 r (bget x (bget r 0 + 1)) (bget x (bget r 0 + 2)) == 1 then (g16 r, (o, k)) else
      (g15 r 0 (bget r 0 + 3), (g25 256 (bget r 1) (bget x (bget r 0 + 1)) (bget x (bget r 0 + 2)) o, k))) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 2 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc, g_1]
  rw [if_neg (by simp [ha]), if_neg (by decide), if_neg (by simp [hc]), if_pos (by simp [hc])]

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

/-- LOCAL -/
theorem v_local {K s L F d i} (hI : Inv K s (L ++ [(1, 0, 0)]) F) (hr0 : bget s.r 0 = i.toUInt64) (hi : i < 2 ^ 31)
    (ht : tg K.X i = 2) : Reach s (VPost K s L F d i) := by
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  have hl6 : (bset s.r 6 L.length.toUInt64).length = 10 := by rw [BufL.length_bset]; exact hI.rl
  have h0 : bget (bset s.r 6 L.length.toUInt64) 0 = i.toUInt64 := by
    rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have h1 : bget (bset s.r 6 L.length.toUInt64) 1 = K.p := by
    rw [rget _ hI.rl 6 1 _ (by decide), if_neg (by decide), hI.r1]
  have h7 : bget (bset s.r 6 L.length.toUInt64) 7 = K.ns := by
    rw [rget _ hI.rl 6 7 _ (by decide), if_neg (by decide), hI.r7]
  have hx : bget s.x i.toUInt64 = 2 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  have hv2 : bget s.x (i.toUInt64 + 2) = tg K.X (i + 2) := by rw [hI.x]; exact tg_u1 _ i 2 (by omega)
  rw [g36_local _ _ _ _ (by rw [h0]; exact hx), h0, hv1, hv2, h1, g43_ok _ _ _ _ h7]
  by_cases hs : SlotOk K (tg K.X (i + 1)) (tg K.X (i + 2))
  · have hs' : tg K.X (i + 2) ≠ 0 ∧ tg K.X (i + 1) < 251 ∧ tg K.X (i + 2) < 251 ∧ ¬K.ns < tg K.X (i + 1) + tg K.X (i + 2) := hs
    rw [if_pos hs']
    simp only [show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false]
    have e := pi_g25 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) s.o
    rw [e]
    by_cases hb : 2 ^ 32 ≤ (s.o ++ em (g25 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s.o.length).length
    · exact Reach.toobig hb
    obtain ⟨q1, q2, q3, q4⟩ := r06 s.r hI.rl L.length.toUInt64 (i.toUInt64 + 3)
    refine Reach.done ⟨_, i + 3, [], .local ht hs, ?_, rfl, ?_, by omega, fun _ => ⟨rfl, ?_⟩⟩
    · simp only [List.map_nil, List.append_nil]
      exact inv_mk hI _ _ _ L q4 q1 q2 (stk_pop hI.stk) hI.kl (by have := hI.Ll; simp at this; omega) (by omega)
    · simp only [g15]; rw [q3]; simp [Nat.toUInt64, UInt64.ofNat_add]
    · simp only [g15]; rw [q4 3 (by decide) (by decide)]
  · have hs' : ¬ (tg K.X (i + 2) ≠ 0 ∧ tg K.X (i + 1) < 251 ∧ tg K.X (i + 2) < 251 ∧ ¬K.ns < tg K.X (i + 1) + tg K.X (i + 2)) := hs
    rw [if_neg hs']
    simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]
    exact Reach.error (g16_err _ hl6)


/-- the operator-range check of g36 -/
def rng (c b : UInt64) : Prop := (c = 3 → b - 1 < 8) ∧ (c = 4 → b - 1 < 2) ∧ (c = 9 → b - 1 < 9)

theorem g36_bin (x r o k : Buf) (hc : bget x (bget r 0) = 3) (hb : bget x (bget r 0 + 1) - 1 < 8) :
    g36 x r o k 0 = (g15 (g15 r 0 (bget r 0 + 2)) 6 (bget r 6 + 3), (o, g18 (g18 (g18 k (bget r 6) 2 (bget x (bget r 0 + 1)) 0)
      (bget r 6 + 1) 1 0 0) (bget r 6 + 2) 1 0 0)) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 3 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc, b, i, hb, g_1]
  rw [if_neg (by simp [ha]), if_neg (by decide), if_neg (by simp [hc]), if_neg (by simp [hc]), if_pos (by simp [hc])]

theorem g36_bin_bad (x r o k : Buf) (hc : bget x (bget r 0) = 3) (hb : ¬ bget x (bget r 0 + 1) - 1 < 8) :
    g36 x r o k 0 = (g16 r, (o, k)) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 3 := by simp [c, c0, i, hc]
  have ha : (a == 0) = true := by simp [a, hc, b, i, hb, g_0]
  rw [if_pos ha]

/-- g37 on a BIN-op item (tag 2) -/
theorem g37_t2 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 2) :
    g37 x r o k t f = (g15 r 6 (bget r 6 - 1), (g31 o (bget k ((bget r 6 - 1) * 3 + 1)), (k, f))) := by
  unfold g37
  extract_lets n c z y r1
  have hc' : c = 2 := by simp [c, n, hc]
  rw [if_neg (by simp [hc']), if_pos (by simp [hc'])]

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

/-- value visit at AST word i (the induction statement) -/
def VS (K : Cx) (i : Nat) : Prop := ∀ s L F, Inv K s (L ++ [(1, 0, 0)]) F → bget s.r 0 = i.toUInt64 →
  L.length + 300 * (K.X.length - i) + 300 < 2 ^ 60 → Reach s (VPost K s L F L.length i)

/-- BIN -/
theorem v_bin {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 3) :
    VS K i := by
  intro s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  have hl6 : (bset s.r 6 L.length.toUInt64).length = 10 := by rw [BufL.length_bset]; exact hI.rl
  have h0 : bget (bset s.r 6 L.length.toUInt64) 0 = i.toUInt64 := by
    rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have h6 : bget (bset s.r 6 L.length.toUInt64) 6 = L.length.toUInt64 := by
    rw [rget _ hI.rl 6 6 _ (by decide), if_pos rfl]
  have hx : bget s.x i.toUInt64 = 3 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  by_cases hb' : ¬ tg K.X (i + 1) - 1 < 8
  · rw [g36_bin_bad _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb')]
    exact Reach.error (g16_err _ hl6)
  have hb : tg K.X (i + 1) - 1 < 8 := Classical.not_not.mp hb'
  rw [g36_bin _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb), h0, h6, hv1]
  dsimp only
  have hLl := hI.Ll; simp at hLl
  have hsk := stk_pop hI.stk
  obtain ⟨sk1, kl1⟩ := stk_push3 s.k L (2, tg K.X (i + 1), 0) (1, 0, 0) (1, 0, 0) hsk hI.kl (by omega)
  simp only at sk1 kl1
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 2) (L.length.toUInt64 + 3) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 3)) _ s.o
    (L ++ [(2, tg K.X (i + 1), 0), (1, 0, 0), (1, 0, 0)])
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) sk1 kl1
    (by simp; omega) hI.ol
  -- child a at i + 2
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 3)) 0 = (i + 2).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  refine Reach.bind (IH (i + 2) (by omega) _ (L ++ [(2, tg K.X (i + 1), 0), (1, 0, 0)]) F (by simpa using hI1) hra
    (by simp; omega)) ?_
  rintro s2 ⟨ca, i1, Ea, hca, hI2, ho2, hr2, hi1, hd2⟩
  refine Reach.bind (IH i1 (by omega) s2 (L ++ [(2, tg K.X (i + 1), 0)]) (F ++ Ea.map Nat.toUInt64)
    (by simpa using hI2) hr2 (by simp; omega)) ?_
  rintro s3 ⟨cb, i2, Eb, hcb, hI3, ho3, hr3, hi2, hd3⟩
  refine Reach.step (live_of hI3 (by simp)) ?_
  obtain ⟨n3, c3, a3, -⟩ := top_item hI3
  have hst : st s3 = ⟨s3.x, g15 s3.r 6 L.length.toUInt64, g31 s3.o (tg K.X (i + 1)), s3.k, s3.t, s3.f⟩ := by
    unfold st; rw [g37_t2 _ _ _ _ _ _ c3, a3, n3]
  rw [hst]
  have e := pi_g31 (tg K.X (i + 1)) s3.o
  simp only at e
  rw [e]
  by_cases hbig : 2 ^ 32 ≤ (s3.o ++ em (fun o => g31 o (tg K.X (i + 1))) s3.o.length).length
  · exact Reach.toobig hbig
  have ho : s3.o = s.o ++ ca ++ cb := by rw [ho3, ho2]
  have hI4 := inv_mk hI3 (g15 s3.r 6 L.length.toUInt64) s3.k (s3.o ++ em (fun o => g31 o (tg K.X (i + 1))) s3.o.length) L
    (fun j a b => by simp only [g15]; rw [rget _ hI3.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (by simp only [g15]; rw [BufL.length_bset]; exact hI3.rl)
    (by simp only [g15]; rw [rget _ hI3.rl 6 6 _ (by decide), if_pos rfl]) (stk_pop hI3.stk) hI3.kl (by omega) (by omega)
  refine Reach.done ⟨ca ++ cb ++ em (fun o => g31 o (tg K.X (i + 1))) (s.o.length + ca.length + cb.length), i2, Ea ++ Eb,
    ?_, ?_, ?_, ?_, by omega, fun hd => ?_⟩
  · have hca' : CG K (L.length + 2) (i + 2) s.o.length ca i1 Ea := by simpa using hca
    have hcb' : CG K (L.length + 1) i1 (s.o.length + ca.length) cb i2 Eb := by
      have : s2.o.length = s.o.length + ca.length := by rw [ho2]; simp
      simpa [this] using hcb
    exact .bin ht hb hca' hcb'
  · rw [List.map_append, ← List.append_assoc]; exact hI4
  · simp only; rw [ho]; simp [List.append_assoc, Nat.add_assoc]
  · simp only [g15]; rw [rget _ hI3.rl 6 0 _ (by decide), if_neg (by decide), hr3]
  · obtain ⟨ea, r3a⟩ := hd2 (by simp)
    obtain ⟨eb, r3b⟩ := hd3 (by simp; omega)
    refine ⟨by rw [ea, eb]; rfl, ?_⟩
    simp only [g15]; rw [rget _ hI3.rl 6 3 _ (by decide), if_neg (by decide), r3b, r3a]
    simp only [g15]
    rw [rset2 _ hl6 0 6 _ _ (by decide) (by decide), if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]


theorem g36_let (x r o k : Buf) (hc : bget x (bget r 0) = 5) :
    g36 x r o k 0 = (if g43 r (bget x (bget r 0 + 1)) (bget x (bget r 0 + 2)) == 1 then (g16 r, (o, k)) else
      (g15 (g15 r 0 (bget r 0 + 3)) 6 (bget r 6 + 3), (o, g18 (g18 (g18 k (bget r 6) 1 0 0) (bget r 6 + 1) 6
        (bget x (bget r 0 + 1)) (bget x (bget r 0 + 2))) (bget r 6 + 2) 1 0 0))) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 5 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc, g_1]
  rw [if_neg (by simp [ha]), if_neg (by decide), if_neg (by simp [hc]), if_neg (by simp [hc]), if_neg (by simp [hc]),
    if_neg (by simp [hc]), if_pos (by simp [hc])]

/-- g37 on a slot-pop item (tag 6) -/
theorem g37_t6 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 6) :
    g37 x r o k t f = (g15 r 6 (bget r 6 - 1), (g26 256 (bget (g15 r 6 (bget r 6 - 1)) 1) (bget k ((bget r 6 - 1) * 3 + 1))
      (bget k ((bget r 6 - 1) * 3 + 2)) o, (k, f))) := by
  unfold g37
  extract_lets n c z y r1
  have hc' : c = 6 := by simp [c, n, hc]
  rw [if_neg (by simp [hc']), if_neg (by simp [hc']), if_neg (by simp [hc']), if_neg (by simp [hc']), if_neg (by simp [hc']),
    if_pos (by simp [hc'])]

/-- LET (value mode) -/
theorem v_let {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 5) :
    VS K i := by
  intro s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  have hl6 : (bset s.r 6 L.length.toUInt64).length = 10 := by rw [BufL.length_bset]; exact hI.rl
  have h0 : bget (bset s.r 6 L.length.toUInt64) 0 = i.toUInt64 := by
    rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have h6 : bget (bset s.r 6 L.length.toUInt64) 6 = L.length.toUInt64 := by
    rw [rget _ hI.rl 6 6 _ (by decide), if_pos rfl]
  have h7 : bget (bset s.r 6 L.length.toUInt64) 7 = K.ns := by
    rw [rget _ hI.rl 6 7 _ (by decide), if_neg (by decide), hI.r7]
  have hx : bget s.x i.toUInt64 = 5 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  have hv2 : bget s.x (i.toUInt64 + 2) = tg K.X (i + 2) := by rw [hI.x]; exact tg_u1 _ i 2 (by omega)
  rw [g36_let _ _ _ _ (by rw [h0]; exact hx), h0, h6, hv1, hv2, g43_ok _ _ _ _ h7]
  by_cases hs : SlotOk K (tg K.X (i + 1)) (tg K.X (i + 2))
  · have hs' : tg K.X (i + 2) ≠ 0 ∧ tg K.X (i + 1) < 251 ∧ tg K.X (i + 2) < 251 ∧ ¬K.ns < tg K.X (i + 1) + tg K.X (i + 2) := hs
    rw [if_pos hs']
    simp only [show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false]
    have hLl := hI.Ll; simp at hLl
    have hsk := stk_pop hI.stk
    obtain ⟨sk1, kl1⟩ := stk_push3 s.k L (1, 0, 0) (6, tg K.X (i + 1), tg K.X (i + 2)) (1, 0, 0) hsk hI.kl (by omega)
    simp only at sk1 kl1
    have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 3) (L.length.toUInt64 + 3) (by decide) (by decide)
    have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 3)) 6 (L.length.toUInt64 + 3)) _ s.o
      (L ++ [(1, 0, 0), (6, tg K.X (i + 1), tg K.X (i + 2)), (1, 0, 0)])
      (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
      (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) sk1 kl1
      (by simp; omega) hI.ol
    have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 3)) 6 (L.length.toUInt64 + 3)) 0 = (i + 3).toUInt64 := by
      simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
    refine Reach.bind (IH (i + 3) (by omega) _ (L ++ [(1, 0, 0), (6, tg K.X (i + 1), tg K.X (i + 2))]) F (by simpa using hI1) hra
      (by simp; omega)) ?_
    rintro s2 ⟨cv, i1, Ev, hcv, hI2, ho2, hr2, hi1, hd2⟩
    -- the slot-pop item
    have hI2' : Inv K s2 ((L ++ [(1, 0, 0)]) ++ [(6, tg K.X (i + 1), tg K.X (i + 2))]) (F ++ Ev.map Nat.toUInt64) := by simpa using hI2
    refine Reach.step (live_of hI2' (by simp)) ?_
    obtain ⟨n2, c2, a2, b2⟩ := top_item hI2'
    have hp2 : bget (g15 s2.r 6 (L ++ [(1, 0, 0)]).length.toUInt64) 1 = K.p := by
      simp only [g15]; rw [rget _ hI2.rl 6 1 _ (by decide), if_neg (by decide), hI2.r1]
    have hst : st s2 = ⟨s2.x, g15 s2.r 6 (L ++ [(1, 0, 0)]).length.toUInt64,
        g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) s2.o, s2.k, s2.t, s2.f⟩ := by
      unfold st; rw [g37_t6 _ _ _ _ _ _ c2, a2, b2, n2, hp2]
    rw [hst]
    have e := pi_g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) s2.o
    rw [e]
    by_cases hbig : 2 ^ 32 ≤ (s2.o ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s2.o.length).length
    · exact Reach.toobig hbig
    have hI3 := inv_mk hI2' (g15 s2.r 6 (L ++ [(1, 0, 0)]).length.toUInt64) s2.k
      (s2.o ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s2.o.length) (L ++ [(1, 0, 0)])
      (fun j a b => by simp only [g15]; rw [rget _ hI2.rl 6 j _ (by decide), if_neg (Ne.symm b)])
      (by simp only [g15]; rw [BufL.length_bset]; exact hI2.rl)
      (by simp only [g15]; rw [rget _ hI2.rl 6 6 _ (by decide), if_pos rfl]) (stk_pop hI2'.stk) hI2.kl (by simp; omega) (by omega)
    have hr3 : bget (g15 s2.r 6 (L ++ [(1, 0, 0)]).length.toUInt64) 0 = i1.toUInt64 := by
      simp only [g15]; rw [rget _ hI2.rl 6 0 _ (by decide), if_neg (by decide), hr2]
    refine Reach.bind (IH i1 (by omega) _ L (F ++ Ev.map Nat.toUInt64) hI3 hr3 (by omega)) ?_
    rintro s4 ⟨cb, i2, Eb, hcb, hI4, ho4, hr4, hi2, hd4⟩
    have hem : s2.o.length = s.o.length + cv.length := by rw [ho2]; simp
    refine Reach.done ⟨cv ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (s.o.length + cv.length) ++ cb, i2, Ev ++ Eb,
      ?_, ?_, ?_, hr4, by omega, fun hd => ?_⟩
    · have hcv' : CG K (L.length + 2) (i + 3) s.o.length cv i1 Ev := by simpa using hcv
      have hcb' : CG K L.length i1 (s.o.length + cv.length +
          (em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (s.o.length + cv.length)).length) cb i2 Eb := by
        simpa [hem, Nat.add_assoc] using hcb
      exact .lett ht hs hcv' hcb'
    · rw [List.map_append, ← List.append_assoc]; exact hI4
    · rw [ho4, ho2]; simp [hem, List.append_assoc]
    · obtain ⟨ev, r3a⟩ := hd2 (by simp)
      obtain ⟨eb, r3b⟩ := hd4 hd
      refine ⟨by rw [ev, eb]; rfl, ?_⟩
      rw [r3b]; simp only [g15]; rw [rget _ hI2.rl 6 3 _ (by decide), if_neg (by decide), r3a]
      simp only [g15]
      rw [rset2 _ hl6 0 6 _ _ (by decide) (by decide), if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
  · have hs' : ¬ (tg K.X (i + 2) ≠ 0 ∧ tg K.X (i + 1) < 251 ∧ tg K.X (i + 2) < 251 ∧ ¬K.ns < tg K.X (i + 1) + tg K.X (i + 2)) := hs
    rw [if_neg hs']
    simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]
    exact Reach.error (g16_err _ hl6)


theorem g20_eq (r o : Buf) (p : UInt64) :
    g20 r o p = (if g14 p (bsize o) == 1 then r else g16 r, bset o p (g13 0 p (bsize o))) := by
  unfold g20
  extract_lets h
  by_cases hc : (g14 p h == 1) = true
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]

theorem g36_if (x r o k : Buf) (hc : bget x (bget r 0) = 4) (hb : bget x (bget r 0 + 1) - 1 < 2) :
    g36 x r o k 0 = (g15 (g15 r 0 (bget r 0 + 2)) 6 (bget r 6 + 7),
      (o, g18 (g18 (g18 (g18 (g18 (g18 (g18 k (bget r 6) 5 0 0) (bget r 6 + 1) 1 0 0) (bget r 6 + 2) 4 0 0) (bget r 6 + 3) 1 0 0)
        (bget r 6 + 4) 3 (bget x (bget r 0 + 1)) 0) (bget r 6 + 5) 1 0 0) (bget r 6 + 6) 1 0 0)) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 4 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc, b, i, hb, g_1]
  rw [if_neg (by simp [ha]), if_neg (by decide), if_neg (by simp [hc]), if_neg (by simp [hc]), if_neg (by simp [hc]),
    if_pos (by simp [hc])]

theorem g36_if_bad (x r o k : Buf) (y : UInt64) (hc : bget x (bget r 0) = 4) (hb : ¬ bget x (bget r 0 + 1) - 1 < 2) :
    g36 x r o k y = (g16 r, (o, k)) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 4 := by simp [c, c0, i, hc]
  have ha : (a == 0) = true := by simp [a, hc, b, i, hb, g_0]
  rw [if_pos ha]

theorem g37_t3 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 3) :
    g37 x r o k t f = (g15 r 6 (bget r 6 - 1), (bpush (bpush (g30 o 16)
      (if bget k ((bget r 6 - 1) * 3 + 1) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0,
      (bset k ((bget r 6 - 1 - 2) * 3 + 1) (bsize o + 4), f))) := by
  unfold g37
  extract_lets n c z y r1
  have hc' : c = 3 := by simp [c, n, hc]
  rw [if_neg (by simp [hc']), if_neg (by simp [hc']), if_pos (by simp [hc'])]

theorem g37_t4 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 4) :
    g37 x r o k t f = (match g20 (g15 r 6 (bget r 6 - 1)) (bpush o 0) (bget k ((bget r 6 - 1) * 3 + 1)) with
      | (r2, o2) => (r2, (o2, (bset k ((bget r 6 - 1 - 2) * 3 + 1) (bsize o), f)))) := by
  unfold g37
  extract_lets n c z y r1
  have hn : n = bget r 6 - 1 := rfl
  have hc1 : c = bget k (n * 3) := rfl
  have hz : z = bget k (n * 3 + 1) := rfl
  have hr1 : r1 = g15 r 6 n := rfl
  clear_value n c z y r1
  subst hn hz hr1
  rw [hc] at hc1
  subst hc1
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]

theorem g37_t5 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 5) :
    g37 x r o k t f = (match g20 (g15 r 6 (bget r 6 - 1)) o (bget k ((bget r 6 - 1) * 3 + 1)) with
      | (r2, o2) => (r2, (o2, (k, f)))) := by
  unfold g37
  extract_lets n c z y r1
  have hn : n = bget r 6 - 1 := rfl
  have hc1 : c = bget k (n * 3) := rfl
  have hz : z = bget k (n * 3 + 1) := rfl
  have hr1 : r1 = g15 r 6 n := rfl
  clear_value n c z y r1
  subst hn hz hr1
  rw [hc] at hc1
  subst hc1
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]

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

theorem uadd (n a b : Nat) : n.toUInt64 + a.toUInt64 + b.toUInt64 = (n + a + b).toUInt64 := by
  simp [Nat.toUInt64, UInt64.ofNat_add]

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


theorem g30_eq (o : Buf) : g30 o 16 = o ++ [g11 6 31 0, g11 5 31 8, g10 31 31 16] := by simp [g30, bpush]

theorem bset_mid (A B : Buf) (x v : UInt64) (p : UInt64) (hp : p.toNat = A.length) :
    bset (A ++ x :: B) p v = A ++ v :: B := by simp only [bset, hp]; exact set_mid A B x v

theorem bsize_u (o : Buf) : bsize o = o.length.toUInt64 := rfl

theorem ulen (l : Buf) (n : Nat) (h : l.length = n) : bsize l = n.toUInt64 := by rw [bsize_u, h]

theorem st_t4 (s : GS) (n P : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 4)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = P) :
    st s = ⟨s.x, if g14 P (bsize (bpush s.o 0)) == 1 then g15 s.r 6 n else g16 (g15 s.r 6 n),
      bset (bpush s.o 0) P (g13 0 P (bsize (bpush s.o 0))), bset s.k ((n - 2) * 3 + 1) (bsize s.o), s.t, s.f⟩ := by
  unfold st; rw [g37_t4 _ _ _ _ _ _ hc, ha, hn, g20_eq]

theorem st_t5 (s : GS) (n P : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 5)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = P) :
    st s = ⟨s.x, if g14 P (bsize s.o) == 1 then g15 s.r 6 n else g16 (g15 s.r 6 n),
      bset s.o P (g13 0 P (bsize s.o)), s.k, s.t, s.f⟩ := by
  unfold st; rw [g37_t5 _ _ _ _ _ _ hc, ha, hn, g20_eq]

/-- IF (value mode) -/
theorem v_if {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 4) :
    VS K i := by
  intro s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  have hl6 : (bset s.r 6 L.length.toUInt64).length = 10 := by rw [BufL.length_bset]; exact hI.rl
  have h0 : bget (bset s.r 6 L.length.toUInt64) 0 = i.toUInt64 := by
    rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have h6 : bget (bset s.r 6 L.length.toUInt64) 6 = L.length.toUInt64 := by
    rw [rget _ hI.rl 6 6 _ (by decide), if_pos rfl]
  have hx : bget s.x i.toUInt64 = 4 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  by_cases hb' : ¬ tg K.X (i + 1) - 1 < 2
  · rw [g36_if_bad _ _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb')]
    exact Reach.error (g16_err _ hl6)
  have hb : tg K.X (i + 1) - 1 < 2 := Classical.not_not.mp hb'
  rw [g36_if _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb), h0, h6, hv1]
  dsimp only
  have hLl := hI.Ll; simp at hLl
  obtain ⟨sk1, kl1⟩ := stk_push7 s.k L (5, 0, 0) (1, 0, 0) (4, 0, 0) (1, 0, 0) (3, (tg K.X (i + 1)), 0) (1, 0, 0) (1, 0, 0)
    (stk_pop hI.stk) hI.kl (by omega)
  simp only at sk1 kl1
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 2) (L.length.toUInt64 + 7) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 7)) _ s.o
    (L ++ [(5, 0, 0), (1, 0, 0), (4, 0, 0), (1, 0, 0), (3, (tg K.X (i + 1)), 0), (1, 0, 0), (1, 0, 0)])
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) sk1 kl1
    (by simp; omega) hI.ol
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 7)) 0 = (i + 2).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  have hr3_1 : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 7)) 3 = bget s.r 3 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
  -- operand a
  refine Reach.bind (IH (i + 2) (by omega) _ (L ++ [(5, 0, 0), (1, 0, 0), (4, 0, 0), (1, 0, 0), (3, (tg K.X (i + 1)), 0), (1, 0, 0)]) F
    (by simpa using hI1) hra (by simp; omega)) ?_
  rintro s2 ⟨ca, i1, Ea, hca, hI2, ho2, hr2, hi1, hd2⟩
  obtain ⟨ea, r3a⟩ := hd2 (by simp)
  subst ea
  -- operand b
  refine Reach.bind (IH i1 (by omega) s2 (L ++ [(5, 0, 0), (1, 0, 0), (4, 0, 0), (1, 0, 0), (3, (tg K.X (i + 1)), 0)]) F
    (by simpa using hI2) hr2 (by simp; omega)) ?_
  rintro s3 ⟨cb, i2, Eb, hcb, hI3, ho3, hr3, hi2, hd3⟩
  obtain ⟨eb, r3b⟩ := hd3 (by simp)
  subst eb
  simp only [List.map_nil, List.append_nil] at hI3
  -- compare item
  have hI3' : Inv K s3 ((L ++ [(5, 0, 0), (1, 0, 0), (4, 0, 0), (1, 0, 0)]) ++ [(3, (tg K.X (i + 1)), 0)]) F := by simpa using hI3
  refine Reach.step (live_of hI3' (by simp)) ?_
  obtain ⟨n3, c3, a3, -⟩ := top_item hI3'
  simp only [List.length_append, List.length_cons, List.length_nil] at n3
  have hidx : ((L.length + 4).toUInt64 - 2) * 3 + 1 = (3 * (L.length + 2) + 1).toUInt64 := by
    apply UInt64.toNat.inj; simp [Nat.toUInt64, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_add]; omega
  have hst : st s3 = ⟨s3.x, g15 s3.r 6 (L.length + 4).toUInt64, bpush (bpush (g30 s3.o 16)
      (if (tg K.X (i + 1)) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0,
      bset s3.k ((3 * (L.length + 2) + 1).toUInt64) (bsize s3.o + 4), s3.t, s3.f⟩ := by
    unfold st; rw [g37_t3 _ _ _ _ _ _ c3, a3, n3, hidx]
  rw [hst]
  have ho3' : s3.o = s.o ++ ca ++ cb := by rw [ho3, ho2]
  by_cases hbig : 2 ^ 32 ≤ (bpush (bpush (g30 s3.o 16) (if (tg K.X (i + 1)) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0).length
  · exact Reach.toobig hbig
  obtain ⟨q1, q2, q3⟩ := r6set s3.r hI3.rl (L.length + 4).toUInt64
  have sk4 : Stk (bset s3.k ((3 * (L.length + 2) + 1).toUInt64) (bsize s3.o + 4))
      (L ++ [(5, 0, 0), (1, 0, 0), (4, bsize s3.o + 4, 0), (1, 0, 0)]) := by
    have hp := stk_pop hI3'.stk
    have := stk_set hp (L.length + 2) (4, 0, 0) (by simp) (bsize s3.o + 4)
    simp only [bset]
    rw [u_toNat _ (by omega)]
    have e : (L ++ [(5, 0, 0), (1, 0, 0), (4, 0, 0), (1, 0, 0)]).set (L.length + 2) ((4 : UInt64), bsize s3.o + 4, (0 : UInt64)) =
        L ++ [(5, 0, 0), (1, 0, 0), (4, bsize s3.o + 4, 0), (1, 0, 0)] := by
      rw [List.set_append_right _ _ (by omega)]; simp
    rw [← e]; simpa using this
  have hI4 := inv_mk hI3' (g15 s3.r 6 (L.length + 4).toUInt64) (bset s3.k ((3 * (L.length + 2) + 1).toUInt64) (bsize s3.o + 4))
    (bpush (bpush (g30 s3.o 16) (if (tg K.X (i + 1)) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0)
    (L ++ [(5, 0, 0), (1, 0, 0), (4, bsize s3.o + 4, 0), (1, 0, 0)])
    (fun j a b => q3 j b) q1 (by simp only [g15]; rw [q2]; simp) sk4 (by rw [BufL.length_bset]; exact hI3.kl) (by simp; omega) (by omega)
  have hr4 : bget (g15 s3.r 6 (L.length + 4).toUInt64) 0 = i2.toUInt64 := by simp only [g15]; rw [q3 0 (by decide), hr3]
  -- then branch
  refine Reach.bind (IH i2 (by omega) _ (L ++ [(5, 0, 0), (1, 0, 0), (4, bsize s3.o + 4, 0)]) F
    (by simpa using hI4) hr4 (by simp; omega)) ?_
  rintro s5 ⟨ct, i3, Et, hct, hI5, ho5, hr5, hi3, hd5⟩
  obtain ⟨et, r3t⟩ := hd5 (by simp)
  subst et
  simp only [List.map_nil, List.append_nil] at hI5
  -- item 4: patch the compare's jump to here + 1, leave the end placeholder
  have hI5' : Inv K s5 ((L ++ [(5, 0, 0), (1, 0, 0)]) ++ [(4, bsize s3.o + 4, 0)]) F := by simpa using hI5
  refine Reach.step (live_of hI5' (by simp)) ?_
  obtain ⟨n5, c5, a5, -⟩ := top_item hI5'
  simp only [List.length_append, List.length_cons, List.length_nil] at n5
  have hidx5 : ((L.length + 2).toUInt64 - 2) * 3 + 1 = (3 * L.length + 1).toUInt64 := by
    apply UInt64.toNat.inj; simp [Nat.toUInt64, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_add]; omega
  have hst5 : st s5 = ⟨s5.x, if g14 (bsize s3.o + 4) (bsize (bpush s5.o 0)) == 1 then g15 s5.r 6 (L.length + 2).toUInt64
      else g16 (g15 s5.r 6 (L.length + 2).toUInt64),
      bset (bpush s5.o 0) (bsize s3.o + 4) (g13 0 (bsize s3.o + 4) (bsize (bpush s5.o 0))),
      bset s5.k (3 * L.length + 1).toUInt64 (bsize s5.o), s5.t, s5.f⟩ := by
    rw [st_t4 s5 _ _ n5 c5 a5, hidx5]
  rw [hst5]
  obtain ⟨p1, p2, p3⟩ := r6set s5.r hI5.rl (L.length + 2).toUInt64
  by_cases hg' : ¬ (g14 (bsize s3.o + 4) (bsize (bpush s5.o 0)) == 1) = true
  · rw [if_neg hg']; exact Reach.error (g16_err _ p1)
  rw [if_pos (Classical.not_not.mp hg')]
  -- the code so far
  have hA : s5.o = (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++ 0 :: ct := by
    rw [ho5, ho3']; simp [g30_eq, bpush, ifHd, List.append_assoc]
  have hl3 : s3.o.length = s.o.length + ca.length + cb.length := by rw [ho3']; simp [Nat.add_assoc]
  have hol3 := hI3.ol
  have hpj : bsize s3.o + 4 = (s.o.length + ca.length + cb.length + 4).toUInt64 := by
    rw [ulen _ _ hl3]; simp [Nat.toUInt64, UInt64.ofNat_add]
  have hP : (bsize s3.o + 4).toNat = (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))).length := by
    rw [hpj, u_toNat _ (by omega)]; simp [ifHd]; omega
  have ho6 : bset (bpush s5.o 0) (bsize s3.o + 4) (g13 0 (bsize s3.o + 4) (bsize (bpush s5.o 0))) =
      (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0]) := by
    have hl5 : (bpush s5.o 0).length = s.o.length + ca.length + cb.length + 5 + ct.length + 1 := by
      rw [bpush, hA]; simp [ifHd]; omega
    rw [ulen _ _ hl5, show bpush s5.o 0 = (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++ 0 :: (ct ++ [0]) by rw [bpush, hA]; simp,
      bset_mid _ _ _ _ _ hP, jw, ← hpj]
  rw [ho6]
  by_cases hbig6 : 2 ^ 32 ≤ ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0])).length
  · exact Reach.toobig hbig6
  have sk6 : Stk (bset s5.k (3 * L.length + 1).toUInt64 (bsize s5.o)) (L ++ [(5, bsize s5.o, 0), (1, 0, 0)]) := by
    have hp := stk_pop hI5'.stk
    have := stk_set hp L.length (5, 0, 0) (by simp) (bsize s5.o)
    simp only [bset]
    rw [u_toNat _ (by omega)]
    have e : (L ++ [(5, 0, 0), (1, 0, 0)]).set L.length ((5 : UInt64), bsize s5.o, (0 : UInt64)) =
        L ++ [(5, bsize s5.o, 0), (1, 0, 0)] := by
      rw [List.set_append_right _ _ (by omega)]; simp
    rw [← e]; simpa using this
  have hI6 := inv_mk hI5' (g15 s5.r 6 (L.length + 2).toUInt64) (bset s5.k (3 * L.length + 1).toUInt64 (bsize s5.o))
    ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0]))
    (L ++ [(5, bsize s5.o, 0), (1, 0, 0)]) (fun j a b => p3 j b) p1 (by simp only [g15]; rw [p2]; simp) sk6
    (by rw [BufL.length_bset]; exact hI5.kl) (by simp; omega) (by omega)
  have hr6 : bget (g15 s5.r 6 (L.length + 2).toUInt64) 0 = i3.toUInt64 := by simp only [g15]; rw [p3 0 (by decide), hr5]
  -- else branch
  refine Reach.bind (IH i3 (by omega) _ (L ++ [(5, bsize s5.o, 0)]) F (by simpa using hI6) hr6 (by simp; omega)) ?_
  rintro s7 ⟨ce, i4, Ee, hce, hI7, ho7, hr7, hi4, hd7⟩
  -- item 5: patch the end placeholder
  have hI7' : Inv K s7 (L ++ [(5, bsize s5.o, 0)]) (F ++ Ee.map Nat.toUInt64) := hI7
  refine Reach.step (live_of hI7' (by simp)) ?_
  obtain ⟨n7, c7, a7, -⟩ := top_item hI7'
  have hst7 : st s7 = ⟨s7.x, if g14 (bsize s5.o) (bsize s7.o) == 1 then g15 s7.r 6 L.length.toUInt64
      else g16 (g15 s7.r 6 L.length.toUInt64), bset s7.o (bsize s5.o) (g13 0 (bsize s5.o) (bsize s7.o)), s7.k, s7.t, s7.f⟩ := by
    rw [st_t5 s7 _ _ n7 c7 a7]
  rw [hst7]
  obtain ⟨w1, w2, w3⟩ := r6set s7.r hI7.rl L.length.toUInt64
  by_cases hg7 : ¬ (g14 (bsize s5.o) (bsize s7.o) == 1) = true
  · rw [if_neg hg7]; exact Reach.error (g16_err _ w1)
  rw [if_pos (Classical.not_not.mp hg7)]
  have e1 : bsize s5.o = (s.o.length + ca.length + cb.length + 5 + ct.length).toUInt64 :=
    ulen _ _ (by rw [hA]; simp [ifHd]; omega)
  have e2 : bsize s7.o = (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length).toUInt64 :=
    ulen _ _ (by rw [ho7]; simp [ifHd]; omega)
  have hQ : (s.o.length + ca.length + cb.length + 5 + ct.length).toUInt64.toNat = ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: ct).length := by
    have hl : s5.o.length < 2 ^ 32 := hI5.ol
    have : s5.o.length = s.o.length + ca.length + cb.length + 5 + ct.length := by rw [hA]; simp [ifHd]; omega
    rw [u_toNat _ (by omega)]; simp [ifHd]; omega
  have ho8 : bset s7.o (bsize s5.o) (g13 0 (bsize s5.o) (bsize s7.o)) = s.o ++ (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
      [jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (s.o.length + ca.length + cb.length + 5 + ct.length)
        (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce) := by
    rw [e1, e2, ho7, show ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0])) ++ ce =
        ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: ct) ++ 0 :: ce by simp]
    rw [bset_mid _ _ _ _ _ hQ]
    simp only [jw, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
  rw [ho8]
  by_cases hbig8 : 2 ^ 32 ≤ (s.o ++ (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
      [jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (s.o.length + ca.length + cb.length + 5 + ct.length)
        (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce)).length
  · exact Reach.toobig hbig8
  have hI8 := inv_mk hI7' (g15 s7.r 6 L.length.toUInt64) s7.k
    (s.o ++ (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
      [jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (s.o.length + ca.length + cb.length + 5 + ct.length)
        (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce)) L (fun j a b => w3 j b) w1
    (by simp only [g15]; rw [w2]) (stk_pop hI7'.stk) hI7.kl (by omega) (by omega)
  refine Reach.done ⟨_, i4, [] ++ [] ++ [] ++ Ee, ?_, ?_, rfl, ?_, by omega, fun hd => ?_⟩
  · have hca' : CG K (L.length + 6) (i + 2) s.o.length ca i1 [] := by simpa using hca
    have hcb' : CG K (L.length + 5) i1 (s.o.length + ca.length) cb i2 [] := by
      have : s2.o.length = s.o.length + ca.length := by rw [ho2]; simp
      simpa [this] using hcb
    have hct' : CG K (L.length + 3) i2 (s.o.length + ca.length + cb.length + 5) ct i3 [] := by
      have : (bpush (bpush (g30 s3.o 16) (if (tg K.X (i + 1) == 1) = true then g4 0 5 6 8 else g4 6 5 6 8)) 0).length =
          s.o.length + ca.length + cb.length + 5 := by rw [g30_eq, ho3']; simp [bpush]; omega
      simp only at hct; rw [this] at hct; simpa using hct
    have hce' : CG K (L.length + 1) i3 (s.o.length + ca.length + cb.length + 5 + ct.length + 1) ce i4 Ee := by
      have : (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0])).length =
          s.o.length + ca.length + cb.length + 5 + ct.length + 1 := by simp [ifHd]; omega
      simp only at hce; rw [this] at hce; simpa using hce
    exact .ite ht hb hca' hcb' hct' hce'
  · simpa using hI8
  · simp only [g15]; rw [w3 0 (by decide), hr7]
  · obtain ⟨ee, r3e⟩ := hd7 (by simp; omega)
    subst ee
    refine ⟨rfl, ?_⟩
    simp only [g15]
    rw [w3 3 (by decide), r3e]; simp only [g15]
    rw [p3 3 (by decide), r3t]; simp only [g15]
    rw [q3 3 (by decide), r3b, r3a, hr3_1]


theorem g36_pair (x r o k : Buf) (hc : bget x (bget r 0) = 6) :
    g36 x r o k 0 = (if bget x (bget r 0 + 1) < 251 then
      (g15 (g15 r 0 (bget r 0 + 2)) 6 (bget r 6 + bget x (bget r 0 + 1)), (o, g27 256 k (bget r 6) (bget x (bget r 0 + 1))))
      else (g16 r, (o, k))) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 6 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc, g_1]
  rw [if_neg (by simp [ha]), if_neg (by decide), if_neg (by simp [hc]), if_neg (by simp [hc]), if_neg (by simp [hc]),
    if_neg (by simp [hc]), if_neg (by simp [hc]), if_pos (by simp [hc])]

theorem g36_call (x r o k : Buf) (hc : bget x (bget r 0) = 8) :
    g36 x r o k 0 = (if bget x (bget r 0 + 2) < 251 then
      (g15 (g15 r 0 (bget r 0 + 3)) 6 (bget r 6 + 1 + bget x (bget r 0 + 2)),
        (o, g27 256 (g18 k (bget r 6) 7 (bget x (bget r 0 + 1)) 0) (bget r 6 + 1) (bget x (bget r 0 + 2))))
      else (g16 r, (o, k))) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 7 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc, g_1]
  rw [if_neg (by simp [ha]), if_neg (by decide), if_neg (by simp [hc]), if_neg (by simp [hc]), if_neg (by simp [hc]),
    if_neg (by simp [hc]), if_neg (by simp [hc]), if_neg (by simp [hc]), if_pos (by simp [hc])]

theorem g36_prim (x r o k : Buf) (hc : bget x (bget r 0) = 9) (hb : bget x (bget r 0 + 1) - 1 < 9) :
    g36 x r o k 0 = (g15 (g15 r 0 (bget r 0 + 2)) 6 (bget r 6 + 1 + g33 (bget x (bget r 0 + 1))),
        (o, g27 256 (g18 k (bget r 6) 8 (bget x (bget r 0 + 1)) 0) (bget r 6 + 1) (g33 (bget x (bget r 0 + 1))))) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 8 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc, b, i, hb, g_1]
  rw [if_neg (by simp [ha]), if_neg (by decide), if_neg (by simp [hc]), if_neg (by simp [hc]), if_neg (by simp [hc]),
    if_neg (by simp [hc]), if_neg (by simp [hc]), if_neg (by simp [hc]), if_neg (by simp [hc]), if_pos (by simp [hc])]

theorem g36_prim_bad (x r o k : Buf) (y : UInt64) (hc : bget x (bget r 0) = 9) (hb : ¬ bget x (bget r 0 + 1) - 1 < 9) :
    g36 x r o k y = (g16 r, (o, k)) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 8 := by simp [c, c0, i, hc]
  have ha : (a == 0) = true := by simp [a, hc, b, i, hb, g_0]
  rw [if_pos ha]

theorem g37_t7 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 7) :
    g37 x r o k t f = (match (if bget k ((bget r 6 - 1) * 3 + 1) < bsize t then
        g19 (g15 r 6 (bget r 6 - 1)) o 1 (bget t (bget k ((bget r 6 - 1) * 3 + 1)))
        else (g16 (g15 r 6 (bget r 6 - 1)), o)) with
      | (r2, o2) => (r2, (o2, (k, f)))) := by
  unfold g37
  extract_lets n c z y r1
  have hn : n = bget r 6 - 1 := rfl
  have hc1 : c = bget k (n * 3) := rfl
  have hz : z = bget k (n * 3 + 1) := rfl
  have hr1 : r1 = g15 r 6 n := rfl
  clear_value n c z y r1
  subst hn hz hr1
  rw [hc] at hc1
  subst hc1
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos (by decide)]

theorem g37_t8 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 8) :
    g37 x r o k t f = (g15 r 6 (bget r 6 - 1), (g32 o (bget k ((bget r 6 - 1) * 3 + 1)) (bget (g15 r 6 (bget r 6 - 1)) 9), (k, f))) := by
  unfold g37
  extract_lets n c z y r1
  have hn : n = bget r 6 - 1 := rfl
  have hc1 : c = bget k (n * 3) := rfl
  have hz : z = bget k (n * 3 + 1) := rfl
  have hr1 : r1 = g15 r 6 n := rfl
  clear_value n c z y r1
  subst hn hz hr1
  rw [hc] at hc1
  subst hc1
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos (by decide)]

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


/-- the postcondition of n consecutive value visits -/
def SPost (K : Cx) (s0 : GS) (L : List Item) (F : List UInt64) (i n : Nat) (s' : GS) : Prop :=
  ∃ c i' E, CGs K L.length i s0.o.length n c i' E ∧ Inv K s' L (F ++ E.map Nat.toUInt64) ∧ s'.o = s0.o ++ c ∧
    bget s'.r 0 = i'.toUInt64 ∧ i ≤ i' ∧ (2 ≤ L.length → E = [] ∧ bget s'.r 3 = bget s0.r 3)

/-- n operand visits (pushed by g27) -/
theorem seq {K i0} (hV : ∀ j, i0 ≤ j → VS K j) : ∀ (n i : Nat) (s : GS) (L : List Item) (F : List UInt64), i0 ≤ i →
    Inv K s (L ++ List.replicate n (1, 0, 0)) F → bget s.r 0 = i.toUInt64 →
    L.length + n + 300 * (K.X.length - i) + 300 < 2 ^ 60 → Reach s (SPost K s L F i n)
  | 0, i, s, L, F, _, hI, hr0, _ => .done ⟨[], i, [], .nil, by simpa using hI, by simp, hr0, Nat.le_refl _, fun _ => ⟨rfl, rfl⟩⟩
  | n + 1, i, s, L, F, hi, hI, hr0, hB => by
    have hI' : Inv K s ((L ++ List.replicate n (1, 0, 0)) ++ [(1, 0, 0)]) F := by
      rw [List.append_assoc, ← List.replicate_succ']; exact hI
    refine Reach.bind (hV i hi s _ F hI' hr0 (by simp; omega)) ?_
    rintro s2 ⟨c, i1, E, hc, hI2, ho2, hr2, hi1, hd2⟩
    refine Reach.bind (seq hV n i1 s2 L (F ++ E.map Nat.toUInt64) (by omega) hI2 hr2 (by omega)) ?_
    rintro s3 ⟨cs, i2, Es, hcs, hI3, ho3, hr3, hi2, hd3⟩
    refine Reach.done ⟨c ++ cs, i2, E ++ Es, ?_, by rw [List.map_append, ← List.append_assoc]; exact hI3,
      by rw [ho3, ho2, List.append_assoc], hr3, by omega, fun hd => ?_⟩
    · have hc' : CG K (L.length + n) i s.o.length c i1 E := by simpa using hc
      have hcs' : CGs K L.length i1 (s.o.length + c.length) n cs i2 Es := by
        have : s2.o.length = s.o.length + c.length := by rw [ho2]; simp
        rw [← this]; exact hcs
      exact .cons hc' hcs'
    · obtain ⟨e1, r1⟩ := hd2 (by simp; omega)
      obtain ⟨e2, r2⟩ := hd3 hd
      exact ⟨by rw [e1, e2]; rfl, by rw [r2, r1]⟩

theorem u_small (q : UInt64) (h : q < 251) : q.toNat < 251 ∧ q.toNat.toUInt64 = q := by
  refine ⟨UInt64.lt_iff_toNat_lt.mp h, by simp [Nat.toUInt64]⟩

/-- PAIR -/
theorem v_pair {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 6) :
    VS K i := by
  intro s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  have hl6 : (bset s.r 6 L.length.toUInt64).length = 10 := by rw [BufL.length_bset]; exact hI.rl
  have h0 : bget (bset s.r 6 L.length.toUInt64) 0 = i.toUInt64 := by
    rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have h6 : bget (bset s.r 6 L.length.toUInt64) 6 = L.length.toUInt64 := by
    rw [rget _ hI.rl 6 6 _ (by decide), if_pos rfl]
  have hx : bget s.x i.toUInt64 = 6 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  rw [g36_pair _ _ _ _ (by rw [h0]; exact hx), h0, h6, hv1]
  by_cases hq' : ¬ tg K.X (i + 1) < 251
  · rw [if_neg hq']; exact Reach.error (g16_err _ hl6)
  have hq : tg K.X (i + 1) < 251 := Classical.not_not.mp hq'
  rw [if_pos hq]
  obtain ⟨qn, qe⟩ := u_small _ hq
  have hLl := hI.Ll; simp at hLl
  obtain ⟨sk1, kl1⟩ := stk_g27 256 s.k L (tg K.X (i + 1)).toNat (by omega) (stk_pop hI.stk) hI.kl (by omega)
  rw [qe] at sk1 kl1
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 2) (L.length.toUInt64 + tg K.X (i + 1)) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + tg K.X (i + 1)))
    _ s.o (L ++ List.replicate (tg K.X (i + 1)).toNat (1, 0, 0))
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; rw [← qe]; simp [Nat.toUInt64, UInt64.ofNat_add]) sk1 kl1
    (by simp; omega) hI.ol
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + tg K.X (i + 1))) 0 =
      (i + 2).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  refine Reach.bind (seq (i0 := i + 2) (fun j hj => IH j (by omega)) _ (i + 2) _ L F (Nat.le_refl _) hI1 hra (by omega)) ?_
  rintro s2 ⟨c, i2, E, hc, hI2, ho2, hr2, hi2, hd2⟩
  refine Reach.done ⟨c, i2, E, .pair ht hq hc, hI2, ho2, hr2, by omega, fun hd => ?_⟩
  obtain ⟨e, r3⟩ := hd2 hd
  refine ⟨e, ?_⟩
  rw [r3]; simp only [g15]
  rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]


theorem g19_eq (r o : Buf) (d b : UInt64) :
    g19 r o d b = (if g14 (bsize o) b == 1 then r else g16 r, bpush o (g13 d (bsize o) b)) := by
  unfold g19
  extract_lets h
  by_cases hc : (g14 h b == 1) = true
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]

theorem st_t7 (s : GS) (n D : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 7)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = D) (hD : D < bsize s.t) :
    st s = ⟨s.x, if g14 (bsize s.o) (bget s.t D) == 1 then g15 s.r 6 n else g16 (g15 s.r 6 n),
      bpush s.o (g13 1 (bsize s.o) (bget s.t D)), s.k, s.t, s.f⟩ := by
  unfold st; rw [g37_t7 _ _ _ _ _ _ hc, ha, hn, if_pos hD, g19_eq]

theorem st_t7_bad (s : GS) (n D : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 7)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = D) (hD : ¬ D < bsize s.t) :
    st s = ⟨s.x, g16 (g15 s.r 6 n), s.o, s.k, s.t, s.f⟩ := by
  unfold st; rw [g37_t7 _ _ _ _ _ _ hc, ha, hn, if_neg hD]

theorem st_t8 (s : GS) (n P : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 8)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = P) :
    st s = ⟨s.x, g15 s.r 6 n, g32 s.o P (bget (g15 s.r 6 n) 9), s.k, s.t, s.f⟩ := by
  unfold st; rw [g37_t8 _ _ _ _ _ _ hc, ha, hn]

/-- CALL -/
theorem v_call {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 8) :
    VS K i := by
  intro s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  have hl6 : (bset s.r 6 L.length.toUInt64).length = 10 := by rw [BufL.length_bset]; exact hI.rl
  have h0 : bget (bset s.r 6 L.length.toUInt64) 0 = i.toUInt64 := by
    rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have h6 : bget (bset s.r 6 L.length.toUInt64) 6 = L.length.toUInt64 := by
    rw [rget _ hI.rl 6 6 _ (by decide), if_pos rfl]
  have hx : bget s.x i.toUInt64 = 8 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  have hv2 : bget s.x (i.toUInt64 + 2) = tg K.X (i + 2) := by rw [hI.x]; exact tg_u1 _ i 2 (by omega)
  rw [g36_call _ _ _ _ (by rw [h0]; exact hx), h0, h6, hv1, hv2]
  by_cases hq' : ¬ tg K.X (i + 2) < 251
  · rw [if_neg hq']; exact Reach.error (g16_err _ hl6)
  have hq : tg K.X (i + 2) < 251 := Classical.not_not.mp hq'
  rw [if_pos hq]
  obtain ⟨qn, qe⟩ := u_small _ hq
  have hLl := hI.Ll; simp at hLl
  obtain ⟨sk0, kl0⟩ := stk_push s.k L 7 (tg K.X (i + 1)) 0 (stk_pop hI.stk) hI.kl (by omega)
  have e1 : L.length.toUInt64 + 1 = (L ++ [(7, tg K.X (i + 1), 0)]).length.toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]
  have hkl := hI.kl
  obtain ⟨sk1, kl1⟩ := stk_g27 256 _ (L ++ [(7, tg K.X (i + 1), 0)]) (tg K.X (i + 2)).toNat (by omega) sk0 (by rw [kl0]; omega)
    (by simp; omega)
  rw [qe, ← e1] at sk1 kl1
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 3) (L.length.toUInt64 + 1 + tg K.X (i + 2)) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 3)) 6 (L.length.toUInt64 + 1 + tg K.X (i + 2)))
    _ s.o (L ++ [(7, tg K.X (i + 1), 0)] ++ List.replicate (tg K.X (i + 2)).toNat (1, 0, 0))
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; rw [← qe]; simp [Nat.toUInt64, UInt64.ofNat_add]; ac_rfl) sk1 kl1
    (by simp; omega) hI.ol
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 3)) 6 (L.length.toUInt64 + 1 + tg K.X (i + 2))) 0 =
      (i + 3).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  refine Reach.bind (seq (i0 := i + 3) (fun j hj => IH j (by omega)) _ (i + 3) _ (L ++ [(7, tg K.X (i + 1), 0)]) F (Nat.le_refl _)
    hI1 hra (by simp; omega)) ?_
  rintro s2 ⟨c, i2, E, hc, hI2, ho2, hr2, hi2, hd2⟩
  refine Reach.step (live_of hI2 (by simp)) ?_
  obtain ⟨n2, c2, a2, -⟩ := top_item hI2
  have ht2 : s2.t = K.T := hI2.t
  by_cases hD' : ¬ tg K.X (i + 1) < bsize s2.t
  · rw [st_t7_bad s2 _ _ n2 c2 a2 hD']
    obtain ⟨p1, -, -⟩ := r6set s2.r hI2.rl L.length.toUInt64
    exact Reach.error (g16_err _ p1)
  have hD : tg K.X (i + 1) < bsize s2.t := Classical.not_not.mp hD'
  rw [st_t7 s2 _ _ n2 c2 a2 hD]
  obtain ⟨p1, p2, p3⟩ := r6set s2.r hI2.rl L.length.toUInt64
  by_cases hg' : ¬ (g14 (bsize s2.o) (bget s2.t (tg K.X (i + 1))) == 1) = true
  · rw [if_neg hg']; exact Reach.error (g16_err _ p1)
  rw [if_pos (Classical.not_not.mp hg')]
  by_cases hbig : 2 ^ 32 ≤ (bpush s2.o (g13 1 (bsize s2.o) (bget s2.t (tg K.X (i + 1))))).length
  · exact Reach.toobig hbig
  have hI3 := inv_mk hI2 (g15 s2.r 6 L.length.toUInt64) s2.k (bpush s2.o (g13 1 (bsize s2.o) (bget s2.t (tg K.X (i + 1))))) L
    (fun j a b => p3 j b) p1 (by simp only [g15]; rw [p2]) (stk_pop hI2.stk) hI2.kl (by omega) (by omega)
  have hl2 : s2.o.length = s.o.length + c.length := by rw [ho2]; simp
  refine Reach.done ⟨c ++ [g13 1 (s.o.length + c.length).toUInt64 (bget K.T (tg K.X (i + 1)))], i2, E, ?_, hI3, ?_, ?_, by omega,
    fun hd => ?_⟩
  · exact .call ht hq (by rw [← ht2]; exact hD) (by simpa using hc)
  · simp only; rw [bpush, ulen _ _ hl2, ho2, ht2]; simp
  · simp only [g15]; rw [p3 0 (by decide), hr2]
  · obtain ⟨e, r3⟩ := hd2 (by simp; omega)
    refine ⟨e, ?_⟩
    simp only [g15]; rw [p3 3 (by decide), r3]; simp only [g15]
    rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]


theorem g33_lt (p : UInt64) : g33 p < 4 := by
  unfold g33
  repeat (first | split | decide)

/-- PRIM -/
theorem v_prim {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 9) :
    VS K i := by
  intro s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  have hl6 : (bset s.r 6 L.length.toUInt64).length = 10 := by rw [BufL.length_bset]; exact hI.rl
  have h0 : bget (bset s.r 6 L.length.toUInt64) 0 = i.toUInt64 := by
    rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have h6 : bget (bset s.r 6 L.length.toUInt64) 6 = L.length.toUInt64 := by
    rw [rget _ hI.rl 6 6 _ (by decide), if_pos rfl]
  have hx : bget s.x i.toUInt64 = 9 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  by_cases hb' : ¬ tg K.X (i + 1) - 1 < 9
  · rw [g36_prim_bad _ _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb')]
    exact Reach.error (g16_err _ hl6)
  have hb : tg K.X (i + 1) - 1 < 9 := Classical.not_not.mp hb'
  rw [g36_prim _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb), h0, h6, hv1]
  have hq : g33 (tg K.X (i + 1)) < 251 := by
    have := g33_lt (tg K.X (i + 1)); rw [UInt64.lt_iff_toNat_lt] at this ⊢; simp at this ⊢; omega
  obtain ⟨qn, qe⟩ := u_small _ hq
  have hLl := hI.Ll; simp at hLl
  obtain ⟨sk0, kl0⟩ := stk_push s.k L 8 (tg K.X (i + 1)) 0 (stk_pop hI.stk) hI.kl (by omega)
  have e1 : L.length.toUInt64 + 1 = (L ++ [(8, tg K.X (i + 1), 0)]).length.toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]
  have hkl := hI.kl
  obtain ⟨sk1, kl1⟩ := stk_g27 256 _ (L ++ [(8, tg K.X (i + 1), 0)]) (g33 (tg K.X (i + 1))).toNat (by omega) sk0
    (by rw [kl0]; omega) (by simp; omega)
  rw [qe, ← e1] at sk1 kl1
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 2) (L.length.toUInt64 + 1 + g33 (tg K.X (i + 1))) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 1 + g33 (tg K.X (i + 1))))
    _ s.o (L ++ [(8, tg K.X (i + 1), 0)] ++ List.replicate (g33 (tg K.X (i + 1))).toNat (1, 0, 0))
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; rw [← qe]; simp [Nat.toUInt64, UInt64.ofNat_add]; ac_rfl) sk1 kl1
    (by simp; omega) hI.ol
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 1 + g33 (tg K.X (i + 1)))) 0 =
      (i + 2).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  refine Reach.bind (seq (i0 := i + 2) (fun j hj => IH j (by omega)) _ (i + 2) _ (L ++ [(8, tg K.X (i + 1), 0)]) F (Nat.le_refl _)
    hI1 hra (by simp; omega)) ?_
  rintro s2 ⟨c, i2, E, hc, hI2, ho2, hr2, hi2, hd2⟩
  refine Reach.step (live_of hI2 (by simp)) ?_
  obtain ⟨n2, c2, a2, -⟩ := top_item hI2
  rw [st_t8 s2 _ _ n2 c2 a2]
  obtain ⟨p1, p2, p3⟩ := r6set s2.r hI2.rl L.length.toUInt64
  have hu : bget (g15 s2.r 6 L.length.toUInt64) 9 = K.u := by simp only [g15]; rw [p3 9 (by decide), hI2.r9]
  rw [hu]
  have e := pi_g32 (tg K.X (i + 1)) K.u s2.o
  simp only at e
  rw [e]
  by_cases hbig : 2 ^ 32 ≤ (s2.o ++ em (fun o => g32 o (tg K.X (i + 1)) K.u) s2.o.length).length
  · exact Reach.toobig hbig
  have hI3 := inv_mk hI2 (g15 s2.r 6 L.length.toUInt64) s2.k (s2.o ++ em (fun o => g32 o (tg K.X (i + 1)) K.u) s2.o.length) L
    (fun j a b => p3 j b) p1 (by simp only [g15]; rw [p2]) (stk_pop hI2.stk) hI2.kl (by omega) (by omega)
  have hl2 : s2.o.length = s.o.length + c.length := by rw [ho2]; simp
  refine Reach.done ⟨c ++ em (fun o => g32 o (tg K.X (i + 1)) K.u) (s.o.length + c.length), i2, E, ?_, hI3, ?_, ?_, by omega,
    fun hd => ?_⟩
  · exact .prim ht hb (by simpa using hc)
  · simp only; rw [hl2, ho2]; simp
  · simp only [g15]; rw [p3 0 (by decide), hr2]
  · obtain ⟨e, r3⟩ := hd2 (by simp; omega)
    refine ⟨e, ?_⟩
    simp only [g15]; rw [p3 3 (by decide), r3]; simp only [g15]
    rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]


/-! ## tail mode (loop arms) -/

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

theorem g36_tval (x r o k : Buf) (hz : nt (bget x (bget r 0)) ≠ 4 ∧ nt (bget x (bget r 0)) ≠ 5 ∧ nt (bget x (bget r 0)) ≠ 10) :
    g36 x r o k 1 = (if rngA (nt (bget x (bget r 0))) (bget x (bget r 0 + 1)) == 0 then (g16 r, (o, k)) else
      (g15 r 6 (bget r 6 + 2), (o, g18 (g18 k (bget r 6) 9 0 0) (bget r 6 + 1) 1 0 0))) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hi : i = bget r 0 := rfl
  have hn : n = bget r 6 := rfl
  have hc0 : c0 = bget x i := rfl
  have hc : c = nt c0 := rfl
  have hb : b = bget x (i + 1) := rfl
  have ha : a = rngA c b := rfl
  have hz' : z = (if c == 4 then g_1 else if c == 5 then g_1 else if c == 10 then g_1 else g_0) := rfl
  clear_value i n c0 c z b a
  subst hi hn hc0 hc hb ha hz'
  rw [if_neg (show ¬ (nt (bget x (bget r 0)) == 4) = true by simpa using hz.1),
    if_neg (show ¬ (nt (bget x (bget r 0)) == 5) = true by simpa using hz.2.1),
    if_neg (show ¬ (nt (bget x (bget r 0)) == 10) = true by simpa using hz.2.2)]
  by_cases h : (rngA (nt (bget x (bget r 0))) (bget x (bget r 0 + 1)) == 0) = true
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_pos (show ((1 : UInt64) == 1) = true by decide), if_pos (show (g_0 == 0) = true by decide)]

theorem g36_tcont (x r o k : Buf) (hc : bget x (bget r 0) = 11) :
    g36 x r o k 1 = (g15 (g15 r 0 (bget r 0 + 1)) 6 (bget r 6 + 2), (o, g18 (g18 k (bget r 6) 10 0 0) (bget r 6 + 1) 1 0 0)) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc' : c = 10 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc', g_1]
  have hz : (z == 0) = false := by simp [z, hc', g_1]
  rw [if_neg (by simp [ha]), if_pos (by decide), if_neg (by simp [hz]), if_pos (by simp [hc'])]

theorem g37_t9 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 9) :
    g37 x r o k t f = (if 65535 < bget (g15 r 6 (bget r 6 - 1)) 8 then (g16 (g15 r 6 (bget r 6 - 1)), (o, (k, f))) else
      (g15 (g15 r 6 (bget r 6 - 1)) 8 (bget (g15 r 6 (bget r 6 - 1)) 8 + 1), (bpush o 0,
        (k, g17 f (bget (g15 r 6 (bget r 6 - 1)) 8) (bsize o))))) := by
  unfold g37
  extract_lets n c z y r1
  have hn : n = bget r 6 - 1 := rfl
  have hc1 : c = bget k (n * 3) := rfl
  have hr1 : r1 = g15 r 6 n := rfl
  clear_value n c z y r1
  subst hn hr1
  rw [hc] at hc1
  subst hc1
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_pos (by decide)]

theorem g37_t10 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 10) :
    g37 x r o k t f =
      (if g14 (bsize (g26 256 (bget (g15 r 6 (bget r 6 - 1)) 1) 1 (bget (g15 r 6 (bget r 6 - 1)) 1 - 1) o))
          (bget (g15 r 6 (bget r 6 - 1)) 3) == 1 then g15 r 6 (bget r 6 - 1) else g16 (g15 r 6 (bget r 6 - 1)),
        (bpush (g26 256 (bget (g15 r 6 (bget r 6 - 1)) 1) 1 (bget (g15 r 6 (bget r 6 - 1)) 1 - 1) o)
          (g13 0 (bsize (g26 256 (bget (g15 r 6 (bget r 6 - 1)) 1) 1 (bget (g15 r 6 (bget r 6 - 1)) 1 - 1) o))
            (bget (g15 r 6 (bget r 6 - 1)) 3)), (k, f))) := by
  unfold g37
  extract_lets n c z y r1
  have hn : n = bget r 6 - 1 := rfl
  have hc1 : c = bget k (n * 3) := rfl
  have hr1 : r1 = g15 r 6 n := rfl
  clear_value n c z y r1
  subst hn hr1
  rw [hc] at hc1
  subst hc1
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  rw [g19_eq]


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
    (ho : o'.length < 2 ^ 32) : Inv K ⟨s.x, r', o', k', s.t, f'⟩ L' F' where
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

theorem st_t9 (s : GS) (n : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 9) :
    st s = if 65535 < bget (g15 s.r 6 n) 8 then ⟨s.x, g16 (g15 s.r 6 n), s.o, s.k, s.t, s.f⟩ else
      ⟨s.x, g15 (g15 s.r 6 n) 8 (bget (g15 s.r 6 n) 8 + 1), bpush s.o 0, s.k, s.t, g17 s.f (bget (g15 s.r 6 n) 8) (bsize s.o)⟩ := by
  unfold st; rw [g37_t9 _ _ _ _ _ _ hc, hn]
  by_cases h : 65535 < bget (g15 s.r 6 n) 8
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- the tail-visit postcondition -/
def TPost (K : Cx) (hd : Nat) (s0 : GS) (L : List Item) (F : List UInt64) (i : Nat) (s' : GS) : Prop :=
  ∃ c i' E, CT K hd L.length i s0.o.length c i' E ∧ Inv K s' L (F ++ E.map Nat.toUInt64) ∧ s'.o = s0.o ++ c ∧
    bget s'.r 0 = i'.toUInt64 ∧ i < i' ∧ bget s'.r 3 = bget s0.r 3

/-- tail visit at AST word i, loop head hd -/
def TS (K : Cx) (hd i : Nat) : Prop := ∀ s L F, 1 ≤ L.length → Inv K s (L ++ [(1, 1, 0)]) F → bget s.r 0 = i.toUInt64 →
  bget s.r 3 = hd.toUInt64 → L.length + 1 + 300 * (K.X.length - i) + 300 < 2 ^ 60 → Reach s (TPost K hd s L F i)

/-- a value node in tail position: the value, then an exit placeholder recorded in f -/
theorem t_val {K hd i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (hV : VS K i)
    (h4 : tg K.X i ≠ 4) (h5 : tg K.X i ≠ 5) (h11 : tg K.X i ≠ 11) : TS K hd i := by
  intro s L F hL1 hI hr0 hr3 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  have hl6 : (bset s.r 6 L.length.toUInt64).length = 10 := by rw [BufL.length_bset]; exact hI.rl
  have h0 : bget (bset s.r 6 L.length.toUInt64) 0 = i.toUInt64 := by
    rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have h6 : bget (bset s.r 6 L.length.toUInt64) 6 = L.length.toUInt64 := by
    rw [rget _ hI.rl 6 6 _ (by decide), if_pos rfl]
  have hx : bget s.x i.toUInt64 = tg K.X i := by rw [hI.x, tg_u _ _ (by omega)]
  rw [g36_tval _ _ _ _ (by rw [h0, hx]; exact nt_tail _ h4 h5 h11), h0, h6]
  by_cases ha : (rngA (nt (bget s.x i.toUInt64)) (bget s.x (i.toUInt64 + 1)) == 0) = true
  · rw [if_pos ha]; exact Reach.error (g16_err _ hl6)
  rw [if_neg ha]
  have hLl := hI.Ll; simp at hLl
  have q1 : L.length.toUInt64 + 1 = (L ++ [(9, 0, 0)]).length.toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]
  obtain ⟨sk0, kl0⟩ := stk_push_at s.k L _ 9 0 0 rfl (stk_pop hI.stk) hI.kl (by omega)
  obtain ⟨sk1, kl1⟩ := stk_push_at _ _ _ 1 0 0 q1 sk0 kl0 (by simp; omega)
  obtain ⟨p1, p2, p3⟩ := r6set (bset s.r 6 L.length.toUInt64) hl6 (L.length.toUInt64 + 2)
  have hI1 := inv_mk hI (g15 (bset s.r 6 L.length.toUInt64) 6 (L.length.toUInt64 + 2)) _ s.o (L ++ [(9, 0, 0), (1, 0, 0)])
    (fun j a b => by simp only [g15]; rw [p3 j b, rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)]) p1
    (by simp only [g15]; rw [p2]; simp [Nat.toUInt64, UInt64.ofNat_add]) (by simpa using sk1) kl1 (by simp; omega) hI.ol
  have hra : bget (g15 (bset s.r 6 L.length.toUInt64) 6 (L.length.toUInt64 + 2)) 0 = i.toUInt64 := by
    simp only [g15]; rw [p3 0 (by decide), h0]
  have hr31 : bget (g15 (bset s.r 6 L.length.toUInt64) 6 (L.length.toUInt64 + 2)) 3 = bget s.r 3 := by
    simp only [g15]; rw [p3 3 (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
  refine Reach.bind (hV _ (L ++ [(9, 0, 0)]) F (by simpa using hI1) hra (by simp; omega)) ?_
  rintro s2 ⟨c, i', E, hc, hI2, ho2, hr2, hi', hd2⟩
  obtain ⟨eE, r32⟩ := hd2 (by simp; omega)
  subst eE
  simp only [List.map_nil, List.append_nil] at hI2
  refine Reach.step (live_of hI2 (by simp)) ?_
  obtain ⟨n2, c2, -, -⟩ := top_item hI2
  rw [st_t9 s2 _ n2 c2]
  obtain ⟨w1, w2, w3⟩ := r6set s2.r hI2.rl L.length.toUInt64
  have hq : bget (g15 s2.r 6 L.length.toUInt64) 8 = F.length.toUInt64 := by simp only [g15]; rw [w3 8 (by decide), hI2.r8]
  rw [hq]
  have hfl := hI2.fx.1
  have hF : F.length ≤ 65536 := Nat.le_trans hfl hI2.fl
  by_cases hbigF : 65535 < F.length.toUInt64
  · rw [if_pos hbigF]; exact Reach.error (g16_err _ w1)
  rw [if_neg hbigF]
  have hF' : F.length ≤ 65535 := by
    have : ¬ (65535 : UInt64).toNat < F.length.toUInt64.toNat := fun h => hbigF (UInt64.lt_iff_toNat_lt.mpr h)
    rw [u_toNat _ (by omega)] at this; simp at this; omega
  by_cases hbig : 2 ^ 32 ≤ (bpush s2.o 0).length
  · exact Reach.toobig hbig
  obtain ⟨fx3, fl3⟩ := fx_push s2.f F (bsize s2.o) hI2.fx hF' hI2.fl
  have hr8 := rset2 _ hI2.rl 6 8 L.length.toUInt64 (F.length.toUInt64 + 1) (by decide) (by decide)
  have hI3 := inv_mk2 hI2 (g15 (g15 s2.r 6 L.length.toUInt64) 8 (F.length.toUInt64 + 1)) s2.k (bpush s2.o 0)
    (g17 s2.f F.length.toUInt64 (bsize s2.o)) L (F ++ [bsize s2.o])
    (fun j a b c => by simp only [g15]; rw [hr8, if_neg (Ne.symm c), if_neg (Ne.symm b)])
    (len2 _ hI2.rl _ _ _ _) (by simp only [g15]; rw [hr8, if_neg (by decide), if_pos rfl])
    (stk_pop hI2.stk) hI2.kl (by omega) fx3 (by simp only [g15]; rw [hr8, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) fl3
    (by omega)
  have hl2 : s2.o.length = s.o.length + c.length := by rw [ho2]; simp
  refine Reach.done ⟨c ++ [0], i', [s.o.length + c.length], ?_, ?_, ?_, ?_, by omega, ?_⟩
  · exact .val h4 h5 h11 (by simpa using hc)
  · have : bsize s2.o = (s.o.length + c.length).toUInt64 := ulen _ _ hl2
    simp only [List.map_cons, List.map_nil]; rw [← this]; exact hI3
  · simp only; rw [bpush, ho2]; simp
  · simp only [g15]; rw [hr8, if_neg (by decide), if_neg (by decide), hr2]
  · simp only [g15]; rw [hr8, if_neg (by decide), if_neg (by decide), r32, hr31]


theorem st_t10 (s : GS) (n : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 10) :
    st s = ⟨s.x, if g14 (bsize (g26 256 (bget (g15 s.r 6 n) 1) 1 (bget (g15 s.r 6 n) 1 - 1) s.o)) (bget (g15 s.r 6 n) 3) == 1
        then g15 s.r 6 n else g16 (g15 s.r 6 n),
      bpush (g26 256 (bget (g15 s.r 6 n) 1) 1 (bget (g15 s.r 6 n) 1 - 1) s.o)
        (g13 0 (bsize (g26 256 (bget (g15 s.r 6 n) 1) 1 (bget (g15 s.r 6 n) 1 - 1) s.o)) (bget (g15 s.r 6 n) 3)),
      s.k, s.t, s.f⟩ := by
  unfold st; rw [g37_t10 _ _ _ _ _ _ hc, hn]

/-- CONTINUE (tail mode): the new state, stored into slots 1…p−1, then the jump to the loop head -/
theorem t_cont {K hd i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j) (ht : tg K.X i = 11) :
    TS K hd i := by
  intro s L F hL1 hI hr0 hr3 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  have hl6 : (bset s.r 6 L.length.toUInt64).length = 10 := by rw [BufL.length_bset]; exact hI.rl
  have h0 : bget (bset s.r 6 L.length.toUInt64) 0 = i.toUInt64 := by
    rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have h6 : bget (bset s.r 6 L.length.toUInt64) 6 = L.length.toUInt64 := by
    rw [rget _ hI.rl 6 6 _ (by decide), if_pos rfl]
  have hx : bget s.x i.toUInt64 = 11 := by rw [hI.x, tg_u _ _ (by omega), ht]
  rw [g36_tcont _ _ _ _ (by rw [h0]; exact hx), h0, h6]
  have hLl := hI.Ll; simp at hLl
  have q1 : L.length.toUInt64 + 1 = (L ++ [(10, 0, 0)]).length.toUInt64 := by simp [Nat.toUInt64, UInt64.ofNat_add]
  obtain ⟨sk0, kl0⟩ := stk_push_at s.k L _ 10 0 0 rfl (stk_pop hI.stk) hI.kl (by omega)
  obtain ⟨sk1, kl1⟩ := stk_push_at _ _ _ 1 0 0 q1 sk0 kl0 (by simp; omega)
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 1) (L.length.toUInt64 + 2) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 1)) 6 (L.length.toUInt64 + 2)) _ s.o
    (L ++ [(10, 0, 0), (1, 0, 0)])
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) (by simpa using sk1) kl1
    (by simp; omega) hI.ol
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 1)) 6 (L.length.toUInt64 + 2)) 0 = (i + 1).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  have hr31 : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 1)) 6 (L.length.toUInt64 + 2)) 3 = bget s.r 3 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
  refine Reach.bind (IH (i + 1) (by omega) _ (L ++ [(10, 0, 0)]) F (by simpa using hI1) hra (by simp; omega)) ?_
  rintro s2 ⟨c, i', E, hc, hI2, ho2, hr2, hi', hd2⟩
  obtain ⟨eE, r32⟩ := hd2 (by simp; omega)
  subst eE
  simp only [List.map_nil, List.append_nil] at hI2
  refine Reach.step (live_of hI2 (by simp)) ?_
  obtain ⟨n2, c2, -, -⟩ := top_item hI2
  rw [st_t10 s2 _ n2 c2]
  obtain ⟨w1, w2, w3⟩ := r6set s2.r hI2.rl L.length.toUInt64
  have hp : bget (g15 s2.r 6 L.length.toUInt64) 1 = K.p := by simp only [g15]; rw [w3 1 (by decide), hI2.r1]
  have hh : bget (g15 s2.r 6 L.length.toUInt64) 3 = hd.toUInt64 := by
    simp only [g15]; rw [w3 3 (by decide), r32, hr31, hr3]
  rw [hp, hh]
  have e := pi_g26 256 K.p 1 (K.p - 1) s2.o
  rw [e]
  have hl2 : s2.o.length = s.o.length + c.length := by rw [ho2]; simp
  have hb : bsize (s2.o ++ em (g26 256 K.p 1 (K.p - 1)) s2.o.length) =
      (s.o.length + c.length + (em (g26 256 K.p 1 (K.p - 1)) (s.o.length + c.length)).length).toUInt64 :=
    ulen _ _ (by simp [hl2])
  rw [hb]
  by_cases hg' : ¬ (g14 (s.o.length + c.length + (em (g26 256 K.p 1 (K.p - 1)) (s.o.length + c.length)).length).toUInt64
      hd.toUInt64 == 1) = true
  · rw [if_neg hg']; exact Reach.error (g16_err _ w1)
  rw [if_pos (Classical.not_not.mp hg')]
  by_cases hbig : 2 ^ 32 ≤ (bpush (s2.o ++ em (g26 256 K.p 1 (K.p - 1)) s2.o.length)
      (g13 0 (s.o.length + c.length + (em (g26 256 K.p 1 (K.p - 1)) (s.o.length + c.length)).length).toUInt64 hd.toUInt64)).length
  · exact Reach.toobig hbig
  have hI3 := inv_mk hI2 (g15 s2.r 6 L.length.toUInt64) s2.k (bpush (s2.o ++ em (g26 256 K.p 1 (K.p - 1)) s2.o.length)
      (g13 0 (s.o.length + c.length + (em (g26 256 K.p 1 (K.p - 1)) (s.o.length + c.length)).length).toUInt64 hd.toUInt64))
    L (fun j a b => w3 j b) w1 (by simp only [g15]; rw [w2])
    (stk_pop hI2.stk) hI2.kl (by omega) (by omega)
  refine Reach.done ⟨c ++ em (g26 256 K.p 1 (K.p - 1)) (s.o.length + c.length) ++
    [jw 0 (s.o.length + c.length + (em (g26 256 K.p 1 (K.p - 1)) (s.o.length + c.length)).length) hd], i', [], ?_, ?_, ?_, ?_,
    by omega, ?_⟩
  · exact .cont ht (by simpa using hc)
  · simpa using hI3
  · simp only; rw [bpush, hl2, ho2]; simp [jw]
  · simp only [g15]; rw [w3 0 (by decide), hr2]
  · simp only [g15]; rw [w3 3 (by decide), r32, hr31]


theorem g36_tif (x r o k : Buf) (hc : bget x (bget r 0) = 4) (hb : bget x (bget r 0 + 1) - 1 < 2) :
    g36 x r o k 1 = (g15 (g15 r 0 (bget r 0 + 2)) 6 (bget r 6 + 7),
      (o, g18 (g18 (g18 (g18 (g18 (g18 (g18 k (bget r 6) 5 0 0) (bget r 6 + 1) 1 1 0) (bget r 6 + 2) 4 0 0) (bget r 6 + 3) 1 1 0)
        (bget r 6 + 4) 3 (bget x (bget r 0 + 1)) 0) (bget r 6 + 5) 1 0 0) (bget r 6 + 6) 1 0 0)) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 4 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc, b, i, hb, g_1]
  have hz : (z == 0) = false := by simp [z, hc, g_1]
  rw [if_neg (by simp [ha]), if_pos (by decide), if_neg (by simp [hz]), if_neg (by simp [hc]), if_pos (by simp [hc])]

theorem t_if {K hd i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j)
    (IHT : ∀ j, i < j → TS K hd j) (ht : tg K.X i = 4) : TS K hd i := by
  intro s L F hL1 hI hr0 hhd hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  have hl6 : (bset s.r 6 L.length.toUInt64).length = 10 := by rw [BufL.length_bset]; exact hI.rl
  have h0 : bget (bset s.r 6 L.length.toUInt64) 0 = i.toUInt64 := by
    rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have h6 : bget (bset s.r 6 L.length.toUInt64) 6 = L.length.toUInt64 := by
    rw [rget _ hI.rl 6 6 _ (by decide), if_pos rfl]
  have hx : bget s.x i.toUInt64 = 4 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  by_cases hb' : ¬ tg K.X (i + 1) - 1 < 2
  · rw [g36_if_bad _ _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb')]
    exact Reach.error (g16_err _ hl6)
  have hb : tg K.X (i + 1) - 1 < 2 := Classical.not_not.mp hb'
  rw [g36_tif _ _ _ _ (by rw [h0]; exact hx) (by rw [h0, hv1]; exact hb), h0, h6, hv1]
  dsimp only
  have hLl := hI.Ll; simp at hLl
  obtain ⟨sk1, kl1⟩ := stk_push7 s.k L (5, 0, 0) (1, 1, 0) (4, 0, 0) (1, 1, 0) (3, (tg K.X (i + 1)), 0) (1, 0, 0) (1, 0, 0)
    (stk_pop hI.stk) hI.kl (by omega)
  simp only at sk1 kl1
  have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 2) (L.length.toUInt64 + 7) (by decide) (by decide)
  have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 7)) _ s.o
    (L ++ [(5, 0, 0), (1, 1, 0), (4, 0, 0), (1, 1, 0), (3, (tg K.X (i + 1)), 0), (1, 0, 0), (1, 0, 0)])
    (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
    (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) sk1 kl1
    (by simp; omega) hI.ol
  have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 7)) 0 = (i + 2).toUInt64 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
  have hr3_1 : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 2)) 6 (L.length.toUInt64 + 7)) 3 = bget s.r 3 := by
    simp only [g15]; rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
  -- operand a
  refine Reach.bind (IH (i + 2) (by omega) _ (L ++ [(5, 0, 0), (1, 1, 0), (4, 0, 0), (1, 1, 0), (3, (tg K.X (i + 1)), 0), (1, 0, 0)]) F
    (by simpa using hI1) hra (by simp; omega)) ?_
  rintro s2 ⟨ca, i1, Ea, hca, hI2, ho2, hr2, hi1, hd2⟩
  obtain ⟨ea, r3a⟩ := hd2 (by simp)
  subst ea
  -- operand b
  refine Reach.bind (IH i1 (by omega) s2 (L ++ [(5, 0, 0), (1, 1, 0), (4, 0, 0), (1, 1, 0), (3, (tg K.X (i + 1)), 0)]) F
    (by simpa using hI2) hr2 (by simp; omega)) ?_
  rintro s3 ⟨cb, i2, Eb, hcb, hI3, ho3, hr3, hi2, hd3⟩
  obtain ⟨eb, r3b⟩ := hd3 (by simp)
  subst eb
  simp only [List.map_nil, List.append_nil] at hI3
  -- compare item
  have hI3' : Inv K s3 ((L ++ [(5, 0, 0), (1, 1, 0), (4, 0, 0), (1, 1, 0)]) ++ [(3, (tg K.X (i + 1)), 0)]) F := by simpa using hI3
  refine Reach.step (live_of hI3' (by simp)) ?_
  obtain ⟨n3, c3, a3, -⟩ := top_item hI3'
  simp only [List.length_append, List.length_cons, List.length_nil] at n3
  have hidx : ((L.length + 4).toUInt64 - 2) * 3 + 1 = (3 * (L.length + 2) + 1).toUInt64 := by
    apply UInt64.toNat.inj; simp [Nat.toUInt64, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_add]; omega
  have hst : st s3 = ⟨s3.x, g15 s3.r 6 (L.length + 4).toUInt64, bpush (bpush (g30 s3.o 16)
      (if (tg K.X (i + 1)) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0,
      bset s3.k ((3 * (L.length + 2) + 1).toUInt64) (bsize s3.o + 4), s3.t, s3.f⟩ := by
    unfold st; rw [g37_t3 _ _ _ _ _ _ c3, a3, n3, hidx]
  rw [hst]
  have ho3' : s3.o = s.o ++ ca ++ cb := by rw [ho3, ho2]
  by_cases hbig : 2 ^ 32 ≤ (bpush (bpush (g30 s3.o 16) (if (tg K.X (i + 1)) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0).length
  · exact Reach.toobig hbig
  obtain ⟨q1, q2, q3⟩ := r6set s3.r hI3.rl (L.length + 4).toUInt64
  have sk4 : Stk (bset s3.k ((3 * (L.length + 2) + 1).toUInt64) (bsize s3.o + 4))
      (L ++ [(5, 0, 0), (1, 1, 0), (4, bsize s3.o + 4, 0), (1, 1, 0)]) := by
    have hp := stk_pop hI3'.stk
    have := stk_set hp (L.length + 2) (4, 0, 0) (by simp) (bsize s3.o + 4)
    simp only [bset]
    rw [u_toNat _ (by omega)]
    have e : (L ++ [(5, 0, 0), (1, 1, 0), (4, 0, 0), (1, 1, 0)]).set (L.length + 2) ((4 : UInt64), bsize s3.o + 4, (0 : UInt64)) =
        L ++ [(5, 0, 0), (1, 1, 0), (4, bsize s3.o + 4, 0), (1, 1, 0)] := by
      rw [List.set_append_right _ _ (by omega)]; simp
    rw [← e]; simpa using this
  have hI4 := inv_mk hI3' (g15 s3.r 6 (L.length + 4).toUInt64) (bset s3.k ((3 * (L.length + 2) + 1).toUInt64) (bsize s3.o + 4))
    (bpush (bpush (g30 s3.o 16) (if (tg K.X (i + 1)) == 1 then g4 0 5 6 8 else g4 6 5 6 8)) 0)
    (L ++ [(5, 0, 0), (1, 1, 0), (4, bsize s3.o + 4, 0), (1, 1, 0)])
    (fun j a b => q3 j b) q1 (by simp only [g15]; rw [q2]; simp) sk4 (by rw [BufL.length_bset]; exact hI3.kl) (by simp; omega) (by omega)
  have hr4 : bget (g15 s3.r 6 (L.length + 4).toUInt64) 0 = i2.toUInt64 := by simp only [g15]; rw [q3 0 (by decide), hr3]
  -- then branch
  refine Reach.bind (IHT i2 (by omega) _ (L ++ [(5, 0, 0), (1, 1, 0), (4, bsize s3.o + 4, 0)]) F (by simp)
    (by simpa using hI4) hr4 (by simp only [g15]; rw [q3 3 (by decide), r3b, r3a, hr3_1, hhd]) (by simp; omega)) ?_
  rintro s5 ⟨ct, i3, Et, hct, hI5, ho5, hr5, hi3, r3t⟩
  -- item 4: patch the compare's jump to here + 1, leave the end placeholder
  have hI5' : Inv K s5 ((L ++ [(5, 0, 0), (1, 1, 0)]) ++ [(4, bsize s3.o + 4, 0)]) (F ++ Et.map Nat.toUInt64) := by simpa using hI5
  refine Reach.step (live_of hI5' (by simp)) ?_
  obtain ⟨n5, c5, a5, -⟩ := top_item hI5'
  simp only [List.length_append, List.length_cons, List.length_nil] at n5
  have hidx5 : ((L.length + 2).toUInt64 - 2) * 3 + 1 = (3 * L.length + 1).toUInt64 := by
    apply UInt64.toNat.inj; simp [Nat.toUInt64, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_add]; omega
  have hst5 : st s5 = ⟨s5.x, if g14 (bsize s3.o + 4) (bsize (bpush s5.o 0)) == 1 then g15 s5.r 6 (L.length + 2).toUInt64
      else g16 (g15 s5.r 6 (L.length + 2).toUInt64),
      bset (bpush s5.o 0) (bsize s3.o + 4) (g13 0 (bsize s3.o + 4) (bsize (bpush s5.o 0))),
      bset s5.k (3 * L.length + 1).toUInt64 (bsize s5.o), s5.t, s5.f⟩ := by
    rw [st_t4 s5 _ _ n5 c5 a5, hidx5]
  rw [hst5]
  obtain ⟨p1, p2, p3⟩ := r6set s5.r hI5.rl (L.length + 2).toUInt64
  by_cases hg' : ¬ (g14 (bsize s3.o + 4) (bsize (bpush s5.o 0)) == 1) = true
  · rw [if_neg hg']; exact Reach.error (g16_err _ p1)
  rw [if_pos (Classical.not_not.mp hg')]
  -- the code so far
  have hA : s5.o = (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++ 0 :: ct := by
    rw [ho5, ho3']; simp [g30_eq, bpush, ifHd, List.append_assoc]
  have hl3 : s3.o.length = s.o.length + ca.length + cb.length := by rw [ho3']; simp [Nat.add_assoc]
  have hol3 := hI3.ol
  have hpj : bsize s3.o + 4 = (s.o.length + ca.length + cb.length + 4).toUInt64 := by
    rw [ulen _ _ hl3]; simp [Nat.toUInt64, UInt64.ofNat_add]
  have hP : (bsize s3.o + 4).toNat = (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))).length := by
    rw [hpj, u_toNat _ (by omega)]; simp [ifHd]; omega
  have ho6 : bset (bpush s5.o 0) (bsize s3.o + 4) (g13 0 (bsize s3.o + 4) (bsize (bpush s5.o 0))) =
      (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0]) := by
    have hl5 : (bpush s5.o 0).length = s.o.length + ca.length + cb.length + 5 + ct.length + 1 := by
      rw [bpush, hA]; simp [ifHd]; omega
    rw [ulen _ _ hl5, show bpush s5.o 0 = (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++ 0 :: (ct ++ [0]) by rw [bpush, hA]; simp,
      bset_mid _ _ _ _ _ hP, jw, ← hpj]
  rw [ho6]
  by_cases hbig6 : 2 ^ 32 ≤ ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0])).length
  · exact Reach.toobig hbig6
  have sk6 : Stk (bset s5.k (3 * L.length + 1).toUInt64 (bsize s5.o)) (L ++ [(5, bsize s5.o, 0), (1, 1, 0)]) := by
    have hp := stk_pop hI5'.stk
    have := stk_set hp L.length (5, 0, 0) (by simp) (bsize s5.o)
    simp only [bset]
    rw [u_toNat _ (by omega)]
    have e : (L ++ [(5, 0, 0), (1, 1, 0)]).set L.length ((5 : UInt64), bsize s5.o, (0 : UInt64)) =
        L ++ [(5, bsize s5.o, 0), (1, 1, 0)] := by
      rw [List.set_append_right _ _ (by omega)]; simp
    rw [← e]; simpa using this
  have hI6 := inv_mk hI5' (g15 s5.r 6 (L.length + 2).toUInt64) (bset s5.k (3 * L.length + 1).toUInt64 (bsize s5.o))
    ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0]))
    (L ++ [(5, bsize s5.o, 0), (1, 1, 0)]) (fun j a b => p3 j b) p1 (by simp only [g15]; rw [p2]; simp) sk6
    (by rw [BufL.length_bset]; exact hI5.kl) (by simp; omega) (by omega)
  have hr6 : bget (g15 s5.r 6 (L.length + 2).toUInt64) 0 = i3.toUInt64 := by simp only [g15]; rw [p3 0 (by decide), hr5]
  -- else branch
  refine Reach.bind (IHT i3 (by omega) _ (L ++ [(5, bsize s5.o, 0)]) (F ++ Et.map Nat.toUInt64) (by simp) (by simpa using hI6) hr6
    (by simp only [g15]; rw [p3 3 (by decide), r3t]; simp only [g15]; rw [q3 3 (by decide), r3b, r3a, hr3_1, hhd])
    (by simp; omega)) ?_
  rintro s7 ⟨ce, i4, Ee, hce, hI7, ho7, hr7, hi4, r3e⟩
  -- item 5: patch the end placeholder
  have hI7' : Inv K s7 (L ++ [(5, bsize s5.o, 0)]) (F ++ Et.map Nat.toUInt64 ++ Ee.map Nat.toUInt64) := hI7
  refine Reach.step (live_of hI7' (by simp)) ?_
  obtain ⟨n7, c7, a7, -⟩ := top_item hI7'
  have hst7 : st s7 = ⟨s7.x, if g14 (bsize s5.o) (bsize s7.o) == 1 then g15 s7.r 6 L.length.toUInt64
      else g16 (g15 s7.r 6 L.length.toUInt64), bset s7.o (bsize s5.o) (g13 0 (bsize s5.o) (bsize s7.o)), s7.k, s7.t, s7.f⟩ := by
    rw [st_t5 s7 _ _ n7 c7 a7]
  rw [hst7]
  obtain ⟨w1, w2, w3⟩ := r6set s7.r hI7.rl L.length.toUInt64
  by_cases hg7 : ¬ (g14 (bsize s5.o) (bsize s7.o) == 1) = true
  · rw [if_neg hg7]; exact Reach.error (g16_err _ w1)
  rw [if_pos (Classical.not_not.mp hg7)]
  have e1 : bsize s5.o = (s.o.length + ca.length + cb.length + 5 + ct.length).toUInt64 :=
    ulen _ _ (by rw [hA]; simp [ifHd]; omega)
  have e2 : bsize s7.o = (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length).toUInt64 :=
    ulen _ _ (by rw [ho7]; simp [ifHd]; omega)
  have hQ : (s.o.length + ca.length + cb.length + 5 + ct.length).toUInt64.toNat = ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: ct).length := by
    have hl : s5.o.length < 2 ^ 32 := hI5.ol
    have : s5.o.length = s.o.length + ca.length + cb.length + 5 + ct.length := by rw [hA]; simp [ifHd]; omega
    rw [u_toNat _ (by omega)]; simp [ifHd]; omega
  have ho8 : bset s7.o (bsize s5.o) (g13 0 (bsize s5.o) (bsize s7.o)) = s.o ++ (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
      [jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (s.o.length + ca.length + cb.length + 5 + ct.length)
        (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce) := by
    rw [e1, e2, ho7, show ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0])) ++ ce =
        ((s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1))) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: ct) ++ 0 :: ce by simp]
    rw [bset_mid _ _ _ _ _ hQ]
    simp only [jw, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
  rw [ho8]
  by_cases hbig8 : 2 ^ 32 ≤ (s.o ++ (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
      [jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (s.o.length + ca.length + cb.length + 5 + ct.length)
        (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce)).length
  · exact Reach.toobig hbig8
  have hI8 := inv_mk hI7' (g15 s7.r 6 L.length.toUInt64) s7.k
    (s.o ++ (ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
      [jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1)] ++ ct ++
      [jw 0 (s.o.length + ca.length + cb.length + 5 + ct.length)
        (s.o.length + ca.length + cb.length + 5 + ct.length + 1 + ce.length)] ++ ce)) L (fun j a b => w3 j b) w1
    (by simp only [g15]; rw [w2]) (stk_pop hI7'.stk) hI7.kl (by omega) (by omega)
  refine Reach.done ⟨_, i4, [] ++ [] ++ Et ++ Ee, ?_, ?_, rfl, ?_, by omega, ?_⟩
  · have hca' : CG K (L.length + 6) (i + 2) s.o.length ca i1 [] := by simpa using hca
    have hcb' : CG K (L.length + 5) i1 (s.o.length + ca.length) cb i2 [] := by
      have : s2.o.length = s.o.length + ca.length := by rw [ho2]; simp
      simpa [this] using hcb
    have hct' : CT K hd (L.length + 3) i2 (s.o.length + ca.length + cb.length + 5) ct i3 Et := by
      have : (bpush (bpush (g30 s3.o 16) (if (tg K.X (i + 1) == 1) = true then g4 0 5 6 8 else g4 6 5 6 8)) 0).length =
          s.o.length + ca.length + cb.length + 5 := by rw [g30_eq, ho3']; simp [bpush]; omega
      simp only at hct; rw [this] at hct; simpa using hct
    have hce' : CT K hd (L.length + 1) i3 (s.o.length + ca.length + cb.length + 5 + ct.length + 1) ce i4 Ee := by
      have : (s.o ++ ca ++ cb ++ ifHd (tg K.X (i + 1)) ++
        jw 0 (s.o.length + ca.length + cb.length + 4) (s.o.length + ca.length + cb.length + 5 + ct.length + 1) :: (ct ++ [0])).length =
          s.o.length + ca.length + cb.length + 5 + ct.length + 1 := by simp [ifHd]; omega
      simp only at hce; rw [this] at hce; simpa using hce
    exact .ite ht hb hca' hcb' hct' hce'
  · simpa using hI8
  · simp only [g15]; rw [w3 0 (by decide), hr7]
  · simp only [g15]
    rw [w3 3 (by decide), r3e]; simp only [g15]
    rw [p3 3 (by decide), r3t]; simp only [g15]
    rw [q3 3 (by decide), r3b, r3a, hr3_1]


theorem g36_tlet (x r o k : Buf) (hc : bget x (bget r 0) = 5) :
    g36 x r o k 1 = (if g43 r (bget x (bget r 0 + 1)) (bget x (bget r 0 + 2)) == 1 then (g16 r, (o, k)) else
      (g15 (g15 r 0 (bget r 0 + 3)) 6 (bget r 6 + 3), (o, g18 (g18 (g18 k (bget r 6) 1 1 0) (bget r 6 + 1) 6
        (bget x (bget r 0 + 1)) (bget x (bget r 0 + 2))) (bget r 6 + 2) 1 0 0))) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 5 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc, g_1]
  have hz : (z == 0) = false := by simp [z, hc, g_1]
  rw [if_neg (by simp [ha]), if_pos (by decide), if_neg (by simp [hz]), if_neg (by simp [hc]), if_neg (by simp [hc])]

theorem t_let {K hd i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length) (IH : ∀ j, i < j → VS K j)
    (IHT : ∀ j, i < j → TS K hd j) (ht : tg K.X i = 5) : TS K hd i := by
  intro s L F hL1 hI hr0 hhd hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  have hl6 : (bset s.r 6 L.length.toUInt64).length = 10 := by rw [BufL.length_bset]; exact hI.rl
  have h0 : bget (bset s.r 6 L.length.toUInt64) 0 = i.toUInt64 := by
    rw [rget _ hI.rl 6 0 _ (by decide), if_neg (by decide), hr0]
  have h6 : bget (bset s.r 6 L.length.toUInt64) 6 = L.length.toUInt64 := by
    rw [rget _ hI.rl 6 6 _ (by decide), if_pos rfl]
  have h7 : bget (bset s.r 6 L.length.toUInt64) 7 = K.ns := by
    rw [rget _ hI.rl 6 7 _ (by decide), if_neg (by decide), hI.r7]
  have hx : bget s.x i.toUInt64 = 5 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  have hv2 : bget s.x (i.toUInt64 + 2) = tg K.X (i + 2) := by rw [hI.x]; exact tg_u1 _ i 2 (by omega)
  rw [g36_tlet _ _ _ _ (by rw [h0]; exact hx), h0, h6, hv1, hv2, g43_ok _ _ _ _ h7]
  by_cases hs : SlotOk K (tg K.X (i + 1)) (tg K.X (i + 2))
  · have hs' : tg K.X (i + 2) ≠ 0 ∧ tg K.X (i + 1) < 251 ∧ tg K.X (i + 2) < 251 ∧ ¬K.ns < tg K.X (i + 1) + tg K.X (i + 2) := hs
    rw [if_pos hs']
    simp only [show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false]
    have hLl := hI.Ll; simp at hLl
    have hsk := stk_pop hI.stk
    obtain ⟨sk1, kl1⟩ := stk_push3 s.k L (1, 1, 0) (6, tg K.X (i + 1), tg K.X (i + 2)) (1, 0, 0) hsk hI.kl (by omega)
    simp only at sk1 kl1
    have hr1 := rset2 _ hl6 0 6 (i.toUInt64 + 3) (L.length.toUInt64 + 3) (by decide) (by decide)
    have hI1 := inv_mk hI (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 3)) 6 (L.length.toUInt64 + 3)) _ s.o
      (L ++ [(1, 1, 0), (6, tg K.X (i + 1), tg K.X (i + 2)), (1, 0, 0)])
      (fun j a b => by simp only [g15]; rw [hr1, if_neg (Ne.symm b), if_neg (Ne.symm a), rget _ hI.rl 6 j _ (by decide), if_neg (Ne.symm b)])
      (len2 _ hl6 _ _ _ _) (by simp only [g15]; rw [hr1, if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]) sk1 kl1
      (by simp; omega) hI.ol
    have hra : bget (g15 (g15 (bset s.r 6 L.length.toUInt64) 0 (i.toUInt64 + 3)) 6 (L.length.toUInt64 + 3)) 0 = (i + 3).toUInt64 := by
      simp only [g15]; rw [hr1, if_neg (by decide), if_pos rfl]; simp [Nat.toUInt64, UInt64.ofNat_add]
    refine Reach.bind (IH (i + 3) (by omega) _ (L ++ [(1, 1, 0), (6, tg K.X (i + 1), tg K.X (i + 2))]) F (by simpa using hI1) hra
      (by simp; omega)) ?_
    rintro s2 ⟨cv, i1, Ev, hcv, hI2, ho2, hr2, hi1, hd2⟩
    -- the slot-pop item
    have hI2' : Inv K s2 ((L ++ [(1, 1, 0)]) ++ [(6, tg K.X (i + 1), tg K.X (i + 2))]) (F ++ Ev.map Nat.toUInt64) := by simpa using hI2
    refine Reach.step (live_of hI2' (by simp)) ?_
    obtain ⟨n2, c2, a2, b2⟩ := top_item hI2'
    have hp2 : bget (g15 s2.r 6 (L ++ [(1, 1, 0)]).length.toUInt64) 1 = K.p := by
      simp only [g15]; rw [rget _ hI2.rl 6 1 _ (by decide), if_neg (by decide), hI2.r1]
    have hst : st s2 = ⟨s2.x, g15 s2.r 6 (L ++ [(1, 1, 0)]).length.toUInt64,
        g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) s2.o, s2.k, s2.t, s2.f⟩ := by
      unfold st; rw [g37_t6 _ _ _ _ _ _ c2, a2, b2, n2, hp2]
    rw [hst]
    have e := pi_g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2)) s2.o
    rw [e]
    by_cases hbig : 2 ^ 32 ≤ (s2.o ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s2.o.length).length
    · exact Reach.toobig hbig
    have hI3 := inv_mk hI2' (g15 s2.r 6 (L ++ [(1, 1, 0)]).length.toUInt64) s2.k
      (s2.o ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) s2.o.length) (L ++ [(1, 1, 0)])
      (fun j a b => by simp only [g15]; rw [rget _ hI2.rl 6 j _ (by decide), if_neg (Ne.symm b)])
      (by simp only [g15]; rw [BufL.length_bset]; exact hI2.rl)
      (by simp only [g15]; rw [rget _ hI2.rl 6 6 _ (by decide), if_pos rfl]) (stk_pop hI2'.stk) hI2.kl (by simp; omega) (by omega)
    have hr3 : bget (g15 s2.r 6 (L ++ [(1, 1, 0)]).length.toUInt64) 0 = i1.toUInt64 := by
      simp only [g15]; rw [rget _ hI2.rl 6 0 _ (by decide), if_neg (by decide), hr2]
    obtain ⟨ev, r3a⟩ := hd2 (by simp)
    refine Reach.bind (IHT i1 (by omega) _ L (F ++ Ev.map Nat.toUInt64) hL1 hI3 hr3 (by
      simp only [g15]; rw [rget _ hI2.rl 6 3 _ (by decide), if_neg (by decide), r3a]
      simp only [g15]
      rw [rset2 _ hl6 0 6 _ _ (by decide) (by decide), if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide),
        if_neg (by decide), hhd]) (by omega)) ?_
    rintro s4 ⟨cb, i2, Eb, hcb, hI4, ho4, hr4, hi2, r3b⟩
    have hem : s2.o.length = s.o.length + cv.length := by rw [ho2]; simp
    refine Reach.done ⟨cv ++ em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (s.o.length + cv.length) ++ cb, i2, Ev ++ Eb,
      ?_, ?_, ?_, hr4, by omega, ?_⟩
    · have hcv' : CG K (L.length + 2) (i + 3) s.o.length cv i1 Ev := by simpa using hcv
      have hcb' : CT K hd L.length i1 (s.o.length + cv.length +
          (em (g26 256 K.p (tg K.X (i + 1)) (tg K.X (i + 2))) (s.o.length + cv.length)).length) cb i2 Eb := by
        simpa [hem, Nat.add_assoc] using hcb
      exact .lett ht hs hcv' hcb'
    · rw [List.map_append, ← List.append_assoc]; exact hI4
    · rw [ho4, ho2]; simp [hem, List.append_assoc]
    · rw [r3b]; simp only [g15]; rw [rget _ hI2.rl 6 3 _ (by decide), if_neg (by decide), r3a]
      simp only [g15]
      rw [rset2 _ hl6 0 6 _ _ (by decide) (by decide), if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
  · have hs' : ¬ (tg K.X (i + 2) ≠ 0 ∧ tg K.X (i + 1) < 251 ∧ tg K.X (i + 2) < 251 ∧ ¬K.ns < tg K.X (i + 1) + tg K.X (i + 2)) := hs
    rw [if_neg hs']
    simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]
    exact Reach.error (g16_err _ hl6)



end GenRef
