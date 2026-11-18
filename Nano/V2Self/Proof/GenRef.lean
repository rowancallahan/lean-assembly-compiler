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

/-- `it m s` = m work items from s -/
def it : Nat → GS → GS
  | 0, s => s
  | n + 1, s => it n (st s)

theorem it_add : ∀ (n m : Nat) (s : GS), it (n + m) s = it n (it m s)
  | n, 0, s => rfl
  | n, m + 1, s => by rw [show n + (m + 1) = (n + m) + 1 by omega]; simp only [it]; exact it_add n m (st s)

def Reach (s : GS) (P : GS → Prop) : Prop :=
  ∃ m, (∀ j < m, live (it j s)) ∧ (P (it m s) ∨ err (it m s))

theorem Reach.done {s : GS} {P : GS → Prop} (h : P s) : Reach s P := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inl h⟩

theorem Reach.error {s : GS} {P : GS → Prop} (h : err s) : Reach s P := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inr h⟩

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

end GenRef
