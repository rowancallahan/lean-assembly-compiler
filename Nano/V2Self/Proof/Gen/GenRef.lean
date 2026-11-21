/- The g39 work-item invariant (Astra-11, Gen soundness on success) for today's RISC-V Gen.
Layout since the emitter factoring: GenBase.lean = the source-independent part (state, item stack, fixups, `Inv`);
GenE.lean = the invariant proved once for any Gen source `Src` and encoders `Em`; this file = the concrete side:
Gen's step `st` / `Reach`, the reference relation `CG` / `CT` / `CGs` over Gen's own words, the unfolding lemmas of
g36 / g37 (`g36_*`, `g37_t*`: the `SrcOK` instance) and of the emitters (`pi_*`, `*_len`: the `EmOK` instance),
`visit_all` as the RISC-V instance of `GenEmit.visit_all`, then the fuelled main loop g39 and the def level. -/
import Nano.V2Self.Proof.Gen.GenE
namespace GenRef
open C CallProbe

/- The g39 work-item invariant (Astra-11, Gen soundness on success), part 1: the state, the step, `Reach`, the item

stack and the fixup list as abstract lists.  Gen's main loop `g39` runs `g37` (one work item) while the stop flags are

clear and items are pending; `Reach s P` = after finitely many items, with every intermediate state live, P holds or

the error flag is set (then g39 returns at once and g42 outputs []).  Items are triples (tag, a, b) stored at

k[3j..3j+2]; stale words above the count are ignored (`Stk`).  Fixups likewise (`Fx`, count = r[8]). -/

/-- one work item (g39's `bget r 6 ≠ 0` branch) -/
def st (s : GS) : GS :=
  match g37 s.x s.r s.o s.k s.t s.f with
  | (r1, (o1, (k1, f1))) => ⟨s.x, r1, o1, k1, s.t, f1⟩

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

/-! ## the item stack and the fixup list -/

theorem pi_g21 : PI g21 := by intro o; simp [em, g21, bpush, bsize]

theorem pi_g22 (d) : PI (fun o => g22 o d) := by intro o; simp [em, g22, bpush, bsize]

theorem pi_g23 (d v) : PI (fun o => g23 o d v) := by intro o; unfold g23; split <;> simp [em, bpush]

theorem pi_g31 (p) : PI (fun o => g31 o p) := by intro o; simp [em, g31, g30, bpush]

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

/-! ## the reference: what Gen emits for a node, as a big-step relation over code words

`CG K d i h c i' E`: the node at AST word i, visited in value mode with d items below its visit item, emits the words c

starting at code word h, ends at AST word i', and records the exit placeholders E (absolute word indices, in f order).

`CT K hd …`: the same in tail mode (a loop arm; hd = the loop head).  `CGs K d i h n …`: n consecutive value nodes

(PAIR / CALL / PRIM operands), the first visited at depth d + n − 1.  Jumps are final (patched) words; exit

placeholders stay 0 until ENDDEF. -/

/-- `jal rd` from word a to word b -/
def jw (rd : UInt64) (a b : Nat) : UInt64 := g13 rd a.toUInt64 b.toUInt64

/-- IF's compare + branch -/
def ifHd (cmp : UInt64) : List UInt64 := [g11 6 31 0, g11 5 31 8, g10 31 31 16, if cmp == 1 then g4 0 5 6 8 else g4 6 5 6 8]

/-- LOOP's head: t0 := fuel; beq t0, x0, +8; (placeholder → the step arm) -/
def lpHd (p : UInt64) : List UInt64 := [g11 5 8 (g24 p 0), g4 0 5 0 8]

/-- LOOP's decrement (item 11) -/
def lpDec (p : UInt64) : List UInt64 := [g10 5 5 g_901, g12 5 8 (g24 p 0)]

/-- Gen's range check on a jump from word a to word b passed -/
def JOk (a b : Nat) : Prop := g14 a.toUInt64 b.toUInt64 = 1

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
      JOk (h + ca.length + cb.length + 4) (h + ca.length + cb.length + 5 + ct.length + 1) →
      JOk (h + ca.length + cb.length + 5 + ct.length) (h + ca.length + cb.length + 5 + ct.length + 1 + ce.length) →
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
      g14 (h + c.length).toUInt64 (bget K.T (tg K.X (i + 1))) = 1 →
      CG K d i h (c ++ [g13 1 (h + c.length).toUInt64 (bget K.T (tg K.X (i + 1)))]) i' E
  | prim {d i h c i' E} : tg K.X i = 9 → tg K.X (i + 1) - 1 < 9 →
      CGs K (d + 1) (i + 2) h (g33 (tg K.X (i + 1))).toNat c i' E →
      CG K d i h (c ++ em (fun o => g32 o (tg K.X (i + 1)) K.u) (h + c.length)) i' E
  | loop {i h cz cs i1 i2 Ez Es} : tg K.X i = 10 →
      CT K h 3 (i + 1) (h + 3) cz i1 Ez →
      CT K h 1 i1 (h + 3 + cz.length + 2) cs i2 Es →
      JOk (h + 2) (h + 3 + cz.length) →
      CG K 1 i h (lpHd K.p ++ [jw 0 (h + 2) (h + 3 + cz.length)] ++ cz ++ lpDec K.p ++ cs) i2 (Ez ++ Es)
inductive CT (K : Cx) : Nat → Nat → Nat → Nat → List UInt64 → Nat → List Nat → Prop
  /-- a value node in tail position: value, then an exit placeholder -/
  | val {hd d i h c i' E} : tg K.X i ≠ 4 → tg K.X i ≠ 5 → tg K.X i ≠ 11 →
      CG K (d + 1) i h c i' E → CT K hd d i h (c ++ [0]) i' (E ++ [h + c.length])
  | cont {hd d i h c i'} : tg K.X i = 11 →
      CG K (d + 1) (i + 1) h c i' [] →
      JOk (h + c.length + (em (g26 256 K.p 1 (K.p - 1)) (h + c.length)).length) hd →
      CT K hd d i h (c ++ em (g26 256 K.p 1 (K.p - 1)) (h + c.length) ++
        [jw 0 (h + c.length + (em (g26 256 K.p 1 (K.p - 1)) (h + c.length)).length) hd]) i' []
  | ite {hd d i h ca cb ct ce i1 i2 i3 i4 Ea Eb Et Ee} : tg K.X i = 4 → tg K.X (i + 1) - 1 < 2 →
      CG K (d + 6) (i + 2) h ca i1 Ea → CG K (d + 5) i1 (h + ca.length) cb i2 Eb →
      CT K hd (d + 3) i2 (h + ca.length + cb.length + 5) ct i3 Et →
      CT K hd (d + 1) i3 (h + ca.length + cb.length + 5 + ct.length + 1) ce i4 Ee →
      JOk (h + ca.length + cb.length + 4) (h + ca.length + cb.length + 5 + ct.length + 1) →
      JOk (h + ca.length + cb.length + 5 + ct.length) (h + ca.length + cb.length + 5 + ct.length + 1 + ce.length) →
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
    bget s'.r 0 = i'.toUInt64 ∧ (i < i' ∧ i' ≤ K.X.length + 3) ∧ (2 ≤ d → E = [] ∧ bget s'.r 3 = bget s0.r 3)

theorem g36_const (x r o k : Buf) (hc : bget x (bget r 0) = 1) :
    g36 x r o k 0 = (g15 r 0 (bget r 0 + 2), (g21 (g23 o 5 (bget x (bget r 0 + 1))), k)) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 1 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc, g_1]
  rw [if_neg (by simp [ha]), if_neg (by decide), if_pos (by simp [hc])]

theorem pi_const (v : UInt64) : PI (fun o => g21 (g23 o 5 v)) := pi_comp (pi_g23 5 v) pi_g21

/-! emitter length bounds (for the `big` outcome: code stays below 2^62 words) -/

theorem g23_len (o : Buf) (d v : UInt64) : (g23 o d v).length ≤ o.length + 17 := by
  unfold g23; split <;> simp [bpush]

theorem g21_len (o : Buf) : (g21 o).length = o.length + 4 := by simp [g21, bpush]

theorem g25_len : ∀ (n : Nat) (p s w : UInt64) (o : Buf), (g25 n p s w o).length ≤ o.length + 5 * n
  | 0, p, s, w, o => by simp [g25]
  | n + 1, p, s, w, o => by
    unfold g25; split
    · omega
    · show (g25 n p (s + 1) (w - 1) (g21 (bpush o (g11 5 8 (g24 p s))))).length ≤ _
      have := g25_len n p (s + 1) (w - 1) (g21 (bpush o (g11 5 8 (g24 p s)))); rw [g21_len] at this; simp only [bpush] at this ⊢; simp at this; omega

theorem g26_len : ∀ (n : Nat) (p s w : UInt64) (o : Buf), (g26 n p s w o).length ≤ o.length + 3 * n
  | 0, p, s, w, o => by simp [g26]
  | n + 1, p, s, w, o => by
    unfold g26; split
    · omega
    · show (g26 n p s (w - 1) (bpush (bpush (bpush o (g11 5 31 0)) (g10 31 31 8)) (g12 5 8 (g24 p (s + w - 1))))).length ≤ _
      have := g26_len n p s (w - 1) (bpush (bpush (bpush o (g11 5 31 0)) (g10 31 31 8)) (g12 5 8 (g24 p (s + w - 1))))
      have hql : (bpush (bpush (bpush o (g11 5 31 0)) (g10 31 31 8)) (g12 5 8 (g24 p (s + w - 1)))).length = o.length + 3 := by
        simp [bpush]
      omega

theorem g32_len (o : Buf) (p u : UInt64) : (g32 o p u).length ≤ o.length + 64 := by
  have e := pi_g32 p u o
  simp only at e
  have : (em (fun o => g32 o p u) o.length).length ≤ 64 := by
    unfold em
    by_cases h1 : p = 1; · subst h1; simp [g32, g22, bpush]
    by_cases h3 : p = 3; · subst h3; simp [g32, g22, bpush]
    by_cases h2 : p = 2; · subst h2; simp [g32, bpush]
    by_cases h5 : p = 5
    · subst h5
      have a1 := g23_len (bpush (List.replicate o.length 0) (g10 5 30 0)) 6 ((u + 2) <<< 3)
      have a2 := g23_len (bpush (bpush (bpush (g23 (bpush (List.replicate o.length 0) (g10 5 30 0)) 6 ((u + 2) <<< 3))
        (g1 0 0 6 6 30)) (g4 7 31 6 8)) (g13 0 (bsize (g23 (bpush (List.replicate o.length 0) (g10 5 30 0)) 6 ((u + 2) <<< 3)) + 2) 1)) 7 u
      simp only [g32, if_neg (show ¬ ((5 : UInt64) == 1) = true by decide), if_neg (show ¬ ((5 : UInt64) == 3) = true by decide),
        if_neg (show ¬ ((5 : UInt64) == 2) = true by decide), if_pos (show ((5 : UInt64) == 5) = true by decide), List.length_drop,
        g21_len]
      simp [bpush] at a1 a2 ⊢; omega
    by_cases h6 : p = 6; · subst h6; simp [g32, bpush]
    by_cases h7 : p = 7; · subst h7; simp [g32, g30, bpush]
    by_cases h8 : p = 8; · subst h8; simp [g32, bpush]
    simp [g32, g30, bpush, bsize, h1, h2, h3, h5, h6, h7, h8]
  rw [e]; simp; omega

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

/-- value visit at AST word i (the induction statement) -/
def VS (K : Cx) (i : Nat) : Prop := i ≤ K.X.length + 3 → ∀ s L F, Inv K s (L ++ [(1, 0, 0)]) F → bget s.r 0 = i.toUInt64 →
  L.length + 300 * (K.X.length - i) + 300 < 2 ^ 60 → Reach s (VPost K s L F L.length i)

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

theorem g30_eq (o : Buf) : g30 o 16 = o ++ [g11 6 31 0, g11 5 31 8, g10 31 31 16] := by simp [g30, bpush]

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

/-- the postcondition of n consecutive value visits -/
def SPost (K : Cx) (s0 : GS) (L : List Item) (F : List UInt64) (i n : Nat) (s' : GS) : Prop :=
  ∃ c i' E, CGs K L.length i s0.o.length n c i' E ∧ Inv K s' L (F ++ E.map Nat.toUInt64) ∧ s'.o = s0.o ++ c ∧
    bget s'.r 0 = i'.toUInt64 ∧ (i ≤ i' ∧ i' ≤ K.X.length + 3) ∧ (2 ≤ L.length → E = [] ∧ bget s'.r 3 = bget s0.r 3)

theorem g19_eq (r o : Buf) (d b : UInt64) :
    g19 r o d b = (if g14 (bsize o) b == 1 then r else g16 r, bpush o (g13 d (bsize o) b)) := by
  unfold g19
  extract_lets h
  by_cases hc : (g14 h b == 1) = true
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]

/-! ## tail mode (loop arms) -/

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

/-- the tail-visit postcondition -/
def TPost (K : Cx) (hd : Nat) (s0 : GS) (L : List Item) (F : List UInt64) (i : Nat) (s' : GS) : Prop :=
  ∃ c i' E, CT K hd L.length i s0.o.length c i' E ∧ Inv K s' L (F ++ E.map Nat.toUInt64) ∧ s'.o = s0.o ++ c ∧
    bget s'.r 0 = i'.toUInt64 ∧ (i < i' ∧ i' ≤ K.X.length + 3) ∧ bget s'.r 3 = bget s0.r 3

/-- tail visit at AST word i, loop head hd -/
def TS (K : Cx) (hd i : Nat) : Prop := i ≤ K.X.length + 3 → ∀ s L F, 1 ≤ L.length → Inv K s (L ++ [(1, 1, 0)]) F → bget s.r 0 = i.toUInt64 →
  bget s.r 3 = hd.toUInt64 → L.length + 1 + 300 * (K.X.length - i) + 300 < 2 ^ 60 → Reach s (TPost K hd s L F i)

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

theorem g36_loop (x r o k : Buf) (hc : bget x (bget r 0) = 10) :
    g36 x r o k 0 = (if bget r 6 == 1 then
      (g15 (g15 (g15 r 0 (bget r 0 + 1)) 3 (bsize o)) 6 (bget r 6 + 3),
        (bpush (bpush (bpush o (g11 5 8 (g24 (bget r 1) 0))) (g4 0 5 0 8)) 0,
         g18 (g18 (g18 k (bget r 6) 1 1 0) (bget r 6 + 1) 11 (bsize o + 2) 0) (bget r 6 + 2) 1 1 0))
      else (g16 r, (o, k))) := by
  unfold g36
  extract_lets i n c0 c z b a
  have hc : c = 9 := by simp [c, c0, i, hc]
  have ha : (a == 0) = false := by simp [a, hc, g_1]
  rw [if_neg (by simp [ha]), if_neg (by decide), if_neg (by simp [hc]), if_neg (by simp [hc]), if_neg (by simp [hc]),
    if_neg (by simp [hc]), if_neg (by simp [hc]), if_neg (by simp [hc]), if_neg (by simp [hc]), if_neg (by simp [hc]),
    if_pos (by simp [hc])]

theorem g37_t11 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 11) :
    g37 x r o k t f = (if g14 (bget k ((bget r 6 - 1) * 3 + 1)) (bsize o) == 1 then g15 r 6 (bget r 6 - 1)
        else g16 (g15 r 6 (bget r 6 - 1)),
      (bpush (bpush (bset o (bget k ((bget r 6 - 1) * 3 + 1)) (g13 0 (bget k ((bget r 6 - 1) * 3 + 1)) (bsize o)))
        (g10 5 5 g_901)) (g12 5 8 (g24 (bget (g15 r 6 (bget r 6 - 1)) 1) 0)), (k, f))) := by
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
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide)]
  rw [g20_eq]

/-! ## closing the induction: every cursor, both modes -/

theorem g36_bad (x r o k : Buf) (hc : nt (bget x (bget r 0)) ≠ 1 ∧ nt (bget x (bget r 0)) ≠ 2 ∧ nt (bget x (bget r 0)) ≠ 3 ∧
    nt (bget x (bget r 0)) ≠ 4 ∧ nt (bget x (bget r 0)) ≠ 5 ∧ nt (bget x (bget r 0)) ≠ 6 ∧ nt (bget x (bget r 0)) ≠ 7 ∧
    nt (bget x (bget r 0)) ≠ 8 ∧ nt (bget x (bget r 0)) ≠ 9) :
    g36 x r o k 0 = (g16 r, (o, k)) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hc
  unfold g36
  extract_lets i n c0 c z b a
  have hi : i = bget r 0 := rfl
  have hc0 : c0 = bget x i := rfl
  have hc : c = nt c0 := rfl
  have ha : a = rngA c b := rfl
  clear_value i n c0 c z b a
  subst hi hc0 hc ha
  have ha' : ¬ (rngA (nt (bget x (bget r 0))) b == 0) = true := by
    simp only [rngA]
    rw [if_neg (by simpa using c3), if_neg (by simpa using c4), if_neg (by simpa using c8)]; decide
  rw [if_neg ha', if_neg (by decide), if_neg (by simpa using c1), if_neg (by simpa using c2), if_neg (by simpa using c3),
    if_neg (by simpa using c4), if_neg (by simpa using c5), if_neg (by simpa using c6), if_neg (by simpa using c7),
    if_neg (by simpa using c8), if_neg (by simpa using c9)]

/-! ## the RISC-V instance of the generic invariant (GenE.lean): today's Gen and encoders -/

theorem g31_len (o : Buf) (p : UInt64) : (g31 o p).length ≤ o.length + 5 := by simp [g31, g30, bpush]

/- the instance equations are closed by unfolding the class projections; Gen's own functions must stay folded
(unfolding g36 / g37 zeta-reduces their lets and blows up) -/
section rv
attribute [local irreducible] g4 g10 g11 g12 g13 g14 g19 g20 g21 g22 g23 g25 g26 g30 g31 g32 g36 g37

instance rvSrc : GenEmit.Src := ⟨g36, g37⟩
instance rvEm : GenEmit.Em := ⟨g4, g10, g11, g12, g13, g14, g19, g20, g21, g22, g23, g25, g26, g30, g31, g32⟩

theorem e36 : @GenEmit.Src.g36 rvSrc = g36 := rfl
theorem e37 : @GenEmit.Src.g37 rvSrc = g37 := rfl
theorem e_g4 : @GenEmit.Em.g4 rvEm = g4 := rfl
theorem e_g10 : @GenEmit.Em.g10 rvEm = g10 := rfl
theorem e_g11 : @GenEmit.Em.g11 rvEm = g11 := rfl
theorem e_g12 : @GenEmit.Em.g12 rvEm = g12 := rfl
theorem e_g13 : @GenEmit.Em.g13 rvEm = g13 := rfl
theorem e_g14 : @GenEmit.Em.g14 rvEm = g14 := rfl
theorem e_g19 : @GenEmit.Em.g19 rvEm = g19 := rfl
theorem e_g20 : @GenEmit.Em.g20 rvEm = g20 := rfl
theorem e_g21 : @GenEmit.Em.g21 rvEm = g21 := rfl
theorem e_g22 : @GenEmit.Em.g22 rvEm = g22 := rfl
theorem e_g23 : @GenEmit.Em.g23 rvEm = g23 := rfl
theorem e_g25 : @GenEmit.Em.g25 rvEm = g25 := rfl
theorem e_g26 : @GenEmit.Em.g26 rvEm = g26 := rfl
theorem e_g30 : @GenEmit.Em.g30 rvEm = g30 := rfl
theorem e_g31 : @GenEmit.Em.g31 rvEm = g31 := rfl
theorem e_g32 : @GenEmit.Em.g32 rvEm = g32 := rfl
/-- fold Gen's functions back into the class projections (plain rewriting: no unfolding, no match reduction) -/
local macro "rvfold" "at" h:ident : tactic => `(tactic| ((try rw [← e36] at $h:ident); (try rw [← e37] at $h:ident); (try rw [← e_g4] at $h:ident); (try rw [← e_g10] at $h:ident); (try rw [← e_g11] at $h:ident); (try rw [← e_g12] at $h:ident); (try rw [← e_g13] at $h:ident); (try rw [← e_g14] at $h:ident); (try rw [← e_g19] at $h:ident); (try rw [← e_g20] at $h:ident); (try rw [← e_g21] at $h:ident); (try rw [← e_g22] at $h:ident); (try rw [← e_g23] at $h:ident); (try rw [← e_g25] at $h:ident); (try rw [← e_g26] at $h:ident); (try rw [← e_g30] at $h:ident); (try rw [← e_g31] at $h:ident); (try rw [← e_g32] at $h:ident)))
instance rvEmOK : GenEmit.EmOK where
  pi_g21 := by have h := @pi_g21; rvfold at h; exact h
  pi_g22 := by have h := @pi_g22; rvfold at h; exact h
  pi_g23 := by have h := @pi_g23; rvfold at h; exact h
  pi_g31 := by have h := @pi_g31; rvfold at h; exact h
  pi_g32 := by have h := @pi_g32; rvfold at h; exact h
  g23_len := by have h := @g23_len; rvfold at h; exact h
  g21_len := by have h := @g21_len; rvfold at h; exact h
  g25_len := by have h := @g25_len; rvfold at h; exact h
  g26_len := by have h := @g26_len; rvfold at h; exact h
  g32_len := by have h := @g32_len; rvfold at h; exact h
  pi_g25 := by have h := @pi_g25; rvfold at h; exact h
  pi_g26 := by have h := @pi_g26; rvfold at h; exact h
  g20_eq := by have h := @g20_eq; rvfold at h; exact h
  g30_eq := by have h := @g30_eq; rvfold at h; exact h
  g19_eq := by have h := @g19_eq; rvfold at h; exact h
  g31_len := by have h := @g31_len; rvfold at h; exact h
instance rvSrcOK : GenEmit.SrcOK where
  g37_visit := by have h := @g37_visit; rvfold at h; exact h
  g36_const := by have h := @g36_const; rvfold at h; exact h
  g36_local := by have h := @g36_local; rvfold at h; exact h
  g36_bin := by have h := @g36_bin; rvfold at h; exact h
  g36_bin_bad := by have h := @g36_bin_bad; rvfold at h; exact h
  g37_t2 := by have h := @g37_t2; rvfold at h; exact h
  g36_let := by have h := @g36_let; rvfold at h; exact h
  g37_t6 := by have h := @g37_t6; rvfold at h; exact h
  g36_if := by have h := @g36_if; rvfold at h; exact h
  g36_if_bad := by have h := @g36_if_bad; rvfold at h; exact h
  g37_t3 := by have h := @g37_t3; rvfold at h; exact h
  g37_t4 := by have h := @g37_t4; rvfold at h; exact h
  g37_t5 := by have h := @g37_t5; rvfold at h; exact h
  g36_pair := by have h := @g36_pair; rvfold at h; exact h
  g36_call := by have h := @g36_call; rvfold at h; exact h
  g36_prim := by have h := @g36_prim; rvfold at h; exact h
  g36_prim_bad := by have h := @g36_prim_bad; rvfold at h; exact h
  g37_t7 := by have h := @g37_t7; rvfold at h; exact h
  g37_t8 := by have h := @g37_t8; rvfold at h; exact h
  g36_tval := by have h := @g36_tval; rvfold at h; exact h
  g36_tcont := by have h := @g36_tcont; rvfold at h; exact h
  g37_t9 := by have h := @g37_t9; rvfold at h; exact h
  g37_t10 := by have h := @g37_t10; rvfold at h; exact h
  g36_tif := by have h := @g36_tif; rvfold at h; exact h
  g36_tlet := by have h := @g36_tlet; rvfold at h; exact h
  g36_loop := by have h := @g36_loop; rvfold at h; exact h
  g37_t11 := by have h := @g37_t11; rvfold at h; exact h
  g36_bad := by have h := @g36_bad; rvfold at h; exact h

theorem it_e : ∀ (n : Nat) (s : GS), GenEmit.it n s = it n s
  | 0, _ => rfl
  | n + 1, s => it_e n (st s)

/-- a generic `Reach` at the RISC-V instance is the concrete one -/
theorem reach_e {s : GS} {P Q : GS → Prop} (h : GenEmit.Reach s P) (hPQ : ∀ s', P s' → Q s') : Reach s Q := by
  obtain ⟨m, a, b⟩ := h
  refine ⟨m, fun j hj => by rw [← it_e]; exact a j hj, ?_⟩
  rw [← it_e]
  rcases b with b | b
  · exact .inl (hPQ _ b)
  · exact .inr b

/-! the generic reference relation at the RISC-V instance is the concrete one -/
mutual
theorem cg_e {K : Cx} : ∀ {d i h c i' E}, GenEmit.CG K d i h c i' E → CG K d i h c i' E
  | _, _, _, _, _, _, .const a => .const a
  | _, _, _, _, _, _, .local a b => .local a b
  | _, _, _, _, _, _, .bin a b x y => .bin a b (cg_e x) (cg_e y)
  | _, _, _, _, _, _, .ite a b x y z w j1 j2 => .ite a b (cg_e x) (cg_e y) (cg_e z) (cg_e w) j1 j2
  | _, _, _, _, _, _, .lett a b x y => .lett a b (cg_e x) (cg_e y)
  | _, _, _, _, _, _, .pair a b xs => .pair a b (cgs_e xs)
  | _, _, _, _, _, _, .call a b c xs j => .call a b c (cgs_e xs) j
  | _, _, _, _, _, _, .prim a b xs => .prim a b (cgs_e xs)
  | _, _, _, _, _, _, .loop a z s j => .loop a (ct_e z) (ct_e s) j
theorem ct_e {K : Cx} : ∀ {hd d i h c i' E}, GenEmit.CT K hd d i h c i' E → CT K hd d i h c i' E
  | _, _, _, _, _, _, _, .val a b c x => .val a b c (cg_e x)
  | _, _, _, _, _, _, _, .cont a x j => .cont a (cg_e x) j
  | _, _, _, _, _, _, _, .ite a b x y z w j1 j2 => .ite a b (cg_e x) (cg_e y) (ct_e z) (ct_e w) j1 j2
  | _, _, _, _, _, _, _, .lett a b x y => .lett a b (cg_e x) (ct_e y)
theorem cgs_e {K : Cx} : ∀ {d i h n c i' E}, GenEmit.CGs K d i h n c i' E → CGs K d i h n c i' E
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons a b => .cons (cg_e a) (cgs_e b)
end

/-- **the g39 visit invariant**: from any state with a visit item on top, Gen's main loop either fails (error / code
too big) or finishes that node, having emitted exactly the reference code (CG / CT).  Instance of `GenEmit.visit_all`. -/
theorem visit_all (K : Cx) (hX : K.X.length < 2 ^ 31) (i : Nat) : VS K i ∧ ∀ hd, TS K hd i := by
  obtain ⟨hv, ht⟩ := GenEmit.visit_all K hX i
  exact ⟨fun a s L F b c d => reach_e (hv a s L F b c d) (fun _ ⟨c, i', E, h, r⟩ => ⟨c, i', E, cg_e h, r⟩),
    fun hd a s L F b c d e f => reach_e (ht hd a s L F b c d e f) (fun _ ⟨c, i', E, h, r⟩ => ⟨c, i', E, ct_e h, r⟩)⟩
end rv


/-! ## from `Reach` to the fuelled main loop g39 -/

/-- g39 on a state -/
def G (n : Nat) (s : GS) : Buf × Buf := g39 n s.x s.r s.o s.k s.t s.f

theorem g55_live (s : GS) (h : live s) : g55 s.x s.r s.o = 0 := by
  obtain ⟨h5, h4, hz, h6, -⟩ := h
  unfold g55
  rw [if_neg (by simpa using h5), if_neg (by simpa using h4), if_neg hz, if_neg (by simpa using h6)]; rfl

theorem g39_step (s : GS) (h : live s) (n : Nat) : G (n + 1) s = G n (st s) := by
  have h6 := h.2.2.2.1
  unfold G st
  rw [g39, g55_live s h, if_neg (by decide)]
  unfold g54
  rw [if_neg (by simpa using h6)]

theorem g39_iter : ∀ (m n : Nat) (s : GS), (∀ j < m, live (it j s)) → G (n + m) s = G n (it m s)
  | 0, n, s, _ => rfl
  | m + 1, n, s, h => by
    rw [show n + (m + 1) = (n + m) + 1 by omega, g39_step s (h 0 (by omega))]
    exact g39_iter m n (st s) (fun j hj => h (j + 1) (by omega))

theorem g16_4 (r : Buf) (h : 5 ≤ r.length) : bget (g16 r) 4 = 1 := by
  unfold g16; rw [BufL.bget_bset, if_pos ⟨rfl, by simp; omega⟩]; rfl

/-- an error state stays an error -/
theorem g39_err (s : GS) (h : err s) : ∀ n, bget (G n s).1 4 = 1
  | 0 => by
    unfold G; rw [g39]
    have : 5 ≤ s.r.length := by
      unfold err bget at h; rcases Nat.lt_or_ge 4 s.r.length with h1 | h1
      · omega
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1] at h
    exact g16_4 _ this
  | n + 1 => by
    unfold err at h
    have h4 : (bget s.r 4 == 1) = true := by simp [h]
    unfold G; rw [g39]
    have hs : g55 s.x s.r s.o = 1 := by
      unfold g55; by_cases h5 : (bget s.r 5 == 1) = true
      · rw [if_pos h5]; rfl
      · rw [if_neg h5, if_pos h4]; rfl
    rw [hs, if_pos (by decide)]
    unfold g56
    by_cases h5 : (bget s.r 5 == 1) = true
    · rw [if_pos h5]; exact h
    · rw [if_neg h5, if_pos h4]; exact h

/-- a too-big state keeps its code (and g42 then rejects it) -/
theorem g39_big (s : GS) (h : big s) : ∀ n, (G n s).2 = s.o
  | 0 => by unfold G; rw [g39]
  | n + 1 => by
    have hz : 16777215 < bsize s.o := by
      rw [bsize_u, UInt64.lt_iff_toNat_lt, u_toNat _ (by have := h.2; omega)]; simp; have := h.1; omega
    unfold G; rw [g39]
    have hs : g55 s.x s.r s.o = 1 := by
      unfold g55
      by_cases h5 : (bget s.r 5 == 1) = true
      · rw [if_pos h5]; rfl
      · rw [if_neg h5]
        by_cases h4 : (bget s.r 4 == 1) = true
        · rw [if_pos h4]; rfl
        · rw [if_neg h4, if_pos hz]; rfl
    rw [hs, if_pos (by decide)]
    unfold g56
    by_cases h5 : (bget s.r 5 == 1) = true
    · rw [if_pos h5]
    · rw [if_neg h5]
      by_cases h4 : (bget s.r 4 == 1) = true
      · rw [if_pos h4]
      · rw [if_neg h4, if_pos hz]

/-- **the bridge**: if the main loop ends without error and with code below 2^24 words, every `Reach` claim held -/
theorem reach_run {s : GS} {P : GS → Prop} (h : Reach s P) (N : Nat) (hok : bget (G N s).1 4 ≠ 1)
    (hsz : ¬ 16777215 < bsize (G N s).2) :
    ∃ m, m ≤ N ∧ P (it m s) ∧ G N s = G (N - m) (it m s) := by
  obtain ⟨m, hm, hp⟩ := h
  by_cases hNm : N < m
  · exfalso
    have e := g39_iter N 0 s (fun j hj => hm j (by omega))
    simp only [Nat.zero_add] at e
    rw [e] at hok
    have hl := hm N hNm
    unfold G at hok; rw [g39] at hok
    exact hok (g16_4 _ hl.2.2.2.2)
  have e := g39_iter m (N - m) s hm
  rw [show N - m + m = N by omega] at e
  rcases hp with hp | he | hb
  · exact ⟨m, by omega, hp, e⟩
  · exfalso
    rw [e] at hok; exact hok (g39_err _ he (N - m))
  · exfalso
    have := g39_big _ hb (N - m)
    rw [e, this] at hsz
    apply hsz
    rw [bsize_u, UInt64.lt_iff_toNat_lt, u_toNat _ (by have := hb.2; omega)]; simp; have := hb.1; omega


/-! ## the def level: header (g38), body, ENDDEF (exit fixups g28, epilogue g29) -/

/-- patch exit placeholders e (last first) to jump to the current end h -/
def patchR (h : UInt64) : Buf → List UInt64 → Buf
  | o, [] => o
  | o, e :: E => patchR h (bset o e (g13 0 e h)) E

theorem patchR_len (h : UInt64) : ∀ (E : List UInt64) (o : Buf), (patchR h o E).length = o.length
  | [], o => rfl
  | e :: E, o => by simp only [patchR]; rw [patchR_len h E]; exact BufL.length_bset _ _ _

/-- ENDDEF's fixup loop: f unchanged, every recorded exit patched, r unchanged or the error flag set -/
theorem g28_ok (n : Nat) : ∀ (F : List UInt64) (f r o : Buf), F.length ≤ n → F.length < 2 ^ 32 →
    (∀ j < F.length, f.getD j 0 = F.getD j 0) →
    (g28 n F.length.toUInt64 (f, (r, o))).1 = f ∧ (g28 n F.length.toUInt64 (f, (r, o))).2.2 = patchR (bsize o) o F.reverse ∧
    (((g28 n F.length.toUInt64 (f, (r, o))).2.1 = r ∧ ∀ e ∈ F, g14 e (bsize o) = 1) ∨
      (5 ≤ r.length → bget (g28 n F.length.toUInt64 (f, (r, o))).2.1 4 = 1)) := by
  induction n with
  | zero =>
    intro F f r o h _ _
    have : F = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [g28, patchR]
  | succ n ih =>
    intro F f r o h hl hF
    rcases List.eq_nil_or_concat F with h0 | ⟨F', e, h1⟩
    · subst h0; simp [g28, patchR]
    subst h1
    simp only [List.concat_eq_append] at *
    replace h : F'.length + 1 ≤ n + 1 := by simpa using h
    replace hl : F'.length + 1 < 2 ^ 32 := by simpa using hl
    have hne : ¬ ((F'.length + 1).toUInt64 == 0) = true := by
      simp [Nat.toUInt64]; intro h2; have := congrArg UInt64.toNat h2; simp at this; omega
    have e1 : (F'.length + 1).toUInt64 - 1 = F'.length.toUInt64 := by simp [Nat.toUInt64]
    have hv : bget f F'.length.toUInt64 = e := by
      simp only [bget]; rw [u_toNat _ (by omega), hF F'.length (by simp)]; simp
    have hF' : ∀ j < F'.length, f.getD j 0 = F'.getD j 0 := fun j hj => by
      rw [hF j (by simp; omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
    rw [show (F' ++ [e]).length.toUInt64 = (F'.length + 1).toUInt64 by simp]
    rw [g28, if_neg hne]
    simp only
    rw [e1, hv, g20_eq]
    obtain ⟨a1, a2, a3⟩ := ih F' f (if g14 e (bsize o) == 1 then r else g16 r) (bset o e (g13 0 e (bsize o))) (by omega) (by omega) hF'
    generalize hr' : (if (g14 e (bsize o) == 1) = true then r else g16 r) = r' at a1 a2 a3 ⊢
    refine ⟨a1, ?_, ?_⟩
    · rw [a2, BufL.bsize_bset]; simp [patchR]
    · by_cases hg : (g14 e (bsize o) == 1) = true
      · rw [if_pos hg] at hr'; subst hr'
        rcases a3 with ⟨a3, a4⟩ | a3
        · refine .inl ⟨a3, fun e' he' => ?_⟩
          rcases List.mem_append.mp he' with h1 | h1
          · rw [← BufL.bsize_bset o e (g13 0 e (bsize o))]; exact a4 e' h1
          · simp at h1; subst h1; simpa using hg
        · exact .inr a3
      · rw [if_neg hg] at hr'; subst hr'
        right; intro hr
        rcases a3 with ⟨a3, -⟩ | a3
        · rw [a3]; exact g16_4 _ hr
        · exact a3 (by unfold g16; rw [BufL.length_bset]; exact hr)

theorem pi_g29 : ∀ (n : Nat) (p q j : UInt64), PI (g29 n p q j)
  | 0, p, q, j => fun o => by simp [g29, em]
  | n + 1, p, q, j => by
    by_cases hj : j < q
    · have := pi_comp (pi_comp (pi_bpush (g11 5 31 ((q - 1 - j) <<< 3))) (pi_bpush (g12 5 8 ((p <<< 3) + g_16 - ((j + 1) <<< 3)))))
        (pi_g29 n p q (j + 1))
      intro o; have e := this o; simp only [g29, hj, if_true] at e ⊢; exact e
    · intro o; simp [g29, hj, em, bpush]


/-- g37 on the ENDDEF item (tag 12), given the fixup loop's result -/
theorem g37_t12 (x r o k t f : Buf) (hc : bget k ((bget r 6 - 1) * 3) = 12) (f1 r3 o3 : Buf)
    (hR : g28 65536 (bget (if bget x (bget (g15 r 6 (bget r 6 - 1)) 0) == 21 then
        g15 (g15 r 6 (bget r 6 - 1)) 0 (bget (g15 r 6 (bget r 6 - 1)) 0 + 1) else g16 (g15 r 6 (bget r 6 - 1))) 8)
      (f, ((if bget x (bget (g15 r 6 (bget r 6 - 1)) 0) == 21 then
        g15 (g15 r 6 (bget r 6 - 1)) 0 (bget (g15 r 6 (bget r 6 - 1)) 0 + 1) else g16 (g15 r 6 (bget r 6 - 1))), o)) = (f1, (r3, o3))) :
    g37 x r o k t f = (g15 r3 8 0, (g29 512
      (bget (if bget x (bget (g15 r 6 (bget r 6 - 1)) 0) == 21 then
        g15 (g15 r 6 (bget r 6 - 1)) 0 (bget (g15 r 6 (bget r 6 - 1)) 0 + 1) else g16 (g15 r 6 (bget r 6 - 1))) 1)
      (bget (if bget x (bget (g15 r 6 (bget r 6 - 1)) 0) == 21 then
        g15 (g15 r 6 (bget r 6 - 1)) 0 (bget (g15 r 6 (bget r 6 - 1)) 0 + 1) else g16 (g15 r 6 (bget r 6 - 1))) 2) 0
      (bpush (bpush o3 (g11 14 8 8)) (g11 15 8 0)), (k, f1))) := by
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
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  rename_i i' r2' p' q' c2'
  have hR' : g28 65536 c2' (f, (r2', o)) = (f1, (r3, o3)) := hR
  rw [hR']


/-- the def prologue (g38): push ra, push s0, s0 := t6, reserve the locals, check room -/
def proW (p ns : UInt64) (o : Buf) : Buf :=
  bpush (bpush (bpush (bpush (g22 (g22 o 1) 8) (g10 8 31 0)) (g10 31 31 (g_0 - ((ns - p) <<< 3)))) (g4 7 31 30 8))
    (g13 0 (bsize (g22 (g22 o 1) 8) + 3) 1)

theorem pi_pro (p ns : UInt64) : PI (proW p ns) := by
  have q : PI (fun o => bpush (bpush (bpush (bpush o (g10 8 31 0)) (g10 31 31 (g_0 - ((ns - p) <<< 3)))) (g4 7 31 30 8))
      (g13 0 (bsize o + 3) 1)) := by intro o; simp [em, bpush, bsize]
  have := pi_comp (pi_comp (pi_g22 1) (pi_g22 8)) q
  intro o; exact this o

/-- a def header DEF id npw nslots kind nres at AST word i, def number = |t| -/
def HdOk (x t : Buf) (i : UInt64) : Prop :=
  bget x i = 20 ∧ bget x (i + 3) < 251 ∧ bget x (i + 2) < bget x (i + 3) + 1 ∧ bget x (i + 5) < 251 ∧ bget x (i + 1) = bsize t

theorem g38_ok (x r o k t : Buf) (h : HdOk x t (bget r 0)) :
    g38 x r o k t = (g15 (g15 (g15 (g15 (g15 r 0 (bget r 0 + 6)) 1 (bget x (bget r 0 + 2))) 7 (bget x (bget r 0 + 3))) 2
        (bget x (bget r 0 + 5))) 6 2,
      (proW (bget x (bget r 0 + 2)) (bget x (bget r 0 + 3)) o, (g18 (g18 k 0 12 0 0) 1 1 0 0, bpush t (bsize o)))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold g38
  extract_lets i d p s q v z0 z1 z2 z3 z4
  have hz : (z4 == 0) = false := by
    simp [z4, z3, z2, z1, z0, v, i, d, p, s, q, h1, h2, h3, h4, h5, g_1, g_0]
  rw [if_neg (by simp [hz])]
  rfl

theorem g38_bad (x r o k t : Buf) (h : ¬ HdOk x t (bget r 0)) : g38 x r o k t = (g16 r, (o, (k, t))) := by
  unfold g38
  extract_lets i d p s q v z0 z1 z2 z3 z4
  have hz : (z4 == 0) = true := by
    simp only [HdOk] at h
    by_cases h1 : bget x (bget r 0) = 20 <;> by_cases h2 : bget x (bget r 0 + 3) < 251 <;>
      by_cases h3 : bget x (bget r 0 + 2) < bget x (bget r 0 + 3) + 1 <;> by_cases h4 : bget x (bget r 0 + 5) < 251 <;>
      by_cases h5 : bget x (bget r 0 + 1) = bsize t <;>
      simp_all [z4, z3, z2, z1, z0, v, i, d, p, s, q, g_1, g_0]
  rw [if_pos hz]


/-- `Run s P`: whenever the fuelled main loop from s ends without error and with small code, it passed a state with P -/
def Run (s : GS) (P : GS → Prop) : Prop :=
  ∀ N, bget (G N s).1 4 ≠ 1 → ¬ 16777215 < bsize (G N s).2 → ∃ m, m ≤ N ∧ ∃ s', P s' ∧ G N s = G (N - m) s'

theorem Run.ofReach {s : GS} {P : GS → Prop} (h : Reach s P) : Run s P := fun N h1 h2 => by
  obtain ⟨m, hm, hp, he⟩ := reach_run h N h1 h2
  exact ⟨m, hm, _, hp, he⟩

theorem Run.done {s : GS} {P : GS → Prop} (h : P s) : Run s P := fun N _ _ => ⟨0, by omega, s, h, by simp⟩

theorem Run.bind {s : GS} {P Q : GS → Prop} (h : Run s P) (hq : ∀ s', P s' → Run s' Q) : Run s Q := fun N h1 h2 => by
  obtain ⟨m, hm, s', hp, he⟩ := h N h1 h2
  rw [he] at h1 h2
  obtain ⟨m', hm', s'', hq', he'⟩ := hq s' hp (N - m) h1 h2
  exact ⟨m + m', by omega, s'', hq', by rw [he, he']; congr 1; omega⟩

theorem Run.error {s : GS} {P : GS → Prop} (h : err s) : Run s P := fun N h1 _ => absurd (g39_err s h N) h1

theorem Run.toobig {s : GS} {P : GS → Prop} (h : big s) : Run s P := fun N _ h2 => by
  exfalso; apply h2; rw [g39_big s h N, bsize_u, UInt64.lt_iff_toNat_lt, u_toNat _ (by have := h.2; omega)]
  simp; have := h.1; omega

/-- one g39 step that is not a `st` step (the def header, r[6] = 0) -/
theorem Run.stepDef {s : GS} {P : GS → Prop} (h0 : g55 s.x s.r s.o = 0) (h6 : bget s.r 6 = 0) (hl : 5 ≤ s.r.length)
    (h : Run (match g38 s.x s.r s.o s.k s.t with | (r1, (o1, (k1, t1))) => ⟨s.x, r1, o1, k1, t1, s.f⟩) P) : Run s P := by
  intro N h1 h2
  cases N with
  | zero => exfalso; apply h1; unfold G; rw [g39]; exact g16_4 _ hl
  | succ n =>
    have e : G (n + 1) s = G n (match g38 s.x s.r s.o s.k s.t with | (r1, (o1, (k1, t1))) => ⟨s.x, r1, o1, k1, t1, s.f⟩) := by
      unfold G; rw [g39, h0, if_neg (by decide)]; unfold g54; rw [if_pos (by simp [h6])]
    rw [e] at h1 h2
    obtain ⟨m, hm, s', hp, he⟩ := h n h1 h2
    exact ⟨m + 1, by omega, s', hp, by rw [e, he]; congr 1; omega⟩

theorem st_t12 (s : GS) (n : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 12) (f1 r3 o3 : Buf)
    (hR : g28 65536 (bget (if bget s.x (bget (g15 s.r 6 n) 0) == 21 then g15 (g15 s.r 6 n) 0 (bget (g15 s.r 6 n) 0 + 1)
        else g16 (g15 s.r 6 n)) 8)
      (s.f, ((if bget s.x (bget (g15 s.r 6 n) 0) == 21 then g15 (g15 s.r 6 n) 0 (bget (g15 s.r 6 n) 0 + 1)
        else g16 (g15 s.r 6 n)), s.o)) = (f1, (r3, o3))) :
    st s = ⟨s.x, g15 r3 8 0, g29 512
      (bget (if bget s.x (bget (g15 s.r 6 n) 0) == 21 then g15 (g15 s.r 6 n) 0 (bget (g15 s.r 6 n) 0 + 1) else g16 (g15 s.r 6 n)) 1)
      (bget (if bget s.x (bget (g15 s.r 6 n) 0) == 21 then g15 (g15 s.r 6 n) 0 (bget (g15 s.r 6 n) 0 + 1) else g16 (g15 s.r 6 n)) 2)
      0 (bpush (bpush o3 (g11 14 8 8)) (g11 15 8 0)), s.k, s.t, f1⟩ := by
  subst hn
  unfold st; rw [g37_t12 _ _ _ _ _ _ hc f1 r3 o3 hR]


/-- the root visit at any cursor below 2^40 (past |X| + 3 the tag is 0: error) -/
theorem root_visit (K : Cx) (hX : K.X.length < 2 ^ 31) (i : Nat) (hi : i < 2 ^ 40) : ∀ s L F, Inv K s (L ++ [(1, 0, 0)]) F →
    bget s.r 0 = i.toUInt64 → L.length + 300 * (K.X.length - i) + 300 < 2 ^ 60 → Reach s (VPost K s L F L.length i) := by
  intro s L F hI hr0 hB
  by_cases hiX : i ≤ K.X.length + 3
  · exact (visit_all K hX i).1 hiX s L F hI hr0 hB
  have ht : tg K.X i = 0 := by simp [tg, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : K.X.length ≤ i)]
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hI]
  obtain ⟨hl6, h0, -⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = tg K.X i := by rw [hI.x, tg_u _ _ (by omega)]
  have hn0 : nt 0 = 0 := rfl
  rw [g36_bad _ _ _ _ (by rw [h0, hx, ht, hn0]; decide)]
  exact Reach.error (g16_err _ hl6)

/-- the state at a def boundary -/
structure Bnd (X : Buf) (u : UInt64) (s : GS) : Prop where
  x : s.x = X
  rl : s.r.length = 10
  r4 : bget s.r 4 ≠ 1
  r5 : bget s.r 5 ≠ 1
  r6 : bget s.r 6 = 0
  r8 : bget s.r 8 = 0
  r9 : bget s.r 9 = u
  kl : s.k.length < 2 ^ 62
  fl : s.f.length ≤ 65536
  ol : s.o.length < 2 ^ 24
  tl : s.t.length < 2 ^ 32

/-- the def context of the header at AST word i (def table T including this def's start) -/
def dK (X : Buf) (u : UInt64) (T : Buf) (i : Nat) : Cx := ⟨X, tg X (i + 2), tg X (i + 3), u, T, tg X (i + 5)⟩

/-- **one def** compiles: header fields valid, the body (root visit, depth 1) is CG with exits E, ENDDEF at i1;
the code after it is: prologue ++ body (exits patched to the epilogue) ++ ld a4/a5 ++ copy-down epilogue; every exit
jump passed Gen's range check -/
def DefC (X : Buf) (u : UInt64) (T : Buf) (i : Nat) (o o' : Buf) (i' : Nat) : Prop :=
  tg X i = 20 ∧ tg X (i + 3) < 251 ∧ tg X (i + 2) < tg X (i + 3) + 1 ∧ tg X (i + 5) < 251 ∧ tg X (i + 1) = bsize T ∧
  ∃ c i1 E, CG (dK X u (bpush T (bsize o)) i) 1 (i + 6) (proW (tg X (i + 2)) (tg X (i + 3)) o).length c i1 E ∧
    tg X i1 = 21 ∧ i' = i1 + 1 ∧
    o' = g29 512 (tg X (i + 2)) (tg X (i + 5)) 0 (bpush (bpush
      (patchR (bsize (proW (tg X (i + 2)) (tg X (i + 3)) o ++ c)) (proW (tg X (i + 2)) (tg X (i + 3)) o ++ c)
        (E.map Nat.toUInt64).reverse) (g11 14 8 8)) (g11 15 8 0)) ∧
    ∀ e ∈ E, JOk e (proW (tg X (i + 2)) (tg X (i + 3)) o ++ c).length

end GenRef
