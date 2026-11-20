/- THROWAWAY PROTOTYPE (plan step 9; design input only, nothing live imports this).
GenRef's work-item invariant, restated over an abstract emitter record `Em` (what a target's Gen appends for each
emit call, the jump cells, the jump-range check) and an abstract Gen source `Src` (its two dispatch functions, g36 and
g37 for RISC-V).  The per-source facts are the dispatch equations `Src.OK` (for RISC-V: GenRef's existing `g36_*` /
`g37_t*` unfolding lemmas, unchanged).  Everything else (Reach, Inv, the item stack, the visit induction) is generic.
Prototyped node kinds: CONST (plain emitter) and CALL (operand sequence, a jump with a range check, the def table).
See Testing/notes/GEN_EMIT_PROTO.md. -/
import Nano.V2Self.Proof.Gen.GenRef
namespace GenEmit
open C GenRef

/-- a target's emitters, in code-buffer cells (RISC-V: 1 cell = 1 instruction word) -/
structure Em where
  /-- CONST v: materialise v and push it -/
  const : UInt64 → Buf → Buf
  /-- a bound on the cells `const` appends -/
  cb : Nat
  /-- the cells of `jump-and-link d` from cell a to cell b -/
  jmp : UInt64 → UInt64 → UInt64 → List UInt64
  /-- their number: it must not depend on the displacement (no relaxation) -/
  jl : Nat
  /-- the range check on a jump from cell a to cell b -/
  rng : UInt64 → UInt64 → Bool

structure Em.OK (E : Em) : Prop where
  pi_const : ∀ v, PI (E.const v)
  const_le : ∀ v (o : Buf), (E.const v o).length ≤ o.length + E.cb
  jmp_len : ∀ d a b, (E.jmp d a b).length = E.jl
  cb_le : E.cb < 2 ^ 32
  jl_le : E.jl < 2 ^ 32

/-- a Gen source: the node visit (g36) and the work-item step (g37) -/
structure Src where
  visit : Buf → Buf → Buf → Buf → UInt64 → Buf × (Buf × Buf)
  item : Buf → Buf → Buf → Buf → Buf → Buf → Buf × (Buf × (Buf × Buf))

/-- the dispatch equations of a source over the emitters E (register/stack helpers g15 g16 g18 g27 are shared) -/
structure Src.OK (S : Src) (E : Em) : Prop where
  item_visit : ∀ x r o k t f : Buf, bget k ((bget r 6 - 1) * 3) = 1 →
    S.item x r o k t f = (match S.visit x (g15 r 6 (bget r 6 - 1)) o k (bget k ((bget r 6 - 1) * 3 + 1)) with
      | (r2, (o2, k2)) => (r2, (o2, (k2, f))))
  visit_const : ∀ x r o k : Buf, bget x (bget r 0) = 1 →
    S.visit x r o k 0 = (g15 r 0 (bget r 0 + 2), (E.const (bget x (bget r 0 + 1)) o, k))
  visit_call : ∀ x r o k : Buf, bget x (bget r 0) = 8 →
    S.visit x r o k 0 = (if bget x (bget r 0 + 2) < 251 then
      (g15 (g15 r 0 (bget r 0 + 3)) 6 (bget r 6 + 1 + bget x (bget r 0 + 2)),
        (o, g27 256 (g18 k (bget r 6) 7 (bget x (bget r 0 + 1)) 0) (bget r 6 + 1) (bget x (bget r 0 + 2))))
      else (g16 r, (o, k)))
  item_call : ∀ x r o k t f : Buf, bget k ((bget r 6 - 1) * 3) = 7 →
    S.item x r o k t f = (match (if bget k ((bget r 6 - 1) * 3 + 1) < bsize t then
        (if E.rng (bsize o) (bget t (bget k ((bget r 6 - 1) * 3 + 1))) then g15 r 6 (bget r 6 - 1)
          else g16 (g15 r 6 (bget r 6 - 1)), o ++ E.jmp 1 (bsize o) (bget t (bget k ((bget r 6 - 1) * 3 + 1))))
        else (g16 (g15 r 6 (bget r 6 - 1)), o)) with
      | (r2, o2) => (r2, (o2, (k, f))))

/-! ## the generic main-loop step and `Reach` (GenRef's, with the source as a parameter) -/
section gen
variable (S : Src)

def st (s : GS) : GS :=
  match S.item s.x s.r s.o s.k s.t s.f with
  | (r1, (o1, (k1, f1))) => ⟨s.x, r1, o1, k1, s.t, f1⟩

def it : Nat → GS → GS
  | 0, s => s
  | n + 1, s => it n (st S s)

theorem it_add : ∀ (n m : Nat) (s : GS), it S (n + m) s = it S n (it S m s)
  | n, 0, s => rfl
  | n, m + 1, s => by rw [show n + (m + 1) = (n + m) + 1 by omega]; simp only [it]; exact it_add n m (st S s)

def Reach (s : GS) (P : GS → Prop) : Prop :=
  ∃ m, (∀ j < m, live (it S j s)) ∧ (P (it S m s) ∨ err (it S m s) ∨ big (it S m s))

variable {S}
theorem Reach.done {s : GS} {P : GS → Prop} (h : P s) : Reach S s P := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inl h⟩
theorem Reach.error {s : GS} {P : GS → Prop} (h : err s) : Reach S s P := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inr (.inl h)⟩
theorem Reach.toobig {s : GS} {P : GS → Prop} (h : big s) : Reach S s P := ⟨0, fun _ h => absurd h (Nat.not_lt_zero _), .inr (.inr h)⟩
theorem Reach.step {s : GS} {P : GS → Prop} (hl : live s) (h : Reach S (st S s) P) : Reach S s P := by
  obtain ⟨m, hm, hp⟩ := h
  refine ⟨m + 1, fun j hj => ?_, hp⟩
  rcases j with _ | j
  · exact hl
  · exact hm j (by omega)
theorem Reach.bind {s : GS} {P Q : GS → Prop} (h : Reach S s P) (hq : ∀ s', P s' → Reach S s' Q) : Reach S s Q := by
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
end gen

/-! ## the reference relation over E (prototype subset of GenRef.CG / CGs) -/
mutual
inductive CG (E : Em) (K : Cx) : Nat → Nat → Nat → List UInt64 → Nat → List Nat → Prop
  | const {d i h} : tg K.X i = 1 → CG E K d i h (em (E.const (tg K.X (i + 1))) h) (i + 2) []
  | call {d i h c i' X} : tg K.X i = 8 → tg K.X (i + 2) < 251 → tg K.X (i + 1) < bsize K.T →
      CGs E K (d + 1) (i + 3) h (tg K.X (i + 2)).toNat c i' X →
      E.rng (h + c.length).toUInt64 (bget K.T (tg K.X (i + 1))) = true →
      CG E K d i h (c ++ E.jmp 1 (h + c.length).toUInt64 (bget K.T (tg K.X (i + 1)))) i' X
inductive CGs (E : Em) (K : Cx) : Nat → Nat → Nat → Nat → List UInt64 → Nat → List Nat → Prop
  | nil {d i h} : CGs E K d i h 0 [] i []
  | cons {d i h n c cs i1 i2 X Xs} : CG E K (d + n) i h c i1 X → CGs E K d i1 (h + c.length) n cs i2 Xs →
      CGs E K d i h (n + 1) (c ++ cs) i2 (X ++ Xs)
end

section inv
variable {S : Src} {E : Em}

theorem st_visit (hS : S.OK E) {K s L F} {m : UInt64} (hI : Inv K s (L ++ [(1, m, 0)]) F) :
    st S s = (match S.visit s.x (bset s.r 6 L.length.toUInt64) s.o s.k m with
      | (r2, (o2, k2)) => ⟨s.x, r2, o2, k2, s.t, s.f⟩) := by
  obtain ⟨hn, e0, e1, -⟩ := top_item hI
  unfold st
  rw [hS.item_visit _ _ _ _ _ _ e0, e1, hn]
  rfl

def VPost (E : Em) (K : Cx) (s0 : GS) (L : List Item) (F : List UInt64) (d i : Nat) (s' : GS) : Prop :=
  ∃ c i' X, CG E K d i s0.o.length c i' X ∧ Inv K s' L (F ++ X.map Nat.toUInt64) ∧ s'.o = s0.o ++ c ∧
    bget s'.r 0 = i'.toUInt64 ∧ (i < i' ∧ i' ≤ K.X.length + 3) ∧ (2 ≤ d → X = [] ∧ bget s'.r 3 = bget s0.r 3)

def VS (S : Src) (E : Em) (K : Cx) (i : Nat) : Prop :=
  i ≤ K.X.length + 3 → ∀ s L F, Inv K s (L ++ [(1, 0, 0)]) F → bget s.r 0 = i.toUInt64 →
  L.length + 300 * (K.X.length - i) + 300 < 2 ^ 60 → Reach S s (VPost E K s L F L.length i)

/-- CONST, for any source and emitters -/
theorem v_const (hS : S.OK E) (hE : E.OK) {K s L F d i} (hI : Inv K s (L ++ [(1, 0, 0)]) F)
    (hr0 : bget s.r 0 = i.toUInt64) (hi : i < 2 ^ 31) (hiX : i < K.X.length)
    (ht : tg K.X i = 1) : Reach S s (VPost E K s L F d i) := by
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hS hI]
  obtain ⟨hl6, h0, -⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = 1 := by rw [hI.x, tg_u _ _ (by omega), ht]
  rw [hS.visit_const _ _ _ _ (by rw [h0]; exact hx), h0]
  dsimp only
  have hv : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  have e : E.const (tg K.X (i + 1)) s.o = s.o ++ em (E.const (tg K.X (i + 1))) s.o.length := hE.pi_const _ s.o
  rw [hv, e]
  by_cases hb : 2 ^ 24 ≤ (s.o ++ em (E.const (tg K.X (i + 1))) s.o.length).length
  · exact Reach.toobig ⟨hb, by
      have := hI.ol; have := em_le (E.const (tg K.X (i + 1))) s.o.length E.cb (hE.const_le _); have := hE.cb_le
      simp; omega⟩
  obtain ⟨q1, q2, q3, q4⟩ := r06 s.r hI.rl L.length.toUInt64 (i.toUInt64 + 2)
  refine Reach.done ⟨_, i + 2, [], .const ht, ?_, rfl, ?_, by omega, fun _ => ⟨rfl, ?_⟩⟩
  · simp only [List.map_nil, List.append_nil]
    exact inv_mk hI _ _ _ L q4 q1 q2 (stk_pop hI.stk) hI.kl (by have := hI.Ll; simp at this; omega) (by omega)
  · simp only [g15]; rw [q3]; simp [Nat.toUInt64, UInt64.ofNat_add]
  · simp only [g15]; rw [q4 3 (by decide) (by decide)]

def SPost (E : Em) (K : Cx) (s0 : GS) (L : List Item) (F : List UInt64) (i n : Nat) (s' : GS) : Prop :=
  ∃ c i' X, CGs E K L.length i s0.o.length n c i' X ∧ Inv K s' L (F ++ X.map Nat.toUInt64) ∧ s'.o = s0.o ++ c ∧
    bget s'.r 0 = i'.toUInt64 ∧ (i ≤ i' ∧ i' ≤ K.X.length + 3) ∧ (2 ≤ L.length → X = [] ∧ bget s'.r 3 = bget s0.r 3)

/-- n operand visits -/
theorem seq {K i0} (hV : ∀ j, i0 ≤ j → VS S E K j) : ∀ (n i : Nat) (s : GS) (L : List Item) (F : List UInt64), i0 ≤ i →
    i ≤ K.X.length + 3 → Inv K s (L ++ List.replicate n (1, 0, 0)) F → bget s.r 0 = i.toUInt64 →
    L.length + n + 300 * (K.X.length - i) + 300 < 2 ^ 60 → Reach S s (SPost E K s L F i n)
  | 0, i, s, L, F, _, hiX, hI, hr0, _ => .done ⟨[], i, [], .nil, by simpa using hI, by simp, hr0, ⟨Nat.le_refl _, hiX⟩, fun _ => ⟨rfl, rfl⟩⟩
  | n + 1, i, s, L, F, hi, hiX, hI, hr0, hB => by
    have hI' : Inv K s ((L ++ List.replicate n (1, 0, 0)) ++ [(1, 0, 0)]) F := by
      rw [List.append_assoc, ← List.replicate_succ']; exact hI
    refine Reach.bind (hV i hi hiX s _ F hI' hr0 (by simp; omega)) ?_
    rintro s2 ⟨c, i1, X, hc, hI2, ho2, hr2, hi1, hd2⟩
    refine Reach.bind (seq hV n i1 s2 L (F ++ X.map Nat.toUInt64) (by omega) (by omega) hI2 hr2 (by omega)) ?_
    rintro s3 ⟨cs, i2, Xs, hcs, hI3, ho3, hr3, hi2, hd3⟩
    refine Reach.done ⟨c ++ cs, i2, X ++ Xs, ?_, by rw [List.map_append, ← List.append_assoc]; exact hI3,
      by rw [ho3, ho2, List.append_assoc], hr3, by omega, fun hd => ?_⟩
    · have hc' : CG E K (L.length + n) i s.o.length c i1 X := by simpa using hc
      have hcs' : CGs E K L.length i1 (s.o.length + c.length) n cs i2 Xs := by
        have : s2.o.length = s.o.length + c.length := by rw [ho2]; simp
        rw [← this]; exact hcs
      exact .cons hc' hcs'
    · obtain ⟨e1, r1⟩ := hd2 (by simp; omega)
      obtain ⟨e2, r2⟩ := hd3 hd
      exact ⟨by rw [e1, e2]; rfl, by rw [r2, r1]⟩

theorem st_call (hS : S.OK E) (s : GS) (n D : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 7)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = D) (hD : D < bsize s.t) :
    st S s = ⟨s.x, if E.rng (bsize s.o) (bget s.t D) then g15 s.r 6 n else g16 (g15 s.r 6 n),
      s.o ++ E.jmp 1 (bsize s.o) (bget s.t D), s.k, s.t, s.f⟩ := by
  unfold st; rw [hS.item_call _ _ _ _ _ _ hc, ha, hn, if_pos hD]

theorem st_call_bad (hS : S.OK E) (s : GS) (n D : UInt64) (hn : bget s.r 6 - 1 = n) (hc : bget s.k ((bget s.r 6 - 1) * 3) = 7)
    (ha : bget s.k ((bget s.r 6 - 1) * 3 + 1) = D) (hD : ¬ D < bsize s.t) :
    st S s = ⟨s.x, g16 (g15 s.r 6 n), s.o, s.k, s.t, s.f⟩ := by
  unfold st; rw [hS.item_call _ _ _ _ _ _ hc, ha, hn, if_neg hD]

/-- CALL, for any source and emitters -/
theorem v_call (hS : S.OK E) (hE : E.OK) {K i} (hX : K.X.length < 2 ^ 31) (hi : i < K.X.length)
    (IH : ∀ j, i < j → VS S E K j) (ht : tg K.X i = 8) : VS S E K i := by
  intro hiX s L F hI hr0 hB
  refine Reach.step (live_of hI (by simp)) ?_
  rw [st_visit hS hI]
  obtain ⟨hl6, h0, h6⟩ := r6_get hI hr0 L.length.toUInt64
  have hx : bget s.x i.toUInt64 = 8 := by rw [hI.x, tg_u _ _ (by omega), ht]
  have hv1 : bget s.x (i.toUInt64 + 1) = tg K.X (i + 1) := by rw [hI.x]; exact tg_u1 _ i 1 (by omega)
  have hv2 : bget s.x (i.toUInt64 + 2) = tg K.X (i + 2) := by rw [hI.x]; exact tg_u1 _ i 2 (by omega)
  rw [hS.visit_call _ _ _ _ (by rw [h0]; exact hx), h0, h6, hv1, hv2]
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
  refine Reach.bind (seq (i0 := i + 3) (fun j hj => IH j (by omega)) _ (i + 3) _ (L ++ [(7, tg K.X (i + 1), 0)]) F (Nat.le_refl _) (by omega)
    hI1 hra (by simp; omega)) ?_
  rintro s2 ⟨c, i2, X, hc, hI2, ho2, hr2, hi2, hd2⟩
  refine Reach.step (live_of hI2 (by simp)) ?_
  obtain ⟨n2, c2, a2, -⟩ := top_item hI2
  have ht2 : s2.t = K.T := hI2.t
  by_cases hD' : ¬ tg K.X (i + 1) < bsize s2.t
  · rw [st_call_bad hS s2 _ _ n2 c2 a2 hD']
    obtain ⟨p1, -, -⟩ := r6set s2.r hI2.rl L.length.toUInt64
    exact Reach.error (g16_err _ p1)
  have hD : tg K.X (i + 1) < bsize s2.t := Classical.not_not.mp hD'
  rw [st_call hS s2 _ _ n2 c2 a2 hD]
  obtain ⟨p1, p2, p3⟩ := r6set s2.r hI2.rl L.length.toUInt64
  by_cases hg' : ¬ E.rng (bsize s2.o) (bget s2.t (tg K.X (i + 1))) = true
  · rw [if_neg hg']; exact Reach.error (g16_err _ p1)
  have hg := Classical.not_not.mp hg'
  rw [if_pos hg]
  have jl := hE.jmp_len 1 (bsize s2.o) (bget s2.t (tg K.X (i + 1)))
  by_cases hbig : 2 ^ 24 ≤ (s2.o ++ E.jmp 1 (bsize s2.o) (bget s2.t (tg K.X (i + 1)))).length
  · exact Reach.toobig ⟨hbig, by have := hI2.ol; have := hE.jl_le; simp [jl]; omega⟩
  have hI3 := inv_mk hI2 (g15 s2.r 6 L.length.toUInt64) s2.k (s2.o ++ E.jmp 1 (bsize s2.o) (bget s2.t (tg K.X (i + 1)))) L
    (fun j a b => p3 j b) p1 (by simp only [g15]; rw [p2]) (stk_pop hI2.stk) hI2.kl (by omega) (by omega)
  have hl2 : s2.o.length = s.o.length + c.length := by rw [ho2]; simp
  refine Reach.done ⟨c ++ E.jmp 1 (s.o.length + c.length).toUInt64 (bget K.T (tg K.X (i + 1))), i2, X, ?_, hI3, ?_, ?_, by omega,
    fun hd => ?_⟩
  · exact .call ht hq (by rw [← ht2]; exact hD) (by simpa using hc) (by rw [← ulen _ _ hl2, ← ht2]; exact hg)
  · simp only; rw [ulen _ _ hl2, ho2, ht2]; simp
  · simp only [g15]; rw [p3 0 (by decide), hr2]
  · obtain ⟨e, r3⟩ := hd2 (by simp; omega)
    refine ⟨e, ?_⟩
    simp only [g15]; rw [p3 3 (by decide), r3]; simp only [g15]
    rw [hr1, if_neg (by decide), if_neg (by decide), rget _ hI.rl 6 3 _ (by decide), if_neg (by decide)]
end inv

/-! ## the RISC-V instance: today's Gen, today's lemmas -/

def rvEm : Em := ⟨fun v o => g21 (g23 o 5 v), 21, fun d a b => [g13 d a b], 1, fun a b => g14 a b == 1⟩
def rvSrc : Src := ⟨g36, g37⟩

theorem rvEm_ok : rvEm.OK where
  pi_const := pi_const
  const_le := fun v o => by have := g23_len o 5 v; show (g21 _).length ≤ _; rw [g21_len]; show _ ≤ _ + 21; omega
  jmp_len := fun _ _ _ => rfl
  cb_le := by decide
  jl_le := by decide

theorem rvSrc_ok : rvSrc.OK rvEm where
  item_visit := g37_visit
  visit_const := g36_const
  visit_call := g36_call
  item_call := fun x r o k t f hc => by
    show g37 x r o k t f = _
    rw [g37_t7 _ _ _ _ _ _ hc]
    by_cases h : bget k ((bget r 6 - 1) * 3 + 1) < bsize t
    · rw [if_pos h, if_pos h, g19_eq]; rfl
    · rw [if_neg h, if_neg h]

/-- the generic step at the RISC-V source is GenRef's step, so is `Reach` -/
theorem st_rv (s : GS) : st rvSrc s = GenRef.st s := rfl
theorem it_rv : ∀ (n : Nat) (s : GS), it rvSrc n s = GenRef.it n s
  | 0, _ => rfl
  | n + 1, s => it_rv n (GenRef.st s)
theorem reach_rv {s : GS} {P : GS → Prop} (h : Reach rvSrc s P) : GenRef.Reach s P := by
  obtain ⟨m, a, b⟩ := h
  exact ⟨m, fun j hj => by rw [← it_rv]; exact a j hj, by rw [← it_rv]; exact b⟩

/-! the generic relation at the RISC-V emitters is GenRef's (on the prototyped node kinds) -/
mutual
theorem cg_rv {K : Cx} : ∀ {d i h c i' X}, CG rvEm K d i h c i' X → GenRef.CG K d i h c i' X
  | _, _, _, _, _, _, .const t => .const t
  | _, _, _, _, _, _, .call t a b cs r => .call t a b (cgs_rv cs) (by simpa [rvEm] using r)
theorem cgs_rv {K : Cx} : ∀ {d i h n c i' X}, CGs rvEm K d i h n c i' X → GenRef.CGs K d i h n c i' X
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, _, .cons a b => .cons (cg_rv a) (cgs_rv b)
end

/-- GenRef's CONST theorem, recovered from the generic one -/
theorem v_const_rv {K s L F d i} (hI : Inv K s (L ++ [(1, 0, 0)]) F) (hr0 : bget s.r 0 = i.toUInt64) (hi : i < 2 ^ 31)
    (hiX : i < K.X.length) (ht : tg K.X i = 1) : GenRef.Reach s (GenRef.VPost K s L F d i) := by
  obtain ⟨m, a, b⟩ := reach_rv (v_const rvSrc_ok rvEm_ok (d := d) hI hr0 hi hiX ht)
  refine ⟨m, a, ?_⟩
  rcases b with ⟨c, i', X, h1, h2⟩ | b
  · exact .inl ⟨c, i', X, cg_rv h1, h2⟩
  · exact .inr b
end GenEmit
