/- Nano/Parser/NumP4: `u31` / `u32` (lw and isL of a node), `u17` (spineLet), `u16` (leaves), `u33` (shapeOk). -/
import Nano.Parser.NumP3
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- what a run of the lw machine from a node returns -/
def LR (bs : List (Nat × List Bool)) (L : List UInt64) (c' : Nat) (r : LO) : Prop :=
  r.2.2.2.2.1 = 1 → encB bs <+: r.1 ∧ r.1.length < 2 ^ 42 ∧ L <+: r.2.1 ∧ r.2.1.length < 2 ^ 42 ∧ r.2.2.1 = u L.length ∧
    r.2.2.2.1 = u c' ∧ r.2.2.2.2.2.length < 2 ^ 42

theorem u20_len (b : Buf) (j v : UInt64) : (u20 b j v).length ≤ b.length + 1 := by
  unfold u20; split <;> simp [bset, bpush]

theorem u63_eq {p w : Buf} (hp : p.length < 2 ^ 62) (hw : w.length < 2 ^ 62) :
    u63 p w = if p.length < 2 ^ 39 ∧ w.length < 2 ^ 39 then 1 else 0 := by
  unfold u63
  have e : (549755813888 : UInt64) = u (2 ^ 39) := rfl
  simp only [bsize_u, e, ult (show p.length < 2 ^ 64 by omega) (show 2 ^ 39 < 2 ^ 64 by omega),
    ult (show w.length < 2 ^ 64 by omega) (show 2 ^ 39 < 2 ^ 64 by omega)]
  by_cases h1 : p.length < 2 ^ 39 <;> by_cases h2 : w.length < 2 ^ 39 <;> simp [h1, h2]

theorem u63_one {p w : Buf} (hp : p.length < 2 ^ 62) (hw : w.length < 2 ^ 62) (h : (u63 p w == 1) = true) :
    p.length < 2 ^ 39 ∧ w.length < 2 ^ 39 := by
  rw [u63_eq hp hw] at h
  by_cases hs : p.length < 2 ^ 39 ∧ w.length < 2 ^ 39
  · exact hs
  · rw [if_neg hs] at h; exact absurd h (by decide)

theorem u63_not {p w : Buf} (hp : p.length < 2 ^ 62) (hw : w.length < 2 ^ 62) (hs : p.length < 2 ^ 39 ∧ w.length < 2 ^ 39) :
    (u63 p w == 1) = true := by
  rw [u63_eq hp hw, if_pos hs]; rfl

/-- `u31`: lw of the node at c -/
theorem u31_ok {x d : Buf} {np : Nat} {ws : List Nat} (hC : LC x d ws) {f : Nat} {e : Nd} {rest : Buf} {c : Nat}
    {bs : List (Nat × List Bool)} {b : Buf} (hf : e.ser.length ≤ f) (hnb : NB np e) (hx : x.drop c = e.ser ++ rest)
    (hc : 0 < c) (hb : encB bs <+: b) (hbl : b.length < 2 ^ 42) (hs : ∀ r ∈ bs, r.1 < 2 ^ 32) {v w : Buf}
    (hv : v.length < 2 ^ 62) (hw : w.length < 2 ^ 62) :
    LR bs ((NumSpec.lw f ws (envOf bs) e).map w2) (c + e.ser.length) (u31 x d b (u (encB bs).length) v w (u c)) := by
  unfold u31
  by_cases h63 : (u63 v w == 1) = true
  · rw [if_pos h63]
    obtain ⟨hv', hw'⟩ := u63_one hv hw h63
    have hQ : QE (LR bs ((NumSpec.lw f ws (envOf bs) e).map w2) (c + e.ser.length)) := fun r h h1 => absurd h1 h
    have hu := u27_ok (ts := []) (t := w) (by simp [encT]) (by omega) (by simp) 0 0 0
    have h0 : LI b bs v [] (u27 w 0 0 0 0) ([] ++ [(0, 0, 0)]) :=
      ⟨hb, hbl, List.nil_prefix, by omega, hu.1, by have h2 : (u27 w 0 0 0 0).length ≤ max w.length 3 := hu.2; omega, hs⟩
    have := lw_all hC f e _ bs [] [] c rest b v (u27 w 0 0 0 0) hf hnb hQ hx hc h0 (by
      intro b1 v1 t1 hI n
      cases n with
      | zero => exact hQ _ (by simp [u28])
      | succ n =>
        simp only [List.nil_append, List.length_nil, show u 0 = 0 from rfl, u28, show ((0 : UInt64) == 0) = true from rfl,
          if_true]
        intro _
        exact ⟨hI.pb, hI.lb, by simpa using hI.pv, hI.lv, by simp, rfl, hI.lt⟩)
    exact this 16777216
  · rw [if_neg h63]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)

/-- `u32`: isL of the node at c (1 / 0; 2 error) -/
theorem u32_ok {x d : Buf} {np : Nat} {ws : List Nat} (hC : LC x d ws) {f : Nat} {e : Nd} {rest : Buf} {c : Nat}
    {bs : List (Nat × List Bool)} {b : Buf} (hf : e.ser.length ≤ f) (hnb : NB np e) (hx : x.drop c = e.ser ++ rest)
    (hc : 0 < c) (hb : encB bs <+: b) (hbl : b.length < 2 ^ 42) (hs : ∀ r ∈ bs, r.1 < 2 ^ 32) {v w : Buf}
    (hv : v.length < 2 ^ 62) (hw : w.length < 2 ^ 62) :
    (u32 x d b (u (encB bs).length) v w (u c)).2.1 ≠ 2 →
      (u32 x d b (u (encB bs).length) v w (u c)).2.1 = w2 (NumSpec.isL f ws (envOf bs) e) ∧
      encB bs <+: (u32 x d b (u (encB bs).length) v w (u c)).1 ∧ (u32 x d b (u (encB bs).length) v w (u c)).1.length < 2 ^ 42 ∧
      (u32 x d b (u (encB bs).length) v w (u c)).2.2.1.length < 2 ^ 42 ∧
      (u32 x d b (u (encB bs).length) v w (u c)).2.2.2.length < 2 ^ 42 := by
  have h := u31_ok hC hf hnb hx hc hb hbl hs hv hw
  unfold u32
  generalize u31 x d b _ _ _ _ = R at h ⊢
  obtain ⟨b1, v1, vt, e', ok, w1⟩ := R
  simp only [LR] at h ⊢
  by_cases hok : ok = 1
  · subst hok
    obtain ⟨p1, p2, p3, p3', p4, -, p5⟩ := h rfl
    simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]
    intro _
    refine ⟨?_, p1, p2, p3', p5⟩
    subst p4
    unfold NumSpec.isL
    generalize NumSpec.lw f ws (envOf bs) e = L at p3 ⊢
    have hl : L.length < 2 ^ 42 := by have := p3.length_le; simp at this; omega
    rcases L with _ | ⟨a, _ | ⟨a', L⟩⟩
    · simp [show (u 0 == 1) = false from rfl, w2]
    · have : bget v1 0 = w2 a := by
        rw [show (0 : UInt64) = u 0 from rfl, bget_pre p3 (by simp) (by omega)]; rfl
      simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, show (u (0 + 1) == 1) = true from rfl, if_true, this]
      cases a <;> rfl
    · have : (u (L.length + 1 + 1) == 1) = false := by rw [u1, ueq (by simp at hl; omega) (by omega)]; simp
      simp only [List.map_cons, List.length_cons, List.length_map, this]
      simp [w2]
  · simp only [show (ok == 1) = false by simpa using hok, Bool.false_eq_true, if_false]
    intro h2; exact absurd rfl h2

/-- the node is a shift -/
def shN : Nd → Bool
  | .bin op _ _ => NumSpec.isShift op
  | _ => false

theorem tag_rd {x : Buf} {e : Nd} {r : Buf} {q : Nat} (hx : x.drop q = e.ser ++ r) (hl : x.length < 2 ^ 62) :
    bget x (u q) = (hdr e).getD 0 0 := by
  have := rdh hx hl (k := 0) (by have := hdr_pos e; omega); simpa using this

theorem tag1_rd {x : Buf} {e : Nd} {r : Buf} {q : Nat} (hx : x.drop q = e.ser ++ r) (hl : x.length < 2 ^ 62)
    (h : 1 < (hdr e).length) : bget x (u q + 1) = (hdr e).getD 1 0 := by
  rw [u1, uadd]; exact rdh hx hl h

theorem u34_ok {x : Buf} {np : Nat} {e : Nd} {r : Buf} {q : Nat} (hx : x.drop q = e.ser ++ r) (hl : x.length < 2 ^ 62)
    (hnb : NB np e) : u34 x (u q) = w2 (shN e) := by
  unfold u34
  rw [tag_rd hx hl]
  cases e with
  | bin op a b =>
    rw [tag1_rd hx hl (by simp [hdr])]
    simp only [hdr, List.getD_cons_zero, List.getD_cons_succ, show ((3 : UInt64) == 3) = true from rfl, if_true, shN,
      NumSpec.isShift]
    obtain ⟨hop, -, -⟩ := hnb
    rw [show (6 : UInt64) = u 6 from rfl, show (7 : UInt64) = u 7 from rfl, ueq (by omega) (by omega),
      ueq (by omega) (by omega)]
    by_cases h6 : op = 6
    · subst h6; rfl
    · by_cases h7 : op = 7
      · subst h7; rfl
      · simp [h6, h7, w2]
  | _ => simp [hdr, shN, w2]

/-- a node on a work stack: its position, fuel, bounds -/
def SP (x : Buf) (np : Nat) (p : Nd × Nat × Nat) : Prop :=
  (∃ r, x.drop p.2.2 = p.1.ser ++ r) ∧ p.1.ser.length ≤ p.2.1 ∧ NB np p.1 ∧ 0 < p.2.2

/-- `u14`'s result word (the old value form) -/
def U14 : Nat → Buf → Buf → UInt64 → UInt64
  | 0, x, w, t => 2
  | n + 1, x, w, t =>
    if t == 0 then 0
    else
      let q := bget w (t - 1);
      let g := bget x q;
      if g == 5 then 1
      else if g == 4 then
        (let b := u15 x (u15 x (q + 2));
         let e := u15 x b;
         if e == 0 then 2 else U14 n x (u20 (u20 w (t - 1) e) t b) (t + 1))
      else U14 n x w (t - 1)

theorem u14_snd (x : Buf) : ∀ (n : Nat) (w : Buf) (t : UInt64), (u14 n x w t).2 = U14 n x w t
  | 0, w, t => rfl
  | n + 1, w, t => by
    unfold u14 U14
    dsimp only
    split
    · rfl
    · split
      · rfl
      · split
        · split
          · rfl
          · exact u14_snd x n _ _
        · exact u14_snd x n _ _

theorem u14_len (x : Buf) : ∀ (n : Nat) (w : Buf) (t : UInt64), (u14 n x w t).1.length ≤ w.length + 2 * n
  | 0, w, t => by simp [u14]
  | n + 1, w, t => by
    unfold u14
    dsimp only
    split
    · simp
    · split
      · simp
      · split
        · split
          · simp
          · have h1 := u14_len x n (u20 (u20 w (t - 1) (u15 x (u15 x (u15 x (bget w (t - 1) + 2))))) t
              (u15 x (u15 x (bget w (t - 1) + 2)))) (t + 1)
            have h2 := u20_len (u20 w (t - 1) (u15 x (u15 x (u15 x (bget w (t - 1) + 2))))) t (u15 x (u15 x (bget w (t - 1) + 2)))
            have h3 := u20_len w (t - 1) (u15 x (u15 x (u15 x (bget w (t - 1) + 2))))
            omega
        · have := u14_len x n w (t - 1); omega

theorem U14_succ (n : Nat) (x w : Buf) (t : UInt64) : U14 (n + 1) x w t =
    if t == 0 then 0
    else
      let q := bget w (t - 1);
      let g := bget x q;
      if g == 5 then 1
      else if g == 4 then
        (let b := u15 x (u15 x (q + 2));
         let e := u15 x b;
         if e == 0 then 2 else U14 n x (u20 (u20 w (t - 1) e) t b) (t + 1))
      else U14 n x w (t - 1) := rfl

theorem upred (n : Nat) (h : n + 1 < 2 ^ 64) : u (n + 1) - 1 = u n := by rw [u1, usub (by omega) h]; rfl

theorem pop_rd {ps : List (Nd × Nat × Nat)} {p : Nd × Nat × Nat} {w : Buf}
    (h : (ps ++ [p]).map (fun p => u p.2.2) <+: w) (hl : w.length < 2 ^ 62) :
    bget w (u (ps ++ [p]).length - 1) = u p.2.2 := by
  have hl2 := h.length_le; simp at hl2
  rw [List.length_append, List.length_singleton, upred _ (by omega), bget_pre h (by simp) (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- `U14`: spineLet of the nodes on the work stack (any) -/
theorem U14_ok {x : Buf} {np : Nat} (hxl : x.length < 2 ^ 23) : ∀ (n : Nat) (ps : List (Nd × Nat × Nat)) (w : Buf),
    ps.map (fun p => u p.2.2) <+: w → w.length + n < 2 ^ 40 → (∀ p ∈ ps, SP x np p) →
    U14 n x w (u ps.length) = 2 ∨ U14 n x w (u ps.length) = w2 (ps.any fun p => NumSpec.spineLet p.2.1 p.1)
  | 0, _, _, _, _, _ => Or.inl rfl
  | n + 1, ps, w, hw, hwl, hps => by
    rcases List.eq_nil_or_concat ps with h0 | ⟨ps0, p, h0⟩
    · subst h0; right; rw [U14_succ]; rfl
    · rw [List.concat_eq_append] at h0; subst h0
      have hl2 := hw.length_le; simp at hl2
      obtain ⟨⟨r, hx⟩, hf, hnb, hc⟩ := hps p (by simp)
      have hps0 : ∀ q ∈ ps0, SP x np q := fun q hq => hps q (by simp [hq])
      have hcl := drop_len hx (ser_pos _)
      have ht0 : (u (ps0 ++ [p]).length == 0) = false := by rw [u0, ueq (by simp; omega) (by omega)]; simp
      rw [U14_succ, ht0]
      simp only [Bool.false_eq_true, if_false]
      rw [pop_rd hw (by omega), tag_rd hx (by omega)]
      obtain ⟨e, f, q⟩ := p
      simp only at hx hf hnb hc hcl ⊢
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by have := ser_pos e; omega⟩
      have hpop : ((hdr e).getD 0 0 == 5) = false → ((hdr e).getD 0 0 == 4) = false → NumSpec.spineLet (f' + 1) e = false →
          (if (hdr e).getD 0 0 == 5 then 1
           else if (hdr e).getD 0 0 == 4 then
             (let b := u15 x (u15 x (u q + 2));
              let e2 := u15 x b;
              if e2 == 0 then 2 else U14 n x (u20 (u20 w (u (ps0 ++ [(e, f' + 1, q)]).length - 1) e2) (u (ps0 ++ [(e, f' + 1, q)]).length) b)
                (u (ps0 ++ [(e, f' + 1, q)]).length + 1))
           else U14 n x w (u (ps0 ++ [(e, f' + 1, q)]).length - 1)) = 2 ∨
          (if (hdr e).getD 0 0 == 5 then 1
           else if (hdr e).getD 0 0 == 4 then
             (let b := u15 x (u15 x (u q + 2));
              let e2 := u15 x b;
              if e2 == 0 then 2 else U14 n x (u20 (u20 w (u (ps0 ++ [(e, f' + 1, q)]).length - 1) e2) (u (ps0 ++ [(e, f' + 1, q)]).length) b)
                (u (ps0 ++ [(e, f' + 1, q)]).length + 1))
           else U14 n x w (u (ps0 ++ [(e, f' + 1, q)]).length - 1)) =
            w2 ((ps0 ++ [(e, f' + 1, q)]).any fun p => NumSpec.spineLet p.2.1 p.1) := by
        intro h5 h4 hsl
        simp only [h5, h4, Bool.false_eq_true, if_false]
        rw [List.length_append, List.length_singleton, upred _ (by omega)]
        have := U14_ok hxl n ps0 w ((by simp : ps0.map (fun p => u p.2.2) <+: (ps0 ++ [(e, f' + 1, q)]).map (fun p => u p.2.2)).trans hw)
          (by omega) hps0
        simpa [List.any_append, hsl] using this
      cases e with
      | letE s w0 v b => right; simp [hdr, NumSpec.spineLet, w2]
      | ite cc a b t el =>
        simp only [NB] at hnb
        obtain ⟨-, hna, hnb1, hnt, hne⟩ := hnb
        have hx2 : x.drop (q + 2) = a.ser ++ (b.ser ++ (t.ser ++ (el.ser ++ r))) := by
          have h0 : x.drop q = [4, u cc] ++ (a.ser ++ (b.ser ++ (t.ser ++ (el.ser ++ r)))) := by rw [hx]; simp [Nd.ser, toU]
          simpa using drop_shift h0
        have hx3 := drop_shift hx2
        have hx4 := drop_shift hx3
        have hx5 := drop_shift hx4
        have hcl' : q + 2 + a.ser.length + b.ser.length + t.ser.length + el.ser.length ≤ x.length := by
          have := drop_len hx5 (ser_pos el); omega
        simp only [hdr, List.getD_cons_zero, show ((4 : UInt64) == 5) = false from rfl,
          show ((4 : UInt64) == 4) = true from rfl, Bool.false_eq_true, if_false, if_true]
        rw [u2, uadd]
        rcases u15_ok (by omega) hx2 hna with h0 | ⟨h1, -⟩
        · left; rw [h0]; rfl
        rw [h1]
        rcases u15_ok (by omega) hx3 hnb1 with h0 | ⟨h1, -⟩
        · left; rw [h0]; rfl
        rw [h1]
        rcases u15_ok (by omega) hx4 hnt with h0 | ⟨h1, -⟩
        · left; rw [h0]; rfl
        rw [h1]
        have hne0 : (u (q + 2 + a.ser.length + b.ser.length + t.ser.length) == 0) = false := by
          rw [u0, ueq (by omega) (by omega)]; exact decide_eq_false (by omega)
        simp only [hne0, Bool.false_eq_true, if_false]
        have hl0 : ps0.length + 1 < 2 ^ 62 := by omega
        rw [List.length_append, List.length_singleton, upred _ (by omega)]
        have hp0 : ps0.map (fun p => u p.2.2) <+: w :=
          (by simp : ps0.map (fun p => u p.2.2) <+: (ps0 ++ [(Nd.ite cc a b t el, f' + 1, q)]).map (fun p => u p.2.2)).trans hw
        obtain ⟨p1, l1⟩ := u20_push hp0 (by omega) (u (q + 2 + a.ser.length + b.ser.length + t.ser.length))
        simp only [List.length_map] at p1 l1
        have e1 : u ps0.length + 1 = u ((ps0 ++ [(el, f', q + 2 + a.ser.length + b.ser.length + t.ser.length)]).map
            (fun p => u p.2.2)).length := by simp [u1, uadd]
        rw [show u (ps0.length + 1) = u ps0.length + 1 by rw [u1, uadd], e1]
        obtain ⟨p2, l2⟩ := u20_push (vs := (ps0 ++ [(el, f', q + 2 + a.ser.length + b.ser.length + t.ser.length)]).map
            (fun p => u p.2.2)) (by simpa using p1) (by omega) (u (q + 2 + a.ser.length + b.ser.length))
        have e2 : ((ps0 ++ [(el, f', q + 2 + a.ser.length + b.ser.length + t.ser.length)]).map (fun p => u p.2.2)).length + 1 =
          (ps0 ++ [(el, f', q + 2 + a.ser.length + b.ser.length + t.ser.length), (t, f', q + 2 + a.ser.length + b.ser.length)]).length := by simp
        have := U14_ok hxl n (ps0 ++ [(el, f', q + 2 + a.ser.length + b.ser.length + t.ser.length), (t, f', q + 2 + a.ser.length + b.ser.length)]) _
          (by simpa using p2) (by simp at l2 l1; omega) (by
            intro p hp
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hp
            have hf' : t.ser.length ≤ f' ∧ el.ser.length ≤ f' := by simp [Nd.ser] at hf; omega
            rcases hp with hp | rfl | rfl
            · exact hps0 p hp
            · exact ⟨⟨r, hx5⟩, hf'.2, hne, by simp only; omega⟩
            · exact ⟨⟨_, hx4⟩, hf'.1, hnt, by simp only; omega⟩)
        rw [show u ((ps0 ++ [(el, f', q + 2 + a.ser.length + b.ser.length + t.ser.length)]).map (fun p => u p.2.2)).length + 1 =
          u (ps0 ++ [(el, f', q + 2 + a.ser.length + b.ser.length + t.ser.length), (t, f', q + 2 + a.ser.length + b.ser.length)]).length by
            simp [u1, uadd]]
        simp only [List.length_map, List.length_append, List.length_cons, List.length_nil] at this ⊢
        rcases this with h | h
        · exact Or.inl h
        · right; rw [h]; simp [List.any_append, NumSpec.spineLet, Bool.or_comm, Bool.or_left_comm]
      | const _ => exact hpop (by simp [hdr]) (by simp [hdr]) (by simp [NumSpec.spineLet])
      | loc _ _ => exact hpop (by simp [hdr]) (by simp [hdr]) (by simp [NumSpec.spineLet])
      | bin _ _ _ => exact hpop (by simp [hdr]) (by simp [hdr]) (by simp [NumSpec.spineLet])
      | pair _ => exact hpop (by simp [hdr]) (by simp [hdr]) (by simp [NumSpec.spineLet])
      | call _ _ => exact hpop (by simp [hdr]) (by simp [hdr]) (by simp [NumSpec.spineLet])
      | prim _ _ => exact hpop (by simp [hdr]) (by simp [hdr]) (by simp [NumSpec.spineLet])
      | loop _ _ => exact hpop (by simp [hdr]) (by simp [hdr]) (by simp [NumSpec.spineLet])
      | cont _ => exact hpop (by simp [hdr]) (by simp [hdr]) (by simp [NumSpec.spineLet])

theorem u17_ok {x : Buf} {np : Nat} (hxl : x.length < 2 ^ 23) {e : Nd} {f q : Nat} {r : Buf}
    (hx : x.drop q = e.ser ++ r) (hf : e.ser.length ≤ f) (hnb : NB np e) (hq : 0 < q) {w : Buf} (hw : w.length < 2 ^ 62) :
    (u17 x w (u q)).1.length < 2 ^ 62 ∧ ((u17 x w (u q)).2 = 2 ∨ (u17 x w (u q)).2 = w2 (NumSpec.spineLet f e)) := by
  unfold u17
  have e39 : (549755813888 : UInt64) = u (2 ^ 39) := rfl
  simp only [bsize_u, e39, ult (show w.length < 2 ^ 64 by omega) (show 2 ^ 39 < 2 ^ 64 by omega)]
  by_cases hs : w.length < 2 ^ 39
  · rw [if_pos hs]
    have hp := u20_push (vs := []) (v := w) List.nil_prefix (by omega) (u q)
    have h1 : [u q] <+: u20 w 0 (u q) := by have := hp.1; simp only [List.nil_append, List.length_nil] at this; exact this
    have hl : (u20 w 0 (u q)).length ≤ w.length + 1 := u20_len _ _ _
    refine ⟨by have := u14_len x 16777216 (u20 w 0 (u q)) 1; omega, ?_⟩
    rw [u14_snd]
    have := U14_ok hxl 16777216 [(e, f, q)] (u20 w 0 (u q)) (by simpa using h1) (by omega)
      (by intro p hp; simp at hp; subst hp; exact ⟨⟨r, hx⟩, hf, hnb, hq⟩)
    rw [show (1 : UInt64) = u ([(e, f, q)] : List (Nd × Nat × Nat)).length from rfl]; simpa using this
  · simp only [hs, if_false]; refine ⟨hw, ?_⟩; simp

/-- the leaves with their positions -/
def lvP : Nat → Nd → Nat → List (Nd × Nat)
  | f + 1, .bin op a b, pos =>
    if NumSpec.isShift op then [(.bin op a b, pos)] else lvP f a (pos + 2) ++ lvP f b (pos + 2 + a.ser.length)
  | _, e, pos => [(e, pos)]

theorem lvP_fst : ∀ (f : Nat) (e : Nd) (pos : Nat), (lvP f e pos).map Prod.fst = NumSpec.leaves f e
  | 0, e, pos => by cases e <;> simp [lvP, NumSpec.leaves]
  | f + 1, e, pos => by
    cases e with
    | bin op a b =>
      simp only [lvP, NumSpec.leaves]
      split
      · simp
      · simp [lvP_fst f a, lvP_fst f b]
    | _ => simp [lvP, NumSpec.leaves]

theorem u13_succ (n : Nat) (x p : Buf) (pt : UInt64) (w : Buf) (t : UInt64) : u13 (n + 1) x p pt w t =
    if t == 0 then (p, (pt, (w, 1)))
    else
      let q := bget w (t - 1);
      if bget x q == 3 then
        (if u34 x q == 1 then u13 n x (u20 p pt q) (pt + 1) w (t - 1)
         else
           (let e := u15 x (q + 2);
            if e == 0 then (p, (pt, (w, 0)))
            else u13 n x p pt (u20 (u20 w (t - 1) e) t (q + 2)) (t + 1)))
      else u13 n x (u20 p pt q) (pt + 1) w (t - 1) := rfl

theorem u13_len (x : Buf) : ∀ (n : Nat) (p : Buf) (pt : UInt64) (w : Buf) (t : UInt64),
    (u13 n x p pt w t).1.length ≤ p.length + n ∧ (u13 n x p pt w t).2.2.1.length ≤ w.length + 2 * n
  | 0, p, pt, w, t => by simp [u13]
  | n + 1, p, pt, w, t => by
    rw [u13_succ]; dsimp only
    split
    · simp
    · split
      · split
        · have := u13_len x n (u20 p pt (bget w (t - 1))) (pt + 1) w (t - 1); have := u20_len p pt (bget w (t - 1)); omega
        · split
          · simp
          · have := u13_len x n p pt (u20 (u20 w (t - 1) (u15 x (bget w (t - 1) + 2))) t (bget w (t - 1) + 2)) (t + 1)
            have := u20_len (u20 w (t - 1) (u15 x (bget w (t - 1) + 2))) t (bget w (t - 1) + 2)
            have := u20_len w (t - 1) (u15 x (bget w (t - 1) + 2)); omega
      · have := u13_len x n (u20 p pt (bget w (t - 1))) (pt + 1) w (t - 1); have := u20_len p pt (bget w (t - 1)); omega

/-- the leaves of the stack's nodes, top first -/
def lvS (ps : List (Nd × Nat × Nat)) : List (Nd × Nat) := ps.reverse.flatMap fun p => lvP p.2.1 p.1 p.2.2

/-- `u13`: the leaves of the nodes on the work stack, written to p after its prefix P -/
theorem u13_ok {x : Buf} {np : Nat} (hxl : x.length < 2 ^ 23) : ∀ (n : Nat) (ps : List (Nd × Nat × Nat)) (P p w : Buf),
    P <+: p → p.length + n < 2 ^ 40 →
    ps.map (fun p => u p.2.2) <+: w → w.length + n < 2 ^ 40 → (∀ p ∈ ps, SP x np p) →
    (u13 n x p (u P.length) w (u ps.length)).2.2.2 = 1 →
      P ++ (lvS ps).map (fun q => u q.2) <+: (u13 n x p (u P.length) w (u ps.length)).1 ∧
      (u13 n x p (u P.length) w (u ps.length)).2.1 = u (P ++ (lvS ps).map (fun q => u q.2)).length
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [u13] at h
  | n + 1, ps, P, p, w, hP, hpl, hw, hwl, hps, h => by
    rcases List.eq_nil_or_concat ps with h0 | ⟨ps0, p', h0⟩
    · subst h0; simp [u13_succ, lvS, show u 0 = 0 from rfl, hP]
    · rw [List.concat_eq_append] at h0; subst h0
      have hl2 := hw.length_le; simp at hl2
      have hPl := hP.length_le
      obtain ⟨⟨r, hx⟩, hf, hnb, hc⟩ := hps p' (by simp)
      have hps0 : ∀ q ∈ ps0, SP x np q := fun q hq => hps q (by simp [hq])
      have hcl := drop_len hx (ser_pos _)
      have ht0 : (u (ps0 ++ [p']).length == 0) = false := by rw [u0, ueq (by simp; omega) (by omega)]; simp
      have hp0 : ps0.map (fun p => u p.2.2) <+: w :=
        (by simp : ps0.map (fun p => u p.2.2) <+: (ps0 ++ [p']).map (fun p => u p.2.2)).trans hw
      rw [u13_succ, ht0] at h ⊢
      simp only [Bool.false_eq_true, if_false] at h ⊢
      rw [pop_rd hw (by omega), tag_rd hx (by omega), u34_ok hx (by omega) hnb] at h ⊢
      rw [List.length_append, List.length_singleton, upred _ (by omega)] at h ⊢
      obtain ⟨e, f, q⟩ := p'
      simp only at hx hf hnb hc hcl h ⊢
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by have := ser_pos e; omega⟩
      have hleaf : lvP (f' + 1) e q = [(e, q)] →
          (u13 n x (u20 p (u P.length) (u q)) (u P.length + 1) w (u ps0.length)).2.2.2 = 1 →
          P ++ (lvS (ps0 ++ [(e, f' + 1, q)])).map (fun q => u q.2) <+:
            (u13 n x (u20 p (u P.length) (u q)) (u P.length + 1) w (u ps0.length)).1 ∧
          (u13 n x (u20 p (u P.length) (u q)) (u P.length + 1) w (u ps0.length)).2.1 =
            u (P ++ (lvS (ps0 ++ [(e, f' + 1, q)])).map (fun q => u q.2)).length := by
        intro hl h1
        obtain ⟨q1, q2⟩ := u20_push hP (by omega) (u q)
        have e1 : u P.length + 1 = u (P ++ [u q]).length := by simp [u1, uadd]
        rw [e1] at h1 ⊢
        have ih := u13_ok hxl n ps0 (P ++ [u q]) _ w q1 (by omega) hp0 (by omega) hps0 h1
        have e2 : P ++ (lvS (ps0 ++ [(e, f' + 1, q)])).map (fun q => u q.2) = P ++ [u q] ++ (lvS ps0).map (fun q => u q.2) := by
          simp [lvS, hl]
        rw [e2]; exact ih
      cases e with
      | bin op a b =>
        simp only [hdr, List.getD_cons_zero, show ((3 : UInt64) == 3) = true from rfl, if_true] at h ⊢
        by_cases hsh : NumSpec.isShift op
        · simp only [shN, hsh, w2, if_true, show ((1 : UInt64) == 1) = true from rfl] at h ⊢
          exact hleaf (by simp [lvP, hsh]) h
        · simp only [shN, hsh, w2, show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false] at h ⊢
          simp only [NB] at hnb
          obtain ⟨-, hna, hnb1⟩ := hnb
          have hx2 : x.drop (q + 2) = a.ser ++ (b.ser ++ r) := by
            have h0 : x.drop q = [3, u op] ++ (a.ser ++ (b.ser ++ r)) := by rw [hx]; simp [Nd.ser, toU]
            simpa using drop_shift h0
          have hx3 := drop_shift hx2
          have hf' : a.ser.length ≤ f' ∧ b.ser.length ≤ f' := by simp [Nd.ser] at hf; omega
          have hsl : (Nd.bin op a b).ser.length = 2 + a.ser.length + b.ser.length := by simp [Nd.ser]; omega
          rw [u2, uadd] at h ⊢
          rcases u15_ok (by omega) hx2 hna with h0 | ⟨h1, -⟩
          · rw [h0] at h; simp at h
          rw [h1] at h ⊢
          have hne0 : (u (q + 2 + a.ser.length) == 0) = false := by
            rw [u0, ueq (by omega) (by omega)]; exact decide_eq_false (by omega)
          simp only [hne0, Bool.false_eq_true, if_false] at h ⊢
          obtain ⟨p1, l1⟩ := u20_push hp0 (by omega) (u (q + 2 + a.ser.length))
          simp only [List.length_map] at p1 l1
          obtain ⟨p2, l2⟩ := u20_push (vs := (ps0 ++ [(b, f', q + 2 + a.ser.length)]).map (fun p => u p.2.2))
            (by simpa using p1) (by omega) (u (q + 2))
          simp only [List.length_map, List.length_append, List.length_singleton] at p2 l2
          have ih := u13_ok hxl n (ps0 ++ [(b, f', q + 2 + a.ser.length), (a, f', q + 2)]) P p _ hP (by omega)
            (by simpa using p2) (by omega) (by
            intro p hp
            simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hp
            rcases hp with hp | rfl | rfl
            · exact hps0 p hp
            · exact ⟨⟨r, hx3⟩, hf'.2, hnb1, by simp only; omega⟩
            · exact ⟨⟨_, hx2⟩, hf'.1, hna, by simp only; omega⟩)
          have e2 : u (ps0.length + 1) + 1 = u (ps0 ++ [(b, f', q + 2 + a.ser.length), (a, f', q + 2)]).length := by
            simp [u1, uadd]
          rw [e2] at h ⊢
          have e3 : lvS (ps0 ++ [(Nd.bin op a b, f' + 1, q)]) =
              lvS (ps0 ++ [(b, f', q + 2 + a.ser.length), (a, f', q + 2)]) := by
            simp [lvS, lvP, hsh]
          rw [e3]
          exact ih h
      | const _ =>
        simp only [hdr, List.getD_cons_zero] at h ⊢; exact hleaf (by simp [lvP]) h
      | loc _ _ => simp only [hdr, List.getD_cons_zero] at h ⊢; exact hleaf (by simp [lvP]) h
      | ite _ _ _ _ _ => simp only [hdr, List.getD_cons_zero] at h ⊢; exact hleaf (by simp [lvP]) h
      | letE _ _ _ _ => simp only [hdr, List.getD_cons_zero] at h ⊢; exact hleaf (by simp [lvP]) h
      | pair _ => simp only [hdr, List.getD_cons_zero] at h ⊢; exact hleaf (by simp [lvP]) h
      | call _ _ => simp only [hdr, List.getD_cons_zero] at h ⊢; exact hleaf (by simp [lvP]) h
      | prim _ _ => simp only [hdr, List.getD_cons_zero] at h ⊢; exact hleaf (by simp [lvP]) h
      | loop _ _ => simp only [hdr, List.getD_cons_zero] at h ⊢; exact hleaf (by simp [lvP]) h
      | cont _ => simp only [hdr, List.getD_cons_zero] at h ⊢; exact hleaf (by simp [lvP]) h

theorem u16_ok {x : Buf} {np : Nat} (hxl : x.length < 2 ^ 23) {e : Nd} {f q : Nat} {r : Buf} {P p w : Buf}
    (hx : x.drop q = e.ser ++ r) (hf : e.ser.length ≤ f) (hnb : NB np e) (hq : 0 < q) (hP : P <+: p)
    (hp : p.length < 2 ^ 62) (hw : w.length < 2 ^ 62) :
    (u16 x p (u P.length) w (u q)).2.2.2 = 1 →
      P ++ (lvP f e q).map (fun q => u q.2) <+: (u16 x p (u P.length) w (u q)).1 ∧
      (u16 x p (u P.length) w (u q)).2.1 = u (P ++ (lvP f e q).map (fun q => u q.2)).length := by
  unfold u16
  by_cases h63 : (u63 p w == 1) = true
  · rw [if_pos h63]
    obtain ⟨hp', hw'⟩ := u63_one hp hw h63
    have hp1 := u20_push (vs := []) (v := w) List.nil_prefix (by omega) (u q)
    have h1 : [u q] <+: u20 w 0 (u q) := by
      have := hp1.1; simp only [List.nil_append, List.length_nil] at this; exact this
    have hl : (u20 w 0 (u q)).length ≤ w.length + 1 := u20_len _ _ _
    have := u13_ok hxl 16777216 [(e, f, q)] P p (u20 w 0 (u q)) hP (by omega) (by simpa using h1) (by omega)
      (by intro z hz; simp at hz; subst hz; exact ⟨⟨r, hx⟩, hf, hnb, hq⟩)
    rw [show (1 : UInt64) = u ([(e, f, q)] : List (Nd × Nat × Nat)).length from rfl]
    intro h; have := this h; simpa [lvS] using this
  · rw [if_neg h63]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)

theorem u16_len (x p : Buf) (pt : UInt64) (w : Buf) (i : UInt64) (hp : p.length < 2 ^ 62) (hw : w.length < 2 ^ 62) :
    (u16 x p pt w i).1.length < 2 ^ 62 ∧ (u16 x p pt w i).2.2.1.length < 2 ^ 62 := by
  unfold u16
  by_cases h63 : (u63 p w == 1) = true
  · rw [if_pos h63]
    obtain ⟨hp', hw'⟩ := u63_one hp hw h63
    have := u13_len x 16777216 p pt (u20 w 0 i) 1; have := u20_len w 0 i; omega
  · rw [if_neg h63]; exact ⟨hp, hw⟩

/-- the shape rules, left to right (l: an earlier operand is literal-only) -/
def shR (f : Nat) (ws : List Nat) (env : List Bool) : Bool → List Nd → Bool
  | _, [] => true
  | l, e :: es => !NumSpec.spineLet f e && !(shN e && l) && shR f ws env (l || NumSpec.isL f ws env e) es

theorem shR_shapeOk (f : Nat) (ws : List Nat) (env : List Bool) :
    ∀ (ls : List Nd) (l : Bool), shR f ws env l ls = true →
      (!ls.any (NumSpec.spineLet f)) = true ∧
      ∀ j, j < ls.length → shN (ls.getD j (.const 0)) = true → (l || (ls.take j).any (NumSpec.isL f ws env)) = false
  | [], _, _ => by simp
  | e :: es, l, h => by
    simp only [shR, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have ih := shR_shapeOk f ws env es _ h3
    refine ⟨by simp only [List.any_cons, h1, Bool.false_or]; exact ih.1, ?_⟩
    intro j hj hs
    cases j with
    | zero =>
      simp only [List.getD_cons_zero] at hs
      simp only [hs, Bool.true_and] at h2
      simp [h2]
    | succ j =>
      have := ih.2 j (by simpa using hj) (by simpa using hs)
      simp only [Bool.or_eq_false_iff] at this
      simp only [List.take_succ_cons, List.any_cons, Bool.or_eq_false_iff]
      exact ⟨this.1.1, this.1.2, this.2⟩

theorem shapeOk_of {f : Nat} {ws : List Nat} {env : List Bool} {ls : List Nd} (h : shR f ws env false ls = true) :
    NumSpec.shapeOk f ws env ls = true := by
  obtain ⟨h1, h2⟩ := shR_shapeOk f ws env ls false h
  unfold NumSpec.shapeOk
  simp only [h1, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false]
  intro j hj
  simp only [List.mem_range] at hj
  have := h2 j hj
  generalize ls.getD j (Nd.const 0) = y at this ⊢
  cases y with
  | bin op a b =>
    cases hs : NumSpec.isShift op
    · simp [hs]
    · have := this (by simp [shN, hs]); simp [hs] at this ⊢; exact this
  | _ => simp

theorem u33_succ (n : Nat) (x d b : Buf) (bt : UInt64) (p : Buf) (j e l : UInt64) (v w : Buf) :
    u33 (n + 1) x d b bt p j e l v w =
    if j < e then
      (let q := bget p j;
       let (w1, h) := u17 x w q;
       if h == 0 then
         (let (b1, z) := u32 x d b bt v w1 q;
          let (r, z1) := z;
          let (v1, w3) := z1;
          if r == 2 then (b1, (0, (v1, w3)))
          else if u34 x q == 1 then (if l == 1 then (b1, (0, (v1, w3))) else u33 n x d b1 bt p (j + 1) e (l ||| r) v1 w3)
          else u33 n x d b1 bt p (j + 1) e (l ||| r) v1 w3)
       else (b, (0, (v, w1))))
    else (b, (1, (v, w))) := rfl

theorem w2_or (p q : Bool) : w2 p ||| w2 q = w2 (p || q) := by cases p <;> cases q <;> rfl

/-- what `u33` returns -/
def U33Q (bs : List (Nat × List Bool)) (f : Nat) (ws : List Nat) (l : Bool) (ls : List (Nd × Nat))
    (R : Buf × (UInt64 × (Buf × Buf))) : Prop :=
  R.2.1 = 1 → shR f ws (envOf bs) l (ls.map Prod.fst) = true ∧ encB bs <+: R.1 ∧ R.1.length < 2 ^ 42 ∧
    R.2.2.1.length < 2 ^ 62 ∧ R.2.2.2.length < 2 ^ 62

/-- `u33`: shapeOk of the leaves (positions p[j .. e)) -/
theorem u33_ok {x d : Buf} {np : Nat} {ws : List Nat} (hC : LC x d ws) {f : Nat} {bs : List (Nat × List Bool)}
    (hs : ∀ r ∈ bs, r.1 < 2 ^ 32) {p : Buf} (hpl : p.length < 2 ^ 62) :
    ∀ (n : Nat) (ls : List (Nd × Nat)) (W : Buf) (l : Bool) (b v w : Buf),
    (∀ q ∈ ls, (∃ r, x.drop q.2 = q.1.ser ++ r) ∧ q.1.ser.length ≤ f ∧ NB np q.1 ∧ 0 < q.2) →
    encB bs <+: b → b.length < 2 ^ 42 → W.length + ls.length < 2 ^ 40 → W ++ ls.map (fun q => u q.2) <+: p →
    v.length < 2 ^ 62 → w.length < 2 ^ 62 →
    U33Q bs f ws l ls (u33 n x d b (u (encB bs).length) p (u W.length) (u (W.length + ls.length)) (w2 l) v w)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _ => by intro h; simp [u33] at h
  | n + 1, [], W, l, b, v, w, _, hb, hbl, _, _, hv, hw => by
    have : (u W.length < u (W.length + 0)) = False := by rw [ult (by omega) (by omega)]; simp
    simp [U33Q, u33_succ, this, shR, hb, hbl, hv, hw]
  | n + 1, (e, q) :: ls, W, l, b, v, w, hls, hb, hbl, hWl, hWp, hv, hw => by
    unfold U33Q
    have hxl := hC.xl
    obtain ⟨⟨r, hx⟩, hf, hnb, hq⟩ := hls (e, q) (by simp)
    simp only at hx hf hnb hq
    simp only [List.length_cons] at hWl
    have hcl := drop_len hx (ser_pos e)
    have hc1 : (u W.length < u (W.length + ((e, q) :: ls).length)) = True := by
      rw [ult (by omega) (by simp; omega)]; simp
    have hrd : bget p (u W.length) = u q := by
      rw [bget_pre hWp (by simp) (by omega)]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    rw [u33_succ]
    simp only [hc1, if_true, hrd]
    obtain ⟨hw1, h17⟩ := u17_ok hxl hx hf hnb hq hw
    generalize u17 x w (u q) = U at hw1 h17
    obtain ⟨w1, hh⟩ := U
    simp only at hw1 h17 ⊢
    rcases h17 with h2 | hsl
    · subst h2; intro h; simp at h
    subst hsl
    cases hsp : NumSpec.spineLet f e
    · simp only [show w2 false = 0 from rfl, show ((0 : UInt64) == 0) = true from rfl, if_true]
      have hL := u32_ok hC hf hnb hx hq hb hbl hs hv hw1
      generalize u32 x d b _ _ _ _ = R at hL ⊢
      obtain ⟨b1, rr, v1, w3⟩ := R
      simp only at hL ⊢
      by_cases hr2 : rr = 2
      · subst hr2; simp
      obtain ⟨hr, hb1, hbl1, hv1, hw3⟩ := hL hr2
      subst hr
      have hr2' : (w2 (NumSpec.isL f ws (envOf bs) e) == 2) = false := by
        cases NumSpec.isL f ws (envOf bs) e <;> rfl
      simp only [hr2', Bool.false_eq_true, if_false]
      rw [u34_ok hx (by omega) hnb]
      have hW : u W.length + 1 = u (W ++ [u q]).length := by simp [u1, uadd]
      have hE : u (W.length + ((e, q) :: ls).length) = u ((W ++ [u q]).length + ls.length) := by
        simp; congr 1; omega
      have hP : W ++ ((e, q) :: ls).map (fun q => u q.2) = (W ++ [u q]) ++ ls.map (fun q => u q.2) := by simp
      rw [hW, hE, w2_or]
      have hrec := u33_ok hC hs hpl n ls (W ++ [u q]) (l || NumSpec.isL f ws (envOf bs) e) b1 v1 w3
        (fun q hq => hls q (by simp [hq])) hb1 hbl1 (by simp; omega) (by rw [← hP]; exact hWp) (by omega) (by omega)
      cases hsh : shN e
      · simp only [show w2 false = 0 from rfl, show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false]
        intro h
        obtain ⟨r1, r2, r3, r4, r5⟩ := hrec h
        refine ⟨?_, r2, r3, r4, r5⟩
        simp [shR, hsp, hsh, r1]
      · simp only [show w2 true = 1 from rfl, show ((1 : UInt64) == 1) = true from rfl, if_true]
        cases l
        · simp only [show w2 false = 0 from rfl, show ((0 : UInt64) == 1) = false from rfl, Bool.false_eq_true, if_false]
          intro h
          obtain ⟨r1, r2, r3, r4, r5⟩ := hrec h
          refine ⟨?_, r2, r3, r4, r5⟩
          simp [shR, hsp, hsh]; simpa using r1
        · simp [show w2 true = 1 from rfl]
    · simp [show w2 true = 1 from rfl]

end NumP
