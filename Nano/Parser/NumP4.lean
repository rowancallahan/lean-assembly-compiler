/- Nano/Parser/NumP4: `u31` / `u32` (lw and isL of a node), `u17` (spineLet), `u16` (leaves), `u33` (shapeOk). -/
import Nano.Parser.NumP3
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- what a run of the lw machine from a node returns -/
def LR (bs : List (Nat × List Bool)) (L : List UInt64) (c' : Nat) (r : LO) : Prop :=
  r.2.2.2.2 = 1 → encB bs <+: r.1 ∧ r.1.length < 2 ^ 42 ∧ L <+: r.2.1 ∧ r.2.1.length < 2 ^ 42 ∧ r.2.2.1 = u L.length ∧
    r.2.2.2.1 = u c'

/-- `u31`: lw of the node at c -/
theorem u31_ok {x d : Buf} {np : Nat} {ws : List Nat} (hC : LC x d ws) {f : Nat} {e : Nd} {rest : Buf} {c : Nat}
    {bs : List (Nat × List Bool)} {b : Buf} (hf : e.ser.length ≤ f) (hnb : NB np e) (hx : x.drop c = e.ser ++ rest)
    (hc : 0 < c) (hb : encB bs <+: b) (hbl : b.length < 2 ^ 42) (hs : ∀ r ∈ bs, r.1 < 2 ^ 32) :
    LR bs ((NumSpec.lw f ws (envOf bs) e).map w2) (c + e.ser.length) (u31 x d b (u (encB bs).length) (u c)) := by
  have hQ : QE (LR bs ((NumSpec.lw f ws (envOf bs) e).map w2) (c + e.ser.length)) := fun r h h1 => absurd h1 h
  have e27 : u27 bnew 0 0 0 0 = [0, 0, 0] := by decide
  have h0 : LI b bs bnew [] (u27 bnew 0 0 0 0) ([] ++ [(0, 0, 0)]) := by
    rw [e27]; exact ⟨hb, hbl, List.nil_prefix, by simp [bnew], by simp [encT], by simp, hs⟩
  have := lw_all hC f e _ bs [] [] c rest b bnew (u27 bnew 0 0 0 0) hf hnb hQ hx hc h0 (by
    intro b1 v1 t1 hI n
    cases n with
    | zero => exact hQ _ (by simp [u28])
    | succ n =>
      simp only [List.nil_append, List.length_nil, show u 0 = 0 from rfl, u28, show ((0 : UInt64) == 0) = true from rfl,
        if_true]
      intro _
      exact ⟨hI.pb, hI.lb, by simpa using hI.pv, hI.lv, by simp, rfl⟩)
  exact this 16777216

/-- `u32`: isL of the node at c (1 / 0; 2 error) -/
theorem u32_ok {x d : Buf} {np : Nat} {ws : List Nat} (hC : LC x d ws) {f : Nat} {e : Nd} {rest : Buf} {c : Nat}
    {bs : List (Nat × List Bool)} {b : Buf} (hf : e.ser.length ≤ f) (hnb : NB np e) (hx : x.drop c = e.ser ++ rest)
    (hc : 0 < c) (hb : encB bs <+: b) (hbl : b.length < 2 ^ 42) (hs : ∀ r ∈ bs, r.1 < 2 ^ 32) :
    (u32 x d b (u (encB bs).length) (u c)).2 ≠ 2 →
      (u32 x d b (u (encB bs).length) (u c)).2 = w2 (NumSpec.isL f ws (envOf bs) e) ∧
      encB bs <+: (u32 x d b (u (encB bs).length) (u c)).1 ∧ (u32 x d b (u (encB bs).length) (u c)).1.length < 2 ^ 42 := by
  have h := u31_ok hC hf hnb hx hc hb hbl hs
  unfold u32
  generalize u31 x d b _ _ = R at h ⊢
  obtain ⟨b1, v, vt, e', ok⟩ := R
  simp only [LR] at h ⊢
  by_cases hok : ok = 1
  · subst hok
    obtain ⟨p1, p2, p3, p3', p4, -⟩ := h rfl
    simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]
    intro _
    refine ⟨?_, p1, p2⟩
    subst p4
    unfold NumSpec.isL
    generalize NumSpec.lw f ws (envOf bs) e = L at p3 ⊢
    have hl : L.length < 2 ^ 42 := by have := p3.length_le; simp at this; omega
    rcases L with _ | ⟨a, _ | ⟨a', L⟩⟩
    · simp [show (u 0 == 1) = false from rfl, w2]
    · have : bget v 0 = w2 a := by
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

theorem u14_succ (n : Nat) (x w : Buf) (t : UInt64) : u14 (n + 1) x w t =
    if t == 0 then 0
    else
      let q := bget w (t - 1);
      let g := bget x q;
      if g == 5 then 1
      else if g == 4 then
        (let b := u15 x (u15 x (q + 2));
         let e := u15 x b;
         if e == 0 then 2 else u14 n x (u20 (u20 w (t - 1) e) t b) (t + 1))
      else u14 n x w (t - 1) := rfl

theorem upred (n : Nat) (h : n + 1 < 2 ^ 64) : u (n + 1) - 1 = u n := by rw [u1, usub (by omega) h]; rfl

theorem pop_rd {ps : List (Nd × Nat × Nat)} {p : Nd × Nat × Nat} {w : Buf}
    (h : (ps ++ [p]).map (fun p => u p.2.2) <+: w) (hl : w.length < 2 ^ 62) :
    bget w (u (ps ++ [p]).length - 1) = u p.2.2 := by
  have hl2 := h.length_le; simp at hl2
  rw [List.length_append, List.length_singleton, upred _ (by omega), bget_pre h (by simp) (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- `u14`: spineLet of the nodes on the work stack (any) -/
theorem u14_ok {x : Buf} {np : Nat} (hxl : x.length < 2 ^ 23) : ∀ (n : Nat) (ps : List (Nd × Nat × Nat)) (w : Buf),
    ps.map (fun p => u p.2.2) <+: w → w.length + n < 2 ^ 40 → (∀ p ∈ ps, SP x np p) →
    u14 n x w (u ps.length) = 2 ∨ u14 n x w (u ps.length) = w2 (ps.any fun p => NumSpec.spineLet p.2.1 p.1)
  | 0, _, _, _, _, _ => Or.inl rfl
  | n + 1, ps, w, hw, hwl, hps => by
    rcases List.eq_nil_or_concat ps with h0 | ⟨ps0, p, h0⟩
    · subst h0; right; rw [u14_succ]; rfl
    · rw [List.concat_eq_append] at h0; subst h0
      have hl2 := hw.length_le; simp at hl2
      obtain ⟨⟨r, hx⟩, hf, hnb, hc⟩ := hps p (by simp)
      have hps0 : ∀ q ∈ ps0, SP x np q := fun q hq => hps q (by simp [hq])
      have hcl := drop_len hx (ser_pos _)
      have ht0 : (u (ps0 ++ [p]).length == 0) = false := by rw [u0, ueq (by simp; omega) (by omega)]; simp
      rw [u14_succ, ht0]
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
              if e2 == 0 then 2 else u14 n x (u20 (u20 w (u (ps0 ++ [(e, f' + 1, q)]).length - 1) e2) (u (ps0 ++ [(e, f' + 1, q)]).length) b)
                (u (ps0 ++ [(e, f' + 1, q)]).length + 1))
           else u14 n x w (u (ps0 ++ [(e, f' + 1, q)]).length - 1)) = 2 ∨
          (if (hdr e).getD 0 0 == 5 then 1
           else if (hdr e).getD 0 0 == 4 then
             (let b := u15 x (u15 x (u q + 2));
              let e2 := u15 x b;
              if e2 == 0 then 2 else u14 n x (u20 (u20 w (u (ps0 ++ [(e, f' + 1, q)]).length - 1) e2) (u (ps0 ++ [(e, f' + 1, q)]).length) b)
                (u (ps0 ++ [(e, f' + 1, q)]).length + 1))
           else u14 n x w (u (ps0 ++ [(e, f' + 1, q)]).length - 1)) =
            w2 ((ps0 ++ [(e, f' + 1, q)]).any fun p => NumSpec.spineLet p.2.1 p.1) := by
        intro h5 h4 hsl
        simp only [h5, h4, Bool.false_eq_true, if_false]
        rw [List.length_append, List.length_singleton, upred _ (by omega)]
        have := u14_ok hxl n ps0 w ((by simp : ps0.map (fun p => u p.2.2) <+: (ps0 ++ [(e, f' + 1, q)]).map (fun p => u p.2.2)).trans hw)
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
        have := u14_ok hxl n (ps0 ++ [(el, f', q + 2 + a.ser.length + b.ser.length + t.ser.length), (t, f', q + 2 + a.ser.length + b.ser.length)]) _
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

end NumP
