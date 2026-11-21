/- Nano/Parser/NumP3: the NODE task of the `lw` machine; `lw_ok`: the machine computes `NumSpec.lw`. -/
import Nano.Parser.NumP2
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- the fixed context: the input and the def table (word 2i+1: def i's result width) -/
structure LC (x d : Buf) (ws : List Nat) : Prop where
  xl : x.length < 2 ^ 23
  dl : d.length = 2 * ws.length
  wl : ws.length < 2 ^ 30
  dw : ∀ i, i < ws.length → d.getD (2 * i + 1) 0 = u (ws.getD i 1)
  wb : ∀ i, i < ws.length → ws.getD i 1 < 2 ^ 32

theorem l_node {x d : Buf} {Q : LO → Prop} (hQ : QE Q) {b bs v vs t ts c} {v1 : Buf} {vt1 : UInt64} {t1 : Buf}
    {tt1 c1 ok : UInt64}
    (hI : LI b bs v vs t (ts ++ [(0, 0, 0)]))
    (h29 : v.length < 2 ^ 40 → t.length < 2 ^ 40 → b.length < 2 ^ 40 →
      u29 x d b (u (encB bs).length) v (u vs.length) t (u ts.length) c = (v1, (vt1, (t1, (tt1, (c1, ok))))))
    (hg : v.length < 2 ^ 40 → t.length < 2 ^ 40 → b.length < 2 ^ 40 → ok = 1 → GL x d Q b (u (encB bs).length) v1 vt1 t1 tt1 c1) :
    GL x d Q b (u (encB bs).length) v (u vs.length) t (u (ts.length + 1)) c := by
  apply gl_top hQ hI
  intro hv ht hb n
  have hts := hI.lts; simp at hts
  simp only [L28, show ((0 : UInt64) == 0) = true from rfl, if_true]
  rw [pop_e ts (by omega), h29 hv ht hb]
  simp only
  by_cases hok : ok = 1
  · subst hok; simp only [show ((1 : UInt64) == 1) = true from rfl, if_true]; exact hg hv ht hb rfl n
  · simp only [show (ok == 1) = false by simpa using hok, Bool.false_eq_true, if_false]
    exact hQ _ (show u 0 ≠ 1 by decide)

/-- reading a header word of the node at c -/
theorem rdh {x : Buf} {e : Nd} {rest : Buf} {c : Nat} (h : x.drop c = e.ser ++ rest) (hl : x.length < 2 ^ 62) {k : Nat}
    (hk : k < (hdr e).length) : bget x (u (c + k)) = (hdr e).getD k 0 := by
  rw [ser_hdr, List.append_assoc] at h
  have := drop_len h (by omega)
  rw [rd h hk (by omega)]

theorem LI.push {b bs v vs t ts} (h : LI b bs v vs t ts) (ht : t.length < 2 ^ 41) (k a c : UInt64) :
    LI b bs v vs (u27 t (u ts.length) k a c) (ts ++ [(k, a, c)]) ∧ (u27 t (u ts.length) k a c).length ≤ t.length + 3 := by
  have h3 := h.pt.length_le; rw [encT_len] at h3
  have := u27_ok h.pt (by omega) (by omega) k a c
  exact ⟨⟨h.pb, h.lb, h.pv, h.lv, this.1, by omega, h.sb⟩, by omega⟩

theorem w2_getD0 (l : List Bool) : (l.map w2).getD 0 0 = w2 (l.getD 0 false) := by cases l <;> rfl
theorem w2_and (p q : Bool) : w2 p &&& w2 q = w2 (p && q) := by cases p <;> cases q <;> rfl

/-- the NODE lemma at fuel f -/
def LN (x d : Buf) (np : Nat) (ws : List Nat) (f : Nat) : Prop :=
  ∀ (e : Nd) (Q : LO → Prop) (bs : List (Nat × List Bool)) (vs : List UInt64) (ts : List T3) (c : Nat) (rest b v t : Buf),
    e.ser.length ≤ f → NB np e → QE Q → x.drop c = e.ser ++ rest → 0 < c →
    LI b bs v vs t (ts ++ [(0, 0, 0)]) →
    LP x d Q bs (vs ++ (NumSpec.lw f ws (envOf bs) e).map w2) ts (c + e.ser.length) →
    GL x d Q b (u (encB bs).length) v (u vs.length) t (u (ts.length + 1)) (u c)

theorem LP.cast {x d Q bs vs vs' ts c c'} (h : LP x d Q bs vs ts c) (h1 : vs' = vs) (h2 : c' = c) :
    LP x d Q bs vs' ts c' := by subst h1 h2; exact h

theorem GL.cast {x d Q b bt v vt vt' t tt tt' c} (h : GL x d Q b bt v vt t tt c) (h1 : vt' = vt) (h2 : tt' = tt) :
    GL x d Q b bt v vt' t tt' c := by subst h1 h2; exact h

theorem lw_seq {x d : Buf} {np : Nat} {ws : List Nat} (hC : LC x d ws) (f : Nat) (ih : LN x d np ws f) :
    ∀ (cs : List Nd) (Q : LO → Prop) (bs : List (Nat × List Bool)) (vs : List UInt64) (ts : List T3) (c : Nat)
      (rest b v t : Buf) (a2 : UInt64),
    (∀ c ∈ cs, c.ser.length ≤ f ∧ NB np c) → cs.length < 2 ^ 32 → QE Q → x.drop c = serL cs ++ rest → 0 < c →
    LI b bs v vs t (ts ++ [(7, u cs.length, a2)]) →
    LP x d Q bs (vs ++ (cs.flatMap (NumSpec.lw f ws (envOf bs))).map w2) ts (c + (serL cs).length) →
    GL x d Q b (u (encB bs).length) v (u vs.length) t (u (ts.length + 1)) (u c)
  | [], Q, bs, vs, ts, c, rest, b, v, t, a2, _, _, hQ, _, _, hI, hP => l_seq0 hQ hI (hP.cast (by simp) (by simp [serL]))
  | e :: cs, Q, bs, vs, ts, c, rest, b, v, t, a2, hcs, hl, hQ, hx, hc, hI, hP => by
    apply l_seq1 hQ (m := cs.length) (by simp at hl; omega) hI
    intro b1 v1 t1 hI1
    have hx1 : x.drop c = e.ser ++ (serL cs ++ rest) := by rw [hx]; simp [serL]
    have := ih e Q bs vs (ts ++ [(7, u cs.length, a2)]) c (serL cs ++ rest) b1 v1 t1 (hcs e (by simp)).1
      (hcs e (by simp)).2 hQ hx1 hc (by simpa using hI1) (by
        intro b2 v2 t2 hI2
        have hx2 : x.drop (c + e.ser.length) = serL cs ++ rest := drop_shift (by rw [hx1])
        have := lw_seq hC f ih cs Q bs (vs ++ (NumSpec.lw f ws (envOf bs) e).map w2) ts (c + e.ser.length) rest b2 v2 t2 a2
          (fun c hc => hcs c (by simp [hc])) (by simp at hl; omega) hQ hx2 (by omega) hI2
          (hP.cast (by simp) (by simp [serL]; omega))
        exact this.cast rfl (by simp))
    exact this.cast rfl (by simp)

theorem GL.cast2 {x d Q b bt bt' v vt vt' t tt tt' c c'} (h : GL x d Q b bt v vt t tt c) (h0 : bt' = bt) (h1 : vt' = vt)
    (h2 : tt' = tt) (h3 : c' = c) : GL x d Q b bt' v vt' t tt' c' := by subst h0 h1 h2 h3; exact h

theorem LI.vpush {b bs v vs t ts} (h : LI b bs v vs t ts) (hv : v.length < 2 ^ 41) (w : UInt64) :
    LI b bs (u20 v (u vs.length) w) (vs ++ [w]) t ts := by
  have h1 := u20_push h.pv (by omega) w
  have h2 := h.pv.length_le
  exact ⟨h.pb, h.lb, h1.1, by have := h1.2; omega, h.pt, h.lt, h.sb⟩

theorem LI.popT {b bs v vs t ts r} (h : LI b bs v vs t (ts ++ [r])) : LI b bs v vs t ts :=
  ⟨h.pb, h.lb, h.pv, h.lv, h.pop, h.lt, h.sb⟩

theorem wd_eq {x d : Buf} {ws : List Nat} (hC : LC x d ws) {id : Nat} (hid : id < 2 ^ 32) :
    (if 2 * u id < bsize d then bget d (2 * u id + 1) else 1) = u (ws.getD id 1) := by
  have hw := hC.wl
  have e1 : (2 : UInt64) * u id = u (2 * id) := by rw [u2, u_mul]
  rw [e1, bsize_u, hC.dl]
  simp only [ult (show 2 * id < 2 ^ 64 by omega) (show 2 * ws.length < 2 ^ 64 by omega)]
  by_cases h : id < ws.length
  · rw [if_pos (by omega), u1, uadd, bget_u d (by omega), hC.dw id h]
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show ws.length ≤ id by omega)]; rfl

theorem LI.pushw {b bs v vs t ts} (h : LI b bs v vs t ts) {n : UInt64} (hn : n = u ts.length) (ht : t.length < 2 ^ 41)
    (k a c : UInt64) :
    LI b bs v vs (u27 t n k a c) (ts ++ [(k, a, c)]) ∧ (u27 t n k a c).length ≤ t.length + 3 := by
  subst hn; exact h.push ht k a c

theorem LI.push4 {b bs v vs t ts} (h : LI b bs v vs t ts) (ht : t.length < 2 ^ 40) (r1 r2 r3 r4 : T3) :
    LI b bs v vs (u27 (u27 (u27 (u27 t (u ts.length) r1.1 r1.2.1 r1.2.2) (u ts.length + 1) r2.1 r2.2.1 r2.2.2)
      (u ts.length + 2) r3.1 r3.2.1 r3.2.2) (u ts.length + 3) r4.1 r4.2.1 r4.2.2) (ts ++ [r1, r2, r3, r4]) := by
  have hts := h.lts
  obtain ⟨h1, l1⟩ := h.pushw rfl (by omega) r1.1 r1.2.1 r1.2.2
  obtain ⟨h2, l2⟩ := h1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by omega) r2.1 r2.2.1 r2.2.2
  obtain ⟨h3, l3⟩ := h2.pushw (n := u ts.length + 2) (by simp [u2, uadd]) (by omega) r3.1 r3.2.1 r3.2.2
  obtain ⟨h4, l4⟩ := h3.pushw (n := u ts.length + 3) (by simp [u3, uadd]) (by omega) r4.1 r4.2.1 r4.2.2
  simpa using h4

theorem LI.push5 {b bs v vs t ts} (h : LI b bs v vs t ts) (ht : t.length < 2 ^ 40) (r1 r2 r3 r4 r5 : T3) :
    LI b bs v vs (u27 (u27 (u27 (u27 (u27 t (u ts.length) r1.1 r1.2.1 r1.2.2) (u ts.length + 1) r2.1 r2.2.1 r2.2.2)
      (u ts.length + 2) r3.1 r3.2.1 r3.2.2) (u ts.length + 3) r4.1 r4.2.1 r4.2.2) (u ts.length + 4) r5.1 r5.2.1 r5.2.2)
      (ts ++ [r1, r2, r3, r4, r5]) := by
  have hts := h.lts
  obtain ⟨h1, l1⟩ := h.pushw rfl (by omega) r1.1 r1.2.1 r1.2.2
  obtain ⟨h2, l2⟩ := h1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by omega) r2.1 r2.2.1 r2.2.2
  obtain ⟨h3, l3⟩ := h2.pushw (n := u ts.length + 2) (by simp [u2, uadd]) (by omega) r3.1 r3.2.1 r3.2.2
  obtain ⟨h4, l4⟩ := h3.pushw (n := u ts.length + 3) (by simp [u3, uadd]) (by omega) r4.1 r4.2.1 r4.2.2
  obtain ⟨h5, l5⟩ := h4.pushw (n := u ts.length + 4) (by simp [show (4 : UInt64) = u 4 from rfl, uadd]) (by omega) r5.1 r5.2.1 r5.2.2
  simpa using h5

theorem LI.castT {b bs v vs t ts ts'} (h : LI b bs v vs t ts) (e : ts = ts') : LI b bs v vs t ts' := e ▸ h
theorem LI.castV {b bs v vs vs' t ts} (h : LI b bs v vs t ts) (e : vs = vs') : LI b bs v vs' t ts := e ▸ h

theorem zip_w2 : ∀ l1 l2 : List Bool,
    (List.zipWith (· && ·) l1 l2).map w2 = List.zipWith (· &&& ·) (l1.map w2) (l2.map w2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: l1, q :: l2 => by simp [List.zipWith_cons_cons, zip_w2 l1 l2, w2_and]

/-- nodes whose lw is [false] and that are skipped -/
theorem l_skip0 {x d : Buf} {Q : LO → Prop} (hQ : QE Q) {np : Nat} {e : Nd} {b bs v vs t ts rest} {c : Nat}
    (hxl : x.length < 2 ^ 23) (hI : LI b bs v vs t (ts ++ [(0, 0, 0)])) (hx : x.drop c = e.ser ++ rest) (hnb : NB np e)
    (h29 : v.length < 2 ^ 40 → t.length < 2 ^ 40 → b.length < 2 ^ 40 →
      u29 x d b (u (encB bs).length) v (u vs.length) t (u ts.length) (u c) =
        (u20 v (u vs.length) 0, (u vs.length + 1, (t, (u ts.length, (u15 x (u c), if u15 x (u c) == 0 then 0 else 1))))))
    (hP : LP x d Q bs (vs ++ [0]) ts (c + e.ser.length)) :
    GL x d Q b (u (encB bs).length) v (u vs.length) t (u (ts.length + 1)) (u c) := by
  apply l_node hQ hI h29
  intro hv ht hb hok
  have hvs := hI.pv.length_le
  rcases u15_ok (by omega) hx hnb with h0 | ⟨h1, -⟩
  · rw [h0] at hok; simp at hok
  · rw [h1]
    exact (hP _ _ _ (hI.vpush (by omega) 0).popT).cast2 rfl (by simp [u1, uadd]) rfl rfl

theorem lw_node_succ {x d : Buf} {np : Nat} {ws : List Nat} (hC : LC x d ws) (f : Nat) (ih : LN x d np ws f) :
    LN x d np ws (f + 1) := by
  intro e Q bs vs ts c rest b v t hf hnb hQ hx hc hI hP
  have hxl := hC.xl
  have hcl := drop_len hx (ser_pos e)
  have hts := hI.lts; simp at hts
  have hvs := hI.pv.length_le
  have hlv := hI.lv
  have hlt := hI.lt
  have hlb := hI.lb
  have tag : ∀ k, k < (hdr e).length → bget x (u c + u k) = (hdr e).getD k 0 := fun k hk => by
    rw [uadd]; exact rdh hx (by omega) hk
  have tag0 : bget x (u c) = (hdr e).getD 0 0 := by
    have := tag 0 (by have := hdr_pos e; omega); rwa [show u c + u 0 = u c from by simp [show u 0 = 0 from rfl]] at this
  cases e with
  | const k =>
    simp only [hdr, List.getD_cons_zero] at tag0
    apply l_node hQ hI (v1 := u20 v (u vs.length) 1) (vt1 := u vs.length + 1) (t1 := t) (tt1 := u ts.length)
      (c1 := u c + 2) (ok := 1) (fun _ _ _ => by simp only [u29, tag0]; rfl)
    intro hv ht hb _
    have hP' := hP.cast (vs' := vs ++ [1]) (c' := c + 2) (by simp [NumSpec.lw, w2]) (by simp [Nd.ser])
    exact (hP' _ _ _ (hI.vpush (by omega) 1).popT).cast2 rfl (by simp [u1, uadd]) rfl (by simp [u2, uadd])
  | loc s w =>
    simp only [hdr, List.getD_cons_zero] at tag0
    have t1 := tag 1 (by simp [hdr]); simp only [hdr, List.getD_cons_succ, List.getD_cons_zero, ← u1] at t1
    have t2 := tag 2 (by simp [hdr]); simp only [hdr, List.getD_cons_succ, List.getD_cons_zero, ← u2] at t2
    obtain ⟨hs, hw⟩ := hnb
    have hu := u22_ok hI.pb (by have := hI.lb; omega) (fun r hr => by have := hI.sb r hr; omega) 16777216 w vs v s hI.pv
      (by have := hI.lv; omega) (by omega) (by omega)
    generalize hR : u22 16777216 b (u (encB bs).length) v (u vs.length) (u s) (u w) = R at hu
    obtain ⟨v1, vt1, ok⟩ := R
    apply l_node hQ hI (v1 := v1) (vt1 := vt1) (t1 := t) (tt1 := u ts.length) (c1 := u c + 3) (ok := ok)
      (fun _ _ _ => by simp only [u29, tag0, t1, t2, hR]; rfl)
    intro hv ht hb hok
    obtain ⟨p1, p2, p3⟩ := hu hok
    simp only at p1 p2 p3
    have hP' := hP.cast (vs' := vs ++ (List.range w).map (fun i => w2 ((envOf bs).getD (s + i) false))) (c' := c + 3)
      (by simp [NumSpec.lw]) (by simp [Nd.ser])
    exact (hP' _ _ _ ⟨hI.pb, hI.lb, p1, by have := hI.lv; omega, hI.pop, hI.lt, hI.sb⟩).cast2 rfl
      (by rw [p2]; simp) rfl (by simp [u3, uadd])
  | bin op a b2 =>
    simp only [hdr, List.getD_cons_zero] at tag0
    have t1 := tag 1 (by simp [hdr]); simp only [hdr, List.getD_cons_succ, List.getD_cons_zero, ← u1] at t1
    have hnb0 := hnb
    obtain ⟨hop, hna, hnb2⟩ := hnb
    have hf' : a.ser.length ≤ f ∧ b2.ser.length ≤ f := by simp [Nd.ser] at hf; omega
    by_cases hsh : op = 6 ∨ op = 7
    · have h34 : u34 x (u c) = 1 := by unfold u34; rw [tag0, t1]; rcases hsh with rfl | rfl <;> rfl
      apply l_skip0 hQ hxl hI hx hnb0 (fun _ _ _ => by simp only [u29, tag0, h34]; rfl)
      exact hP.cast (by rcases hsh with rfl | rfl <;> simp [NumSpec.lw, NumSpec.isShift, w2]) rfl
    · have h34 : u34 x (u c) = 0 := by
        unfold u34; rw [tag0, t1, show (6 : UInt64) = u 6 from rfl, show (7 : UInt64) = u 7 from rfl]
        simp only [show (3 : UInt64) == 3 from rfl, if_true, u_ne (show op < 2 ^ 64 by omega) (show 6 < 2 ^ 64 by omega) (by omega),
          u_ne (show op < 2 ^ 64 by omega) (show 7 < 2 ^ 64 by omega) (by omega)]
        rfl
      have hx2 : x.drop (c + 2) = a.ser ++ (b2.ser ++ rest) := by
        have h0 : x.drop c = [3, u op] ++ (a.ser ++ (b2.ser ++ rest)) := by rw [hx]; simp [Nd.ser, toU]
        simpa using drop_shift h0
      have hx3 : x.drop (c + 2 + a.ser.length) = b2.ser ++ rest := drop_shift hx2
      apply l_node hQ hI (ok := 1) (fun _ _ _ => by simp only [u29, tag0, h34]; rfl)
      intro hv ht hb _
      have hI5 := hI.popT.push5 ht (2, u vs.length, 0) (1, u vs.length + 1, 0) (0, 0, 0) (1, u vs.length, 0) (0, 0, 0)
      refine (ih a Q bs vs (ts ++ [(2, u vs.length, 0), (1, u vs.length + 1, 0), (0, 0, 0), (1, u vs.length, 0)]) (c + 2)
        (b2.ser ++ rest) b v _ hf'.1 hna hQ hx2 (by omega) (hI5.castT (by simp)) ?_).cast2 rfl rfl (by simp [show (5 : UInt64) = u 5 from rfl, uadd]) (by simp [u2, uadd])
      intro b1 v1 t1 hI1
      refine (l_first hQ (W := vs) (ts := ts ++ [(2, u vs.length, 0), (1, u vs.length + 1, 0), (0, 0, 0)]) (a2 := 0)
        (hI1.castT (by simp)) ?_).cast2 rfl rfl (by simp) rfl
      intro b3 v3 t3 hI3
      refine (ih b2 Q bs _ (ts ++ [(2, u vs.length, 0), (1, u vs.length + 1, 0)]) (c + 2 + a.ser.length)
        rest b3 v3 t3 hf'.2 hnb2 hQ hx3 (by omega) (hI3.castT (by simp)) ?_).cast2 rfl rfl (by simp) rfl
      intro b4 v4 t4 hI4
      have e1 : u vs.length + 1 = u (vs ++ [(List.map w2 (NumSpec.lw f ws (envOf bs) a)).getD 0 0]).length := by
        simp [u1, uadd]
      refine (l_first hQ (W := vs ++ [(List.map w2 (NumSpec.lw f ws (envOf bs) a)).getD 0 0]) (ts := ts ++ [(2, u vs.length, 0)])
        (a2 := 0) (hI4.castT (by simp [e1])) ?_).cast2 rfl rfl (by simp) rfl
      intro b5 v5 t5 hI5
      refine (l_and hQ (W := vs) (ts := ts) (a2 := 0) (p := (List.map w2 (NumSpec.lw f ws (envOf bs) a)).getD 0 0)
        (q := (List.map w2 (NumSpec.lw f ws (envOf bs) b2)).getD 0 0) (hI5.castV (by simp)) ?_).cast2 rfl (by simp) (by simp) rfl
      refine hP.cast ?_ (by simp only [Nd.ser, List.length_cons, List.length_append]; omega)
      have hs : NumSpec.isShift op = false := by simp [NumSpec.isShift]; omega
      simp only [NumSpec.lw, hs, Bool.not_false, Bool.true_and, List.map_cons, List.map_nil]
      rw [w2_getD0, w2_getD0, w2_and]
  | ite cc a1 b1 t1 e1 =>
    simp only [hdr, List.getD_cons_zero] at tag0
    simp only [NB] at hnb
    obtain ⟨-, hna, hnb1, hnt, hne⟩ := hnb
    have hf' : t1.ser.length ≤ f ∧ e1.ser.length ≤ f := by simp [Nd.ser] at hf; omega
    have hx2 : x.drop (c + 2) = a1.ser ++ (b1.ser ++ (t1.ser ++ (e1.ser ++ rest))) := by
      have h0 : x.drop c = [4, u cc] ++ (a1.ser ++ (b1.ser ++ (t1.ser ++ (e1.ser ++ rest)))) := by rw [hx]; simp [Nd.ser, toU]
      simpa using drop_shift h0
    have hx3 := drop_shift hx2
    have hx4 := drop_shift hx3
    have hx5 := drop_shift hx4
    have hcl' : c + 2 + a1.ser.length + b1.ser.length + t1.ser.length + e1.ser.length ≤ x.length := by
      have := drop_len hx5 (ser_pos e1); omega
    apply l_node hQ hI (v1 := u20 v (u vs.length) 0) (vt1 := u vs.length + 1) (tt1 := u ts.length + 4)
      (c1 := u15 x (u15 x (u c + 2))) (ok := if u15 x (u15 x (u c + 2)) == 0 then 0 else 1)
      (fun _ _ _ => by simp only [u29, tag0]; rfl)
    intro hv ht hb hok
    rw [u2, uadd] at hok
    have hp : u15 x (u15 x (u c + 2)) = u (c + 2 + a1.ser.length + b1.ser.length) := by
      rw [u2, uadd]
      rcases u15_ok (by omega) hx2 hna with h0 | ⟨h1, -⟩
      · rw [h0, show u15 x 0 = 0 from rfl] at hok; simp at hok
      · rw [h1]
        rcases u15_ok (by omega) hx3 hnb1 with h0 | ⟨h1, -⟩
        · rw [h1, h0] at hok; simp at hok
        · rw [h1]
    rw [hp]
    have hI4 := (hI.vpush (by omega) 0).popT.push4 ht (4, u vs.length, 0) (0, 0, 0) (3, u vs.length, 0) (0, 0, 0)
    refine (ih t1 Q bs (vs ++ [0]) (ts ++ [(4, u vs.length, 0), (0, 0, 0), (3, u vs.length, 0)])
      (c + 2 + a1.ser.length + b1.ser.length) (e1.ser ++ rest) b _ _ hf'.1 hnt hQ hx4 (by omega) (hI4.castT (by simp))
      ?_).cast2 rfl (by simp [u1, uadd]) (by simp [show (4 : UInt64) = u 4 from rfl, uadd]) rfl
    intro b2 v2 t2 hI2
    refine (l_len hQ (W := vs) (z := 0) (R := (NumSpec.lw f ws (envOf bs) t1).map w2)
      (ts := ts ++ [(4, u vs.length, 0), (0, 0, 0)]) (a2 := 0)
      (hI2.castT (by simp) |>.castV (by simp)) ?_).cast2 rfl (by simp) (by simp) rfl
    intro b3 v3 t3 hI3
    refine (ih e1 Q bs _ (ts ++ [(4, u vs.length, 0)]) (c + 2 + a1.ser.length + b1.ser.length + t1.ser.length) rest
      b3 v3 t3 hf'.2 hne hQ hx5 (by omega) (hI3.castT (by simp)) ?_).cast2 rfl rfl (by simp) rfl
    intro b4 v4 t4 hI4
    refine (l_zip hQ (W := vs) (A := (NumSpec.lw f ws (envOf bs) t1).map w2) (B := (NumSpec.lw f ws (envOf bs) e1).map w2)
      (ts := ts) (a2 := 0) (hI4.castV (by simp)) ?_).cast2 rfl (by simp) (by simp) rfl
    refine hP.cast ?_ (by simp only [Nd.ser, List.length_cons, List.length_append]; omega)
    simp only [NumSpec.lw, zip_w2]
  | letE sl w v1 b1 =>
    simp only [hdr, List.getD_cons_zero] at tag0
    have t1 := tag 1 (by simp [hdr]); simp only [hdr, List.getD_cons_succ, List.getD_cons_zero, ← u1] at t1
    simp only [NB] at hnb
    obtain ⟨hsl, -, hnv, hnb1⟩ := hnb
    have hf' : v1.ser.length ≤ f ∧ b1.ser.length ≤ f := by simp [Nd.ser] at hf; omega
    have hx2 : x.drop (c + 3) = v1.ser ++ (b1.ser ++ rest) := by
      have h0 : x.drop c = [5, u sl, u w] ++ (v1.ser ++ (b1.ser ++ rest)) := by rw [hx]; simp [Nd.ser, toU]
      simpa using drop_shift h0
    have hx3 := drop_shift hx2
    apply l_node hQ hI (v1 := v) (vt1 := u vs.length) (tt1 := u ts.length + 4) (c1 := u c + 3) (ok := 1)
      (fun _ _ _ => by simp only [u29, tag0, t1]; rfl)
    intro hv ht hb _
    have hI4 := hI.popT.push4 ht (6, u (encB bs).length, 0) (0, 0, 0) (5, u sl, u vs.length) (0, 0, 0)
    refine (ih v1 Q bs vs (ts ++ [(6, u (encB bs).length, 0), (0, 0, 0), (5, u sl, u vs.length)]) (c + 3)
      (b1.ser ++ rest) b v _ hf'.1 hnv hQ hx2 (by omega) (hI4.castT (by simp)) ?_).cast2 rfl rfl
      (by simp [show (4 : UInt64) = u 4 from rfl, uadd]) (by simp [u3, uadd])
    intro b2 v2 t2 hI2
    refine (l_bind hQ (W := vs) (ts := ts ++ [(6, u (encB bs).length, 0), (0, 0, 0)]) hsl
      (hI2.castT (by simp)) ?_).cast2 rfl rfl (by simp) rfl
    intro b3 v3 t3 hI3
    refine (ih b1 Q _ vs (ts ++ [(6, u (encB bs).length, 0)]) (c + 3 + v1.ser.length) rest b3 v3 t3 hf'.2 hnb1 hQ hx3
      (by omega) (hI3.castT (by simp)) ?_).cast2 rfl rfl (by simp) rfl
    intro b4 v4 t4 hI4
    refine (l_unbind hQ (bs0 := bs) (ts := ts) (a2 := 0) (List.prefix_append _ _) hI4 ?_).cast2 rfl rfl (by simp) rfl
    refine hP.cast ?_ (by simp only [Nd.ser, List.length_cons, List.length_append]; omega)
    simp only [NumSpec.lw, envOf_snoc]
  | pair cs =>
    simp only [hdr, List.getD_cons_zero] at tag0
    have t1 := tag 1 (by simp [hdr]); simp only [hdr, List.getD_cons_succ, List.getD_cons_zero, ← u1] at t1
    simp only [NB] at hnb
    obtain ⟨hcl2, hncs⟩ := hnb
    rw [nbl_iff] at hncs
    have hx2 : x.drop (c + 2) = serL cs ++ rest := by
      have h0 : x.drop c = [6, u cs.length] ++ (serL cs ++ rest) := by rw [hx]; simp [Nd.ser, toU]
      simpa using drop_shift h0
    apply l_node hQ hI (v1 := v) (vt1 := u vs.length) (tt1 := u ts.length + 1) (c1 := u c + 2) (ok := 1)
      (fun _ _ _ => by simp only [u29, tag0, t1]; rfl)
    intro hv ht hb _
    obtain ⟨hI1, -⟩ := hI.popT.push (by omega) 7 (u cs.length) 0
    refine (lw_seq hC f ih cs Q bs vs ts (c + 2) rest b v _ 0 (fun c' hc' => ⟨?_, hncs c' hc'⟩) hcl2 hQ hx2 (by omega) hI1
      ?_).cast2 rfl rfl (by simp [u1, uadd]) (by simp [u2, uadd])
    · have := mem_serL_len hc'; simp [Nd.ser] at hf; omega
    · refine hP.cast ?_ (by simp only [Nd.ser, List.length_cons]; omega)
      simp [NumSpec.lw]
  | call id as =>
    simp only [hdr, List.getD_cons_zero] at tag0
    have t1 := tag 1 (by simp [hdr]); simp only [hdr, List.getD_cons_succ, List.getD_cons_zero, ← u1] at t1
    have hnb0 := hnb
    simp only [NB] at hnb
    obtain ⟨hid, -, -⟩ := hnb
    have hwd := wd_eq hC hid
    have hwb : ws.getD id 1 < 2 ^ 32 := by
      by_cases h : id < ws.length
      · exact hC.wb id h
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show ws.length ≤ id by omega)]
    have hu := u23_ok 16777216 (ws.getD id 1) vs v hI.pv (by omega) (by omega)
    generalize hR : u23 16777216 v (u vs.length) (u (ws.getD id 1)) = R at hu
    obtain ⟨v1, vt1, ok⟩ := R
    apply l_node hQ hI (v1 := v1) (vt1 := vt1) (tt1 := u ts.length) (c1 := u15 x (u c))
      (ok := if u15 x (u c) == 0 then 0 else ok) (fun _ _ _ => by simp only [u29, tag0, t1, hwd, hR]; rfl)
    intro hv ht hb hok
    rcases u15_ok (by omega) hx hnb0 with h0 | ⟨h1, -⟩
    · rw [h0] at hok; simp at hok
    · rw [h1] at hok ⊢
      have hok' : ok = 1 := by
        have : (u (c + (Nd.call id as).ser.length) == 0) = false := by
          rw [u0, ueq (by omega) (by omega)]; simp; omega
        simpa [this] using hok
      obtain ⟨p1, p2, p3⟩ := hu hok'
      simp only at p1 p2 p3
      refine (hP _ _ _ ⟨hI.pb, hI.lb, ?_, by omega, hI.pop, hI.lt, hI.sb⟩).cast2 rfl
        (by rw [p2]; simp [NumSpec.lw, List.getD_eq_getElem?_getD]) rfl rfl
      simpa [NumSpec.lw, List.map_replicate, w2] using p1
  | prim pn as =>
    simp only [hdr, List.getD_cons_zero] at tag0
    apply l_skip0 hQ hxl hI hx hnb (fun _ _ _ => by simp only [u29, tag0]; rfl)
    exact hP.cast (by simp [NumSpec.lw, w2]) rfl
  | loop z st =>
    simp only [hdr, List.getD_cons_zero] at tag0
    apply l_skip0 hQ hxl hI hx hnb (fun _ _ _ => by simp only [u29, tag0]; rfl)
    exact hP.cast (by simp [NumSpec.lw, w2]) rfl
  | cont e1 =>
    simp only [hdr, List.getD_cons_zero] at tag0
    apply l_skip0 hQ hxl hI hx hnb (fun _ _ _ => by simp only [u29, tag0]; rfl)
    exact hP.cast (by simp [NumSpec.lw, w2]) rfl

theorem lw_all {x d : Buf} {np : Nat} {ws : List Nat} (hC : LC x d ws) : ∀ f, LN x d np ws f
  | 0 => fun e _ _ _ _ _ _ _ _ _ hf => by have := ser_pos e; omega
  | f + 1 => lw_node_succ hC f (lw_all hC f)

end NumP
