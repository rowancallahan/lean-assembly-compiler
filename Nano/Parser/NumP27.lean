/- Nano/Parser/NumP27: the late-slot check (`NumSpec.lateOk`): `u73` scans a body node by node (`u77`) in pre-order;
at a let it marks the slots (`u75`, `u76`: 1 late, 2 literal-only), at a shift it checks the left operand (`u84`); the
mark of a value is a scan of its operand-tree leaves (`u82`). -/
import Nano.Parser.NumP26
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

theorem nodes_succ (k : Nat) (e : Nd) : NumSpec.nodes (k + 1) e = e :: (kids e).flatMap (NumSpec.nodes k) := by
  cases e <;> rfl

/-- one node: its header is skipped, its children join the pending nodes -/
theorem u77_node {np : Nat} {x : Buf} {e : Nd} {r : Buf} {i k : Nat} (hx : x.drop i = e.ser ++ r) (hnb : NB np e)
    (hl : x.length < 2 ^ 64) (hk : k + 1 + (kids e).length < 2 ^ 64) :
    u77 x (u i) (u (k + 1)) = (u (i + (hdr e).length), u (k + (kids e).length)) := by
  have hil := drop_len hx (ser_pos e)
  unfold u77
  rw [ser_hdr e, List.append_assoc] at hx
  have hil2 : i + (hdr e).length ≤ x.length := by
    have := drop_len hx (hdr_pos e); omega
  have r0 := rd hx (k := 0) (by have := hdr_pos e; omega) (by have := hdr_pos e; omega)
  rw [Nat.add_zero] at r0
  rw [r0]
  have hsub' : u (k + 1) - u 1 = u k := by rw [u_sub (by omega) (by omega)]; rfl
  have ha : ∀ m : Nat, u i + (OfNat.ofNat m : UInt64) = u (i + m) := fun m => by rw [lit, u_add]
  cases e with
  | const v => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]
  | loc s w => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]
  | bin op a b => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]
  | ite c a b t el => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]
  | letE s w v b => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]
  | pair cs =>
    have r1 := rd hx (k := 1) (by simp [hdr]) (by simp [hdr] at hil2; omega)
    simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at r1
    simp only [hdr, kids, List.getD_cons_zero]; simp; rw [ha 1, r1]; simp only [lit, u_add, hsub', and_self]
  | call id as =>
    have r2 := rd hx (k := 2) (by simp [hdr]) (by simp [hdr] at hil2; omega)
    simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at r2
    simp only [hdr, kids, List.getD_cons_zero]; simp; rw [ha 2, r2]; simp only [lit, u_add, hsub', and_self]
  | prim pn as =>
    have r1 := rd hx (k := 1) (by simp [hdr]) (by simp [hdr] at hil2; omega)
    simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at r1
    obtain ⟨hp, hpa, -⟩ := hnb
    have hg : g33 (u pn) = u as.length := by
      rw [hpa]; simp only [toU]; unfold u; simp
    simp only [hdr, kids, List.getD_cons_zero]; simp; rw [ha 1, r1, hg]; simp only [lit, u_add, hsub', and_self]
  | loop z s => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]
  | cont e => simp only [hdr, kids, List.getD_cons_zero]; simp; simp only [lit, u_add, hsub', and_self]

/-- the facts about the pending nodes that a scan's step needs -/
theorem scan_step {np : Nat} {x : Buf} {e : Nd} {es : List Nd} {r : Buf} {i : Nat}
    (hx : x.drop i = serL (e :: es) ++ r) (hnb : ∀ c ∈ e :: es, NB np c) (hl : x.length < 2 ^ 23) :
    x.drop i = e.ser ++ (serL es ++ r) ∧ x.drop (i + (hdr e).length) = serL (kids e ++ es) ++ r ∧
      (∀ c ∈ kids e ++ es, NB np c) ∧ es.length + 1 + (kids e).length < 2 ^ 64 ∧ i + e.ser.length ≤ x.length := by
  have hx' : x.drop i = e.ser ++ (serL es ++ r) := by rw [hx]; simp [serL]
  have hil := drop_len hx (by simp [serL]; have := ser_pos e; omega)
  have h1 := len_le_serL (kids e ++ es)
  rw [serL_append] at h1
  have h2 := ser_len_kids e
  simp only [serL, List.length_append] at hil h1
  refine ⟨hx', ?_, ?_, by omega, by omega⟩
  · rw [serL_append, List.append_assoc]; apply drop_shift; rw [hx', ser_hdr e]; simp
  · intro c hc; rcases List.mem_append.1 hc with hc | hc
    · exact nb_kids (hnb e (by simp)) c hc
    · exact hnb c (by simp [hc])

/-- from the nodes of the kids and the node itself to the nodes of the node -/
theorem nodes_all {P : Nd → Prop} {e : Nd} {es : List Nd} (he : P e)
    (hk : ∀ e' ∈ kids e ++ es, ∀ k, ∀ c ∈ NumSpec.nodes k e', P c) :
    ∀ e' ∈ e :: es, ∀ k, ∀ c ∈ NumSpec.nodes k e', P c := by
  intro e' he' k c hc
  rcases List.mem_cons.1 he' with rfl | he'
  · cases k with
    | zero => simp [NumSpec.nodes] at hc
    | succ k =>
      rw [nodes_succ] at hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact he
      · obtain ⟨c', hc', hc⟩ := List.mem_flatMap.1 hc
        exact hk c' (by simp [hc']) k c hc
  · exact hk e' (by simp [he']) k c hc

/-! ## marks -/
def two (b : Bool) : UInt64 := if b then 2 else 0
/-- a slot's mark: 1 late ||| 2 literal-only -/
def cd (a b : Bool) : UInt64 := w2 a ||| two b

theorem cd_1 (a b : Bool) : cd a b &&& 1 = w2 a := by cases a <;> cases b <;> rfl
theorem cd_2 (a b : Bool) : cd a b &&& 2 = two b := by cases a <;> cases b <;> rfl
theorem two_and (a b : Bool) : two a &&& two b = two (a && b) := by cases a <;> cases b <;> rfl
theorem cd_ne4 (a b : Bool) : (cd a b == 4) = false := by cases a <;> cases b <;> rfl
theorem w2t_0 (a b : Bool) : (w2 a ||| two b == 0) = !(a || b) := by cases a <;> cases b <;> rfl

/-- the marks buffer holds the literal-only (`le`) and the late (`lv`) slots -/
def Rep (F : Buf) (le lv : List Bool) : Prop := ∀ p, F.getD p 0 = cd (lv.getD p false) (le.getD p false)

/-! ## the leaves of an operand tree -/
def U82 : Nat → Buf → Buf → Buf → UInt64 → UInt64 → UInt64 → UInt64
  | 0, x, f, w, t, b, c => 4
  | n + 1, x, f, w, t, b, c =>
    if t == 0 then b ||| c
    else
      let q := bget w (t - 1);
      let g := bget x q;
      if g == 3 then
        (if u34 x q == 1 then 0
         else
           (let e := u15 x (q + 2);
            if e == 0 then 4 else U82 n x f (u20 (u20 w (t - 1) e) t (q + 2)) (t + 1) b c))
      else if g == 4 then
        (let p := u15 x (u15 x (q + 2));
         let p2 := u15 x p;
         if p == 0 then 4 else if p2 == 0 then 4 else U82 n x f (u20 (u20 w (t - 1) p2) t p) (t + 1) b c)
      else if g == 5 then U82 n x f w (t - 1) 1 0
      else if g == 1 then U82 n x f w (t - 1) b c
      else if g == 2 then
        (let m := bget f (bget x (q + 1));
         let lw := m &&& 1;
         let ll := (if bget x (q + 2) == 1 then m &&& 2 else 0);
         if lw ||| ll == 0 then 0 else U82 n x f w (t - 1) (b ||| lw) (c &&& ll))
      else 0

theorem U82_succ (n : Nat) (x f w : Buf) (t b c : UInt64) : U82 (n + 1) x f w t b c =
    if t == 0 then b ||| c
    else
      let q := bget w (t - 1);
      let g := bget x q;
      if g == 3 then
        (if u34 x q == 1 then 0
         else
           (let e := u15 x (q + 2);
            if e == 0 then 4 else U82 n x f (u20 (u20 w (t - 1) e) t (q + 2)) (t + 1) b c))
      else if g == 4 then
        (let p := u15 x (u15 x (q + 2));
         let p2 := u15 x p;
         if p == 0 then 4 else if p2 == 0 then 4 else U82 n x f (u20 (u20 w (t - 1) p2) t p) (t + 1) b c)
      else if g == 5 then U82 n x f w (t - 1) 1 0
      else if g == 1 then U82 n x f w (t - 1) b c
      else if g == 2 then
        (let m := bget f (bget x (q + 1));
         let lw := m &&& 1;
         let ll := (if bget x (q + 2) == 1 then m &&& 2 else 0);
         if lw ||| ll == 0 then 0 else U82 n x f w (t - 1) (b ||| lw) (c &&& ll))
      else 0 := rfl

theorem u82_snd (x f : Buf) : ∀ (n : Nat) (w : Buf) (t b c : UInt64), (u82 n x f w t b c).2 = U82 n x f w t b c
  | 0, _, _, _, _ => rfl
  | n + 1, w, t, b, c => by
    unfold u82 U82
    dsimp only
    repeat' split
    all_goals first | exact u82_snd x f n _ _ _ _ | rfl | contradiction

theorem len22 {w w' : Buf} {m : Nat} (h : w'.length ≤ w.length + 2) : w'.length + 2 * m ≤ w.length + 2 * (m + 1) := by
  omega
theorem len_u20u20 (w : Buf) (a b c d : UInt64) : (u20 (u20 w a b) c d).length ≤ w.length + 2 := by
  have := u20_len (u20 w a b) c d; have := u20_len w a b; omega

theorem u82_len (x f : Buf) : ∀ (n : Nat) (w : Buf) (t b c : UInt64), (u82 n x f w t b c).1.length ≤ w.length + 2 * n
  | 0, w, t, b, c => by simp [u82]
  | n + 1, w, t, b, c => by
    unfold u82
    dsimp only
    repeat' split
    all_goals first
      | (simp; done)
      | exact Nat.le_trans (u82_len x f n _ _ _ _) (len22 (len_u20u20 _ _ _ _ _))
      | exact Nat.le_trans (u82_len x f n _ _ _ _) (len22 (by omega))

/-- the leaves' mark: every leaf waits or is literal-only → 1 some waits ||| 2 all literal-only, else 0 -/
def lv82 (le lv : List Bool) (ls : List Nd) (B C : Bool) : UInt64 :=
  if ls.all (fun l => NumSpec.leafW lv l || NumSpec.leafL le l) then
    cd (B || ls.any (NumSpec.leafW lv)) (C && ls.all (NumSpec.leafL le))
  else 0

theorem lv82_wt (f : Nat) (le lv : List Bool) (e : Nd) :
    lv82 le lv (NumSpec.opl f e) false true = cd (NumSpec.wt f le lv e) (NumSpec.litE f le e) := by
  unfold lv82 NumSpec.wt NumSpec.litE
  generalize NumSpec.opl f e = ls
  cases h : ls.all (fun l => NumSpec.leafW lv l || NumSpec.leafL le l)
  · have : ls.all (NumSpec.leafL le) = false := by
      rw [List.all_eq_false] at h ⊢
      obtain ⟨l, hl, hl'⟩ := h
      exact ⟨l, hl, by simp at hl' ⊢; exact hl'.2⟩
    simp [this, cd, two, w2]
  · simp

theorem lv82_swap (le lv : List Bool) (L A A' : List Nd) (B C : Bool) :
    lv82 le lv (L ++ (A' ++ A)) B C = lv82 le lv (L ++ (A ++ A')) B C := by
  unfold lv82
  simp only [List.all_append, List.any_append]
  generalize L.all (fun l => NumSpec.leafW lv l || NumSpec.leafL le l) = a1
  generalize A.all (fun l => NumSpec.leafW lv l || NumSpec.leafL le l) = a2
  generalize A'.all (fun l => NumSpec.leafW lv l || NumSpec.leafL le l) = a3
  generalize L.any (NumSpec.leafW lv) = b1
  generalize A.any (NumSpec.leafW lv) = b2
  generalize A'.any (NumSpec.leafW lv) = b3
  generalize L.all (NumSpec.leafL le) = c1
  generalize A.all (NumSpec.leafL le) = c2
  generalize A'.all (NumSpec.leafL le) = c3
  cases a1 <;> cases a2 <;> cases a3 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases c1 <;> cases c2 <;> cases c3 <;>
    cases B <;> cases C <;> rfl

theorem lv82_leaf (le lv : List Bool) (L : List Nd) (e : Nd) (B C : Bool)
    (h : (NumSpec.leafW lv e || NumSpec.leafL le e) = true) :
    lv82 le lv L (B || NumSpec.leafW lv e) (C && NumSpec.leafL le e) = lv82 le lv (L ++ [e]) B C := by
  unfold lv82
  simp only [List.all_append, List.any_append, List.all_cons, List.any_cons, List.all_nil, List.any_nil, h,
    Bool.and_true, Bool.or_false]
  generalize L.all (fun l => NumSpec.leafW lv l || NumSpec.leafL le l) = a1
  generalize L.any (NumSpec.leafW lv) = b1
  generalize L.all (NumSpec.leafL le) = c1
  generalize NumSpec.leafW lv e = we
  generalize NumSpec.leafL le e = le'
  cases a1 <;> cases b1 <;> cases c1 <;> cases we <;> cases le' <;> cases B <;> cases C <;> rfl

theorem lv82_none (le lv : List Bool) (L : List Nd) (e : Nd) (B C : Bool) (h1 : NumSpec.leafW lv e = false)
    (h2 : NumSpec.leafL le e = false) : lv82 le lv (L ++ [e]) B C = 0 := by
  unfold lv82; simp [h1, h2]

/-- `U82`: the mark of the leaves of the operand trees on the work stack -/
theorem U82_ok {x F : Buf} {np : Nat} {le lv : List Bool} (hxl : x.length < 2 ^ 23) (hR : Rep F le lv) :
    ∀ (n : Nat) (ps : List (Nd × Nat × Nat)) (w : Buf) (B C : Bool),
    ps.map (fun p => u p.2.2) <+: w → w.length + n < 2 ^ 40 → (∀ p ∈ ps, SP x np p) →
    U82 n x F w (u ps.length) (w2 B) (two C) = 4 ∨
      U82 n x F w (u ps.length) (w2 B) (two C) = lv82 le lv (ps.flatMap fun p => NumSpec.opl p.2.1 p.1) B C
  | 0, _, _, _, _, _, _, _ => Or.inl rfl
  | n + 1, ps, w, B, C, hw, hwl, hps => by
    rcases List.eq_nil_or_concat ps with h0 | ⟨ps0, p, h0⟩
    · subst h0; right
      rw [U82_succ, if_pos (show (u ([] : List (Nd × Nat × Nat)).length == 0) = true from rfl)]; simp [lv82, cd]
    · rw [List.concat_eq_append] at h0; subst h0
      have hl2 := hw.length_le; simp at hl2
      obtain ⟨⟨r, hx⟩, hf, hnb, hc⟩ := hps p (by simp)
      have hps0 : ∀ q ∈ ps0, SP x np q := fun q hq => hps q (by simp [hq])
      have hcl := drop_len hx (ser_pos _)
      have ht0 : (u (ps0 ++ [p]).length == 0) = false := by rw [u0, ueq (by simp; omega) (by omega)]; simp
      have hp0 : ps0.map (fun p => u p.2.2) <+: w :=
        (by simp : ps0.map (fun p => u p.2.2) <+: (ps0 ++ [p]).map (fun p => u p.2.2)).trans hw
      rw [U82_succ, ht0]
      simp only [Bool.false_eq_true, if_false]
      rw [pop_rd hw (by omega), tag_rd hx (by omega)]
      rw [List.length_append, List.length_singleton, upred _ (by omega)]
      obtain ⟨e, f, q⟩ := p
      simp only at hx hf hnb hc hcl ⊢
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by have := ser_pos e; omega⟩
      have hL : (ps0 ++ [(e, f' + 1, q)]).flatMap (fun p => NumSpec.opl p.2.1 p.1) =
          ps0.flatMap (fun p => NumSpec.opl p.2.1 p.1) ++ NumSpec.opl (f' + 1) e := by simp
      rw [hL]
      generalize hL0 : ps0.flatMap (fun p => NumSpec.opl p.2.1 p.1) = L0
      -- a leaf: the rest of the stack, B and C updated
      have hleaf : ∀ (B' C' : Bool), NumSpec.opl (f' + 1) e = [e] → (NumSpec.leafW lv e || NumSpec.leafL le e) = true →
          B' = (B || NumSpec.leafW lv e) → C' = (C && NumSpec.leafL le e) →
          U82 n x F w (u ps0.length) (w2 B') (two C') = 4 ∨
          U82 n x F w (u ps0.length) (w2 B') (two C') = lv82 le lv (L0 ++ NumSpec.opl (f' + 1) e) B C := by
        intro B' C' ho hwl' hB hC
        rcases U82_ok hxl hR n ps0 w B' C' hp0 (by omega) hps0 with h | h
        · exact Or.inl h
        · right; rw [h, ho, hL0, hB, hC]; exact lv82_leaf le lv L0 e B C hwl'
      -- the top replaced by two nodes (an operator's operands, an if's branches)
      have hpush : ∀ (c1 c2 : Nd) (p1 p2 : Nat) (r1 r2 : Buf), x.drop p1 = c1.ser ++ r1 → x.drop p2 = c2.ser ++ r2 →
          c1.ser.length ≤ f' → c2.ser.length ≤ f' → NB np c1 → NB np c2 → 0 < p1 → 0 < p2 →
          NumSpec.opl (f' + 1) e = NumSpec.opl f' c2 ++ NumSpec.opl f' c1 →
          U82 n x F (u20 (u20 w (u ps0.length) (u p1)) (u (ps0.length + 1)) (u p2)) (u (ps0.length + 1) + 1)
            (w2 B) (two C) = 4 ∨
          U82 n x F (u20 (u20 w (u ps0.length) (u p1)) (u (ps0.length + 1)) (u p2)) (u (ps0.length + 1) + 1)
            (w2 B) (two C) = lv82 le lv (L0 ++ NumSpec.opl (f' + 1) e) B C := by
        intro c1 c2 p1 p2 r1 r2 hx1 hx2 hf1 hf2 hn1 hn2 hp1 hp2 ho
        obtain ⟨q1, l1⟩ := u20_push hp0 (by omega) (u p1)
        simp only [List.length_map] at q1 l1
        obtain ⟨q2, l2⟩ := u20_push (vs := (ps0 ++ [(c1, f', p1)]).map (fun p => u p.2.2))
          (by simpa using q1) (by omega) (u p2)
        simp only [List.length_map, List.length_append, List.length_singleton] at q2 l2
        have e2 : u (ps0.length + 1) + 1 = u (ps0 ++ [(c1, f', p1), (c2, f', p2)]).length := by simp [u1, uadd]
        rw [e2]
        have ih := U82_ok hxl hR n (ps0 ++ [(c1, f', p1), (c2, f', p2)]) _ B C (by simpa using q2) (by omega) (by
          intro p hp
          simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with hp | rfl | rfl
          · exact hps0 p hp
          · exact ⟨⟨r1, hx1⟩, hf1, hn1, hp1⟩
          · exact ⟨⟨r2, hx2⟩, hf2, hn2, hp2⟩)
        rcases ih with h | h
        · exact Or.inl h
        · right; rw [h, ho]
          have : (ps0 ++ [(c1, f', p1), (c2, f', p2)]).flatMap (fun p => NumSpec.opl p.2.1 p.1) =
              L0 ++ (NumSpec.opl f' c1 ++ NumSpec.opl f' c2) := by rw [← hL0]; simp
          rw [this, lv82_swap]
      cases e with
      | bin op a b =>
        simp only [hdr, List.getD_cons_zero, show ((3 : UInt64) == 3) = true from rfl, if_true]
        rw [u34_ok hx (by omega) hnb]
        by_cases hsh : NumSpec.isShift op
        · right; simp only [shN, hsh, show (w2 true == 1) = true from rfl, if_true]
          have ho : NumSpec.opl (f' + 1) (.bin op a b) = [.bin op a b] := by simp [NumSpec.opl, hsh]
          rw [ho, lv82_none le lv L0 _ B C rfl rfl]
        · simp only [shN, hsh, show (w2 false == 1) = false from rfl, Bool.false_eq_true, if_false]
          simp only [NB] at hnb
          obtain ⟨-, hna, hnb1⟩ := hnb
          have hx2 : x.drop (q + 2) = a.ser ++ (b.ser ++ r) := by
            have h0 : x.drop q = [3, u op] ++ (a.ser ++ (b.ser ++ r)) := by rw [hx]; simp [Nd.ser, toU]
            simpa using drop_shift h0
          have hx3 := drop_shift hx2
          have hf' : a.ser.length ≤ f' ∧ b.ser.length ≤ f' := by simp [Nd.ser] at hf; omega
          have hsl : (Nd.bin op a b).ser.length = 2 + a.ser.length + b.ser.length := by simp [Nd.ser]; omega
          rw [show u q + 2 = u (q + 2) by rw [u2, uadd]]
          rcases u15_ok (by omega) hx2 hna with h0 | ⟨h1, -⟩
          · left; rw [h0]; rfl
          rw [h1]
          have hne0 : (u (q + 2 + a.ser.length) == 0) = false := by
            rw [u0, ueq (by omega) (by omega)]; exact decide_eq_false (by omega)
          simp only [hne0, Bool.false_eq_true, if_false]
          exact hpush b a _ _ r _ hx3 hx2 hf'.2 hf'.1 hnb1 hna (by omega) (by omega) (by simp [NumSpec.opl, hsh])
      | ite cc a b t el =>
        simp only [NB] at hnb
        obtain ⟨-, hna, hnb1, hnt, hne⟩ := hnb
        have hx2 : x.drop (q + 2) = a.ser ++ (b.ser ++ (t.ser ++ (el.ser ++ r))) := by
          have h0 : x.drop q = [4, u cc] ++ (a.ser ++ (b.ser ++ (t.ser ++ (el.ser ++ r)))) := by rw [hx]; simp [Nd.ser, toU]
          simpa using drop_shift h0
        have hx3 := drop_shift hx2
        have hx4 := drop_shift hx3
        have hx5 := drop_shift hx4
        have hf' : t.ser.length ≤ f' ∧ el.ser.length ≤ f' := by simp [Nd.ser] at hf; omega
        have hsl : (Nd.ite cc a b t el).ser.length = 2 + a.ser.length + b.ser.length + t.ser.length + el.ser.length := by
          simp [Nd.ser]; omega
        simp only [hdr, List.getD_cons_zero, show ((4 : UInt64) == 3) = false from rfl,
          show ((4 : UInt64) == 4) = true from rfl, Bool.false_eq_true, if_false, if_true]
        rw [show u q + 2 = u (q + 2) by rw [u2, uadd]]
        rcases u15_ok (by omega) hx2 hna with h0 | ⟨h1, -⟩
        · left; rw [h0, u15_zero', u15_zero']; rfl
        rw [h1]
        rcases u15_ok (by omega) hx3 hnb1 with h0 | ⟨h1', -⟩
        · left; rw [h0, u15_zero']; rfl
        rw [h1']
        have hne0 : (u (q + 2 + a.ser.length + b.ser.length) == 0) = false := by
          rw [u0, ueq (by omega) (by omega)]; exact decide_eq_false (by omega)
        simp only [hne0, Bool.false_eq_true, if_false]
        rcases u15_ok (by omega) hx4 hnt with h0 | ⟨h2, -⟩
        · left; rw [h0]; rfl
        rw [h2]
        have hne1 : (u (q + 2 + a.ser.length + b.ser.length + t.ser.length) == 0) = false := by
          rw [u0, ueq (by omega) (by omega)]; exact decide_eq_false (by omega)
        simp only [hne1, Bool.false_eq_true, if_false]
        exact hpush el t _ _ r _ hx5 hx4 hf'.2 hf'.1 hne hnt (by omega) (by omega) (by simp [NumSpec.opl])
      | letE s w0 v bd =>
        simp only [hdr, List.getD_cons_zero, show ((5 : UInt64) == 3) = false from rfl,
          show ((5 : UInt64) == 4) = false from rfl, show ((5 : UInt64) == 5) = true from rfl, Bool.false_eq_true,
          if_false, if_true]
        exact hleaf true false rfl rfl (by simp [NumSpec.leafW]) (by simp [NumSpec.leafL])
      | const v =>
        simp only [hdr, List.getD_cons_zero, show ((1 : UInt64) == 3) = false from rfl,
          show ((1 : UInt64) == 4) = false from rfl, show ((1 : UInt64) == 5) = false from rfl,
          show ((1 : UInt64) == 1) = true from rfl, Bool.false_eq_true, if_false, if_true]
        exact hleaf B C rfl rfl (by simp [NumSpec.leafW]) (by simp [NumSpec.leafL])
      | loc s wd =>
        simp only [hdr, List.getD_cons_zero, show ((2 : UInt64) == 3) = false from rfl,
          show ((2 : UInt64) == 4) = false from rfl, show ((2 : UInt64) == 5) = false from rfl,
          show ((2 : UInt64) == 1) = false from rfl, show ((2 : UInt64) == 2) = true from rfl, Bool.false_eq_true,
          if_false, if_true]
        simp only [NB] at hnb
        obtain ⟨hs, hwd⟩ := hnb
        have h1 : bget x (u q + 1) = u s := by rw [tag1_rd hx (by omega) (by simp [hdr])]; simp [hdr]
        have h2 : bget x (u q + 2) = u wd := by
          rw [show u q + 2 = u (q + 2) by rw [u2, uadd], rdh hx (by omega) (k := 2) (by simp [hdr])]; simp [hdr]
        rw [h1, h2, bget_u _ (by omega), hR s, cd_1]
        have hll : (if (u wd == 1) = true then cd (lv.getD s false) (le.getD s false) &&& 2 else 0) =
            two (wd == 1 && le.getD s false) := by
          rw [cd_2, show (1 : UInt64) = u 1 from rfl, ueq (by omega) (by omega)]
          by_cases h : wd = 1 <;> simp [h, two]
        rw [hll, w2t_0]
        cases hn : (lv.getD s false || (wd == 1 && le.getD s false))
        · right; simp only [Bool.not_false, if_true]
          obtain ⟨hn1, hn2⟩ := Bool.or_eq_false_iff.1 hn
          exact (lv82_none le lv L0 (.loc s wd) B C hn1 hn2).symm
        · simp only [Bool.not_true, Bool.false_eq_true, if_false]
          rw [w2_or', two_and]
          exact hleaf _ _ rfl hn rfl rfl
      | pair cs =>
        right; simp (config := {decide := true}) only [hdr, List.getD_cons_zero, Bool.false_eq_true, if_false]
        exact (lv82_none le lv L0 _ B C rfl rfl).symm
      | call id as =>
        right; simp (config := {decide := true}) only [hdr, List.getD_cons_zero, Bool.false_eq_true, if_false]
        exact (lv82_none le lv L0 _ B C rfl rfl).symm
      | prim pn as =>
        right; simp (config := {decide := true}) only [hdr, List.getD_cons_zero, Bool.false_eq_true, if_false]
        exact (lv82_none le lv L0 _ B C rfl rfl).symm
      | loop z s =>
        right; simp (config := {decide := true}) only [hdr, List.getD_cons_zero, Bool.false_eq_true, if_false]
        exact (lv82_none le lv L0 _ B C rfl rfl).symm
      | cont c =>
        right; simp (config := {decide := true}) only [hdr, List.getD_cons_zero, Bool.false_eq_true, if_false]
        exact (lv82_none le lv L0 _ B C rfl rfl).symm

theorem u83_ok {x F : Buf} {np : Nat} {le lv : List Bool} (hxl : x.length < 2 ^ 23) (hR : Rep F le lv) {e : Nd}
    {f q : Nat} {r : Buf} (hx : x.drop q = e.ser ++ r) (hf : e.ser.length ≤ f) (hnb : NB np e) (hq : 0 < q) {w : Buf}
    (hw : w.length < 2 ^ 62) :
    (u83 x F w (u q)).1.length < 2 ^ 62 ∧
      ((u83 x F w (u q)).2 = 4 ∨ (u83 x F w (u q)).2 = cd (NumSpec.wt f le lv e) (NumSpec.litE f le e)) := by
  unfold u83
  have e39 : (549755813888 : UInt64) = u (2 ^ 39) := rfl
  simp only [bsize_u, e39, ult (show w.length < 2 ^ 64 by omega) (show 2 ^ 39 < 2 ^ 64 by omega)]
  by_cases hs : w.length < 2 ^ 39
  · rw [if_pos hs]
    have hp := u20_push (vs := []) (v := w) List.nil_prefix (by omega) (u q)
    have h1 : [u q] <+: u20 w 0 (u q) := by have := hp.1; simp only [List.nil_append, List.length_nil] at this; exact this
    have hl : (u20 w 0 (u q)).length ≤ w.length + 1 := u20_len _ _ _
    refine ⟨by have := u82_len x F 16777216 (u20 w 0 (u q)) 1 0 2; omega, ?_⟩
    rw [u82_snd]
    have := U82_ok hxl hR 16777216 [(e, f, q)] (u20 w 0 (u q)) false true (by simpa using h1) (by omega)
      (by intro p hp; simp at hp; subst hp; exact ⟨⟨r, hx⟩, hf, hnb, hq⟩)
    rcases this with h | h
    · exact Or.inl h
    · right; refine h.trans ?_; rw [← lv82_wt]; simp
  · simp only [hs, if_false]; refine ⟨hw, ?_⟩; simp

theorem u78_ok : ∀ (n : Nat) (F : Buf) (s j k : Nat) (v : UInt64), j ≤ k → s + k < 2 ^ 62 → F.length < 2 ^ 62 →
    (u78 n F (u s) (u j) (u k) v).2 = 1 → (u78 n F (u s) (u j) (u k) v).1.length = F.length ∧
      ∀ p, (u78 n F (u s) (u j) (u k) v).1.getD p 0 = if s + j ≤ p ∧ p < s + k then v else F.getD p 0
  | 0, _, _, _, _, _, _, _, _, h => by simp [u78] at h
  | n + 1, F, s, j, k, v, hjk, hs, hF, h => by
    simp only [u78] at h ⊢
    by_cases hc : j < k
    · have hc' : u j < u k := by rw [ult (by omega) (by omega)]; exact hc
      rw [if_pos hc'] at h ⊢
      by_cases h2 : s + j < F.length
      · have hc2 : u s + u j < bsize F := by rw [uadd, bsize_u, ult (by omega) (by omega)]; exact h2
        rw [if_pos hc2] at h ⊢
        have e1 : u j + 1 = u (j + 1) := by rw [u1, uadd]
        rw [e1, uadd, bset_u _ (by omega)] at h ⊢
        have hF' : (F.set (s + j) v).length = F.length := by simp
        obtain ⟨l1, g1⟩ := u78_ok n _ s (j + 1) k v (by omega) hs (by omega) h
        refine ⟨by rw [l1, hF'], fun p => ?_⟩
        rw [g1 p, getD_set]
        by_cases hp : s + j = p
        · subst hp; simp [h2]; intro h'; omega
        · by_cases hp2 : s + (j + 1) ≤ p ∧ p < s + k
          · rw [if_pos hp2, if_pos (by omega)]
          · rw [if_neg hp2, if_neg (by omega), if_neg (by omega)]
      · have hc2 : ¬ (u s + u j < bsize F) := by rw [uadd, bsize_u, ult (by omega) (by omega)]; exact h2
        rw [if_neg hc2] at h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
    · have hc' : ¬ (u j < u k) := by rw [ult (by omega) (by omega)]; exact hc
      rw [if_neg hc']
      refine ⟨rfl, fun p => ?_⟩
      rw [if_neg (by omega)]

theorem rep_set {F F' : Buf} {le lv : List Bool} (hR : Rep F le lv) {s k : Nat} {a b : Bool}
    (h : ∀ p, F'.getD p 0 = if s ≤ p ∧ p < s + k then cd a b else F.getD p 0) :
    Rep F' (NumSpec.setW le s (List.replicate k b)) (NumSpec.setW lv s (List.replicate k a)) := by
  intro p
  rw [h p, setW_getD, setW_getD]
  simp only [List.length_replicate]
  by_cases hp : s ≤ p ∧ p < s + k
  · rw [if_pos hp, if_pos hp, if_pos hp]
    simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, show p - s < k by omega]
  · rw [if_neg hp, if_neg hp, if_neg hp]; exact hR p

/-- `u85`: one tuple field -/
theorem u85_ok {np : Nat} {x : Buf} (hl : x.length < 2 ^ 23) (f0 : Nat) {c : Nd} {q : Nat} {r : Buf}
    (hx : x.drop q = c.ser ++ r) (hnc : NB np c) (hfc : c.ser.length ≤ f0) (hq : 0 < q) {F w : Buf} {le lv : List Bool}
    (hw : w.length < 2 ^ 62) (hF : F.length < 2 ^ 62) {s j : Nat} (hsj : s + j + 1 < 2 ^ 62) (hR : Rep F le lv) :
    (u85 x F w (u q) (u s) (u j)).2.2.2 = 1 →
    (u85 x F w (u q) (u s) (u j)).2.2.1 = u (q + c.ser.length) ∧
    Rep (u85 x F w (u q) (u s) (u j)).1 (NumSpec.bind1 f0 le lv (s + j) 1 c).1 (NumSpec.bind1 f0 le lv (s + j) 1 c).2 ∧
    (u85 x F w (u q) (u s) (u j)).2.1.length < 2 ^ 62 ∧ (u85 x F w (u q) (u s) (u j)).1.length = F.length := by
  have hcl := drop_len hx (ser_pos c)
  unfold u85
  obtain ⟨hw1, h83⟩ := u83_ok (f := f0) hl hR hx hfc hnc hq hw
  generalize u83 x F w (u q) = V at hw1 h83 ⊢
  obtain ⟨w1, rr⟩ := V
  dsimp only at hw1 h83 ⊢
  rcases h83 with h4 | h83
  · subst h4; rw [if_pos (keq rfl)]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
  subst h83
  rw [if_neg (kne (cd_ne4 _ _))]
  rcases u15_ok (by omega) hx hnc with h15 | ⟨h15, -⟩
  · rw [h15, if_pos (keq rfl)]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
  have hne : (u (q + c.ser.length) == 0) = false := by
    rw [u0, ueq (by omega) (by omega)]; exact decide_eq_false (by omega)
  rw [h15, if_neg (kne hne)]
  have e1 : u j + 1 = u (j + 1) := by rw [u1, uadd]
  rw [e1]
  have h78 := u78_ok 16777216 F s j (j + 1) (cd (NumSpec.wt f0 le lv c) (NumSpec.litE f0 le c)) (by omega) (by omega) hF
  generalize u78 16777216 F (u s) (u j) (u (j + 1)) (cd (NumSpec.wt f0 le lv c) (NumSpec.litE f0 le c)) = M at h78 ⊢
  obtain ⟨F1, ok⟩ := M
  dsimp only at h78 ⊢
  intro hok
  subst hok
  obtain ⟨hl1, hg1⟩ := h78 rfl
  refine ⟨rfl, rep_set (k := 1) hR (s := s + j) (a := NumSpec.wt f0 le lv c) (b := NumSpec.litE f0 le c)
    (fun p => by rw [hg1 p, show s + (j + 1) = s + j + 1 by omega]), hw1, hl1⟩

/-- `u76`: the fields of a tuple value, field by field -/
theorem u76_ok {np : Nat} {x : Buf} (hl : x.length < 2 ^ 23) (f0 s : Nat) :
    ∀ (n : Nat) (cs : List Nd) (F w : Buf) (q j : Nat) (r : Buf) (le lv : List Bool), x.drop q = serL cs ++ r →
    (∀ c ∈ cs, NB np c ∧ c.ser.length ≤ f0) → 0 < q → w.length < 2 ^ 62 → F.length < 2 ^ 62 →
    s + j + cs.length < 2 ^ 62 → Rep F le lv →
    (u76 n x F w (u q) (u s) (u j) (u (j + cs.length))).2.2 = 1 →
    Rep (u76 n x F w (u q) (u s) (u j) (u (j + cs.length))).1 (NumSpec.bindF f0 (le, lv) (s + j) cs).1
        (NumSpec.bindF f0 (le, lv) (s + j) cs).2 ∧
      (u76 n x F w (u q) (u s) (u j) (u (j + cs.length))).2.1.length < 2 ^ 62 ∧
      (u76 n x F w (u q) (u s) (u j) (u (j + cs.length))).1.length = F.length
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [u76] at h
  | n + 1, [], F, w, q, j, r, le, lv, _, _, _, hw, _, _, hR, _ => by
    have : ¬ (u j < u (j + ([] : List Nd).length)) := by rw [ult (by simp; omega) (by simp; omega)]; simp
    simp only [u76]; rw [if_neg this]; exact ⟨hR, hw, rfl⟩
  | n + 1, c :: cs, F, w, q, j, r, le, lv, hx, hcs, hq, hw, hF, hsj, hR, h => by
    obtain ⟨hnc, hfc⟩ := hcs c (by simp)
    have hx' : x.drop q = c.ser ++ (serL cs ++ r) := by rw [hx]; simp [serL]
    have hx2 := drop_shift hx'
    simp only [List.length_cons] at hsj h ⊢
    have hc : u j < u (j + (cs.length + 1)) := by rw [ult (by omega) (by omega)]; omega
    simp only [u76] at h ⊢
    rw [if_pos hc] at h ⊢
    have h85 := u85_ok hl f0 hx' hnc hfc hq hw hF (s := s) (j := j) (by omega) hR
    generalize u85 x F w (u q) (u s) (u j) = V at h85 h ⊢
    obtain ⟨F1, w1, e, ok⟩ := V
    dsimp only at h85 h ⊢
    by_cases hok : ok = 1
    · subst hok
      rw [if_pos (keq rfl)] at h ⊢
      obtain ⟨he, hR1, hw1, hl1⟩ := h85 rfl
      subst he
      have e1 : u j + 1 = u (j + 1) := by rw [u1, uadd]
      have e2 : u (j + (cs.length + 1)) = u (j + 1 + cs.length) := by congr 1; omega
      rw [e1, e2] at h ⊢
      have ih := u76_ok hl f0 s n cs F1 w1 (q + c.ser.length) (j + 1) r _ _ hx2 (fun c' h' => hcs c' (by simp [h']))
        (by omega) hw1 (by rw [hl1]; exact hF) (by omega) hR1 h
      rw [show s + (j + 1) = s + j + 1 by omega] at ih
      exact ⟨ih.1, ih.2.1, by rw [ih.2.2, hl1]⟩
    · rw [if_neg (by simpa using hok)] at h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)

theorem lateStep_pair (f0 : Nat) (le lv : List Bool) (ok : Bool) (s w : Nat) (cs : List Nd) (b : Nd) :
    NumSpec.lateStep f0 (le, lv, ok) (.letE s w (.pair cs) b) =
      ((NumSpec.bindF f0 (le, lv) s cs).1, (NumSpec.bindF f0 (le, lv) s cs).2, ok) := by
  simp only [NumSpec.lateStep]

theorem lateStep_np (f0 : Nat) (le lv : List Bool) (ok : Bool) (s w : Nat) (v b : Nd) (hv : (hdr v).getD 0 0 ≠ 6) :
    NumSpec.lateStep f0 (le, lv, ok) (.letE s w v b) =
      ((NumSpec.bind1 f0 le lv s w v).1, (NumSpec.bind1 f0 le lv s w v).2, ok) := by
  cases v <;> first | (simp [hdr] at hv; done) | rfl | simp [NumSpec.lateStep, NumSpec.bind1]

/-- `u75`: the slots of `let s := v` -/
theorem u75_ok {np : Nat} {x : Buf} (hl : x.length < 2 ^ 23) (f0 : Nat) {v : Nd} {q : Nat} {r : Buf} {s wd : Nat}
    (hx : x.drop q = v.ser ++ r) (hnb : NB np v) (hf : v.ser.length ≤ f0) (hq : 0 < q) {F w : Buf} {le lv : List Bool}
    (hw : w.length < 2 ^ 62) (hF : F.length < 2 ^ 62) (hs : s < 2 ^ 32) (hwd : wd < 2 ^ 32) (hR : Rep F le lv) (bd : Nd) :
    (u75 x F w (u q) (u s) (u wd)).2.2 = 1 →
    ∃ le' lv', NumSpec.lateStep f0 (le, lv, true) (.letE s wd v bd) = (le', lv', true) ∧
      Rep (u75 x F w (u q) (u s) (u wd)).1 le' lv' ∧ (u75 x F w (u q) (u s) (u wd)).2.1.length < 2 ^ 62 ∧
      (u75 x F w (u q) (u s) (u wd)).1.length = F.length := by
  have hcl := drop_len hx (ser_pos v)
  unfold u75
  rw [tag_rd hx (by omega)]
  by_cases hv : (hdr v).getD 0 0 = 6
  · cases v with
    | pair cs =>
      rw [if_pos (show ((hdr (Nd.pair cs)).getD 0 0 == 6) = true from rfl)]
      simp only [NB] at hnb
      obtain ⟨hcsl, hcs⟩ := hnb
      have h1 : bget x (u q + 1) = u cs.length := by
        rw [tag1_rd hx (by omega) (by simp [hdr])]; simp [hdr]
      have hx2 : x.drop (q + 2) = serL cs ++ r := by
        have h0 : x.drop q = [6, u cs.length] ++ (serL cs ++ r) := by rw [hx]; simp [Nd.ser, toU]
        simpa using drop_shift h0
      rw [h1, show u q + 2 = u (q + 2) by rw [u2, uadd]]
      have hf' : (serL cs).length + 2 ≤ f0 := by simp [Nd.ser] at hf; omega
      intro h
      have := u76_ok hl f0 s 16777216 cs F w (q + 2) 0 r le lv hx2
        (fun c hc => ⟨(nbl_iff cs).1 hcs c hc, by have := mem_serL_len hc; omega⟩) (by omega) hw hF (by omega) hR
        (by rw [Nat.zero_add]; exact h)
      rw [Nat.zero_add, Nat.add_zero] at this
      exact ⟨_, _, lateStep_pair f0 le lv true s wd cs bd, this⟩
    | _ => simp [hdr] at hv
  · rw [if_neg (by simpa using hv)]
    obtain ⟨hw1, h83⟩ := u83_ok (f := f0) hl hR hx hf hnb hq hw
    generalize u83 x F w (u q) = V at hw1 h83 ⊢
    obtain ⟨w1, rr⟩ := V
    dsimp only at hw1 h83 ⊢
    rcases h83 with h4 | h83
    · subst h4; rw [if_pos (keq rfl)]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
    subst h83
    rw [if_neg (kne (cd_ne4 _ _))]
    have h78 := u78_ok 16777216 F s 0 wd (cd (NumSpec.wt f0 le lv v) (NumSpec.litE f0 le v)) (by omega) (by omega) hF
    rw [show u 0 = (0 : UInt64) from rfl] at h78
    generalize u78 16777216 F (u s) 0 (u wd) (cd (NumSpec.wt f0 le lv v) (NumSpec.litE f0 le v)) = M at h78 ⊢
    obtain ⟨F1, ok⟩ := M
    dsimp only at h78 ⊢
    intro h
    subst h
    obtain ⟨hl1, hg1⟩ := h78 rfl
    exact ⟨_, _, lateStep_np f0 le lv true s wd v bd hv, rep_set hR (fun p => by rw [hg1 p, Nat.add_zero]), hw1, hl1⟩

/-- `u84`: the step at one node -/
theorem u84_ok {np : Nat} {x : Buf} (hl : x.length < 2 ^ 23) (f0 : Nat) {e : Nd} {i : Nat} {r : Buf}
    (hx : x.drop i = e.ser ++ r) (hnb : NB np e) (hf : e.ser.length ≤ f0) (hi : 0 < i) {F w : Buf} {le lv : List Bool}
    (hw : w.length < 2 ^ 62) (hF : F.length < 2 ^ 62) (hR : Rep F le lv) :
    (u84 x F w (u i)).2.2 = 1 →
    ∃ le' lv', NumSpec.lateStep f0 (le, lv, true) e = (le', lv', true) ∧
      Rep (u84 x F w (u i)).1 le' lv' ∧ (u84 x F w (u i)).2.1.length < 2 ^ 62 ∧ (u84 x F w (u i)).1.length = F.length := by
  have hcl := drop_len hx (ser_pos e)
  unfold u84
  rw [tag_rd hx (by omega)]
  have hrd : ∀ m, m < e.ser.length → bget x (u i + u m) = e.ser.getD m 0 := by
    intro m hm; rw [uadd, rd hx hm (by omega)]
  cases e with
  | letE s wd v bd =>
    simp only [hdr, List.getD_cons_zero, show ((5 : UInt64) == 5) = true from rfl, if_true]
    simp only [NB] at hnb
    obtain ⟨hs, hwd, hnv, -⟩ := hnb
    have h1 : bget x (u i + 1) = u s := by rw [show (1 : UInt64) = u 1 from rfl, hrd 1 (by simp [Nd.ser])]; simp [Nd.ser, toU]
    have h2 : bget x (u i + 2) = u wd := by rw [show (2 : UInt64) = u 2 from rfl, hrd 2 (by simp [Nd.ser])]; simp [Nd.ser, toU]
    have hx3 : x.drop (i + 3) = v.ser ++ (bd.ser ++ r) := by
      have h0 : x.drop i = [5, u s, u wd] ++ (v.ser ++ (bd.ser ++ r)) := by rw [hx]; simp [Nd.ser, toU]
      simpa using drop_shift h0
    rw [h1, h2, show u i + 3 = u (i + 3) by rw [u3, uadd]]
    exact u75_ok hl f0 hx3 hnv (by simp [Nd.ser] at hf; omega) (by omega) hw hF hs hwd hR bd
  | bin op a b =>
    simp only [hdr, List.getD_cons_zero, show ((3 : UInt64) == 5) = false from rfl, Bool.false_eq_true, if_false]
    rw [u34_ok hx (by omega) hnb]
    by_cases hsh : NumSpec.isShift op
    · simp only [shN, hsh, show (w2 true == 1) = true from rfl, if_true]
      simp only [NB] at hnb
      obtain ⟨-, hna, -⟩ := hnb
      have hx2 : x.drop (i + 2) = a.ser ++ (b.ser ++ r) := by
        have h0 : x.drop i = [3, u op] ++ (a.ser ++ (b.ser ++ r)) := by rw [hx]; simp [Nd.ser, toU]
        simpa using drop_shift h0
      rw [show u i + 2 = u (i + 2) by rw [u2, uadd]]
      obtain ⟨hw1, h83⟩ := u83_ok (f := f0) hl hR hx2 (by simp [Nd.ser] at hf; omega) hna (by omega) hw
      generalize u83 x F w (u (i + 2)) = V at hw1 h83 ⊢
      obtain ⟨w1, rr⟩ := V
      dsimp only at hw1 h83 ⊢
      rcases h83 with h4 | h83
      · subst h4; rw [if_pos (keq rfl)]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
      subst h83
      rw [if_neg (kne (cd_ne4 _ _)), cd_1]
      cases hW : NumSpec.wt f0 le lv a
      · simp only [show (w2 false == 1) = false from rfl, Bool.false_eq_true, if_false]
        intro _
        exact ⟨le, lv, by simp [NumSpec.lateStep, hsh, hW], hR, hw1, by simp⟩
      · simp only [show (w2 true == 1) = true from rfl, if_true]
        intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
    · simp only [shN, hsh, show (w2 false == 1) = false from rfl, Bool.false_eq_true, if_false]
      intro _
      exact ⟨le, lv, by simp [NumSpec.lateStep, hsh], hR, hw, by simp⟩
  | _ =>
    simp (config := {decide := true}) only [hdr, List.getD_cons_zero, Bool.false_eq_true, if_false]
    rw [u34_ok hx (by omega) hnb]
    simp only [shN, show (w2 false == 1) = false from rfl, Bool.false_eq_true, if_false]
    intro _
    exact ⟨le, lv, rfl, hR, hw, by simp⟩

theorem u73_ok {np : Nat} {x : Buf} (hl : x.length < 2 ^ 23) (f0 : Nat) :
    ∀ (n : Nat) (es : List (Nd × Nat)) (r : Buf) (i : Nat) (F w : Buf) (le lv : List Bool),
    x.drop i = serL (es.map Prod.fst) ++ r → (∀ p ∈ es, NB np p.1 ∧ p.1.ser.length ≤ p.2 ∧ p.1.ser.length ≤ f0) →
    0 < i → w.length < 2 ^ 62 → F.length < 2 ^ 62 → Rep F le lv → (u73 n x F w (u i) (u es.length)).2.2 = 1 →
    ((es.flatMap fun p => NumSpec.nodes p.2 p.1).foldl (NumSpec.lateStep f0) (le, lv, true)).2.2 = true ∧
      (u73 n x F w (u i) (u es.length)).2.1.length < 2 ^ 62 ∧ (u73 n x F w (u i) (u es.length)).1.length = F.length
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [u73] at h
  | n + 1, [], r, i, F, w, le, lv, _, _, _, hw, _, _, _ => by simp [u73, show u 0 = 0 from rfl, hw]
  | n + 1, (e, k) :: es, r, i, F, w, le, lv, hx, hnb, hi, hw, hF, hR, h => by
    obtain ⟨hne, hk, hkf⟩ := hnb (e, k) (by simp)
    simp only at hne hk hkf
    have hx0 : x.drop i = serL (e :: es.map Prod.fst) ++ r := by simpa using hx
    have hnb0 : ∀ c ∈ e :: es.map Prod.fst, NB np c := by
      intro c hc; simp only [List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨p, hp, rfl⟩
      · exact hne
      · exact (hnb p (by simp [hp])).1
    obtain ⟨hx', hx2, hnb2, hkl, hil⟩ := scan_step hx0 hnb0 hl
    simp only [List.length_map] at hkl
    have hne0 : (u (es.length + 1) == 0) = false := by rw [u0, ueq (by omega) (by omega)]; simp
    rw [List.length_cons] at h ⊢
    simp only [u73] at h ⊢
    rw [if_neg (kne hne0)] at h ⊢
    have h84 := u84_ok hl f0 hx' hne hkf hi hw hF hR
    generalize u84 x F w (u i) = V at h84 h ⊢
    obtain ⟨F1, w1, ok⟩ := V
    dsimp only at h84 h ⊢
    rw [u77_node hx' hne (by omega) hkl] at h ⊢
    dsimp only at h ⊢
    by_cases hok : ok = 1
    · subst hok
      rw [if_pos (keq rfl)] at h ⊢
      obtain ⟨le', lv', hst, hR1, hw1, hl1⟩ := h84 rfl
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := ser_pos e; omega⟩
      have hes : ((kids e).map (·, k') ++ es).map Prod.fst = kids e ++ es.map Prod.fst := by
        simp [List.map_append, List.map_map, Function.comp_def]
      have ih := u73_ok hl f0 n ((kids e).map (·, k') ++ es) r _ F1 w1 le' lv' (by rw [hes]; exact hx2) (by
          intro p hp
          simp only [List.mem_append, List.mem_map] at hp
          rcases hp with ⟨c, hc, rfl⟩ | hp
          · have := kid_len hc
            exact ⟨nb_kids hne c hc, by simp only; omega, by simp only; omega⟩
          · exact hnb p (by simp [hp]))
        (by omega) hw1 (by rw [hl1]; exact hF) hR1
      have hl2 : ((kids e).map (·, k') ++ es).length = es.length + (kids e).length := by simp; omega
      rw [hl2] at ih
      obtain ⟨i1, i2, i3⟩ := ih h
      refine ⟨?_, i2, by rw [i3, hl1]⟩
      rw [List.flatMap_cons, nodes_succ, List.cons_append, List.foldl_cons, hst]
      have : (kids e).flatMap (NumSpec.nodes k') ++ es.flatMap (fun p => NumSpec.nodes p.2 p.1) =
          ((kids e).map (·, k') ++ es).flatMap (fun p => NumSpec.nodes p.2 p.1) := by
        rw [List.flatMap_append]; congr 1
        generalize kids e = ks
        induction ks with
        | nil => rfl
        | cons c cs ih => simp [ih]
      rw [this]; exact i1
    · rw [if_neg (by simpa using hok)] at h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)

/-- **the late-slot check**: `u79` accepts only if `lateOk` holds -/
theorem u79_ok {np : Nat} {x : Buf} (hl : x.length < 2 ^ 23) {e : Nd} {r : Buf} {i ns : Nat}
    (h3 : bget x (u i + 3) = u ns) (hns : ns < 2 ^ 32) (hx : x.drop (i + 6) = e.ser ++ r) (hnb : NB np e)
    (hf : e.ser.length ≤ 2 ^ 24) (hi : 0 < i) {y1 y2 : Buf} (h1 : y1.length < 2 ^ 62) (h2 : y2.length < 2 ^ 62) :
    (u79 x y1 y2 (u i)).2.2 = 1 →
    NumSpec.lateOk (2 ^ 24) e = true ∧ (u79 x y1 y2 (u i)).2.1.length < 2 ^ 62 ∧ (u79 x y1 y2 (u i)).1.length < 2 ^ 62 := by
  unfold u79
  rw [h3]
  have hN : (if u ns < bsize y2 then bsize y2 else u ns) = u (max y2.length ns) := by
    split
    · rename_i h; rw [bsize_u, ult (by omega) (by omega)] at h; rw [bsize_u, Nat.max_eq_left (by omega)]
    · rename_i h; rw [bsize_u, ult (by omega) (by omega)] at h; rw [Nat.max_eq_right (by omega)]
  dsimp only
  rw [hN]
  have z0 := u57_ok 16777216 y2 0 (max y2.length ns) (by omega) (by omega) h2 (by omega) (by intro i hi; omega)
  rw [show u 0 = (0 : UInt64) from rfl] at z0
  generalize u57 16777216 y2 0 (u (max y2.length ns)) = Z at z0 ⊢
  obtain ⟨f0, k0⟩ := Z
  dsimp only at z0 ⊢
  by_cases hk0 : k0 = 1
  · subst hk0
    rw [if_pos (keq rfl)]
    obtain ⟨hz1, hz2, hz3⟩ := z0 rfl
    have hR : Rep f0 [] [] := by
      intro p
      by_cases hp : p < max y2.length ns
      · rw [hz3 p hp]; simp [cd, two, w2]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp [cd, two, w2]
    have e6 : u i + 6 = u (i + 6) := by rw [show (6 : UInt64) = u 6 from rfl, uadd]
    rw [e6]
    intro h
    have := u73_ok (np := np) hl (2 ^ 24) 16777216 [(e, 2 ^ 24)] r (i + 6) f0 y1 [] [] (by simpa [serL] using hx)
      (by intro p hp; simp at hp; subst hp; exact ⟨hnb, hf, hf⟩) (by omega) h1 (by omega) hR h
    refine ⟨?_, this.2.1, lt_of_eq_of_lt this.2.2 (by omega)⟩
    have h0 := this.1
    simpa [NumSpec.lateOk] using h0
  · rw [if_neg (by simpa using hk0)]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)

end NumP
