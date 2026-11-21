/- Nano/Parser/NumP16: LIT (`litG`: the slots and the arithmetic flag of a literal-only expression). -/
import Nano.Parser.NumP15
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

theorem u49_1 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb a a2 : UInt64) :
    u49 x d b bt t tt c s st gb 1 a a2 = u44 x d b bt t tt c s st gb := by
  unfold u49; rw [if_neg (kne (show ((1 : UInt64) == 0) = false from rfl)), if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))]

section
variable {x d b : Buf} {bt : UInt64} {t : Buf} {tt c : UInt64} {s : Buf} {st gb : UInt64}

theorem u44_2 (hg : bget x c = 2) :
    u44 x d b bt t tt c s st gb = (b, (bt, (t, (tt, (c + 3, (u20 s st (bget x (c + 1)), (st + 1, (gb, 1)))))))) := by
  unfold u44; rw [hg]; zeta_only; rw [if_pos (keq (show ((2 : UInt64) == 2) = true from rfl))]

theorem u44_3 (hg : bget x c = 3) :
    u44 x d b bt t tt c s st gb = (b, (bt, (u27 (u27 t tt 1 0 0) (tt + 1) 1 0 0, (tt + 2, (c + 2, (bset s gb 1, (st, (gb, 1)))))))) := by
  unfold u44; rw [hg]; zeta_only
  rw [if_neg (kne (show ((3 : UInt64) == 2) = false from rfl)), if_pos (keq (show ((3 : UInt64) == 3) = true from rfl))]

theorem u44_4 (hg : bget x c = 4) :
    u44 x d b bt t tt c s st gb =
      (b, (bt, (u27 (u27 (u27 t tt 1 0 0) (tt + 1) 1 0 0) (tt + 2) 2 0 0, (tt + 3, (c + 2, (s, (st, (gb, 1)))))))) := by
  unfold u44; rw [hg]; zeta_only
  rw [if_neg (kne (show ((4 : UInt64) == 2) = false from rfl)), if_neg (kne (show ((4 : UInt64) == 3) = false from rfl)),
    if_pos (keq (show ((4 : UInt64) == 4) = true from rfl))]

theorem u44_5 (hg : bget x c = 5) :
    u44 x d b bt t tt c s st gb =
      (b, (bt, (u27 (u27 (u27 (u27 t tt 5 bt 0) (tt + 1) 1 0 0) (tt + 2) 6 (bget x (c + 1)) (c + 3)) (tt + 3) 3 (bget x (c + 1)) 0,
       (tt + 4, (c + 3, (s, (st, (gb, 1)))))))) := by
  unfold u44; rw [hg]; zeta_only
  rw [if_neg (kne (show ((5 : UInt64) == 2) = false from rfl)), if_neg (kne (show ((5 : UInt64) == 3) = false from rfl)),
    if_neg (kne (show ((5 : UInt64) == 4) = false from rfl)), if_pos (keq (show ((5 : UInt64) == 5) = true from rfl))]

theorem u44_skip {k : UInt64} (hg : bget x c = k) (h2 : (k == 2) = false) (h3 : (k == 3) = false) (h4 : (k == 4) = false)
    (h5 : (k == 5) = false) :
    u44 x d b bt t tt c s st gb = (b, (bt, (t, (tt, (u15 x c, (s, (st, (gb, (if u15 x c == 0 then 0 else 1))))))))) := by
  unfold u44; rw [hg]; zeta_only
  rw [if_neg (kne h2), if_neg (kne h3), if_neg (kne h4), if_neg (kne h5)]

end

/-- LIT entry: the u44 result -/
theorem m_lit_read {x d : Buf} {Q : MO → Prop} (hQ : QM Q) {b bs t ts g s S} {c gb : UInt64}
    (hI : MI b bs t (ts ++ [(1, 0, 0)]) g s S)
    (H : SZ b t g s → ∀ R : R9, u44 x d b (u (encB bs).length) t (u ts.length) c s (u S.length) gb = R →
      R.2.2.2.2.2.2.2.2 = 1 → GM x d Q R.1 R.2.1 R.2.2.1 R.2.2.2.1 R.2.2.2.2.1 g R.2.2.2.2.2.1 R.2.2.2.2.2.2.1 R.2.2.2.2.2.2.2.1) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) c g s (u S.length) gb := by
  apply m_read hQ (Or.inr (Or.inl rfl)) hI _ (fun _ => rfl)
  intro hsz
  rw [u49_1]
  exact H hsz _ rfl

/-- the common hypotheses of a LIT case at fuel f + 1 -/
structure LH (x d : Buf) (np : Nat) (f : Nat) (e : Nd) (Q : MO → Prop) (c : Nat) (rest : Buf) : Prop where
  hf : e.ser.length ≤ f + 1
  hnb : NB np e
  hQ : QM Q
  hx : x.drop c = e.ser ++ rest
  hc : 0 < c

/-- LIT at a node that adds nothing (a constant; a node that is not literal-only): skip it -/
theorem m_lit_skip {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} {e : Nd}
    {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat} {rest b t g s : Buf}
    {S0 : List UInt64} {a0 : Bool} {SL : List UInt64} (hH : LH x d np f e Q c rest)
    (hk2 : ((hdr e).getD 0 0 == 2) = false) (hk3 : ((hdr e).getD 0 0 == 3) = false)
    (hk4 : ((hdr e).getD 0 0 == 4) = false) (hk5 : ((hdr e).getD 0 0 == 5) = false)
    (hsk : NumSpec.litG (f + 1) ks ws (envOf bs) e = (([], false), NumSpec.R.ok))
    (hI : MI b bs t (ts ++ [(1, 0, 0)]) g s (S0 ++ w2 a0 :: SL))
    (hP : MLp x d Q bs ts g S0 a0 SL (c + e.ser.length) (NumSpec.litG (f + 1) ks ws (envOf bs) e)) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u (S0 ++ w2 a0 :: SL).length) (u S0.length) := by
  apply m_lit_read hH.hQ hI
  intro hsz R hR hok
  have hxl : x.length < 2 ^ 62 := by have := hK.lc.xl; omega
  rw [u44_skip (tag_rd hH.hx hxl) hk2 hk3 hk4 hk5] at hR
  rcases u15_ok (by omega) hH.hx hH.hnb with h1 | ⟨h1, -⟩
  · rw [h1] at hR; subst hR; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)
  have hcl := drop_len hH.hx (ser_pos e)
  have hne : (u (c + e.ser.length) == 0) = false := by
    rw [u0, ueq (by omega) (by omega)]; exact decide_eq_false (by have := hH.hc; omega)
  rw [h1, if_neg (kne hne)] at hR
  subst hR
  rw [hsk] at hP
  exact (hP rfl b t g s (by simpa using hI.pop) (GA.nil g)).cast rfl rfl rfl (by simp) rfl

/-- LIT at a slot: the slot joins the open group -/
theorem m_lit_loc {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} {sl w : Nat}
    {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat} {rest b t g s : Buf}
    {S0 : List UInt64} {a0 : Bool} {SL : List UInt64} (hH : LH x d np f (.loc sl w) Q c rest)
    (hI : MI b bs t (ts ++ [(1, 0, 0)]) g s (S0 ++ w2 a0 :: SL))
    (hP : MLp x d Q bs ts g S0 a0 SL (c + (Nd.loc sl w).ser.length) (NumSpec.litG (f + 1) ks ws (envOf bs) (.loc sl w))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u (S0 ++ w2 a0 :: SL).length) (u S0.length) := by
  apply m_lit_read hH.hQ hI
  intro hsz R hR hok
  have hxl : x.length < 2 ^ 62 := by have := hK.lc.xl; omega
  rw [u44_2 (tag_rd hH.hx hxl), tag1 hH.hx hxl (by simp [hdr])] at hR
  simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at hR
  subst hR
  dsimp only
  rw [litG_succ] at hP; dsimp only at hP
  obtain ⟨h1, -⟩ := hI.pop.spush (by have := hsz.2.2.2; omega) (u sl)
  have e1 : u (S0 ++ w2 a0 :: SL).length + 1 = u (S0 ++ w2 (a0 || false) :: (SL ++ [sl].map u)).length := by
    simp only [List.length_append, List.length_cons, List.length_map, List.length_nil, u1, uadd]; congr 1
  rw [e1]
  refine (hP rfl b t g _ ?_ (GA.nil g)).cast rfl rfl (by simp [Nd.ser, u3, uadd]) rfl rfl
  simpa using h1

theorem MI.castS {b bs t ts g s S S'} (h : MI b bs t ts g s S) (e : S = S') : MI b bs t ts g s S' := e ▸ h

/-- LIT at an operator: the group does arithmetic; LIT on both operands -/
theorem m_lit_bin {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hLIT : MLIT x d np ks ws f)
    {op : Nat} {a bb : Nd}
    {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat} {rest b t g s : Buf}
    {S0 : List UInt64} {a0 : Bool} {SL : List UInt64} (hH : LH x d np f (.bin op a bb) Q c rest)
    (hI : MI b bs t (ts ++ [(1, 0, 0)]) g s (S0 ++ w2 a0 :: SL))
    (hP : MLp x d Q bs ts g S0 a0 SL (c + (Nd.bin op a bb).ser.length) (NumSpec.litG (f + 1) ks ws (envOf bs) (.bin op a bb))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u (S0 ++ w2 a0 :: SL).length) (u S0.length) := by
  apply m_lit_read hH.hQ hI
  intro hsz R hR hok
  have hxl : x.length < 2 ^ 62 := by have := hK.lc.xl; omega
  rw [u44_3 (tag_rd hH.hx hxl)] at hR
  subst hR
  dsimp only
  rw [litG_succ] at hP; dsimp only at hP
  have hnb := hH.hnb; simp only [NB] at hnb
  obtain ⟨-, na, nb⟩ := hnb
  have hf := hH.hf; simp [Nd.ser] at hf
  have hx1 : x.drop (c + 2) = a.ser ++ (bb.ser ++ rest) := by
    have h0 : x.drop c = [3, u op] ++ (a.ser ++ (bb.ser ++ rest)) := by rw [hH.hx]; simp [Nd.ser, toU]
    simpa using drop_shift h0
  have hx2 := drop_shift hx1
  have hts := hI.lts; simp at hts
  have hI0 := hI.pop
  have hSl := hI0.ps.length_le
  have hs1 : bset s (u S0.length) 1 = s.set S0.length 1 := bset_u _ (by have := hI0.ls; simp at hSl; omega) _
  have hI1 : MI b bs t ts g (s.set S0.length 1) (S0 ++ w2 true :: SL) :=
    ⟨hI0.pb, hI0.lb, hI0.sb, hI0.pt, hI0.lt, hI0.lg, set_prefix hI0.ps _, by simpa using hI0.ls⟩
  obtain ⟨k1, l1⟩ := hI1.pushw rfl (by have := hsz.2.1; omega) 1 0 0
  obtain ⟨k2, -⟩ := k1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 1 0 0
  rw [hs1]
  refine (hLIT a Q bs (ts ++ [(1, 0, 0)]) (c + 2) (bb.ser ++ rest) b _ g _ S0 true SL (by omega) na hH.hQ hx1 (by omega)
    (by simpa using k2) ?_).cast rfl (by simp [u2, uadd]) (by simp [u2, uadd]) (by simp) rfl
  intro hA b2 t2 g2 s2 hI2 hga
  refine (hLIT bb Q bs ts (c + 2 + a.ser.length) rest b2 t2 g2 s2 S0 _ _ (by omega) nb hH.hQ hx2 (by omega)
    (by simpa using hI2) ?_).cast rfl (by simp) rfl rfl rfl
  intro hB b3 t3 g3 s3 hI3 hgb
  have e : c + 2 + a.ser.length + bb.ser.length = c + (Nd.bin op a bb).ser.length := by simp [Nd.ser]; omega
  rw [e]
  have hS : S0 ++ w2 (true || (NumSpec.litG f ks ws (envOf bs) a).1.2 || (NumSpec.litG f ks ws (envOf bs) bb).1.2) ::
      (SL ++ List.map u (NumSpec.litG f ks ws (envOf bs) a).1.1 ++ List.map u (NumSpec.litG f ks ws (envOf bs) bb).1.1) =
      S0 ++ w2 (a0 || true) :: (SL ++ List.map u ((NumSpec.litG f ks ws (envOf bs) a).1.1 ++
        (NumSpec.litG f ks ws (envOf bs) bb).1.1)) := by simp
  rw [hS] at hI3 ⊢
  exact hP (by simp [NumSpec.R.app, hA, hB]) b3 t3 g3 s3 hI3 (hga.trans hgb)

/-- LIT at an if: CMP on the condition (its own groups), LIT on both branches -/
theorem m_lit_ite {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hLIT : MLIT x d np ks ws f)
    (hCMP : MCMP x d np ks ws f) {cm : Nat} {a bb tb eb : Nd}
    {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat} {rest b t g s : Buf}
    {S0 : List UInt64} {a0 : Bool} {SL : List UInt64} (hH : LH x d np f (.ite cm a bb tb eb) Q c rest)
    (hI : MI b bs t (ts ++ [(1, 0, 0)]) g s (S0 ++ w2 a0 :: SL))
    (hP : MLp x d Q bs ts g S0 a0 SL (c + (Nd.ite cm a bb tb eb).ser.length)
      (NumSpec.litG (f + 1) ks ws (envOf bs) (.ite cm a bb tb eb))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u (S0 ++ w2 a0 :: SL).length) (u S0.length) := by
  apply m_lit_read hH.hQ hI
  intro hsz R hR hok
  have hxl : x.length < 2 ^ 62 := by have := hK.lc.xl; omega
  rw [u44_4 (tag_rd hH.hx hxl)] at hR
  subst hR
  dsimp only
  rw [litG_succ] at hP; dsimp only at hP
  have hnb := hH.hnb; simp only [NB] at hnb
  obtain ⟨-, na, nb, nt, ne⟩ := hnb
  have hf := hH.hf; simp [Nd.ser] at hf
  have := ser_pos a; have := ser_pos bb; have := ser_pos tb; have := ser_pos eb
  have hx1 : x.drop (c + 2) = a.ser ++ (bb.ser ++ (tb.ser ++ (eb.ser ++ rest))) := by
    have h0 : x.drop c = [4, u cm] ++ (a.ser ++ (bb.ser ++ (tb.ser ++ (eb.ser ++ rest)))) := by
      rw [hH.hx]; simp [Nd.ser, toU]
    simpa using drop_shift h0
  have hx2 := drop_shift hx1
  have hx3 := drop_shift hx2
  have hx4 := drop_shift hx3
  have hts := hI.lts; simp at hts
  have hI0 := hI.pop
  obtain ⟨k1, l1⟩ := hI0.pushw rfl (by have := hsz.2.1; omega) 1 0 0
  obtain ⟨k2, l2⟩ := k1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 1 0 0
  obtain ⟨k3, -⟩ := k2.pushw (n := u ts.length + 2) (by simp [u2, uadd]) (by have := hsz.2.1; omega) 2 0 0
  refine (hCMP a bb Q bs (ts ++ [(1, 0, 0), (1, 0, 0)]) (c + 2) (tb.ser ++ (eb.ser ++ rest)) b _ g s _ (u S0.length)
    (by omega) (by omega) na nb hH.hQ hx1 (by omega) (by simpa using k3) ?_).cast rfl (by simp [u3, uadd])
    (by simp [u2, uadd]) rfl rfl
  intro hA b2 t2 g2 s2 hI2 hga
  refine (hLIT tb Q bs (ts ++ [(1, 0, 0)]) (c + 2 + a.ser.length + bb.ser.length) (eb.ser ++ rest) b2 t2 g2 s2 S0 a0 SL
    (by omega) nt hH.hQ hx3 (by omega) (by simpa using hI2) ?_).cast rfl (by simp) (by simp) rfl rfl
  intro hB b3 t3 g3 s3 hI3 hgb
  refine (hLIT eb Q bs ts (c + 2 + a.ser.length + bb.ser.length + tb.ser.length) rest b3 t3 g3 s3 S0 _ _
    (by omega) ne hH.hQ hx4 (by omega) (by simpa using hI3) ?_).cast rfl (by simp) rfl rfl rfl
  intro hC b4 t4 g4 s4 hI4 hgc
  have e : c + 2 + a.ser.length + bb.ser.length + tb.ser.length + eb.ser.length =
      c + (Nd.ite cm a bb tb eb).ser.length := by simp [Nd.ser]; omega
  rw [e]
  have hS : ∀ (p q : Bool) (L1 L2 : List Nat), S0 ++ w2 (a0 || p || q) :: (SL ++ List.map u L1 ++ List.map u L2) =
      S0 ++ w2 (a0 || (p || q)) :: (SL ++ List.map u (L1 ++ L2)) := by intro p q L1 L2; simp [Bool.or_assoc]
  rw [hS] at hI4 ⊢
  exact hP (by simp [NumSpec.R.app, hA, hB, hC]) b4 t4 g4 s4 hI4 (hga.trans (hgb.trans hgc))

/-- LIT at a let: LETG on the value, BINDM, LIT on the body, POPM -/
theorem m_lit_let {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hLIT : MLIT x d np ks ws f)
    (hLETG : MLETG x d np ks ws f) {sl w : Nat} {v bd : Nd}
    {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat} {rest b t g s : Buf}
    {S0 : List UInt64} {a0 : Bool} {SL : List UInt64} (hH : LH x d np f (.letE sl w v bd) Q c rest)
    (hI : MI b bs t (ts ++ [(1, 0, 0)]) g s (S0 ++ w2 a0 :: SL))
    (hP : MLp x d Q bs ts g S0 a0 SL (c + (Nd.letE sl w v bd).ser.length)
      (NumSpec.litG (f + 1) ks ws (envOf bs) (.letE sl w v bd))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u (S0 ++ w2 a0 :: SL).length) (u S0.length) := by
  apply m_lit_read hH.hQ hI
  intro hsz R hR hok
  have hxl : x.length < 2 ^ 62 := by have := hK.lc.xl; omega
  rw [u44_5 (tag_rd hH.hx hxl), tag1 hH.hx hxl (by simp [hdr])] at hR
  simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at hR
  rw [show u c + 3 = u (c + 3) by rw [u3, uadd]] at hR
  subst hR
  dsimp only
  rw [litG_succ] at hP; dsimp only at hP
  have hnb := hH.hnb; simp only [NB] at hnb
  obtain ⟨hsl, -, nv, nbd⟩ := hnb
  have hf := hH.hf; simp [Nd.ser] at hf
  have := ser_pos v; have := ser_pos bd
  have hx1 : x.drop (c + 3) = v.ser ++ (bd.ser ++ rest) := by
    have h0 : x.drop c = [5, u sl, u w] ++ (v.ser ++ (bd.ser ++ rest)) := by rw [hH.hx]; simp [Nd.ser, toU]
    simpa using drop_shift h0
  have hx2 := drop_shift hx1
  have hts := hI.lts; simp at hts
  have hI0 := hI.pop
  obtain ⟨k1, l1⟩ := hI0.pushw rfl (by have := hsz.2.1; omega) 5 (u (encB bs).length) 0
  obtain ⟨k2, l2⟩ := k1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 1 0 0
  obtain ⟨k3, l3⟩ := k2.pushw (n := u ts.length + 2) (by simp [u2, uadd]) (by have := hsz.2.1; omega) 6 (u sl) (u (c + 3))
  obtain ⟨k4, -⟩ := k3.pushw (n := u ts.length + 3) (by simp [u3, uadd]) (by have := hsz.2.1; omega) 3 (u sl) 0
  refine (hLETG v sl w Q bs (ts ++ [(5, u (encB bs).length, 0), (1, 0, 0), (6, u sl, u (c + 3))]) (c + 3)
    (bd.ser ++ rest) b _ g s _ (u S0.length) (by omega) nv hsl hH.hQ hx1 (by omega) (by simpa using k4) ?_).cast rfl
    (by simp only [List.length_append, List.length_cons, List.length_nil]; rw [show (4 : UInt64) = u 4 from rfl, uadd])
    rfl rfl rfl
  intro hA b2 t2 g2 s2 hI2 hga
  refine (m_bindm hK.lc hH.hQ (f := f) (v := v) (pv := c + 3) hsl (by omega) nv hx1 (by omega)
    (ts := ts ++ [(5, u (encB bs).length, 0), (1, 0, 0)]) (by simpa using hI2) ?_).cast rfl (by simp) rfl rfl rfl
  intro b3 hI3
  have hI3' : MI b3 (bs ++ [(sl, NumSpec.lw f ws (envOf bs) v)]) t2 ((ts ++ [(5, u (encB bs).length, 0)]) ++ [(1, 0, 0)])
      g2 s2 (S0 ++ w2 a0 :: SL) := by simpa using hI3
  refine (hLIT bd Q (bs ++ [(sl, NumSpec.lw f ws (envOf bs) v)]) (ts ++ [(5, u (encB bs).length, 0)])
    (c + 3 + v.ser.length) rest b3 t2 g2 s2 S0 a0 SL (by omega) nbd hH.hQ hx2 (by omega) hI3' ?_).cast rfl
    (by simp) rfl rfl rfl
  intro hB b4 t4 g4 s4 hI4 hgb
  rw [envOf_snoc] at hB hgb hI4 ⊢
  refine (m_popm hH.hQ (bs0 := bs) (List.prefix_append _ _) hI4 ?_).cast rfl (by simp) rfl rfl rfl
  intro hI5
  have e : c + 3 + v.ser.length + bd.ser.length = c + (Nd.letE sl w v bd).ser.length := by simp [Nd.ser]; omega
  rw [e]
  exact hP (by simp [NumSpec.R.app, hA, hB]) b4 t4 g4 s4 hI5 (hga.trans hgb)

theorem m_lit_succ {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hLIT : MLIT x d np ks ws f)
    (hCMP : MCMP x d np ks ws f) (hLETG : MLETG x d np ks ws f) : MLIT x d np ks ws (f + 1) := by
  intro e Q bs ts c rest b t g s S0 a0 SL hf hnb hQ hx hc hI hP
  have hH : LH x d np f e Q c rest := ⟨hf, hnb, hQ, hx, hc⟩
  cases e with
  | const v => exact m_lit_skip hK hH rfl rfl rfl rfl rfl hI hP
  | loc sl w => exact m_lit_loc hK hH hI hP
  | bin op a bb => exact m_lit_bin hK hLIT hH hI hP
  | ite cm a bb tb eb => exact m_lit_ite hK hLIT hCMP hH hI hP
  | letE sl w v bd => exact m_lit_let hK hLIT hLETG hH hI hP
  | pair cs => exact m_lit_skip hK hH rfl rfl rfl rfl rfl hI hP
  | call id cs => exact m_lit_skip hK hH rfl rfl rfl rfl rfl hI hP
  | prim pn cs => exact m_lit_skip hK hH rfl rfl rfl rfl rfl hI hP
  | loop z sv => exact m_lit_skip hK hH rfl rfl rfl rfl rfl hI hP
  | cont a => exact m_lit_skip hK hH rfl rfl rfl rfl rfl hI hP

theorem m_lit_zero {x d : Buf} {np : Nat} {ks ws : List Nat} : MLIT x d np ks ws 0 := by
  intro e _ _ _ _ _ _ _ _ _ _ _ _ hf; have := ser_pos e; omega

end NumP
