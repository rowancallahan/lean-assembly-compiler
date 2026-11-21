/- Nano/Parser/NumP14: COL at an if and at a let. -/
import Nano.Parser.NumP13
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

theorem u42_4 {x d b : Buf} {bt : UInt64} {t : Buf} {tt c : UInt64} {s : Buf} {st gb e : UInt64} {y y1 y2 : Buf}
    (hg : bget x c = 4) (R : R12) (hR : u42 x d b bt t tt c s st gb e y y1 y2 = R) :
    ((if u15 x (u15 x (u15 x (c + 2))) == 0 then u64 b t s y y1 y2
     else
       (let (b1, z) := u32 x d b bt y y1 (u15 x (u15 x (c + 2)));
        let (lt, z1) := z;
        let (y3, y4) := z1;
        let (b2, z2) := u32 x d b1 bt y3 y4 (u15 x (u15 x (u15 x (c + 2))));
        let (le, z3) := z2;
        let (y5, y6) := z3;
        let (y7, pt) := u17 x y6 (u15 x (u15 x (c + 2)));
        let (y8, pe) := u17 x y7 (u15 x (u15 x (u15 x (c + 2))));
        if lt == 2 then u64 b2 t s y5 y8 y2
        else if le == 2 then u64 b2 t s y5 y8 y2
        else if pt == 2 then u64 b2 t s y5 y8 y2
        else if pe == 2 then u64 b2 t s y5 y8 y2
        else if e == 0 then
          (if ((lt &&& pe) ||| (le &&& pt)) == 1 then u64 b2 t s y5 y8 y2
           else (b2, (bt, (u27 (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0) (tt + 2) 2 0 0, (tt + 3, (c + 2, (s, (st, (gb, (1, (y5, (y8, y2))))))))))))
        else (b2, (bt, (u27 (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0) (tt + 2) 2 0 0, (tt + 3, (c + 2, (s, (st, (gb, (1, (y5, (y8, y2))))))))))))) :
      R12) = R := by
  rw [← hR]; unfold u42; rw [hg]; zeta_only; unfold u65; zeta_only
  rw [if_neg (kne (show ((4 : UInt64) == 3) = false from rfl)), if_pos (keq (show ((4 : UInt64) == 4) = true from rfl))]

theorem u15_zero (x : Buf) : u15 x 0 = 0 := by
  unfold u15; rw [if_pos (keq (show ((0 : UInt64) == 0) = true from rfl))]

theorem w2_eq1 (p : Bool) : (w2 p == 1) = p := by cases p <;> rfl
theorem w2_eq2 (p : Bool) : (w2 p == 2) = false := by cases p <;> rfl

/-- an IF: the r5 rule at demand 0; CMP on the condition, COL 1 on both branches -/
theorem m_col_ite {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    (hCMP : MCMP x d np ks ws f)
    {cm : Nat} {a bb tb eb : Nd} {dd : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat}
    {rest b t g s : Buf} {S : List UInt64} {gb : UInt64} (hH : CH x d np f (.ite cm a bb tb eb) Q c rest) (hdd : dd < 3)
    (hI : MI b bs t (ts ++ [(0, u dd, 0)]) g s S) (hl : NumSpec.isL f ws (envOf bs) (.ite cm a bb tb eb) = false)
    (hP : MCp x d Q bs ts g S gb (c + (Nd.ite cm a bb tb eb).ser.length)
      (NumSpec.col (f + 1) ks ws (envOf bs) dd (.ite cm a bb tb eb))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_col_nl hK hH.hf hH.hnb hH.hQ hH.hx hH.hc hI hl
  intro b1 hb1 hbl1 hsz y y1 y2 hsc R hR hok
  have hxl : x.length < 2 ^ 62 := by have := hK.lc.xl; omega
  have hx23 := hK.lc.xl
  have hR' := u42_4 (by rw [hH.tag hxl]; rfl) R hR
  have hnb := hH.hnb; simp only [NB] at hnb
  obtain ⟨-, na, nb, nt, ne⟩ := hnb
  have hf := hH.hf; simp [Nd.ser] at hf
  have hx1 : x.drop (c + 2) = a.ser ++ (bb.ser ++ (tb.ser ++ (eb.ser ++ rest))) := by
    have h0 : x.drop c = [4, u cm] ++ (a.ser ++ (bb.ser ++ (tb.ser ++ (eb.ser ++ rest)))) := by
      rw [hH.hx]; simp [Nd.ser, toU]
    simpa using drop_shift h0
  have hx2 := drop_shift hx1
  have hx3 := drop_shift hx2
  have hx4 := drop_shift hx3
  have hcl := drop_len hH.hx (ser_pos _); simp [Nd.ser] at hcl
  rw [show u c + 2 = u (c + 2) by rw [u2, uadd]] at hR'
  have rej : ∀ b' t' s' y' y'' y''' : Buf, u64 b' t' s' y' y'' y''' = R → False := by
    intro b' t' s' y' y'' y''' h; subst h; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)
  rcases u15_ok (by omega) hx1 na with h1 | ⟨h1, -⟩
  · rw [h1, u15_zero, u15_zero, if_pos (keq (show ((0 : UInt64) == 0) = true from rfl))] at hR'; exact (rej _ _ _ _ _ _ hR').elim
  rcases u15_ok (by omega) hx2 nb with h2 | ⟨h2, -⟩
  · rw [h1, h2, u15_zero, if_pos (keq (show ((0 : UInt64) == 0) = true from rfl))] at hR'; exact (rej _ _ _ _ _ _ hR').elim
  rcases u15_ok (by omega) hx3 nt with h3 | ⟨h3, -⟩
  · rw [h1, h2, h3, if_pos (keq (show ((0 : UInt64) == 0) = true from rfl))] at hR'; exact (rej _ _ _ _ _ _ hR').elim
  rw [h1, h2, h3, if_neg (kne (by rw [u0, ueq (by omega) (by omega)]; simp))] at hR'
  have hU1 := u32_ok hK.lc (f := f) (by omega) nt hx3 (by omega) hb1 hbl1 hI.sb hsc.1 hsc.2.1
  generalize hU1e : u32 x d b1 (u (encB bs).length) y y1 (u (c + 2 + a.ser.length + bb.ser.length)) = U1 at hU1 hR'
  obtain ⟨b2, lt, y3, y4⟩ := U1
  iota_only at hR'
  simp only at hU1
  generalize hU2e : u32 x d b2 (u (encB bs).length) y3 y4 (u (c + 2 + a.ser.length + bb.ser.length + tb.ser.length)) = U2 at hR'
  obtain ⟨b3, le, y5, y6⟩ := U2
  iota_only at hR'
  generalize hV1e : u17 x y6 (u (c + 2 + a.ser.length + bb.ser.length)) = V1 at hR'
  obtain ⟨y7, pt⟩ := V1
  iota_only at hR'
  generalize hV2e : u17 x y7 (u (c + 2 + a.ser.length + bb.ser.length + tb.ser.length)) = V2 at hR'
  obtain ⟨y8, pe⟩ := V2
  iota_only at hR'
  by_cases hlt : lt = 2
  · subst hlt; rw [if_pos (keq (show ((2 : UInt64) == 2) = true from rfl))] at hR'; exact (rej _ _ _ _ _ _ hR').elim
  obtain ⟨elt, hb2, hbl2, hy3, hy4⟩ := hU1 hlt
  have hU2 := u32_ok hK.lc (f := f) (by omega) ne hx4 (by omega) hb2 hbl2 hI.sb (v := y3) (w := y4) (by omega) (by omega)
  rw [hU2e] at hU2
  simp only at hU2
  rw [if_neg (kne (by rw [elt]; exact w2_eq2 _))] at hR'
  by_cases hle : le = 2
  · subst hle; rw [if_pos (keq (show ((2 : UInt64) == 2) = true from rfl))] at hR'; exact (rej _ _ _ _ _ _ hR').elim
  obtain ⟨ele, hb3, hbl3, hy5, hy6⟩ := hU2 hle
  rw [if_neg (kne (by rw [ele]; exact w2_eq2 _))] at hR'
  have q1 := u17_ok (f := f) hx23 hx3 (by omega) nt (by omega) (w := y6) (by omega)
  rw [hV1e] at q1
  obtain ⟨hy7, p1⟩ := q1
  simp only at hy7 p1
  rcases p1 with p1 | p1
  · rw [p1, if_pos (keq (show ((2 : UInt64) == 2) = true from rfl))] at hR'; exact (rej _ _ _ _ _ _ hR').elim
  rw [p1, if_neg (kne (w2_eq2 _))] at hR'
  have q2 := u17_ok (f := f) hx23 hx4 (by omega) ne (by omega) (w := y7) (by omega)
  rw [hV2e] at q2
  obtain ⟨hy8, p2⟩ := q2
  simp only at hy8 p2
  rcases p2 with p2 | p2
  · rw [p2, if_pos (keq (show ((2 : UInt64) == 2) = true from rfl))] at hR'; exact (rej _ _ _ _ _ _ hR').elim
  rw [p2, if_neg (kne (w2_eq2 _)), elt, ele, w2_and, w2_and, w2_or, w2_eq1] at hR'
  rw [col_succ, if_neg (by simp [hl])] at hP; dsimp only at hP
  -- the pushed state
  have hgo : ((b3, (u (encB bs).length, (u27 (u27 (u27 t (u ts.length) 0 1 0) (u ts.length + 1) 0 1 0) (u ts.length + 2) 2 0 0,
      (u ts.length + 3, (u (c + 2), (s, (u S.length, (gb, (1, (y5, (y8, y2))))))))))) : R12) = R →
      (!(dd == 0 && ((NumSpec.isL f ws (envOf bs) tb && NumSpec.spineLet f eb) ||
        (NumSpec.isL f ws (envOf bs) eb && NumSpec.spineLet f tb)))) = true →
      SCR R ∧ GM x d Q R.1 R.2.1 R.2.2.1 R.2.2.2.1 R.2.2.2.2.1 g R.2.2.2.2.2.1 R.2.2.2.2.2.2.1 R.2.2.2.2.2.2.2.1 := by
    intro h r5; subst h
    refine ⟨⟨by dsimp only; omega, by dsimp only; omega, hsc.2.2⟩, ?_⟩
    dsimp only
    have hP1 := MCp.app hP r5 (GA.nil g)
    have hts := hI.lts; simp at hts
    have hI0 := hI.pop.withb hb3 hbl3
    obtain ⟨k1, l1⟩ := hI0.pushw rfl (by have := hsz.2.1; omega) 0 1 0
    obtain ⟨k2, l2⟩ := k1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 0 1 0
    obtain ⟨k3, -⟩ := k2.pushw (n := u ts.length + 2) (by simp [u2, uadd]) (by have := hsz.2.1; omega) 2 0 0
    refine (hCMP a bb Q bs (ts ++ [(0, 1, 0), (0, 1, 0)]) (c + 2) (tb.ser ++ (eb.ser ++ rest)) b3 _ g s S gb (by omega)
      (by omega) na nb hH.hQ hx1 (by omega) (by simpa using k3) ?_).cast rfl (by simp [u3, uadd]) rfl rfl rfl
    intro hA b4 t4 g4 s4 hI4 hga
    have hP2 := MCp.app hP1 hA hga
    refine (hCOL tb 1 Q bs (ts ++ [(0, 1, 0)]) (c + 2 + a.ser.length + bb.ser.length) (eb.ser ++ rest) b4 t4 g4 s4 S gb
      (by omega) nt (by omega) hH.hQ hx3 (by omega) (by rw [u1e]; simpa using hI4) ?_).cast rfl (by simp) rfl rfl rfl
    intro hB b5 t5 g5 s5 hI5 hgb
    have hP3 := MCp.app hP2 hB hgb
    refine (hCOL eb 1 Q bs ts (c + 2 + a.ser.length + bb.ser.length + tb.ser.length) rest b5 t5 g5 s5 S gb
      (by omega) ne (by omega) hH.hQ hx4 (by omega) (by rw [u1e]; simpa using hI5) ?_).cast rfl (by simp) rfl rfl rfl
    have e : c + 2 + a.ser.length + bb.ser.length + tb.ser.length + eb.ser.length = c + (Nd.ite cm a bb tb eb).ser.length := by
      simp [Nd.ser]; omega
    rw [e]; exact hP3
  by_cases hd0 : dd = 0
  · subst hd0
    rw [if_pos (keq (show (u 0 == 0) = true from rfl))] at hR'
    cases hX : (NumSpec.isL f ws (envOf bs) tb && NumSpec.spineLet f eb || NumSpec.isL f ws (envOf bs) eb && NumSpec.spineLet f tb)
    · rw [hX, if_neg (by simp)] at hR'
      exact hgo hR' (by simp [hX])
    · rw [hX, if_pos rfl] at hR'; exact (rej _ _ _ _ _ _ hR').elim
  · rw [if_neg (kne (by rw [u0, ueq (by omega) (by omega)]; simp [hd0]))] at hR'
    exact hgo hR' (by simp [hd0])

/-- a LET: LETG on the value, BINDM, COL dd on the body, POPM -/
theorem m_col_let {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    (hLETG : MLETG x d np ks ws f)
    {sl w : Nat} {v bd : Nd} {dd : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat}
    {rest b t g s : Buf} {S : List UInt64} {gb : UInt64} (hH : CH x d np f (.letE sl w v bd) Q c rest) (hdd : dd < 3)
    (hI : MI b bs t (ts ++ [(0, u dd, 0)]) g s S) (hl : NumSpec.isL f ws (envOf bs) (.letE sl w v bd) = false)
    (hP : MCp x d Q bs ts g S gb (c + (Nd.letE sl w v bd).ser.length)
      (NumSpec.col (f + 1) ks ws (envOf bs) dd (.letE sl w v bd))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_col_nl hK hH.hf hH.hnb hH.hQ hH.hx hH.hc hI hl
  intro b1 hb1 hbl1 hsz y y1 y2 hsc R hR hok
  have hxl : x.length < 2 ^ 62 := by have := hK.lc.xl; omega
  rw [u42_5 (by rw [hH.tag hxl]; rfl), tag1 hH.hx hxl (by simp [hdr])] at hR
  simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at hR
  rw [show u c + 3 = u (c + 3) by rw [u3, uadd]] at hR
  subst hR
  refine ⟨hsc, ?_⟩
  dsimp only
  have hnb := hH.hnb; simp only [NB] at hnb
  obtain ⟨hsl, -, nv, nbd⟩ := hnb
  have hf := hH.hf; simp [Nd.ser] at hf
  have hx1 : x.drop (c + 3) = v.ser ++ (bd.ser ++ rest) := by
    have h0 : x.drop c = [5, u sl, u w] ++ (v.ser ++ (bd.ser ++ rest)) := by rw [hH.hx]; simp [Nd.ser, toU]
    simpa using drop_shift h0
  have hx2 := drop_shift hx1
  rw [col_succ, if_neg (by simp [hl])] at hP; dsimp only at hP
  have hts := hI.lts; simp at hts
  have hI0 := hI.pop.withb hb1 hbl1
  obtain ⟨k1, l1⟩ := hI0.pushw rfl (by have := hsz.2.1; omega) 5 (u (encB bs).length) 0
  obtain ⟨k2, l2⟩ := k1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 0 (u dd) 0
  obtain ⟨k3, l3⟩ := k2.pushw (n := u ts.length + 2) (by simp [u2, uadd]) (by have := hsz.2.1; omega) 6 (u sl) (u (c + 3))
  obtain ⟨k4, -⟩ := k3.pushw (n := u ts.length + 3) (by simp [u3, uadd]) (by have := hsz.2.1; omega) 3 (u sl) 0
  refine (hLETG v sl w Q bs (ts ++ [(5, u (encB bs).length, 0), (0, u dd, 0), (6, u sl, u (c + 3))]) (c + 3)
    (bd.ser ++ rest) b1 _ g s S gb (by omega) nv hsl hH.hQ hx1 (by omega) (by simpa using k4) ?_).cast rfl
    (by simp only [List.length_append, List.length_cons, List.length_nil]; rw [show (4 : UInt64) = u 4 from rfl, uadd])
    rfl rfl rfl
  intro hA b2 t2 g2 s2 hI2 hga
  have hP1 := MCp.app hP hA hga
  refine (m_bindm hK.lc hH.hQ (f := f) (v := v) (pv := c + 3) hsl (by omega) nv hx1 (by omega)
    (ts := ts ++ [(5, u (encB bs).length, 0), (0, u dd, 0)]) (by simpa using hI2) ?_).cast rfl (by simp) rfl rfl rfl
  intro b3 hI3
  have hI3' : MI b3 (bs ++ [(sl, NumSpec.lw f ws (envOf bs) v)]) t2 ((ts ++ [(5, u (encB bs).length, 0)]) ++ [(0, u dd, 0)])
      g2 s2 S := by simpa using hI3
  refine (hCOL bd dd Q (bs ++ [(sl, NumSpec.lw f ws (envOf bs) v)]) (ts ++ [(5, u (encB bs).length, 0)])
    (c + 3 + v.ser.length) rest b3 t2 g2 s2 S gb (by omega) nbd hdd hH.hQ hx2 (by omega) hI3' ?_).cast rfl
    (by simp) rfl rfl rfl
  intro hB b4 t4 g4 s4 hI4 hgb
  rw [envOf_snoc] at hB hgb
  refine (m_popm hH.hQ (bs0 := bs) (List.prefix_append _ _) hI4 ?_).cast rfl (by simp) rfl rfl rfl
  intro hI5
  have e : c + 3 + v.ser.length + bd.ser.length = c + (Nd.letE sl w v bd).ser.length := by simp [Nd.ser]; omega
  rw [e]
  exact hP1 hB b4 t4 g4 s4 hI5 hgb

end NumP
