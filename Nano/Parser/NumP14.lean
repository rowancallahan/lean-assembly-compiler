/- Nano/Parser/NumP14: COL at an if and at a let. -/
import Nano.Parser.NumP13
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

theorem u42_4 {x d b : Buf} {bt : UInt64} {t : Buf} {tt c : UInt64} {s : Buf} {st gb e : UInt64} {y y1 y2 : Buf}
    (hg : bget x c = 4) (R : R12) (hR : u42 x d b bt t tt c s st gb e y y1 y2 = R) :
    ((if e == 0 then
      (let (b1, z) := u70 x d b bt y y1 c;
       let (mx, z1) := z;
       let (y3, y4) := z1;
       if mx == 0 then
         (b1, (bt, (u27 (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0) (tt + 2) 2 0 0, (tt + 3, (c + 2, (s, (st, (gb, (1, (y3, (y4, y2)))))))))))
       else u64 b1 t s y3 y4 y2)
     else (b, (bt, (u27 (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0) (tt + 2) 2 0 0, (tt + 3, (c + 2, (s, (st, (gb, (1, (y, (y1, y2)))))))))))) :
      R12) = R := by
  rw [← hR]; unfold u42; rw [hg]; zeta_only; unfold u65; zeta_only
  rw [if_neg (kne (show ((4 : UInt64) == 3) = false from rfl)), if_pos (keq (show ((4 : UInt64) == 4) = true from rfl))]

theorem u15_zero (x : Buf) : u15 x 0 = 0 := by
  unfold u15; rw [if_pos (keq (show ((0 : UInt64) == 0) = true from rfl))]

theorem w2_eq1 (p : Bool) : (w2 p == 1) = p := by cases p <;> rfl
theorem w2_eq2 (p : Bool) : (w2 p == 2) = false := by cases p <;> rfl

/-- an IF: the mixIte rule at demand 0; CMP on the condition, COL 1 on both branches -/
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
  rw [col_succ, if_neg (by simp [hl])] at hP; dsimp only at hP
  -- the pushed state
  have hgo : ∀ b3 y5 y8 : Buf, encB bs <+: b3 → b3.length < 2 ^ 42 → SC y5 y8 y2 →
      ((b3, (u (encB bs).length, (u27 (u27 (u27 t (u ts.length) 0 1 0) (u ts.length + 1) 0 1 0) (u ts.length + 2) 2 0 0,
      (u ts.length + 3, (u c + 2, (s, (u S.length, (gb, (1, (y5, (y8, y2))))))))))) : R12) = R →
      (!(dd == 0 && NumSpec.mixIte f ws (envOf bs) (.ite cm a bb tb eb))) = true →
      SCR R ∧ GM x d Q R.1 R.2.1 R.2.2.1 R.2.2.2.1 R.2.2.2.2.1 g R.2.2.2.2.2.1 R.2.2.2.2.2.2.1 R.2.2.2.2.2.2.2.1 := by
    intro b3 y5 y8 hb3 hbl3 hsc3 h r5; subst h
    refine ⟨hsc3, ?_⟩
    dsimp only
    rw [show u c + 2 = u (c + 2) by rw [u2, uadd]]
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
    have hM := u70_ok hK.lc (f := f) hH.hf hH.hnb hH.hx hH.hc hb1 hbl1 hI.sb hsc.1 hsc.2.1
    generalize u70 x d b1 (u (encB bs).length) y y1 (u c) = M at hM hR'
    obtain ⟨b3, mx, y5, y8⟩ := M
    dsimp only at hM hR'
    by_cases hm2 : mx = 2
    · subst hm2; rw [if_neg (kne (show ((2 : UInt64) == 0) = false from rfl))] at hR'
      subst hR'; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)
    obtain ⟨hm, hb3, hbl3, hy5, hy8⟩ := hM hm2
    cases hX : NumSpec.mixIte f ws (envOf bs) (.ite cm a bb tb eb)
    · rw [hm, hX, if_pos (keq (show (w2 false == 0) = true from rfl))] at hR'
      exact hgo b3 y5 y8 hb3 hbl3 ⟨hy5, hy8, hsc.2.2⟩ hR' (by simp [hX])
    · rw [hm, hX, if_neg (kne (show (w2 true == 0) = false from rfl))] at hR'
      subst hR'; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)
  · rw [if_neg (kne (by rw [u0, ueq (by omega) (by omega)]; simp [hd0]))] at hR'
    exact hgo b1 y y1 hb1 hbl1 hsc hR' (by simp [hd0])

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
