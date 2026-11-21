/- Nano/Parser/NumP17: CMP (`cmpG`: a comparison's operands). -/
import Nano.Parser.NumP16
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

theorem u49_2 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb a a2 : UInt64) :
    u49 x d b bt t tt c s st gb 2 a a2 = u45 x d b bt t tt c s st gb := by
  unfold u49; rw [if_neg (kne (show ((2 : UInt64) == 0) = false from rfl)), if_neg (kne (show ((2 : UInt64) == 1) = false from rfl)),
    if_pos (keq (show ((2 : UInt64) == 2) = true from rfl))]

theorem u45_eq {x d b : Buf} {bt : UInt64} {t : Buf} {tt c : UInt64} {s : Buf} {st gb : UInt64}
    (R : R9) (hR : u45 x d b bt t tt c s st gb = R) :
    ((if u15 x c == 0 then (b, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
     else
      (match u16 x bnew c with
       | (p1, o1) =>
         match u16 x p1 (u15 x c) with
         | (p2, o2) =>
           if o1 == 1 then
             (if o2 == 1 then
               (match u33 16777216 x d b bt p2 0 (bsize p2) 0 with
                | (b1, h) =>
                  if h == 1 then
                    (match u32 x d b1 bt c with
                     | (b2, la) =>
                       match u32 x d b2 bt (u15 x c) with
                       | (b3, lb) =>
                         if la == 2 then (b3, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
                         else if lb == 2 then (b3, (bt, (t, (tt, (c, (s, (st, (gb, 0))))))))
                         else if (la &&& lb) == 1 then
                           (b3, (bt, (u27 (u27 (u27 t tt 4 0 gb) (tt + 1) 1 0 0) (tt + 2) 1 0 0, (tt + 3, (c, (u20 s st 0,
                             (st + 1, (st, 1))))))))
                         else (b3, (bt, (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0, (tt + 2, (c, (s, (st, (gb, 1)))))))))
                  else (b1, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))
              else (b, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))
           else (b, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))) : R9) = R := by
  rw [← hR]; unfold u45; zeta_only

theorem m_cmp_succ {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    (hLIT : MLIT x d np ks ws f) : MCMP x d np ks ws (f + 1) := by
  intro a e2 Q bs ts c rest b t g s S gb ha he na ne hQ hx hc hI hP
  apply m_read hQ (Or.inr (Or.inr (Or.inl rfl))) hI _ (fun _ => rfl)
  intro hsz
  rw [u49_2]
  generalize hR : u45 x d b (u (encB bs).length) t (u ts.length) (u c) s (u S.length) gb = R
  intro hok
  have hR' := u45_eq R hR
  have rej : ∀ b' : Buf, ((b', (u (encB bs).length, (t, (u ts.length, (u c, (s, (u S.length, (gb, 0)))))))) : R9) = R →
      False := by
    intro b' h; subst h; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)
  have hx23 := hK.lc.xl
  have hxl : x.length < 2 ^ 62 := by omega
  have hxe := drop_shift hx
  have hcl := drop_len hxe (ser_pos _)
  rcases u15_ok (by omega) hx na with h1 | ⟨h1, -⟩
  · rw [h1, if_pos (keq (show ((0 : UInt64) == 0) = true from rfl))] at hR'; exact (rej _ hR').elim
  have hpb : (u (c + a.ser.length) == 0) = false := by
    rw [u0, ueq (by omega) (by omega)]; exact decide_eq_false (by omega)
  rw [h1, if_neg (kne hpb)] at hR'
  have hV1 := u16_ok (f := f) hx23 bnew hx (by omega) na hc
  generalize hV1e : u16 x bnew (u c) = V1 at hV1 hR'
  obtain ⟨p1, o1⟩ := V1
  iota_only at hR'
  have hV2 := u16_ok (f := f) hx23 p1 hxe (by omega) ne (by omega)
  generalize hV2e : u16 x p1 (u (c + a.ser.length)) = V2 at hV2 hR'
  obtain ⟨p2, o2⟩ := V2
  iota_only at hR'
  by_cases ho1 : o1 = 1
  rotate_left
  · rw [if_neg (by simpa using ho1)] at hR'; exact (rej _ hR').elim
  subst ho1
  rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))] at hR'
  by_cases ho2 : o2 = 1
  rotate_left
  · rw [if_neg (by simpa using ho2)] at hR'; exact (rej _ hR').elim
  subst ho2
  rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))] at hR'
  have hp1 := hV1 rfl; simp only [bnew, List.nil_append] at hp1
  have hp2 := hV2 rfl; simp only at hp2
  rw [hp1, ← List.map_append] at hp2
  subst hp2
  generalize hls : lvP f a c ++ lvP f e2 (c + a.ser.length) = ls at *
  have hsp : ∀ q ∈ ls, (∃ r', x.drop q.2 = q.1.ser ++ r') ∧ q.1.ser.length ≤ f ∧ NB np q.1 ∧ 0 < q.2 := by
    rw [← hls]; intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨h1, h2, h3, h4⟩ := lvP_sp f a c _ hx na hc q hq; exact ⟨h1, by omega, h3, h4⟩
    · obtain ⟨h1, h2, h3, h4⟩ := lvP_sp f e2 _ _ hxe ne (by omega) q hq; exact ⟨h1, by omega, h3, h4⟩
  have hlen : ls.length ≤ a.ser.length + e2.ser.length := by
    rw [← hls, List.length_append]; have := lvP_len f a c; have := lvP_len f e2 (c + a.ser.length); omega
  have hI0 := hI.pop
  have h33 := u33_ok hK.lc (f := f) hI.sb 16777216 ls [] false b hsp hI.pb (by have := hsz.1; omega) (by simp; omega)
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h33
  have eb : bsize (ls.map fun q => u q.2) = u ls.length := by rw [bsize_u, List.length_map]
  rw [eb] at hR'
  generalize hWe : u33 16777216 x d b (u (encB bs).length) (ls.map fun q => u q.2) 0 (u ls.length) 0 = W at hR'
  have hW : u33 16777216 x d b (u (encB bs).length) (ls.map fun q => u q.2) (u 0) (u ls.length) (w2 false) = W := hWe
  rw [hW] at h33
  obtain ⟨b1, h⟩ := W
  iota_only at hR'
  by_cases hh : h = 1
  rotate_left
  · rw [if_neg (by simpa using hh)] at hR'; exact (rej _ hR').elim
  subst hh
  rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))] at hR'
  obtain ⟨hshp, hb1, hbl1⟩ := h33 rfl
  simp only at hb1 hbl1
  have hU1 := u32_ok hK.lc (f := f) (by omega) na hx hc hb1 hbl1 hI.sb
  generalize hU1e : u32 x d b1 (u (encB bs).length) (u c) = U1 at hU1 hR'
  obtain ⟨b2, la⟩ := U1
  iota_only at hR'
  simp only at hU1
  generalize hU2e : u32 x d b2 (u (encB bs).length) (u (c + a.ser.length)) = U2 at hR'
  obtain ⟨b3, lb⟩ := U2
  iota_only at hR'
  by_cases hla : la = 2
  · subst hla; rw [if_pos (keq (show ((2 : UInt64) == 2) = true from rfl))] at hR'; exact (rej _ hR').elim
  obtain ⟨ela, hb2, hbl2⟩ := hU1 hla
  have hU2 := u32_ok hK.lc (f := f) (by omega) ne hxe (by omega) hb2 hbl2 hI.sb
  rw [hU2e] at hU2; simp only at hU2
  rw [if_neg (kne (by rw [ela]; exact w2_eq2 _))] at hR'
  by_cases hlb : lb = 2
  · subst hlb; rw [if_pos (keq (show ((2 : UInt64) == 2) = true from rfl))] at hR'; exact (rej _ hR').elim
  obtain ⟨elb, hb3, hbl3⟩ := hU2 hlb
  rw [if_neg (kne (by rw [elb]; exact w2_eq2 _)), ela, elb, w2_and, w2_eq1] at hR'
  -- the spec
  rw [cmpG_succ] at hP
  have hsh : NumSpec.shapeOk f ws (envOf bs) (NumSpec.leaves f a ++ NumSpec.leaves f e2) = true := by
    rw [← lvP_fst f a c, ← lvP_fst f e2 (c + a.ser.length), ← List.map_append, hls]; exact shapeOk_of hshp
  rw [hsh] at hP
  have hts := hI.lts; simp at hts
  have hI3 := hI0.withb hb3 hbl3
  have hf := ha
  cases hab : (NumSpec.isL f ws (envOf bs) a && NumSpec.isL f ws (envOf bs) e2)
  · rw [hab, if_neg (by simp)] at hR'
    subst hR'
    rw [if_neg (by simp [hab])] at hP
    have hP1 := MCp.app (A := ([], true)) hP rfl (GA.nil g)
    dsimp only
    obtain ⟨k1, l1⟩ := hI3.pushw rfl (by have := hsz.2.1; omega) 0 1 0
    obtain ⟨k2, -⟩ := k1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 0 1 0
    refine (hCOL a 1 Q bs (ts ++ [(0, 1, 0)]) c (e2.ser ++ rest) b3 _ g s S gb (by omega) na (by omega) hQ hx hc
      (by rw [u1e]; simpa using k2) ?_).cast rfl (by simp [u2, uadd]) rfl rfl rfl
    intro hA b4 t4 g4 s4 hI4 hga
    refine (hCOL e2 1 Q bs ts (c + a.ser.length) rest b4 t4 g4 s4 S gb (by omega) ne (by omega) hQ hxe (by omega)
      (by rw [u1e]; simpa using hI4) ?_).cast rfl (by simp) rfl rfl rfl
    exact MCp.app hP1 hA hga
  · rw [hab, if_pos rfl] at hR'
    subst hR'
    rw [if_pos (by simp [hab])] at hP
    have hP1 := MCp.app (A := ([], true)) hP rfl (GA.nil g)
    dsimp only
    obtain ⟨k1, l1⟩ := hI3.pushw rfl (by have := hsz.2.1; omega) 4 0 gb
    obtain ⟨k2, l2⟩ := k1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 1 0 0
    obtain ⟨k3, -⟩ := k2.pushw (n := u ts.length + 2) (by simp [u2, uadd]) (by have := hsz.2.1; omega) 1 0 0
    obtain ⟨k4, -⟩ := k3.spush (by have := hsz.2.2.2; omega) (w2 false)
    refine (hLIT a Q bs (ts ++ [(4, 0, gb), (1, 0, 0)]) c (e2.ser ++ rest) b3 _ g _ S false [] (by omega) na hQ hx hc
      (by simpa [w2] using k4) ?_).cast rfl (by simp [u3, uadd]) rfl (by simp [u1, uadd]) rfl
    intro hA b4 t4 g4 s4 hI4 hga
    refine (hLIT e2 Q bs (ts ++ [(4, 0, gb)]) (c + a.ser.length) rest b4 t4 g4 s4 S _ _ (by omega) ne hQ hxe (by omega)
      (by simpa using hI4) ?_).cast rfl (by simp) rfl rfl rfl
    intro hB b5 t5 g5 s5 hI5 hgb
    generalize hLa : NumSpec.litG f ks ws (envOf bs) a = La at *
    generalize hLb : NumSpec.litG f ks ws (envOf bs) e2 = Lb at *
    have hS : S ++ w2 (false || La.1.2 || Lb.1.2) :: ([] ++ List.map u La.1.1 ++ List.map u Lb.1.1) =
        S ++ w2 (La.1.2 || Lb.1.2) :: (La.1.1 ++ Lb.1.1).map u := by simp
    rw [hS] at hI5 ⊢
    have hI5' : MI b5 bs t5 (ts ++ [(4, u 0, gb)]) g5 s5 (S ++ w2 (La.1.2 || Lb.1.2) :: (La.1.1 ++ Lb.1.1).map u) := hI5
    refine (m_close hQ (by omega) hI5' ?_).cast rfl (by simp) rfl rfl rfl
    intro hI6
    refine hP1 (by simp [NumSpec.R.app, hA, hB]) _ _ _ _ hI6 ?_
    obtain ⟨X, hX, rfl⟩ := hga.trans hgb
    refine ⟨X ++ [⟨La.1.1 ++ Lb.1.1, 0, La.1.2 || Lb.1.2⟩], ?_, by simp [encG]⟩
    exact (List.perm_append_singleton _ _).trans (List.Perm.cons _ hX)

theorem m_cmp_zero {x d : Buf} {np : Nat} {ks ws : List Nat} : MCMP x d np ks ws 0 := by
  intro a _ _ _ _ _ _ _ _ _ _ _ _ ha; omega

end NumP
