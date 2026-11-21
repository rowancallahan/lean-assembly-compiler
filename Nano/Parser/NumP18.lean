/- Nano/Parser/NumP18: LETG (`letG`) and LPSEQ (a tuple value's fields). -/
import Nano.Parser.NumP17
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

theorem u49_3 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb a a2 : UInt64) (y y1 y2 : Buf) :
    u49 x d b bt t tt c s st gb 3 a a2 y y1 y2 = u46 x d b bt t tt c s st gb a y y1 y2 := by
  unfold u49; rw [if_neg (kne (show ((3 : UInt64) == 0) = false from rfl)), if_neg (kne (show ((3 : UInt64) == 1) = false from rfl)),
    if_neg (kne (show ((3 : UInt64) == 2) = false from rfl)), if_pos (keq (show ((3 : UInt64) == 3) = true from rfl))]

theorem u49_9 (x d b : Buf) (bt : UInt64) (t : Buf) (tt c : UInt64) (s : Buf) (st gb a a2 : UInt64) (y y1 y2 : Buf) :
    u49 x d b bt t tt c s st gb 9 a a2 y y1 y2 = u39 x d b bt t tt c s st gb a a2 y y1 y2 := by
  unfold u49; rw [if_neg (kne (show ((9 : UInt64) == 0) = false from rfl)), if_neg (kne (show ((9 : UInt64) == 1) = false from rfl)),
    if_neg (kne (show ((9 : UInt64) == 2) = false from rfl)), if_neg (kne (show ((9 : UInt64) == 3) = false from rfl)),
    if_pos (keq (show ((9 : UInt64) == 9) = true from rfl))]

section
variable {x d b : Buf} {bt : UInt64} {t : Buf} {tt c : UInt64} {s : Buf} {st gb : UInt64} {y y1 y2 : Buf}

theorem u46_6 {l : UInt64} (hg : bget x c = 6) :
    u46 x d b bt t tt c s st gb l y y1 y2 =
      (b, (bt, (u27 t tt 9 l (bget x (c + 1)), (tt + 1, (c + 2, (s, (st, (gb, (1, (y, (y1, y2))))))))))) := by
  unfold u46; unfold u65; zeta_only; rw [hg, if_pos (keq (show ((6 : UInt64) == 6) = true from rfl))]

theorem u46_n {l : UInt64} (hg : (bget x c == 6) = false) (R : R12) (hR : u46 x d b bt t tt c s st gb l y y1 y2 = R) :
    ((let (b1, z) := u32 x d b bt y y1 c;
      let (r, z1) := z;
      let (y3, y4) := z1;
      if r == 2 then u64 b1 t s y3 y4 y2
      else if r == 1 then
        (b1, (bt, (u27 (u27 t tt 4 0 gb) (tt + 1) 1 0 0,
          (tt + 2, (c, (u20 (u20 s st 0) (st + 1) l, (st + 2, (st, (1, (y3, (y4, y2)))))))))))
      else (b1, (bt, (u27 t tt 0 0 0, (tt + 1, (c, (s, (st, (gb, (1, (y3, (y4, y2)))))))))))) : R12) = R := by
  rw [← hR]; unfold u46 u66; unfold u65; zeta_only; rw [if_neg (kne hg)]

theorem u39_0 {l : UInt64} : u39 x d b bt t tt c s st gb l 0 y y1 y2 = (b, (bt, (t, (tt, (c, (s, (st, (gb, (1, (y, (y1, y2))))))))))) := by
  unfold u39; unfold u65; zeta_only; rw [if_pos (keq (show ((0 : UInt64) == 0) = true from rfl))]

theorem u39_s {l k : UInt64} (hk : (k == 0) = false) (R : R12) (hR : u39 x d b bt t tt c s st gb l k y y1 y2 = R) :
    ((let (b1, z) := u32 x d b bt y y1 c;
      let (r, z1) := z;
      let (y3, y4) := z1;
      if r == 2 then u64 b1 (u27 t tt 9 (l + 1) (k - 1)) s y3 y4 y2
      else if r == 1 then
        (b1, (bt, (u27 (u27 (u27 t tt 9 (l + 1) (k - 1)) (tt + 1) 4 0 gb) (tt + 2) 1 0 0,
          (tt + 3, (c, (u20 (u20 s st 0) (st + 1) l, (st + 2, (st, (1, (y3, (y4, y2)))))))))))
      else (b1, (bt, (u27 (u27 t tt 9 (l + 1) (k - 1)) (tt + 1) 0 1 0, (tt + 2, (c, (s, (st, (gb, (1, (y3, (y4, y2)))))))))))) : R12) = R := by
  have e1 : tt + 1 + 1 = tt + 2 := by rw [UInt64.add_assoc]; rfl
  have e2 : tt + 1 + 2 = tt + 3 := by rw [UInt64.add_assoc]; rfl
  rw [← hR]; unfold u39 u66; unfold u65; zeta_only; rw [if_neg (kne hk), e1, e2]

end

/-- a tuple field of a let value -/
def lf (f : Nat) (ks ws : List Nat) (env : List Bool) (sl : Nat) (p : Nd × Nat) : NumSpec.R :=
  if NumSpec.isL f ws env p.1 then
    (⟨(sl + p.2) :: (NumSpec.litG f ks ws env p.1).1.1, 0, (NumSpec.litG f ks ws env p.1).1.2⟩ ::
      (NumSpec.litG f ks ws env p.1).2.1, (NumSpec.litG f ks ws env p.1).2.2)
  else NumSpec.col f ks ws env 1 p.1

def lpL (f : Nat) (ks ws : List Nat) (env : List Bool) (sl : Nat) (cs : List Nd) (i : Nat) : NumSpec.R :=
  (cs.zipIdx i).foldr (fun p r => (lf f ks ws env sl p).app r) NumSpec.R.ok

theorem lp_attach (f : Nat) (ks ws : List Nat) (env : List Bool) (sl : Nat) : ∀ (cs : List Nd) (i : Nat),
    (cs.zipIdx i).attach.foldr (fun ⟨(c, j), _⟩ r =>
        (if NumSpec.isL f ws env c then
          let (ic, rc) := NumSpec.litG f ks ws env c
          (⟨(sl + j) :: ic.1, 0, ic.2⟩ :: rc.1, rc.2)
        else NumSpec.col f ks ws env 1 c).app r) NumSpec.R.ok = lpL f ks ws env sl cs i
  | [], _ => rfl
  | c :: cs, i => by
    have ih := lp_attach f ks ws env sl cs (i + 1)
    simp only [List.zipIdx_cons, List.attach_cons, List.foldr_cons, List.foldr_map, lpL] at ih ⊢
    rw [ih]; rfl

theorem letG_succ (f : Nat) (ks ws : List Nat) (env : List Bool) (sl w : Nat) (v : Nd) :
    NumSpec.letG (f + 1) ks ws env sl w v =
      match v with
      | .pair cs => lpL f ks ws env sl cs 0
      | _ =>
        if NumSpec.isL f ws env v then
          (⟨sl :: (NumSpec.litG f ks ws env v).1.1, 0, (NumSpec.litG f ks ws env v).1.2⟩ :: (NumSpec.litG f ks ws env v).2.1,
            (NumSpec.litG f ks ws env v).2.2)
        else NumSpec.col f ks ws env 0 v := by
  cases v with
  | pair cs => exact lp_attach f ks ws env sl cs 0
  | _ => rfl

theorem lpL_cons (f : Nat) (ks ws : List Nat) (env : List Bool) (sl : Nat) (c : Nd) (cs : List Nd) (i : Nat) :
    lpL f ks ws env sl (c :: cs) i = (lf f ks ws env sl (c, i)).app (lpL f ks ws env sl cs (i + 1)) := rfl

/-- LPSEQ over the fields cs (slot sl + i for the first) -/
theorem m_lpseq {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    (hLIT : MLIT x d np ks ws f) {Q : MO → Prop} (hQ : QM Q) (bs : List (Nat × List Bool)) (sl : Nat) (S : List UInt64)
    (gb : UInt64) : ∀ (cs : List Nd) (i : Nat) (ts : List T3) (c : Nat) (rest b t g s : Buf),
    (∀ e ∈ cs, e.ser.length + 1 ≤ f) → (∀ e ∈ cs, NB np e) → x.drop c = serL cs ++ rest → 0 < c → cs.length < 2 ^ 32 →
    MI b bs t (ts ++ [(9, u (sl + i), u cs.length)]) g s S →
    MCp x d Q bs ts g S gb (c + (serL cs).length) (lpL f ks ws (envOf bs) sl cs i) →
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb
  | [], i, ts, c, rest, b, t, g, s, _, _, _, _, _, hI, hP => by
    apply m_read hQ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hI
    intro hsz y y1 y2 hsc R0 hR0
    subst hR0
    rw [u49_9, show u ([] : List Nd).length = 0 from rfl, u39_0]
    intro _
    refine ⟨hsc, ?_⟩
    exact (hP rfl b t g s hI.pop (GA.nil g)).cast rfl rfl (by simp [serL]) rfl rfl
  | e :: cs, i, ts, c, rest, b, t, g, s, hf, hnb, hx, hc, hl, hI, hP => by
    apply m_read hQ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hI
    intro hsz y y1 y2 hsc R0 hR0
    subst hR0
    rw [u49_9]
    simp only [List.length_cons] at hl
    have hk0 : (u (e :: cs).length == 0) = false := by
      rw [u0, ueq (by simp; omega) (by omega)]; simp
    generalize hR : u39 x d b (u (encB bs).length) t (u ts.length) (u c) s (u S.length) gb (u (sl + i)) (u (e :: cs).length) y y1 y2 = R
    intro hok
    have hR' := u39_s hk0 R hR
    rw [show u (sl + i) + 1 = u (sl + (i + 1)) by rw [u1, uadd, Nat.add_assoc],
      show u (e :: cs).length - 1 = u cs.length from upred _ (by simp; omega)] at hR'
    have hx' : x.drop c = e.ser ++ (serL cs ++ rest) := by rw [hx]; simp [serL]
    have hx2 := drop_shift hx'
    have hfe := hf e (by simp)
    have hne := hnb e (by simp)
    have hU := u32_ok hK.lc (f := f) (by omega) hne hx' hc hI.pb (by have := hsz.1; omega) hI.sb hsc.1 hsc.2.1
    generalize hUe : u32 x d b (u (encB bs).length) y y1 (u c) = U at hU hR'
    obtain ⟨b1, r, y3, y4⟩ := U
    iota_only at hR'
    simp only at hU
    by_cases hr2 : r = 2
    · subst hr2; rw [if_pos (keq (show ((2 : UInt64) == 2) = true from rfl))] at hR'
      subst hR'; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)
    obtain ⟨er, hb1, hbl1, hy3, hy4⟩ := hU hr2
    subst er
    rw [if_neg (kne (w2_eq2 _))] at hR'
    rw [lpL_cons] at hP
    have hts := hI.lts; simp at hts
    have hI0 := hI.pop.withb hb1 hbl1
    obtain ⟨k1, l1⟩ := hI0.pushw rfl (by have := hsz.2.1; omega) 9 (u (sl + (i + 1))) (u cs.length)
    have hrec : ∀ (b2 t2 g2 s2 : Buf), MI b2 bs t2 (ts ++ [(9, u (sl + (i + 1)), u cs.length)]) g2 s2 S →
        (lf f ks ws (envOf bs) sl (e, i)).2 = true → GA g g2 (lf f ks ws (envOf bs) sl (e, i)).1 →
        GM x d Q b2 (u (encB bs).length) t2 (u (ts.length + 1)) (u (c + e.ser.length)) g2 s2 (u S.length) gb := by
      intro b2 t2 g2 s2 hI2 hA hga
      refine (m_lpseq hK hCOL hLIT hQ bs sl S gb cs (i + 1) ts (c + e.ser.length) rest b2 t2 g2 s2
        (fun e he => hf e (by simp [he])) (fun e he => hnb e (by simp [he])) hx2 (by omega) (by omega) hI2 ?_)
      have := MCp.app hP hA hga
      simpa [serL, Nat.add_assoc] using this
    cases hle : NumSpec.isL f ws (envOf bs) e
    · rw [hle, if_neg (kne (show (w2 false == 1) = false from rfl))] at hR'
      subst hR'
      refine ⟨⟨by dsimp only; omega, by dsimp only; omega, hsc.2.2⟩, ?_⟩
      dsimp only
      obtain ⟨k2, -⟩ := k1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 0 1 0
      refine (hCOL e 1 Q bs (ts ++ [(9, u (sl + (i + 1)), u cs.length)]) c (serL cs ++ rest) b1 _ g s S gb hfe hne
        (by omega) hQ hx' hc (by rw [u1e]; simpa using k2) ?_).cast rfl (by simp [u2, uadd]) rfl rfl rfl
      intro hA b2 t2 g2 s2 hI2 hga
      have hlf : lf f ks ws (envOf bs) sl (e, i) = NumSpec.col f ks ws (envOf bs) 1 e := by simp [lf, hle]
      exact (hrec b2 t2 g2 s2 (by simpa using hI2) (by rw [hlf]; exact hA) (by rw [hlf]; exact hga)).cast rfl
        (by simp) rfl rfl rfl
    · rw [hle, if_pos (keq (show (w2 true == 1) = true from rfl))] at hR'
      subst hR'
      refine ⟨⟨by dsimp only; omega, by dsimp only; omega, hsc.2.2⟩, ?_⟩
      dsimp only
      obtain ⟨k2, l2⟩ := k1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 4 0 gb
      obtain ⟨k3, -⟩ := k2.pushw (n := u ts.length + 2) (by simp [u2, uadd]) (by have := hsz.2.1; omega) 1 0 0
      obtain ⟨k4, l4⟩ := k3.spush (by have := hsz.2.2.2; omega) (w2 false)
      obtain ⟨k5, -⟩ := k4.spush (by have := hsz.2.2.2; omega) (u (sl + i))
      have e1 : u S.length + 1 = u (S ++ [w2 false]).length := by simp [u1, uadd]
      rw [e1]
      refine (hLIT e Q bs (ts ++ [(9, u (sl + (i + 1)), u cs.length), (4, 0, gb)]) c (serL cs ++ rest) b1 _ g _ S false
        [u (sl + i)] (by omega) hne hQ hx' hc (by simpa [w2] using k5) ?_).cast rfl (by simp [u3, uadd])
        rfl (by simp [u2, uadd]) (by simp)
      intro hA b2 t2 g2 s2 hI2 hga
      generalize hL : NumSpec.litG f ks ws (envOf bs) e = L at *
      have hS : S ++ w2 (false || L.1.2) :: ([u (sl + i)] ++ L.1.1.map u) = S ++ w2 L.1.2 :: ((sl + i) :: L.1.1).map u := by
        simp
      rw [hS] at hI2 ⊢
      have hI2' : MI b2 bs t2 ((ts ++ [(9, u (sl + (i + 1)), u cs.length)]) ++ [(4, u 0, gb)]) g2 s2
          (S ++ w2 L.1.2 :: ((sl + i) :: L.1.1).map u) := by rw [← u0]; simpa using hI2
      refine (m_close hQ (by omega) hI2' ?_).cast rfl (by simp) rfl rfl rfl
      intro hI3
      have hlf : lf f ks ws (envOf bs) sl (e, i) = (⟨(sl + i) :: L.1.1, 0, L.1.2⟩ :: L.2.1, L.2.2) := by
        simp [lf, hle, hL]
      refine (hrec _ _ _ _ (by simpa using hI3) (by rw [hlf]; exact hA) ?_).cast rfl (by simp) rfl rfl rfl
      rw [hlf]
      obtain ⟨X, hX, rfl⟩ := hga
      refine ⟨X ++ [⟨(sl + i) :: L.1.1, 0, L.1.2⟩], ?_, by simp [encG]⟩
      exact (List.perm_append_singleton _ _).trans (List.Perm.cons _ hX)

/-- LETG at a value that is not a tuple -/
theorem m_letg_np {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    (hLIT : MLIT x d np ks ws f) {v : Nd} {sl : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat}
    {rest b t g s : Buf} {S : List UInt64} {gb : UInt64}
    (hv : v.ser.length + 2 ≤ f + 1) (nv : NB np v) (hQ : QM Q) (hx : x.drop c = v.ser ++ rest) (hc : 0 < c)
    (hg : ((hdr v).getD 0 0 == 6) = false)
    (hI : MI b bs t (ts ++ [(3, u sl, 0)]) g s S)
    (hP : MCp x d Q bs ts g S gb (c + v.ser.length)
      (if NumSpec.isL f ws (envOf bs) v then
          (⟨sl :: (NumSpec.litG f ks ws (envOf bs) v).1.1, 0, (NumSpec.litG f ks ws (envOf bs) v).1.2⟩ ::
            (NumSpec.litG f ks ws (envOf bs) v).2.1, (NumSpec.litG f ks ws (envOf bs) v).2.2)
        else NumSpec.col f ks ws (envOf bs) 0 v)) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_read hQ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hI
  intro hsz y y1 y2 hsc R0 hR0
  subst hR0
  rw [u49_3]
  generalize hR : u46 x d b (u (encB bs).length) t (u ts.length) (u c) s (u S.length) gb (u sl) y y1 y2 = R
  intro hok
  have hxl : x.length < 2 ^ 62 := by have := hK.lc.xl; omega
  have hR' := u46_n (by rw [tag_rd hx hxl]; exact hg) R hR
  have hU := u32_ok hK.lc (f := f) (by omega) nv hx hc hI.pb (by have := hsz.1; omega) hI.sb hsc.1 hsc.2.1
  generalize hUe : u32 x d b (u (encB bs).length) y y1 (u c) = U at hU hR'
  obtain ⟨b1, r, y3, y4⟩ := U
  iota_only at hR'
  simp only at hU
  by_cases hr2 : r = 2
  · subst hr2; rw [if_pos (keq (show ((2 : UInt64) == 2) = true from rfl))] at hR'
    subst hR'; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)
  obtain ⟨er, hb1, hbl1, hy3, hy4⟩ := hU hr2
  subst er
  rw [if_neg (kne (w2_eq2 _))] at hR'
  have hts := hI.lts; simp at hts
  have hI0 := hI.pop.withb hb1 hbl1
  cases hle : NumSpec.isL f ws (envOf bs) v
  · rw [hle, if_neg (kne (show (w2 false == 1) = false from rfl))] at hR'
    subst hR'
    refine ⟨⟨by dsimp only; omega, by dsimp only; omega, hsc.2.2⟩, ?_⟩
    dsimp only
    rw [hle] at hP
    obtain ⟨k1, -⟩ := hI0.pushw rfl (by have := hsz.2.1; omega) 0 0 0
    exact (hCOL v 0 Q bs ts c rest b1 _ g s S gb (by omega) nv (by omega) hQ hx hc (by rw [← u0]; simpa using k1)
      hP).cast rfl (by simp [u1, uadd]) rfl rfl rfl
  · rw [hle, if_pos (keq (show (w2 true == 1) = true from rfl))] at hR'
    subst hR'
    refine ⟨⟨by dsimp only; omega, by dsimp only; omega, hsc.2.2⟩, ?_⟩
    dsimp only
    rw [hle] at hP
    obtain ⟨k1, l1⟩ := hI0.pushw rfl (by have := hsz.2.1; omega) 4 0 gb
    obtain ⟨k2, -⟩ := k1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 1 0 0
    obtain ⟨k3, l3⟩ := k2.spush (by have := hsz.2.2.2; omega) (w2 false)
    obtain ⟨k4, -⟩ := k3.spush (by have := hsz.2.2.2; omega) (u sl)
    have e1 : u S.length + 1 = u (S ++ [w2 false]).length := by simp [u1, uadd]
    rw [e1]
    refine (hLIT v Q bs (ts ++ [(4, 0, gb)]) c rest b1 _ g _ S false [u sl] (by omega) nv hQ hx hc
      (by simpa [w2] using k4) ?_).cast rfl (by simp [u2, uadd]) rfl (by simp [u2, uadd]) (by simp)
    intro hA b2 t2 g2 s2 hI2 hga
    generalize hL : NumSpec.litG f ks ws (envOf bs) v = L at *
    have hS : S ++ w2 (false || L.1.2) :: ([u sl] ++ L.1.1.map u) = S ++ w2 L.1.2 :: (sl :: L.1.1).map u := by simp
    rw [hS] at hI2 ⊢
    have hI2' : MI b2 bs t2 (ts ++ [(4, u 0, gb)]) g2 s2 (S ++ w2 L.1.2 :: (sl :: L.1.1).map u) := by
      rw [← u0]; simpa using hI2
    refine (m_close hQ (by omega) hI2' ?_).cast rfl (by simp) rfl rfl rfl
    intro hI3
    refine hP hA _ _ _ _ hI3 ?_
    obtain ⟨X, hX, rfl⟩ := hga
    refine ⟨X ++ [⟨sl :: L.1.1, 0, L.1.2⟩], ?_, by simp [encG]⟩
    exact (List.perm_append_singleton _ _).trans (List.Perm.cons _ hX)

theorem m_letg_succ {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    (hLIT : MLIT x d np ks ws f) : MLETG x d np ks ws (f + 1) := by
  intro v sl w Q bs ts c rest b t g s S gb hv nv hsl hQ hx hc hI hP
  rw [letG_succ] at hP
  cases v with
  | pair cs =>
    apply m_read hQ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hI
    intro hsz y y1 y2 hsc R0 hR0
    subst hR0
    have hxl : x.length < 2 ^ 62 := by have := hK.lc.xl; omega
    rw [u49_3, u46_6 (tag_rd hx hxl), tag1 hx hxl (by simp [hdr])]
    simp only [hdr, List.getD_cons_succ, List.getD_cons_zero]
    intro _
    refine ⟨hsc, ?_⟩
    simp only [NB] at nv
    have hf := hv; simp [Nd.ser] at hf
    have hx1 : x.drop (c + 2) = serL cs ++ rest :=
      drop_hdr (hd := [6, u cs.length]) rfl (by rw [hx]; simp [Nd.ser, toU])
    have hts := hI.lts; simp at hts
    obtain ⟨k1, -⟩ := hI.pop.pushw rfl (by have := hsz.2.1; omega) 9 (u sl) (u cs.length)
    refine (m_lpseq hK hCOL hLIT hQ bs sl S gb cs 0 ts (c + 2) rest b _ g s
      (fun e he => by have := serL_mem_len he; omega) ((nbl_iff cs).1 nv.2) hx1 (by omega) nv.1 (by simpa using k1)
      ?_).cast rfl (by simp [u1, uadd]) (by simp [u2, uadd]) rfl rfl
    have e : c + 2 + (serL cs).length = c + (Nd.pair cs).ser.length := by simp [Nd.ser]; omega
    rw [e]; exact hP
  | const v => exact m_letg_np hK hCOL hLIT hv nv hQ hx hc rfl hI hP
  | loc a b' => exact m_letg_np hK hCOL hLIT hv nv hQ hx hc rfl hI hP
  | bin op a b' => exact m_letg_np hK hCOL hLIT hv nv hQ hx hc rfl hI hP
  | ite cm a b' t' e' => exact m_letg_np hK hCOL hLIT hv nv hQ hx hc rfl hI hP
  | letE a b' c' d' => exact m_letg_np hK hCOL hLIT hv nv hQ hx hc rfl hI hP
  | call a b' => exact m_letg_np hK hCOL hLIT hv nv hQ hx hc rfl hI hP
  | prim a b' => exact m_letg_np hK hCOL hLIT hv nv hQ hx hc rfl hI hP
  | loop a b' => exact m_letg_np hK hCOL hLIT hv nv hQ hx hc rfl hI hP
  | cont a => exact m_letg_np hK hCOL hLIT hv nv hQ hx hc rfl hI hP

theorem m_letg_zero {x d : Buf} {np : Nat} {ks ws : List Nat} : MLETG x d np ks ws 0 := by
  intro v _ _ _ _ _ _ _ _ _ _ _ _ _ hv; omega

theorem m_col_zero {x d : Buf} {np : Nat} {ks ws : List Nat} : MCOL x d np ks ws 0 := by
  intro e _ _ _ _ _ _ _ _ _ _ _ hf; omega

/-- **the main walk**: COL, LIT, CMP, LETG at every fuel -/
theorem m_all {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) : ∀ f,
    MCOL x d np ks ws f ∧ MLIT x d np ks ws f ∧ MCMP x d np ks ws f ∧ MLETG x d np ks ws f
  | 0 => ⟨m_col_zero, m_lit_zero, m_cmp_zero, m_letg_zero⟩
  | f + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := m_all hK f
    exact ⟨m_col_succ hK h1 h2 h3 h4, m_lit_succ hK h2 h3 h4, m_cmp_succ hK h1 h2, m_letg_succ hK h1 h2⟩

end NumP
