/- Nano/Parser/NumP11: COL at a node that is not literal-only: the dispatch to `u42`, the simple tags. -/
import Nano.Parser.NumP10
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- zeta-reduce only (no match/projection conversions: those make the kernel evaluate the fuel-2^24 loops) -/
macro "zeta_only" : tactic =>
  `(tactic| dsimp (config := {iota := false, proj := false, etaStruct := .none, beta := false, eta := false}) only)

section
variable {x d b : Buf} {bt : UInt64} {t : Buf} {tt c : UInt64} {s : Buf} {st gb e : UInt64} {y y1 y2 : Buf}

theorem u42_2 (hg : bget x c = 2) : u42 x d b bt t tt c s st gb e y y1 y2 = (b, (bt, (t, (tt, (c + 3, (s, (st, (gb, (1, (y, (y1, y2))))))))))) := by
  unfold u42; rw [hg]; zeta_only
  rw [if_neg (kne (show ((2 : UInt64) == 3) = false from rfl)), if_neg (kne (show ((2 : UInt64) == 4) = false from rfl)),
    if_neg (kne (show ((2 : UInt64) == 5) = false from rfl)), if_neg (kne (show ((2 : UInt64) == 6) = false from rfl)),
    if_neg (kne (show ((2 : UInt64) == 8) = false from rfl)), if_neg (kne (show ((2 : UInt64) == 9) = false from rfl)),
    if_neg (kne (show ((2 : UInt64) == 10) = false from rfl)), if_neg (kne (show ((2 : UInt64) == 11) = false from rfl)),
    if_neg (kne (show ((2 : UInt64) == 1) = false from rfl)), if_pos (keq (show ((2 : UInt64) == 2) = true from rfl))]

theorem u42_6 (hg : bget x c = 6) :
    u42 x d b bt t tt c s st gb e y y1 y2 = (b, (bt, (u27 t tt 7 (bget x (c + 1)) 0, (tt + 1, (c + 2, (s, (st, (gb, (1, (y, (y1, y2))))))))))) := by
  unfold u42; rw [hg]; zeta_only
  rw [if_neg (kne (show ((6 : UInt64) == 3) = false from rfl)), if_neg (kne (show ((6 : UInt64) == 4) = false from rfl)),
    if_neg (kne (show ((6 : UInt64) == 5) = false from rfl)), if_pos (keq (show ((6 : UInt64) == 6) = true from rfl))]

theorem u42_9 (hg : bget x c = 9) :
    u42 x d b bt t tt c s st gb e y y1 y2 = (b, (bt, (u27 t tt 7 (g33 (bget x (c + 1))) 0, (tt + 1, (c + 2, (s, (st, (gb, (1, (y, (y1, y2))))))))))) := by
  unfold u42; rw [hg]; zeta_only
  rw [if_neg (kne (show ((9 : UInt64) == 3) = false from rfl)), if_neg (kne (show ((9 : UInt64) == 4) = false from rfl)),
    if_neg (kne (show ((9 : UInt64) == 5) = false from rfl)), if_neg (kne (show ((9 : UInt64) == 6) = false from rfl)),
    if_neg (kne (show ((9 : UInt64) == 8) = false from rfl)), if_pos (keq (show ((9 : UInt64) == 9) = true from rfl))]

theorem u42_10 (hg : bget x c = 10) :
    u42 x d b bt t tt c s st gb e y y1 y2 = (b, (bt, (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0, (tt + 2, (c + 1, (s, (st, (gb, (1, (y, (y1, y2))))))))))) := by
  unfold u42; rw [hg]; zeta_only
  rw [if_neg (kne (show ((10 : UInt64) == 3) = false from rfl)), if_neg (kne (show ((10 : UInt64) == 4) = false from rfl)),
    if_neg (kne (show ((10 : UInt64) == 5) = false from rfl)), if_neg (kne (show ((10 : UInt64) == 6) = false from rfl)),
    if_neg (kne (show ((10 : UInt64) == 8) = false from rfl)), if_neg (kne (show ((10 : UInt64) == 9) = false from rfl)),
    if_pos (keq (show ((10 : UInt64) == 10) = true from rfl))]

theorem u42_11 (hg : bget x c = 11) :
    u42 x d b bt t tt c s st gb e y y1 y2 = (b, (bt, (u27 t tt 0 1 0, (tt + 1, (c + 1, (s, (st, (gb, (1, (y, (y1, y2))))))))))) := by
  unfold u42; rw [hg]; zeta_only
  rw [if_neg (kne (show ((11 : UInt64) == 3) = false from rfl)), if_neg (kne (show ((11 : UInt64) == 4) = false from rfl)),
    if_neg (kne (show ((11 : UInt64) == 5) = false from rfl)), if_neg (kne (show ((11 : UInt64) == 6) = false from rfl)),
    if_neg (kne (show ((11 : UInt64) == 8) = false from rfl)), if_neg (kne (show ((11 : UInt64) == 9) = false from rfl)),
    if_neg (kne (show ((11 : UInt64) == 10) = false from rfl)), if_pos (keq (show ((11 : UInt64) == 11) = true from rfl))]

theorem u42_5 (hg : bget x c = 5) :
    u42 x d b bt t tt c s st gb e y y1 y2 = (b, (bt, (u27 (u27 (u27 (u27 t tt 5 bt 0) (tt + 1) 0 e 0) (tt + 2) 6 (bget x (c + 1)) (c + 3))
      (tt + 3) 3 (bget x (c + 1)) 0, (tt + 4, (c + 3, (s, (st, (gb, (1, (y, (y1, y2))))))))))) := by
  unfold u42; rw [hg]; zeta_only
  rw [if_neg (kne (show ((5 : UInt64) == 3) = false from rfl)), if_neg (kne (show ((5 : UInt64) == 4) = false from rfl)),
    if_pos (keq (show ((5 : UInt64) == 5) = true from rfl))]

theorem u42_8 (hg : bget x c = 8) :
    u42 x d b bt t tt c s st gb e y y1 y2 = if bget x (c + 2) == 0 then (b, (bt, (t, (tt, (c + 3, (s, (st, (gb, (1, (y, (y1, y2)))))))))))
      else (b, (bt, (u27 (u27 t tt 7 (bget x (c + 2) - 1) 0) (tt + 1) 0
        (if 2 * bget x (c + 1) < bsize d then (if bget d (2 * bget x (c + 1)) == 1 then 2 else 1) else 1) 0,
        (tt + 2, (c + 3, (s, (st, (gb, (1, (y, (y1, y2))))))))))) := by
  unfold u42; rw [hg]; zeta_only
  rw [if_neg (kne (show ((8 : UInt64) == 3) = false from rfl)), if_neg (kne (show ((8 : UInt64) == 4) = false from rfl)),
    if_neg (kne (show ((8 : UInt64) == 5) = false from rfl)), if_neg (kne (show ((8 : UInt64) == 6) = false from rfl)),
    if_pos (keq (show ((8 : UInt64) == 8) = true from rfl))]

end

/-- COL at a node that is not literal-only: `u32` says 0, then `u42` -/
theorem m_col_nl {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat}
    {e : Nd} {dd : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat} {rest b t g s : Buf}
    {S : List UInt64} {gb : UInt64}
    (hf : e.ser.length ≤ f) (hnb : NB np e) (hQ : QM Q) (hx : x.drop c = e.ser ++ rest) (hc : 0 < c)
    (hI : MI b bs t (ts ++ [(0, u dd, 0)]) g s S) (hl : NumSpec.isL f ws (envOf bs) e = false)
    (H : ∀ b1 : Buf, encB bs <+: b1 → b1.length < 2 ^ 42 → SZ b t g s →
      ∀ y y1 y2, SC y y1 y2 → ∀ R : R12,
      u42 x d b1 (u (encB bs).length) t (u ts.length) (u c) s (u S.length) gb (u dd) y y1 y2 = R → R.2.2.2.2.2.2.2.2.1 = 1 →
      SCR R ∧ GM x d Q R.1 R.2.1 R.2.2.1 R.2.2.2.1 R.2.2.2.2.1 g R.2.2.2.2.2.1 R.2.2.2.2.2.2.1 R.2.2.2.2.2.2.2.1) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_read hQ (Or.inl rfl) hI
  intro hsz y y1 y2 hsc R hR
  subst hR
  have hU := u32_ok hK.lc hf hnb hx hc hI.pb (by have := hsz.1; omega) hI.sb hsc.1 hsc.2.1
  generalize hUe : u32 x d b (u (encB bs).length) y y1 (u c) = U at hU
  obtain ⟨b1, r, y3, y4⟩ := U
  rw [u49_0, u41_eq hUe]
  by_cases hr2 : r = 2
  · subst hr2; rw [if_pos (keq rfl)]; intro h; exact absurd h (show (0 : UInt64) ≠ 1 by decide)
  obtain ⟨hr, hb1, hbl1, hy3, hy4⟩ := hU hr2
  simp only at hr hb1 hbl1 hy3 hy4
  rw [hl] at hr; subst hr
  rw [if_neg (kne (show (w2 false == 2) = false from rfl)), if_neg (kne (show (w2 false == 1) = false from rfl))]
  exact H b1 hb1 hbl1 hsz y3 y4 y2 ⟨by omega, by omega, hsc.2.2⟩ _ rfl

theorem MI.withb {b bs t ts g s S} (h : MI b bs t ts g s S) {b1 : Buf} (h1 : encB bs <+: b1) (h2 : b1.length < 2 ^ 42) :
    MI b1 bs t ts g s S := ⟨h1, by omega, h.sb, h.pt, h.lt, h.lg, h.ps, h.ls⟩

/-- the common hypotheses of a COL case at fuel f + 1 -/
structure CH (x d : Buf) (np : Nat) (f : Nat) (e : Nd) (Q : MO → Prop) (c : Nat) (rest : Buf) : Prop where
  hf : e.ser.length ≤ f
  hnb : NB np e
  hQ : QM Q
  hx : x.drop c = e.ser ++ rest
  hc : 0 < c

theorem CH.tag {x d np f e Q c rest} (h : CH x d np f e Q c rest) (hl : x.length < 2 ^ 62) :
    bget x (u c) = (hdr e).getD 0 0 := tag_rd h.hx hl

/-- a leaf that is not literal-only: a slot (a constant is literal-only) -/
theorem m_col_loc {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} {sl w : Nat}
    {dd : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat} {rest b t g s : Buf}
    {S : List UInt64} {gb : UInt64} (hH : CH x d np f (.loc sl w) Q c rest)
    (hI : MI b bs t (ts ++ [(0, u dd, 0)]) g s S) (hl : NumSpec.isL f ws (envOf bs) (.loc sl w) = false)
    (hP : MCp x d Q bs ts g S gb (c + (Nd.loc sl w).ser.length) (NumSpec.col (f + 1) ks ws (envOf bs) dd (.loc sl w))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_col_nl hK hH.hf hH.hnb hH.hQ hH.hx hH.hc hI hl
  intro b1 hb1 hbl1 hsz y y1 y2 hsc R hR _
  rw [u42_2 (by rw [hH.tag (by have := hK.lc.xl; omega)]; rfl)] at hR
  subst hR
  refine ⟨hsc, ?_⟩
  rw [col_succ, if_neg (by simp [hl])] at hP; dsimp only at hP
  exact (hP rfl b1 t g s (hI.pop.withb hb1 hbl1) (GA.nil g)).cast rfl rfl (by simp [Nd.ser, u3, uadd]) rfl rfl

theorem m_col_const {ws : List Nat} {f : Nat} {v : UInt64} {env : List Bool} (hf : (Nd.const v).ser.length ≤ f)
    (hl : NumSpec.isL f ws env (.const v) = false) : False := by
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp [Nd.ser] at hf; omega⟩
  simp [NumSpec.isL, NumSpec.lw] at hl

/-- CONTINUE: COL 1 on the operand -/
theorem m_col_cont {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    {a : Nd} {dd : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat} {rest b t g s : Buf}
    {S : List UInt64} {gb : UInt64} (hH : CH x d np f (.cont a) Q c rest)
    (hI : MI b bs t (ts ++ [(0, u dd, 0)]) g s S) (hl : NumSpec.isL f ws (envOf bs) (.cont a) = false)
    (hP : MCp x d Q bs ts g S gb (c + (Nd.cont a).ser.length) (NumSpec.col (f + 1) ks ws (envOf bs) dd (.cont a))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_col_nl hK hH.hf hH.hnb hH.hQ hH.hx hH.hc hI hl
  intro b1 hb1 hbl1 hsz y y1 y2 hsc R hR _
  rw [u42_11 (by rw [hH.tag (by have := hK.lc.xl; omega)]; rfl)] at hR
  subst hR
  refine ⟨hsc, ?_⟩
  rw [col_succ, if_neg (by simp [hl])] at hP; dsimp only at hP
  have hts := hI.lts; simp at hts
  obtain ⟨h1, -⟩ := (hI.pop.withb hb1 hbl1).pushw rfl (by have := hsz.2.1; omega) 0 1 0
  have hx1 : x.drop (c + 1) = a.ser ++ rest := by
    have h0 : x.drop c = [11] ++ (a.ser ++ rest) := by rw [hH.hx]; simp [Nd.ser]
    simpa using drop_shift h0
  have hf := hH.hf; simp [Nd.ser] at hf
  refine (hCOL a 1 Q bs ts (c + 1) rest b1 _ g s S gb (by omega) hH.hnb.2 (by omega) hH.hQ hx1 (by omega)
    (by rw [show (u 1 : UInt64) = 1 from rfl]; simpa using h1) ?_).cast rfl (by simp [u1, uadd]) (by simp [u1, uadd]) rfl rfl
  exact (show MCp x d Q bs ts g S gb (c + 1 + a.ser.length) (NumSpec.col f ks ws (envOf bs) 1 a) by
    simpa [Nd.ser, Nat.add_assoc, Nat.add_comm 1] using hP)

end NumP
