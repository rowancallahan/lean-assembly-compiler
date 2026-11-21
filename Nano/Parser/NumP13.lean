/- Nano/Parser/NumP13: COL at an operator node (shift; operator tree). -/
import Nano.Parser.NumP12
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- reduce matches on constructors only -/
macro "iota_only" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| dsimp (config := {zeta := false, proj := false, etaStruct := .none, eta := false}) only $(loc)?)

theorem u42_3 {x d b : Buf} {bt : UInt64} {t : Buf} {tt c : UInt64} {s : Buf} {st gb e : UInt64} (hg : bget x c = 3)
    (R : R9) (hR : u42 x d b bt t tt c s st gb e = R) :
    ((if u34 x c == 1 then
      (match u32 x d b bt (c + 2) with
       | (b1, r) =>
         if r == 0 then
           (if u17 x (c + 2) == 0 then
             (b1, (bt, (u27 (u27 t tt 0 1 0) (tt + 1) 0 1 0, (tt + 2, (c + 2, (s, (st, (gb, 1))))))))
            else (b1, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))
         else (b1, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))
     else
      (match u16 x bnew c with
       | (p, ok) =>
         if ok == 1 then
           (match u33 16777216 x d b bt p 0 (bsize p) 0 with
            | (b1, h) =>
              if h == 1 then
                (match u43 16777216 t tt p (bsize p) with
                 | (t1, z) => match z with | (tt1, ok1) => (b1, (bt, (t1, (tt1, (c, (s, (st, (gb, ok1)))))))))
              else (b1, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))
         else (b, (bt, (t, (tt, (c, (s, (st, (gb, 0)))))))))) : R9) = R := by
  rw [← hR]; unfold u42; rw [hg]; zeta_only
  rw [if_pos (keq (show ((3 : UInt64) == 3) = true from rfl))]

/-- a SHIFT: the left operand must be neither literal-only nor a spine let; COL 1 on both operands -/
theorem m_col_shift {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    {op : Nat} {a bb : Nd} {dd : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat}
    {rest b t g s : Buf} {S : List UInt64} {gb : UInt64} (hH : CH x d np f (.bin op a bb) Q c rest)
    (hsh : NumSpec.isShift op = true)
    (hI : MI b bs t (ts ++ [(0, u dd, 0)]) g s S) (hl : NumSpec.isL f ws (envOf bs) (.bin op a bb) = false)
    (hP : MCp x d Q bs ts g S gb (c + (Nd.bin op a bb).ser.length) (NumSpec.col (f + 1) ks ws (envOf bs) dd (.bin op a bb))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_col_nl hK hH.hf hH.hnb hH.hQ hH.hx hH.hc hI hl
  intro b1 hb1 hbl1 hsz R hR hok
  have hxl : x.length < 2 ^ 62 := by have := hK.lc.xl; omega
  have hR' := u42_3 (by rw [hH.tag hxl]; rfl) R hR
  rw [u34_ok hH.hx hxl hH.hnb, show shN (.bin op a bb) = true from hsh,
    if_pos (keq (show (w2 true == 1) = true from rfl))] at hR'
  have hnb := hH.hnb; simp only [NB] at hnb
  have hx1 : x.drop (c + 2) = a.ser ++ (bb.ser ++ rest) := by
    have h0 : x.drop c = [3, u op] ++ (a.ser ++ (bb.ser ++ rest)) := by rw [hH.hx]; simp [Nd.ser, toU]
    simpa using drop_shift h0
  have hx2 := drop_shift hx1
  have hf := hH.hf; simp [Nd.ser] at hf
  have e2 : u c + 2 = u (c + 2) := by rw [u2, uadd]
  rw [e2] at hR'
  have hU := u32_ok hK.lc (f := f) (by omega) hnb.2.1 hx1 (by omega) hb1 hbl1 hI.sb
  generalize hUe : u32 x d b1 (u (encB bs).length) (u (c + 2)) = U at hU hR'
  obtain ⟨b2, r⟩ := U
  simp only at hU
  dsimp only at hR'
  by_cases hr2 : r = 2
  · subst hr2; rw [if_neg (kne (show ((2 : UInt64) == 0) = false from rfl))] at hR'
    subst hR'; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)
  obtain ⟨hr, hb2, hbl2⟩ := hU hr2
  subst hr
  cases hla : NumSpec.isL f ws (envOf bs) a
  · rw [hla, if_pos (keq (show (w2 false == 0) = true from rfl))] at hR'
    rcases u17_ok (f := f) (by have := hK.lc.xl; omega) hx1 (by omega) hnb.2.1 (by omega) with h17 | h17
    · rw [h17, if_neg (kne (show ((2 : UInt64) == 0) = false from rfl))] at hR'
      subst hR'; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)
    cases hsa : NumSpec.spineLet f a
    · rw [h17, hsa, if_pos (keq (show (w2 false == 0) = true from rfl))] at hR'
      subst hR'
      rw [col_succ, if_neg (by simp [hl])] at hP; dsimp only at hP
      rw [if_pos hsh, hla, hsa] at hP
      have hts := hI.lts; simp at hts
      obtain ⟨h1, l1⟩ := (hI.pop.withb hb2 hbl2).pushw rfl (by have := hsz.2.1; omega) 0 1 0
      obtain ⟨h2, -⟩ := h1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 0 1 0
      dsimp only
      refine (hCOL a 1 Q bs (ts ++ [(0, 1, 0)]) (c + 2) _ b2 _ g s S gb (by omega) hnb.2.1 (by omega) hH.hQ hx1
        (by omega) (by rw [u1e]; simpa using h2) ?_).cast rfl (by simp [u2, uadd]) rfl rfl rfl
      intro hA b3 t3 g3 s3 hI3 hga
      refine (hCOL bb 1 Q bs ts (c + 2 + a.ser.length) rest b3 t3 g3 s3 S gb (by omega) hnb.2.2 (by omega) hH.hQ hx2
        (by omega) (by rw [u1e]; simpa using hI3) ?_).cast rfl (by simp) rfl rfl rfl
      have hP2 := MCp.app (A := ([], true)) hP rfl (GA.nil g)
      have e : c + 2 + a.ser.length + bb.ser.length = c + (Nd.bin op a bb).ser.length := by simp [Nd.ser]; omega
      rw [e]; exact MCp.app hP2 hA hga
    · rw [h17, hsa, if_neg (kne (show (w2 true == 0) = false from rfl))] at hR'
      subst hR'; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)
  · rw [hla, if_neg (kne (show (w2 true == 0) = false from rfl))] at hR'
    subst hR'; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)

theorem lvP_len : ∀ (f : Nat) (e : Nd) (pos : Nat), (lvP f e pos).length ≤ e.ser.length
  | 0, e, pos => by have := ser_pos e; cases e <;> simp [lvP] <;> omega
  | f + 1, e, pos => by
    cases e with
    | bin op a b =>
      simp only [lvP]; split
      · simp [Nd.ser]
      · have := lvP_len f a (pos + 2); have := lvP_len f b (pos + 2 + a.ser.length); simp [Nd.ser]; omega
    | _ => simp [lvP]; exact ser_pos _

/-- an OPERATOR TREE: the leaves, the shape rules, COLAT at each leaf -/
theorem m_col_tree {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    {op : Nat} {a bb : Nd} {dd : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat}
    {rest b t g s : Buf} {S : List UInt64} {gb : UInt64} (hH : CH x d np f (.bin op a bb) Q c rest)
    (hsh : NumSpec.isShift op = false)
    (hI : MI b bs t (ts ++ [(0, u dd, 0)]) g s S) (hl : NumSpec.isL f ws (envOf bs) (.bin op a bb) = false)
    (hP : MCp x d Q bs ts g S gb (c + (Nd.bin op a bb).ser.length) (NumSpec.col (f + 1) ks ws (envOf bs) dd (.bin op a bb))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_col_nl hK hH.hf hH.hnb hH.hQ hH.hx hH.hc hI hl
  intro b1 hb1 hbl1 hsz R hR hok
  have hxl : x.length < 2 ^ 62 := by have := hK.lc.xl; omega
  have hR' := u42_3 (by rw [hH.tag hxl]; rfl) R hR
  rw [u34_ok hH.hx hxl hH.hnb, show shN (.bin op a bb) = false from hsh,
    if_neg (kne (show (w2 false == 1) = false from rfl))] at hR'
  have hf := hH.hf
  have hV := u16_ok (f := f) (by have := hK.lc.xl; omega) bnew hH.hx hf hH.hnb hH.hc
  generalize hVe : u16 x bnew (u c) = V at hV hR'
  obtain ⟨p, ok⟩ := V
  iota_only at hR' hV
  by_cases hok1 : ok = 1
  rotate_left
  · rw [if_neg (by simpa using hok1)] at hR'; subst hR'; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)
  subst hok1
  rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))] at hR'
  have hp := hV rfl
  simp only [bnew, List.nil_append] at hp
  subst hp
  generalize hls : lvP f (Nd.bin op a bb) c = ls at *
  have hsp := lvP_sp (x := x) (np := np) f (Nd.bin op a bb) c rest hH.hx hH.hnb hH.hc
  rw [hls] at hsp
  have hlen : ls.length ≤ (Nd.bin op a bb).ser.length := by rw [← hls]; exact lvP_len _ _ _
  have hcl := drop_len hH.hx (ser_pos _)
  have hx23 := hK.lc.xl
  have h33 := u33_ok hK.lc (f := f) hI.sb 16777216 ls [] false b1 (fun q hq => by
      obtain ⟨h1, h2, h3, h4⟩ := hsp q hq; exact ⟨h1, by omega, h3, h4⟩) hb1 hbl1 (by simp; omega)
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h33
  have e0 : (0 : UInt64) = u 0 := rfl
  have ew : (0 : UInt64) = w2 false := rfl
  have eb : bsize (ls.map fun q => u q.2) = u ls.length := by rw [bsize_u, List.length_map]
  rw [eb] at hR'
  generalize hWe : u33 16777216 x d b1 (u (encB bs).length) (ls.map fun q => u q.2) 0 (u ls.length) 0 = W at hR'
  have hW : u33 16777216 x d b1 (u (encB bs).length) (ls.map fun q => u q.2) (u 0) (u ls.length) (w2 false) = W := hWe
  rw [hW] at h33
  obtain ⟨b2, h⟩ := W
  iota_only at hR' h33
  by_cases hh : h = 1
  rotate_left
  · rw [if_neg (by simpa using hh)] at hR'; subst hR'; exact absurd hok (show (0 : UInt64) ≠ 1 by decide)
  subst hh
  obtain ⟨hshp, hb2, hbl2⟩ := h33 rfl
  simp only at hb2 hbl2
  rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))] at hR'
  have hts := hI.pop.pt.length_le; rw [encT_len] at hts
  have h43 := u43_ok (ls.map fun q => u q.2) (by simp; omega) 16777216 ls.length ts t (by simp) (by omega) hI.pop.pt
    (by have := hsz.2.1; omega) (by have := hsz.2.1; omega)
  generalize hXe : u43 16777216 t (u ts.length) (ls.map fun q => u q.2) (u ls.length) = X at h43 hR'
  obtain ⟨t1, tt1, ok1⟩ := X
  iota_only at hR' h43
  obtain ⟨q1, q2, q3, q4⟩ := h43
  dsimp only at q1 q2 q3 q4
  subst q1 q4
  subst hR'
  rw [List.take_of_length_le (by simp)] at q2
  have hI1 : MI b2 bs t1 (ts ++ colat (ls.map fun q => u q.2)) g s S :=
    ⟨hb2, by omega, hI.sb, q2, by have := q3 (2 ^ 41) (by have := hsz.2.1; omega) (by have := hsz.2.1; omega); omega,
      hI.lg, hI.ps, hI.ls⟩
  rw [col_succ, if_neg (by simp [hl])] at hP; dsimp only at hP
  rw [if_neg (by simp [hsh]), colL_attach, ← lvP_fst f _ c, hls] at hP
  have hshape : NumSpec.shapeOk f ws (envOf bs) (ls.map Prod.fst) = true := shapeOk_of hshp
  rw [hshape] at hP
  have hP2 := MCp.app (A := ([], true)) hP rfl (GA.nil g)
  have hend : lend c ls = c + (Nd.bin op a bb).ser.length := by rw [← hls]; exact lvP_lend _ _ _ _
  rw [← hend] at hP2
  dsimp only
  have hf1 : 1 ≤ f := by have := ser_pos (Nd.bin op a bb); omega
  have hlt := lvP_lt (f := f - 1) (x := x) hH.hx hH.hnb hH.hc hsh
  rw [show f - 1 + 1 = f by omega, hls] at hlt
  refine m_colats hCOL hH.hQ bs ts S gb ls c b2 t1 g s (fun q hq => ?_) hI1 hP2
  obtain ⟨h1, h2, h3, h4⟩ := hsp q hq
  exact ⟨h1, by have := hlt q hq; omega, h3, h4⟩

end NumP
