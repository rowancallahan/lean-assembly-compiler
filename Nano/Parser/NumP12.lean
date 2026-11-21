/- Nano/Parser/NumP12: COL at a loop, a tuple, a prim, a call. -/
import Nano.Parser.NumP11
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

theorem u1e : (u 1 : UInt64) = 1 := rfl

/-- LOOP: COL 1 on z, then on s -/
theorem m_col_loop {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    {z sv : Nd} {dd : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat} {rest b t g s : Buf}
    {S : List UInt64} {gb : UInt64} (hH : CH x d np f (.loop z sv) Q c rest)
    (hI : MI b bs t (ts ++ [(0, u dd, 0)]) g s S) (hl : NumSpec.isL f ws (envOf bs) (.loop z sv) = false)
    (hP : MCp x d Q bs ts g S gb (c + (Nd.loop z sv).ser.length) (NumSpec.col (f + 1) ks ws (envOf bs) dd (.loop z sv))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_col_nl hK hH.hf hH.hnb hH.hQ hH.hx hH.hc hI hl
  intro b1 hb1 hbl1 hsz R hR _
  rw [u42_10 (by rw [hH.tag (by have := hK.lc.xl; omega)]; rfl)] at hR
  subst hR
  rw [col_succ, if_neg (by simp [hl])] at hP; dsimp only at hP
  have hts := hI.lts; simp at hts
  obtain ⟨h1, l1⟩ := (hI.pop.withb hb1 hbl1).pushw rfl (by have := hsz.2.1; omega) 0 1 0
  obtain ⟨h2, -⟩ := h1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 0 1 0
  have hx1 : x.drop (c + 1) = z.ser ++ (sv.ser ++ rest) := by
    have h0 : x.drop c = [10] ++ (z.ser ++ (sv.ser ++ rest)) := by rw [hH.hx]; simp [Nd.ser]
    simpa using drop_shift h0
  have hx2 := drop_shift hx1
  have hf := hH.hf; simp [Nd.ser] at hf
  have hnb := hH.hnb
  refine (hCOL z 1 Q bs (ts ++ [(0, 1, 0)]) (c + 1) _ b1 _ g s S gb (by omega) hnb.1 (by omega) hH.hQ hx1 (by omega)
    (by rw [u1e]; simpa using h2) ?_).cast rfl (by simp [u2, uadd]) (by simp [u1, uadd]) rfl rfl
  intro hA b2 t2 g2 s2 hI2 hga
  refine (hCOL sv 1 Q bs ts (c + 1 + z.ser.length) rest b2 t2 g2 s2 S gb (by omega) hnb.2 (by omega) hH.hQ hx2 (by omega)
    (by rw [u1e]; simpa using hI2) ?_).cast rfl (by simp) rfl rfl rfl
  exact MCp.app (by simpa [Nd.ser, Nat.add_assoc, Nat.add_comm 1] using hP) hA hga

theorem tag1 {x : Buf} {e : Nd} {r : Buf} {q : Nat} (hx : x.drop q = e.ser ++ r) (hl : x.length < 2 ^ 62)
    (h : 1 < (hdr e).length) : bget x (u q + 1) = (hdr e).getD 1 0 := tag1_rd hx hl h
theorem tag2 {x : Buf} {e : Nd} {r : Buf} {q : Nat} (hx : x.drop q = e.ser ++ r) (hl : x.length < 2 ^ 62)
    (h : 2 < (hdr e).length) : bget x (u q + 2) = (hdr e).getD 2 0 := by rw [u2, uadd]; exact rdh hx hl h

theorem serL_mem_len {cs : List Nd} {e : Nd} (h : e ∈ cs) : e.ser.length ≤ (serL cs).length := mem_serL_len h

/-- a node list behind a header of k words -/
theorem drop_hdr {x : Buf} {c k : Nat} {hd : List UInt64} {cs : List Nd} {rest : Buf} (hk : hd.length = k)
    (hx : x.drop c = (hd ++ serL cs) ++ rest) : x.drop (c + k) = serL cs ++ rest := by
  subst hk; rw [List.append_assoc] at hx; exact drop_shift hx

/-- a TUPLE: COLSEQ over the fields -/
theorem m_col_pair {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    {cs : List Nd} {dd : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat} {rest b t g s : Buf}
    {S : List UInt64} {gb : UInt64} (hH : CH x d np f (.pair cs) Q c rest)
    (hI : MI b bs t (ts ++ [(0, u dd, 0)]) g s S) (hl : NumSpec.isL f ws (envOf bs) (.pair cs) = false)
    (hP : MCp x d Q bs ts g S gb (c + (Nd.pair cs).ser.length) (NumSpec.col (f + 1) ks ws (envOf bs) dd (.pair cs))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_col_nl hK hH.hf hH.hnb hH.hQ hH.hx hH.hc hI hl
  intro b1 hb1 hbl1 hsz R hR _
  rw [u42_6 (by rw [hH.tag (by have := hK.lc.xl; omega)]; rfl), tag1 hH.hx (by have := hK.lc.xl; omega) (by simp [hdr])] at hR
  simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at hR
  subst hR
  rw [col_succ, if_neg (by simp [hl])] at hP; dsimp only at hP
  rw [colL_attach] at hP
  have hts := hI.lts; simp at hts
  obtain ⟨h1, -⟩ := (hI.pop.withb hb1 hbl1).pushw rfl (by have := hsz.2.1; omega) 7 (u cs.length) 0
  have hx1 : x.drop (c + 2) = serL cs ++ rest := drop_hdr (hd := [6, u cs.length]) rfl (by rw [hH.hx]; simp [Nd.ser, toU])
  have hf := hH.hf; simp [Nd.ser] at hf
  have hnb := hH.hnb; simp only [NB] at hnb
  refine (m_colseq hCOL hH.hQ cs bs ts (c + 2) rest b1 _ g s S gb 0 (fun e he => by have := serL_mem_len he; omega)
    ((nbl_iff cs).1 hnb.2) hx1 (by omega) hnb.1 h1 ?_).cast rfl (by simp [u1, uadd]) (by simp [u2, uadd]) rfl rfl
  have e : c + 2 + (serL cs).length = c + (Nd.pair cs).ser.length := by simp [Nd.ser]; omega
  rw [e]; exact hP

/-- a PRIM: COLSEQ over the operands -/
theorem m_col_prim {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    {pn : Nat} {cs : List Nd} {dd : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat}
    {rest b t g s : Buf} {S : List UInt64} {gb : UInt64} (hH : CH x d np f (.prim pn cs) Q c rest)
    (hI : MI b bs t (ts ++ [(0, u dd, 0)]) g s S) (hl : NumSpec.isL f ws (envOf bs) (.prim pn cs) = false)
    (hP : MCp x d Q bs ts g S gb (c + (Nd.prim pn cs).ser.length) (NumSpec.col (f + 1) ks ws (envOf bs) dd (.prim pn cs))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_col_nl hK hH.hf hH.hnb hH.hQ hH.hx hH.hc hI hl
  intro b1 hb1 hbl1 hsz R hR _
  have hnb := hH.hnb; simp only [NB] at hnb
  have hg : g33 (u pn) = u cs.length := by rw [hnb.2.1]; simp only [toU]; unfold u; simp
  rw [u42_9 (by rw [hH.tag (by have := hK.lc.xl; omega)]; rfl), tag1 hH.hx (by have := hK.lc.xl; omega) (by simp [hdr])] at hR
  simp only [hdr, List.getD_cons_succ, List.getD_cons_zero, hg] at hR
  subst hR
  rw [col_succ, if_neg (by simp [hl])] at hP; dsimp only at hP
  rw [colL_attach] at hP
  have hts := hI.lts; simp at hts
  obtain ⟨h1, -⟩ := (hI.pop.withb hb1 hbl1).pushw rfl (by have := hsz.2.1; omega) 7 (u cs.length) 0
  have hx1 : x.drop (c + 2) = serL cs ++ rest := drop_hdr (hd := [9, u pn]) rfl (by rw [hH.hx]; simp [Nd.ser, toU])
  have hf := hH.hf; simp [Nd.ser] at hf
  have hcl : cs.length < 2 ^ 32 := by have := len_le_serL cs; have := hK.lc.xl; have := drop_len hH.hx (ser_pos _); simp [Nd.ser] at this; omega
  refine (m_colseq hCOL hH.hQ cs bs ts (c + 2) rest b1 _ g s S gb 0 (fun e he => by have := serL_mem_len he; omega)
    ((nbl_iff cs).1 hnb.2.2) hx1 (by omega) hcl h1 ?_).cast rfl (by simp [u1, uadd]) (by simp [u2, uadd]) rfl rfl
  have e : c + 2 + (serL cs).length = c + (Nd.prim pn cs).ser.length := by simp [Nd.ser]; omega
  rw [e]; exact hP

end NumP
