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

theorem call_rest (f : Nat) (ks ws : List Nat) (env : List Bool) (id : Nat) :
    ∀ (as : List Nd) (n : Nat), 1 ≤ n →
    (as.zipIdx n).attach.foldr (fun ⟨(a, i), _⟩ r =>
        (NumSpec.col f ks ws env (if ks.getD id 0 == 1 && i == 0 then 2 else 1) a).app r) NumSpec.R.ok =
      colL f ks ws env as
  | [], _, _ => rfl
  | a :: as, n, hn => by
    have ih := call_rest f ks ws env id as (n + 1) (by omega)
    have hn0 : (n == 0) = false := by simp; omega
    simp only [List.zipIdx_cons, List.attach_cons, List.foldr_cons, List.foldr_map, hn0, Bool.and_false,
      Bool.false_eq_true, if_false, colL] at ih ⊢
    rw [ih]

theorem call_spec (f : Nat) (ks ws : List Nat) (env : List Bool) (id : Nat) (a : Nd) (as : List Nd) :
    ((a :: as).zipIdx.attach.foldr (fun ⟨(a, i), _⟩ r =>
        (NumSpec.col f ks ws env (if ks.getD id 0 == 1 && i == 0 then 2 else 1) a).app r) NumSpec.R.ok) =
      (NumSpec.col f ks ws env (if ks.getD id 0 == 1 then 2 else 1) a).app (colL f ks ws env as) := by
  have ih := call_rest f ks ws env id as 1 (Nat.le_refl 1)
  simp only [List.zipIdx_cons, List.attach_cons, List.foldr_cons, List.foldr_map, colL] at ih ⊢
  rw [ih]; simp

/-- the demand of a call's first argument, from the def table -/
theorem dem_eq {x d : Buf} {ks ws : List Nat} (hK : LK x d ks ws) {id : Nat} (hid : id < 2 ^ 32) :
    (if 2 * u id < bsize d then (if bget d (2 * u id) == 1 then (2 : UInt64) else 1) else 1) =
      u (if ks.getD id 0 == 1 then 2 else 1) := by
  have hdl := hK.lc.dl; have hwl := hK.lc.wl
  have e2 : (2 : UInt64) * u id = u (2 * id) := by rw [u2, u_mul]
  have hlt : (u (2 * id) < u d.length) = (2 * id < d.length) := ult (by omega) (by omega)
  rw [e2, bsize_u]; simp only [hlt]
  by_cases hi : id < ws.length
  · rw [if_pos (by omega), bget_u _ (by omega), hK.dk id hi, u1, ueq (by have := hK.kb id hi; omega) (by omega)]
    by_cases hk : ks.getD id 0 = 1
    · rw [if_pos (by simp only [decide_eq_true_eq]; exact hk), if_pos (by simp only [beq_iff_eq]; exact hk)]; rfl
    · rw [if_neg (by simp only [decide_eq_true_eq]; exact hk), if_neg (by simp only [beq_iff_eq]; exact hk)]
  · rw [if_neg (by omega), getD_ge _ (by rw [hK.kl]; omega)]; rfl

/-- a CALL: COL at the first argument's demand, then COLSEQ over the others -/
theorem m_col_call {x d : Buf} {np : Nat} {ks ws : List Nat} (hK : LK x d ks ws) {f : Nat} (hCOL : MCOL x d np ks ws f)
    {id : Nat} {cs : List Nd} {dd : Nat} {Q : MO → Prop} {bs : List (Nat × List Bool)} {ts : List T3} {c : Nat}
    {rest b t g s : Buf} {S : List UInt64} {gb : UInt64} (hH : CH x d np f (.call id cs) Q c rest)
    (hI : MI b bs t (ts ++ [(0, u dd, 0)]) g s S) (hl : NumSpec.isL f ws (envOf bs) (.call id cs) = false)
    (hP : MCp x d Q bs ts g S gb (c + (Nd.call id cs).ser.length) (NumSpec.col (f + 1) ks ws (envOf bs) dd (.call id cs))) :
    GM x d Q b (u (encB bs).length) t (u (ts.length + 1)) (u c) g s (u S.length) gb := by
  apply m_col_nl hK hH.hf hH.hnb hH.hQ hH.hx hH.hc hI hl
  intro b1 hb1 hbl1 hsz R hR hok
  have hnb := hH.hnb; simp only [NB] at hnb
  have hxl : x.length < 2 ^ 62 := by have := hK.lc.xl; omega
  rw [u42_8 (by rw [hH.tag hxl]; rfl), tag1 hH.hx hxl (by simp [hdr]), tag2 hH.hx hxl (by simp [hdr])] at hR
  simp only [hdr, List.getD_cons_succ, List.getD_cons_zero] at hR
  rw [col_succ, if_neg (by simp [hl])] at hP; dsimp only at hP
  have hts := hI.lts; simp at hts
  have hf := hH.hf; simp [Nd.ser] at hf
  have hx1 : x.drop (c + 3) = serL cs ++ rest :=
    drop_hdr (hd := [8, u id, u cs.length]) rfl (by rw [hH.hx]; simp [Nd.ser, toU])
  have hI0 := hI.pop.withb hb1 hbl1
  cases cs with
  | nil =>
    rw [if_pos (keq (show (u ([] : List Nd).length == 0) = true from rfl))] at hR
    subst hR
    exact (hP rfl b1 t g s hI0 (GA.nil g)).cast rfl rfl (by simp [Nd.ser, serL, u3, uadd]) rfl rfl
  | cons a as =>
    have h0 : (u (a :: as).length == 0) = false := by
      rw [u0, ueq (by have := hnb.2.1; omega) (by omega)]; simp
    rw [if_neg (kne h0), dem_eq hK hnb.1, show u (a :: as).length - 1 = u as.length from upred _ (by have := hnb.2.1; simp at this; omega)] at hR
    subst hR
    rw [call_spec] at hP
    obtain ⟨h1, l1⟩ := hI0.pushw rfl (by have := hsz.2.1; omega) 7 (u as.length) 0
    obtain ⟨h2, -⟩ := h1.pushw (n := u ts.length + 1) (by simp [u1, uadd]) (by have := hsz.2.1; omega) 0
      (u (if ks.getD id 0 == 1 then 2 else 1)) 0
    have hxa : x.drop (c + 3) = a.ser ++ (serL as ++ rest) := by rw [hx1]; simp [serL]
    have hxs := drop_shift hxa
    have hnbl := (nbl_iff _).1 hnb.2.2
    have hfa : a.ser.length + 1 ≤ f := by simp [serL] at hf; omega
    have hdd : (if ks.getD id 0 == 1 then 2 else 1) < 3 := by split <;> omega
    dsimp only
    refine (hCOL a (if ks.getD id 0 == 1 then 2 else 1) Q bs (ts ++ [(7, u as.length, 0)]) (c + 3) (serL as ++ rest) b1
      (u27 (u27 t (u ts.length) 7 (u as.length) 0) (u ts.length + 1) 0 (u (if ks.getD id 0 == 1 then 2 else 1)) 0) g s S gb
      hfa (hnbl a (by simp)) hdd hH.hQ hxa (by omega) h2 ?_).cast rfl (by simp [u2, uadd]) (by simp [u3, uadd])
      rfl rfl
    intro hA b2 t2 g2 s2 hI2 hga
    refine (m_colseq hCOL hH.hQ as bs ts (c + 3 + a.ser.length) rest b2 t2 g2 s2 S gb 0
      (fun e he => by have := serL_mem_len he; simp [serL] at hf; omega) (fun e he => hnbl e (by simp [he])) hxs
      (by omega) (by have := hnb.2.1; simp at this; omega) hI2 ?_).cast rfl (by simp) rfl rfl rfl
    have e : c + 3 + a.ser.length + (serL as).length = c + (Nd.call id (a :: as)).ser.length := by
      simp [Nd.ser, serL]; omega
    rw [e]; exact MCp.app hP hA hga

end NumP
