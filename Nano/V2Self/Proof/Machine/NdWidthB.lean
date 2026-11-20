/- Machine bridge (Opus box E): A's width relation (`GenRef.W`, from the width pass g53) gives the width side
conditions `WdV` of the node theorem: `wV` / `wT` / `wL`, by induction on the AST node serialized at the cursor. -/
import Nano.V2Self.Proof.Machine.NdWidth
import Nano.V2Self.Proof.Machine.NdCG
import Nano.V2Self.Proof.Gen.GenWidth
namespace Templates
open CallProbe C GenRef ParSpec

section inv
variable {X : Buf} {D : List (UInt64 × UInt64)} {p q : UInt64}

theorem winv_const {top i w i'} (h : W X D p q top i w i') (t : tg X i = 1) : w = 1 ∧ i' = i + 2 := by
  cases h <;> first | exact ⟨rfl, rfl⟩ | simp_all
theorem winv_local {top i w i'} (h : W X D p q top i w i') (t : tg X i = 2) : w = tg X (i + 2) ∧ i' = i + 3 := by
  cases h <;> first | exact ⟨rfl, rfl⟩ | simp_all
theorem winv_bin {top i w i'} (h : W X D p q top i w i') (t : tg X i = 3) :
    ∃ i1, w = 1 ∧ W X D p q false (i + 2) 1 i1 ∧ W X D p q false i1 1 i' := by
  cases h <;> first | exact ⟨_, rfl, by assumption, by assumption⟩ | simp_all
theorem winv_ite {top i w i'} (h : W X D p q top i w i') (t : tg X i = 4) :
    ∃ i1 i2 i3, W X D p q false (i + 2) 1 i1 ∧ W X D p q false i1 1 i2 ∧ W X D p q false i2 w i3 ∧
      W X D p q false i3 w i' := by
  cases h <;> first | exact ⟨_, _, _, by assumption, by assumption, by assumption, by assumption⟩ | simp_all
theorem winv_lett {top i w i'} (h : W X D p q top i w i') (t : tg X i = 5) :
    ∃ i1, W X D p q false (i + 3) (tg X (i + 2)) i1 ∧ W X D p q false i1 w i' := by
  cases h <;> first | exact ⟨_, by assumption, by assumption⟩ | simp_all
theorem winv_pair {top i w i'} (h : W X D p q top i w i') (t : tg X i = 6) :
    ∃ ws, Ws X D p q (i + 2) ws i' ∧ ws.length = (tg X (i + 1)).toNat ∧ w = ws.foldl (· + ·) 0 := by
  cases h <;> first | exact ⟨_, by assumption, by assumption, rfl⟩ | simp_all
theorem winv_call {top i w i'} (h : W X D p q top i w i') (t : tg X i = 8) :
    ∃ ws, (tg X (i + 1)).toNat < D.length ∧ Ws X D p q (i + 3) ws i' ∧ ws.length = (tg X (i + 2)).toNat ∧
      ws.foldl (· + ·) 0 = (D.getD (tg X (i + 1)).toNat (0, 0)).1 ∧ w = (D.getD (tg X (i + 1)).toNat (0, 0)).2 := by
  cases h <;> first | exact ⟨_, by assumption, by assumption, by assumption, by assumption, rfl⟩ | simp_all
theorem winv_prim {top i w i'} (h : W X D p q top i w i') (t : tg X i = 9) :
    ∃ ws, Ws X D p q (i + 2) ws i' ∧ ws.length = (g33 (tg X (i + 1))).toNat ∧ (∀ c ∈ ws, c = 1) ∧ w = 1 := by
  cases h <;> first | exact ⟨_, by assumption, by assumption, by assumption, rfl⟩ | simp_all
theorem winv_loop {top i w i'} (h : W X D p q top i w i') (t : tg X i = 10) :
    ∃ i1, w = q ∧ W X D p q false (i + 1) q i1 ∧ W X D p q false i1 q i' := by
  cases h <;> first | exact ⟨_, rfl, by assumption, by assumption⟩ | simp_all
theorem winv_cont {top i w i'} (h : W X D p q top i w i') (t : tg X i = 11) :
    ∃ w0, W X D p q false (i + 1) w0 i' ∧ w0 + 1 = p := by
  cases h <;> first | exact ⟨_, by assumption, by assumption⟩ | simp_all
theorem wsinv_nil {i ws i'} (h : Ws X D p q i ws i') (hw : ws = []) : i' = i := by
  subst hw; cases h; rfl
theorem wsinv_cons {i c cs i'} (h : Ws X D p q i (c :: cs) i') :
    ∃ i1, W X D p q false i c i1 ∧ Ws X D p q i1 cs i' := by
  cases h; exact ⟨_, by assumption, by assumption⟩

end inv

/-! ## widths are small -/

mutual
theorem ser_pos : ∀ e : Nd, 1 ≤ e.ser.length
  | .const _ => by simp [Nd.ser]
  | .loc _ _ => by simp [Nd.ser]
  | .bin _ _ _ => by simp [Nd.ser]
  | .ite _ _ _ _ _ => by simp [Nd.ser]
  | .letE _ _ _ _ => by simp [Nd.ser]
  | .pair _ => by simp [Nd.ser]
  | .call _ _ => by simp [Nd.ser]
  | .prim _ _ => by simp [Nd.ser]
  | .loop _ _ => by simp [Nd.ser]
  | .cont _ => by simp [Nd.ser]
end

mutual
theorem wd_le (S : SC) (hr : ∀ n, S.nresOf n < 2 ^ 32) (hq : S.q < 2 ^ 32) :
    ∀ e : Nd, NB S.p e → wd S e ≤ 2 ^ 32 * e.ser.length
  | .const _, _ => by simp [wd, Nd.ser]
  | .loc _ w, nb => by simp only [NB] at nb; simp [wd, Nd.ser]; omega
  | .bin _ _ _, _ => by simp [wd, Nd.ser]; omega
  | .ite _ a b t e, nb => by
    simp only [NB] at nb; have := wd_le S hr hq t nb.2.2.2.1; simp [wd, Nd.ser]; omega
  | .letE _ _ v b, nb => by
    simp only [NB] at nb; have := wd_le S hr hq b nb.2.2.2; simp [wd, Nd.ser]; omega
  | .pair cs, nb => by
    simp only [NB] at nb; have := wdL_le S hr hq cs nb.2; simp [wd, Nd.ser]; omega
  | .call n _, _ => by have := hr n; simp [wd, Nd.ser]; omega
  | .prim _ _, _ => by simp [wd, Nd.ser]; omega
  | .loop _ _, _ => by simp [wd, Nd.ser]; omega
  | .cont _, _ => by simp [wd]
theorem wdL_le (S : SC) (hr : ∀ n, S.nresOf n < 2 ^ 32) (hq : S.q < 2 ^ 32) :
    ∀ cs : List Nd, NBL S.p cs → wdL S cs ≤ 2 ^ 32 * (serL cs).length
  | [], _ => by simp [wdL]
  | c :: cs, nb => by
    simp only [NBL] at nb
    have := wd_le S hr hq c nb.1; have := wdL_le S hr hq cs nb.2
    simp [wdL, serL]; omega
end

theorem ofNat_inj' {a b : Nat} (h : UInt64.ofNat a = UInt64.ofNat b) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a = b := by
  have := congrArg UInt64.toNat h; simp at this; omega

theorem ofNat_toNat' (x : UInt64) : UInt64.ofNat x.toNat = x := by simp

theorem g33_arity (pn : Nat) (h : pn < 2 ^ 32) : (g33 pn.toUInt64).toNat = arity pn := by
  unfold g33 arity
  by_cases h1 : pn = 1; · subst h1; rfl
  by_cases h5 : pn = 5; · subst h5; rfl
  by_cases h3 : pn = 3; · subst h3; rfl
  by_cases h2 : pn = 2; · subst h2; rfl
  by_cases h6 : pn = 6; · subst h6; rfl
  by_cases h8 : pn = 8; · subst h8; rfl
  have ne : ∀ k : Nat, k < 2 ^ 32 → pn ≠ k → (pn.toUInt64 == k.toUInt64) = false := by
    intro k hk hne; simp [Nat.toUInt64]; intro e; have := congrArg UInt64.toNat e; simp at this; omega
  simp only [show (pn.toUInt64 == 1) = false from ne 1 (by omega) h1, show (pn.toUInt64 == 5) = false from ne 5 (by omega) h5,
    show (pn.toUInt64 == 3) = false from ne 3 (by omega) h3, show (pn.toUInt64 == 2) = false from ne 2 (by omega) h2,
    show (pn.toUInt64 == 6) = false from ne 6 (by omega) h6, show (pn.toUInt64 == 8) = false from ne 8 (by omega) h8]
  simp [h1, h5, h3, h2, h6, h8]

theorem NBL_mem {p : Nat} : ∀ {cs : List Nd} {c : Nd}, NBL p cs → c ∈ cs → NB p c
  | [], _, _, hc => by simp at hc
  | x :: xs, c, h, hc => by
    simp only [NBL] at h
    rcases List.mem_cons.mp hc with e | e
    · subst e; exact h.1
    · exact NBL_mem h.2 e

theorem serL_mem_le : ∀ {cs : List Nd} {c : Nd}, c ∈ cs → c.ser.length ≤ (serL cs).length
  | [], _, hc => by simp at hc
  | x :: xs, c, hc => by
    simp only [serL, List.length_append]
    rcases List.mem_cons.mp hc with e | e
    · subst e; omega
    · have := serL_mem_le e; omega

theorem wdL_ones (S : SC) : ∀ cs : List Nd, (∀ c ∈ cs, wd S c = 1) → wdL S cs = cs.length
  | [], _ => by simp [wdL]
  | c :: cs, h => by
    simp only [wdL, List.length_cons]; rw [h c (by simp), wdL_ones S cs (fun c' hc => h c' (by simp [hc]))]; omega

theorem foldl_wd (S : SC) : ∀ (cs : List Nd) (a : UInt64),
    (cs.map (fun c => UInt64.ofNat (wd S c))).foldl (· + ·) a = a + UInt64.ofNat (wdL S cs)
  | [], a => by simp [wdL]
  | c :: cs, a => by
    simp only [List.map_cons, List.foldl_cons, wdL]
    rw [foldl_wd S cs]; simp [UInt64.ofNat_add, UInt64.add_assoc]

/-- the width-pass context agrees with the template context -/
structure WK (S : SC) (D : List (UInt64 × UInt64)) (p q : UInt64) : Prop where
  ep : S.p = p.toNat
  eq : S.q = q.toNat
  q251 : q.toNat < 251
  p251 : p.toNat < 251
  npw : ∀ n, n < D.length → S.npwOf n = (D.getD n (0, 0)).1.toNat
  nres : ∀ n, n < D.length → S.nresOf n = (D.getD n (0, 0)).2.toNat
  r32 : ∀ n, S.nresOf n < 2 ^ 32

section br
variable {S : SC} {X : Buf} {D : List (UInt64 × UInt64)} {p q : UInt64}

theorem wd_lt (hK : WK S D p q) (e : Nd) (nb : NB S.p e) (hl : e.ser.length < 2 ^ 31) : wd S e < 2 ^ 63 := by
  have := wd_le S hK.r32 (by rw [hK.eq]; have := hK.q251; omega) e nb; omega

theorem wdL_lt (hK : WK S D p q) (cs : List Nd) (nb : NBL S.p cs) (hl : (serL cs).length < 2 ^ 31) :
    wdL S cs < 2 ^ 63 := by
  have := wdL_le S hK.r32 (by rw [hK.eq]; have := hK.q251; omega) cs nb; omega

set_option maxHeartbeats 1000000 in
mutual
theorem wV (hK : WK S D p q) : ∀ (e : Nd) (top : Bool) (i : Nat) (w : UInt64) (i' : Nat), NB S.p e → ScV S e →
    SerAt X i e.ser → W X D p q top i w i' → e.ser.length < 2 ^ 31 →
    i' = i + e.ser.length ∧ WdV S e ∧ UInt64.ofNat (wd S e) = w
  | .const v, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [Nd.ser] at sa
    obtain ⟨rfl, rfl⟩ := winv_const hw sa.cons.1
    simp [WdV, wd, Nd.ser]
  | .loc s w0, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [Nd.ser] at sa
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨_, sa2⟩ := sa1.cons; obtain ⟨t2, -⟩ := sa2.cons
    obtain ⟨rfl, rfl⟩ := winv_local hw t0
    rw [t2]; simp [WdV, wd, Nat.toUInt64, Nd.ser]
  | .bin op a b, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [Nd.ser] at sa hl
    simp only [NB] at nb; simp only [ScV] at sc
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨_, sa2⟩ := sa1.cons; obtain ⟨saA, saB⟩ := sa2.app
    obtain ⟨i1, rfl, hA, hB⟩ := winv_bin hw t0
    simp only [List.length_cons, List.length_append] at hl
    obtain ⟨e1, wa, ea⟩ := wV hK a false (i + 2) 1 i1 nb.2.1 sc.1 (by simpa using saA) hA (by omega)
    subst e1
    obtain ⟨e2, wb, eb⟩ := wV hK b false _ 1 i' nb.2.2 sc.2.1 (by simpa [Nat.add_assoc] using saB) hB (by omega)
    have la := wd_lt hK a nb.2.1 (by omega); have lb := wd_lt hK b nb.2.2 (by omega)
    refine ⟨by rw [e2]; simp [Nd.ser]; omega, ?_, by simp [wd]⟩
    simp only [WdV]
    exact ⟨wa, wb, ofNat_inj' (by simpa using ea) (by omega) (by omega),
      ofNat_inj' (by simpa using eb) (by omega) (by omega)⟩
  | .ite cm a b t e, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [Nd.ser] at sa hl
    simp only [NB] at nb; simp only [ScV] at sc
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨_, sa2⟩ := sa1.cons
    obtain ⟨sa3, saE⟩ := sa2.app; obtain ⟨sa4, saT⟩ := sa3.app; obtain ⟨saA, saB⟩ := sa4.app
    obtain ⟨i1, i2, i3, hA, hB, hT, hE⟩ := winv_ite hw t0
    simp only [List.length_cons, List.length_append] at hl
    obtain ⟨e1, wa, ea⟩ := wV hK a false (i + 2) 1 i1 nb.2.1 sc.1 (by simpa using saA) hA (by omega)
    subst e1
    obtain ⟨e2, wb, eb⟩ := wV hK b false _ 1 i2 nb.2.2.1 sc.2.1 (by simpa [Nat.add_assoc] using saB) hB (by omega)
    subst e2
    obtain ⟨e3, wt, et⟩ := wV hK t false _ w i3 nb.2.2.2.1 sc.2.2.1 (by simpa [Nat.add_assoc] using saT) hT (by omega)
    subst e3
    obtain ⟨e4, we, ee⟩ := wV hK e false _ w i' nb.2.2.2.2 sc.2.2.2.1 (by simpa [Nat.add_assoc] using saE) hE (by omega)
    have la := wd_lt hK a nb.2.1 (by omega); have lb := wd_lt hK b nb.2.2.1 (by omega)
    have lt := wd_lt hK t nb.2.2.2.1 (by omega); have le := wd_lt hK e nb.2.2.2.2 (by omega)
    refine ⟨by rw [e4]; simp [Nd.ser]; omega, ?_, by simpa [wd] using et⟩
    simp only [WdV]
    exact ⟨wa, wb, wt, we, ofNat_inj' (by simpa using ea) (by omega) (by omega),
      ofNat_inj' (by simpa using eb) (by omega) (by omega), ofNat_inj' (by rw [ee, et]) (by omega) (by omega)⟩
  | .letE s w0 v b, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [Nd.ser] at sa hl
    simp only [NB] at nb; simp only [ScV] at sc
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨_, sa2⟩ := sa1.cons; obtain ⟨t2, sa3⟩ := sa2.cons
    obtain ⟨saV, saB⟩ := sa3.app
    obtain ⟨i1, hV, hB⟩ := winv_lett hw t0
    rw [t2] at hV
    simp only [List.length_cons, List.length_append] at hl
    obtain ⟨e1, wv, ev⟩ := wV hK v false (i + 3) _ i1 nb.2.2.1 sc.1 (by simpa using saV) hV (by omega)
    subst e1
    obtain ⟨e2, wb, eb⟩ := wV hK b false _ w i' nb.2.2.2 sc.2.1 (by simpa [Nat.add_assoc] using saB) hB (by omega)
    have lv := wd_lt hK v nb.2.2.1 (by omega)
    refine ⟨by rw [e2]; simp [Nd.ser]; omega, ?_, by simpa [wd] using eb⟩
    simp only [WdV]
    exact ⟨wv, wb, ofNat_inj' (by simpa [Nat.toUInt64] using ev) (by omega) (by omega)⟩
  | .pair cs, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [Nd.ser] at sa hl
    simp only [NB] at nb; simp only [ScV] at sc
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨t1, sa2⟩ := sa1.cons
    obtain ⟨ws, hws, hlen, rfl⟩ := winv_pair hw t0
    rw [t1, toU_lt _ nb.1] at hlen
    simp only [List.length_cons] at hl
    obtain ⟨e1, wl, el⟩ := wL hK cs (i + 1 + 1) ws i' nb.2 sc sa2 hws hlen (by omega)
    refine ⟨by rw [e1]; simp [Nd.ser]; omega, by simpa [WdV] using wl, ?_⟩
    rw [el, foldl_wd]; simp [wd]
  | .call n as, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [Nd.ser] at sa hl
    simp only [NB] at nb; simp only [ScV] at sc
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨t1, sa2⟩ := sa1.cons; obtain ⟨t2, sa3⟩ := sa2.cons
    obtain ⟨ws, hnD, hws, hlen, hsum, rfl⟩ := winv_call hw t0
    rw [t1, toU_lt _ nb.1] at hnD hsum ⊢
    rw [t2, toU_lt _ nb.2.1] at hlen
    simp only [List.length_cons] at hl
    obtain ⟨e1, wl, el⟩ := wL hK as (i + 1 + 1 + 1) ws i' nb.2.2 sc.1 sa3 hws hlen (by omega)
    have ll := wdL_lt hK as nb.2.2 (by omega)
    refine ⟨by rw [e1]; simp [Nd.ser]; omega, ?_, ?_⟩
    · simp only [WdV]
      refine ⟨wl, ?_⟩
      rw [hK.npw n hnD, ← hsum, el, foldl_wd]; simp; omega
    · simp only [wd]; rw [hK.nres n hnD]; simp
  | .prim pn as, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [Nd.ser] at sa hl
    simp only [NB] at nb; simp only [ScV] at sc
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨t1, sa2⟩ := sa1.cons
    obtain ⟨ws, hws, hlen, h1, rfl⟩ := winv_prim hw t0
    rw [t1, ← nb.2.1] at hlen
    simp only [List.length_cons] at hl
    obtain ⟨e1, wl, el⟩ := wL hK as (i + 1 + 1) ws i' nb.2.2 sc sa2 hws hlen (by omega)
    have ones : ∀ c ∈ as, wd S c = 1 := by
      intro c hc
      have hm : UInt64.ofNat (wd S c) ∈ ws := by rw [el]; exact List.mem_map_of_mem hc
      have := h1 _ hm
      have lc := wd_lt hK c (NBL_mem nb.2.2 hc) (by have := serL_mem_le hc; omega)
      exact ofNat_inj' (by simpa using this) (by omega) (by omega)
    refine ⟨by rw [e1]; simp [Nd.ser]; omega, ?_, by simp [wd]⟩
    simp only [WdV]
    have ga := g33_arity pn nb.1
    refine ⟨wl, by rw [wdL_ones S as ones, nb.2.1, ga], fun hp => ?_⟩
    have : as.length = 0 := by rw [nb.2.1, ga]; unfold arity; simp [hp]
    exact List.eq_nil_of_length_eq_zero this
  | .loop z s', top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [Nd.ser] at sa hl
    simp only [NB] at nb; simp only [ScV] at sc
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨saZ, saS⟩ := sa1.app
    obtain ⟨i1, ew, hZ, hS⟩ := winv_loop hw t0
    rw [ew]
    simp only [List.length_cons, List.length_append] at hl
    obtain ⟨e1, wz⟩ := wTx hK z false (i + 1) q i1 nb.1 sc.1 saZ hZ (by omega)
    subst e1
    obtain ⟨e2, ws⟩ := wTx hK s' false _ q i' nb.2 sc.2.1 (by simpa [Nat.add_assoc] using saS) hS (by omega)
    refine ⟨by rw [e2]; simp [Nd.ser]; omega, ?_, by simp [wd, hK.eq]⟩
    simp only [WdV]; rw [hK.eq]; exact ⟨wz, ws⟩
  | .cont e, top, i, w, i', nb, sc, sa, hw, hl => by simp [ScV] at sc
termination_by e => 3 * sizeOf e
theorem wTx (hK : WK S D p q) : ∀ (e : Nd) (top : Bool) (i : Nat) (w : UInt64) (i' : Nat), NB S.p e → ScT S e →
    SerAt X i e.ser → W X D p q top i w i' → e.ser.length < 2 ^ 31 → i' = i + e.ser.length ∧ WdT S e w.toNat
  | .ite cm a b t e, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [Nd.ser] at sa hl
    simp only [NB] at nb; simp only [ScT] at sc
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨_, sa2⟩ := sa1.cons
    obtain ⟨sa3, saE⟩ := sa2.app; obtain ⟨sa4, saT⟩ := sa3.app; obtain ⟨saA, saB⟩ := sa4.app
    obtain ⟨i1, i2, i3, hA, hB, hT, hE⟩ := winv_ite hw t0
    simp only [List.length_cons, List.length_append] at hl
    obtain ⟨e1, wa, ea⟩ := wV hK a false (i + 2) 1 i1 nb.2.1 sc.1 (by simpa using saA) hA (by omega)
    subst e1
    obtain ⟨e2, wb, eb⟩ := wV hK b false _ 1 i2 nb.2.2.1 sc.2.1 (by simpa [Nat.add_assoc] using saB) hB (by omega)
    subst e2
    obtain ⟨e3, wt⟩ := wTx hK t false _ w i3 nb.2.2.2.1 sc.2.2.1 (by simpa [Nat.add_assoc] using saT) hT (by omega)
    subst e3
    obtain ⟨e4, we⟩ := wTx hK e false _ w i' nb.2.2.2.2 sc.2.2.2.1 (by simpa [Nat.add_assoc] using saE) hE (by omega)
    have la := wd_lt hK a nb.2.1 (by omega); have lb := wd_lt hK b nb.2.2.1 (by omega)
    refine ⟨by rw [e4]; simp [Nd.ser]; omega, ?_⟩
    simp only [WdT]
    exact ⟨wa, wb, wt, we, ofNat_inj' (by simpa using ea) (by omega) (by omega),
      ofNat_inj' (by simpa using eb) (by omega) (by omega)⟩
  | .letE s w0 v b, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [Nd.ser] at sa hl
    simp only [NB] at nb; simp only [ScT] at sc
    obtain ⟨t0, sa1⟩ := sa.cons; obtain ⟨_, sa2⟩ := sa1.cons; obtain ⟨t2, sa3⟩ := sa2.cons
    obtain ⟨saV, saB⟩ := sa3.app
    obtain ⟨i1, hV, hB⟩ := winv_lett hw t0
    rw [t2] at hV
    simp only [List.length_cons, List.length_append] at hl
    obtain ⟨e1, wv, ev⟩ := wV hK v false (i + 3) _ i1 nb.2.2.1 sc.1 (by simpa using saV) hV (by omega)
    subst e1
    obtain ⟨e2, wb⟩ := wTx hK b false _ w i' nb.2.2.2 sc.2.1 (by simpa [Nat.add_assoc] using saB) hB (by omega)
    have lv := wd_lt hK v nb.2.2.1 (by omega)
    refine ⟨by rw [e2]; simp [Nd.ser]; omega, ?_⟩
    simp only [WdT]
    exact ⟨wv, wb, ofNat_inj' (by simpa [Nat.toUInt64] using ev) (by omega) (by omega)⟩
  | .cont e, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [Nd.ser] at sa hl
    simp only [NB] at nb; simp only [ScT] at sc
    obtain ⟨t0, saE⟩ := sa.cons
    obtain ⟨w0, hE, hp⟩ := winv_cont hw t0
    obtain ⟨e1, we, ee⟩ := wV hK e false (i + 1) w0 i' nb.2 sc.1 saE hE (by simp at hl; omega)
    have le := wd_lt hK e nb.2 (by simp at hl; omega)
    refine ⟨by rw [e1]; simp [Nd.ser]; omega, ?_⟩
    simp only [WdT]
    refine ⟨we, ?_⟩
    have h1 : (wd S e) = w0.toNat := by rw [← ee]; simp; omega
    have h2 := congrArg UInt64.toNat hp
    rw [UInt64.toNat_add] at h2
    have := hK.p251; rw [hK.ep]; simp at h2; omega
  | .const v, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [ScT] at sc
    obtain ⟨e1, we, ee⟩ := wV hK _ top i w i' nb sc sa hw hl
    have := wd_lt hK _ nb hl
    exact ⟨e1, by simp only [WdT]; exact ⟨we, by rw [← ee]; simp; omega⟩⟩
  | .loc a b, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [ScT] at sc
    obtain ⟨e1, we, ee⟩ := wV hK _ top i w i' nb sc sa hw hl
    have := wd_lt hK _ nb hl
    exact ⟨e1, by simp only [WdT]; exact ⟨we, by rw [← ee]; simp; omega⟩⟩
  | .bin o a b, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [ScT] at sc
    obtain ⟨e1, we, ee⟩ := wV hK _ top i w i' nb sc sa hw hl
    have := wd_lt hK _ nb hl
    exact ⟨e1, by simp only [WdT]; exact ⟨we, by rw [← ee]; simp; omega⟩⟩
  | .pair cs, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [ScT] at sc
    obtain ⟨e1, we, ee⟩ := wV hK _ top i w i' nb sc sa hw hl
    have := wd_lt hK _ nb hl
    exact ⟨e1, by simp only [WdT]; exact ⟨we, by rw [← ee]; simp; omega⟩⟩
  | .call n as, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [ScT] at sc
    obtain ⟨e1, we, ee⟩ := wV hK _ top i w i' nb sc sa hw hl
    have := wd_lt hK _ nb hl
    exact ⟨e1, by simp only [WdT]; exact ⟨we, by rw [← ee]; simp; omega⟩⟩
  | .prim pn as, top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [ScT] at sc
    obtain ⟨e1, we, ee⟩ := wV hK _ top i w i' nb sc sa hw hl
    have := wd_lt hK _ nb hl
    exact ⟨e1, by simp only [WdT]; exact ⟨we, by rw [← ee]; simp; omega⟩⟩
  | .loop z s', top, i, w, i', nb, sc, sa, hw, hl => by
    simp only [ScT] at sc
    obtain ⟨e1, we, ee⟩ := wV hK _ top i w i' nb sc sa hw hl
    have := wd_lt hK _ nb hl
    exact ⟨e1, by simp only [WdT]; exact ⟨we, by rw [← ee]; simp; omega⟩⟩
termination_by e => 3 * sizeOf e + 2
theorem wL (hK : WK S D p q) : ∀ (cs : List Nd) (i : Nat) (ws : List UInt64) (i' : Nat), NBL S.p cs → ScL S cs →
    SerAt X i (serL cs) → Ws X D p q i ws i' → ws.length = cs.length → (serL cs).length < 2 ^ 31 →
    i' = i + (serL cs).length ∧ WdL S cs ∧ ws = cs.map (fun c => UInt64.ofNat (wd S c))
  | [], i, ws, i', _, _, _, hw, hl, _ => by
    have : ws = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst this
    exact ⟨by rw [wsinv_nil hw rfl]; simp [serL], by simp [WdL], rfl⟩
  | c :: cs, i, ws, i', nb, sc, sa, hw, hl, hsl => by
    rcases ws with _ | ⟨w1, ws⟩
    · simp at hl
    simp only [NBL] at nb; simp only [ScL] at sc
    simp only [serL] at sa hsl
    obtain ⟨sa1, sa2⟩ := sa.app
    obtain ⟨i1, h1, h2⟩ := wsinv_cons hw
    simp only [List.length_append] at hsl
    obtain ⟨e1, wc, ec⟩ := wV hK c false i w1 i1 nb.1 sc.1 sa1 h1 (by omega)
    subst e1
    obtain ⟨e2, wl, el⟩ := wL hK cs _ ws i' nb.2 sc.2.1 sa2 h2 (by simpa using hl) (by omega)
    refine ⟨by rw [e2]; simp [serL]; omega, by simp only [WdL]; exact ⟨wc, wl⟩, by rw [el, ← ec]; rfl⟩
termination_by cs => 3 * sizeOf cs
end

end br

end Templates
