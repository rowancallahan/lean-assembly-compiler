/- Nano/Parser/NumSound: **the numeral check is sound**: `C.u10` (Nano/Parser/NumC.lean) accepts a serialized program
only if `NumSpec.numOkP` holds, and then returns its input. -/
import Nano.Parser.NumP27
namespace NumP
open C ParSpec OwnP
open Templates (NB NBL)

/-- the def table: kind and result width per def -/
def tbl (q : List DefA) : Buf := q.flatMap fun df => [u df.kind, u df.nres]

theorem tbl_len (q : List DefA) : (tbl q).length = 2 * q.length := by
  induction q with
  | nil => rfl
  | cons df q ih => simp [tbl] at ih ⊢; omega

theorem tbl_get : ∀ (q : List DefA) (i : Nat), i < q.length →
    (tbl q).getD (2 * i) 0 = u ((q.map (·.kind)).getD i 0) ∧ (tbl q).getD (2 * i + 1) 0 = u ((q.map (·.nres)).getD i 1)
  | [], _, h => by simp at h
  | df :: q, 0, _ => by simp [tbl]
  | df :: q, i + 1, h => by
    have := tbl_get q i (by simp at h; omega)
    simp only [tbl, List.flatMap_cons] at this ⊢
    refine ⟨?_, ?_⟩
    · rw [show 2 * (i + 1) = [u df.kind, u df.nres].length + 2 * i by simp; omega, getD_app_right, this.1]; simp
    · rw [show 2 * (i + 1) + 1 = [u df.kind, u df.nres].length + (2 * i + 1) by simp; omega, getD_app_right, this.2]
      simp

theorem ser_def_len (df : DefA) : df.ser.length = df.body.ser.length + 7 := by simp [DefA.ser]

theorem drop_defs {x : Buf} {i : Nat} {df : DefA} {q : List DefA} (hx : x.drop i = (df :: q).flatMap DefA.ser) :
    x.drop i = df.ser ++ q.flatMap DefA.ser ∧ x.drop (i + df.ser.length) = q.flatMap DefA.ser := by
  have h1 : x.drop i = df.ser ++ q.flatMap DefA.ser := by rw [hx]; simp
  exact ⟨h1, by rw [← List.drop_drop, h1]; simp⟩

/-- `u60`: the def table -/
theorem u60_ok {x : Buf} (hxl : x.length < 2 ^ 23) : ∀ (n : Nat) (q : List DefA) (D : Buf) (i : Nat),
    x.drop i = q.flatMap DefA.ser → (∀ df ∈ q, Templates.DB df) → 0 < i → i ≤ x.length →
    (u60 n x D (u i)).2 = 1 → (u60 n x D (u i)).1 = D ++ tbl q
  | 0, _, _, _, _, _, _, _, h => by simp [u60] at h
  | n + 1, [], D, i, hx, _, _, hil, _ => by
    have hi : x.length ≤ i := by
      have := congrArg List.length hx; simp at this; omega
    rw [u60, if_neg (by rw [bsize_u, ult (by omega) (by omega)]; omega)]; simp [tbl]
  | n + 1, df :: q, D, i, hx, hdb, hi, hil, h => by
    obtain ⟨hx1, hx2⟩ := drop_defs hx
    have hcl := drop_len hx1 (by simp [DefA.ser])
    obtain ⟨-, -, -, hk, hr, hnb⟩ := hdb df (by simp)
    have hlt : u i < bsize x := by rw [bsize_u, ult (by omega) (by omega)]; simp [DefA.ser] at hcl; omega
    have r0 : bget x (u i) = 20 := by
      rw [show u i = u (i + 0) from rfl, rd hx1 (k := 0) (by simp [DefA.ser]) (by omega)]; simp [DefA.ser]
    have r4 : bget x (u i + 4) = u df.kind := by
      rw [show (4 : UInt64) = u 4 from rfl, uadd, rd hx1 (k := 4) (by simp [DefA.ser]) (by omega)]; simp [DefA.ser, toU]
    have r5 : bget x (u i + 5) = u df.nres := by
      rw [show (5 : UInt64) = u 5 from rfl, uadd, rd hx1 (k := 5) (by simp [DefA.ser]) (by omega)]; simp [DefA.ser, toU]
    have hx6 : x.drop (i + 6) = df.body.ser ++ ([21] ++ q.flatMap DefA.ser) := by
      have h0 : x.drop i = [20, u df.id, u df.npw, u df.nslots, u df.kind, u df.nres] ++
          (df.body.ser ++ ([21] ++ q.flatMap DefA.ser)) := by rw [hx1]; simp [DefA.ser, toU]
      simpa using drop_shift h0
    have e6 : u i + 6 = u (i + 6) := by rw [show (6 : UInt64) = u 6 from rfl, uadd]
    rw [u60] at h ⊢
    zeta_at at h ⊢
    rw [if_pos hlt, r0, if_pos (keq (show ((20 : UInt64) == 20) = true from rfl)), e6] at h ⊢
    rcases u15_ok (by omega) hx6 hnb with h15 | ⟨h15, -⟩
    · rw [h15, if_pos (keq (show ((0 : UInt64) == 0) = true from rfl))] at h
      exact absurd h (show (0 : UInt64) ≠ 1 by decide)
    have hne : (u (i + 6 + df.body.ser.length) == 0) = false := by
      rw [u0, ueq (by simp [DefA.ser] at hcl; omega) (by omega)]; exact decide_eq_false (by omega)
    have r21 : bget x (u (i + 6 + df.body.ser.length)) = 21 := by
      have := drop_shift hx6
      rw [show i + 6 + df.body.ser.length = i + 6 + df.body.ser.length + 0 from rfl,
        rd this (k := 0) (by simp) (by simp [DefA.ser] at hcl; omega)]; rfl
    rw [h15, if_neg (kne hne), r21, if_pos (keq (show ((21 : UInt64) == 21) = true from rfl)), r4, r5] at h ⊢
    have e1 : u (i + 6 + df.body.ser.length) + 1 = u (i + df.ser.length) := by rw [u1, uadd, ser_def_len]; congr 1; omega
    rw [e1] at h ⊢
    rw [u60_ok hxl n q _ _ hx2 (fun d hd => hdb d (by simp [hd])) (by omega) hcl h]
    simp [tbl, bpush]

/-- the table is the program's kinds and widths -/
theorem lk_tbl {x : Buf} (hxl : x.length < 2 ^ 23) (p : List DefA) (hp : p.length < 2 ^ 23)
    (hdb : ∀ df ∈ p, Templates.DB df) : LK x (tbl p) (p.map (·.kind)) (p.map (·.nres)) := by
  refine ⟨⟨hxl, by rw [tbl_len]; simp, by simp; omega, fun i hi => ?_, fun i hi => ?_⟩, by simp, fun i hi => ?_, fun i hi => ?_⟩
  · simp at hi; exact (tbl_get p i hi).2
  · simp at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
    simpa using (hdb p[i] (List.getElem_mem hi)).2.2.2.2.1
  · simp at hi; exact (tbl_get p i hi).1
  · simp at hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
    simpa using (hdb p[i] (List.getElem_mem hi)).2.2.2.1

/-- `u61`: every def passes -/
theorem u61_ok {x d : Buf} {ks ws : List Nat} (hK : LK x d ks ws) : ∀ (n : Nat) (q : List DefA) (i : Nat)
    (b t g s y y1 y2 : Buf) (A : List NumSpec.G),
    x.drop i = q.flatMap DefA.ser → (∀ df ∈ q, Templates.DB df) → 0 < i → BI b t g s y y1 y2 → g = encG A →
    u61 n x d (u i) b t g s y y1 y2 = 1 → ∀ df ∈ q, NumSpec.numOkD ks ws df = true
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [u61] at h
  | n + 1, [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp
  | n + 1, df :: q, i, b, t, g, s, y, y1, y2, A, hx, hdb, hi, hB, hgA, h => by
    obtain ⟨hx1, hx2⟩ := drop_defs hx
    have hxl := hK.lc.xl
    have hcl := drop_len hx1 (by simp [DefA.ser])
    have hlt : u i < bsize x := by rw [bsize_u, ult (by omega) (by omega)]; simp [DefA.ser] at hcl; omega
    rw [u61, if_pos hlt] at h
    obtain ⟨-, -, hns, -, -, hnbd⟩ := hdb df (by simp)
    have hx3 : bget x (u i + 3) = u df.nslots := by
      rw [u3, uadd, rd hx1 (k := 3) (by simp [DefA.ser]) (by omega)]; simp [DefA.ser, toU]
    have hx6 : x.drop (i + 6) = df.body.ser ++ ([21] ++ q.flatMap DefA.ser) := by
      have h0 : x.drop i = [20, u df.id, u df.npw, u df.nslots, u df.kind, u df.nres] ++
          (df.body.ser ++ ([21] ++ q.flatMap DefA.ser)) := by rw [hx1]; simp [DefA.ser, toU]
      simpa using drop_shift h0
    have e6 : u i + 6 = u (i + 6) := by rw [show (6 : UInt64) = u 6 from rfl, uadd]
    generalize hR : u80 x d (u i) b t g s y y1 y2 = R at h
    obtain ⟨k, i1, b1', t1', g1', s1', y3', y4', y5'⟩ := R
    iota_only at h
    by_cases hk : k = 1
    rotate_left
    · rw [if_neg (by simpa using hk)] at h; exact absurd h (by decide)
    subst hk
    rw [if_pos (keq rfl)] at h
    unfold u80 at hR
    generalize h79 : u79 x y1 y2 (u i) = R at hR
    obtain ⟨fa, wa, ka⟩ := R
    iota_only at hR
    by_cases hka : ka = 1
    rotate_left
    · rw [if_neg (by simpa using hka)] at hR; simp only [Prod.mk.injEq] at hR; exact absurd hR.1 (by decide)
    subst hka
    rw [if_pos (keq rfl)] at hR
    unfold u79 at h79
    rw [hx3, e6] at h79
    have z0 := u57_ok 16777216 y2 0 df.nslots (by omega) (by omega) hB.sc.2.2 (by omega) (by intro i hi; omega)
    rw [show u 0 = (0 : UInt64) from rfl] at z0
    generalize u57 16777216 y2 0 (u df.nslots) = Z at h79 z0
    obtain ⟨f0, k0⟩ := Z
    iota_only at h79
    dsimp only at z0
    by_cases hk0 : k0 = 1
    rotate_left
    · rw [if_neg (by simpa using hk0)] at h79; simp only [Prod.mk.injEq] at h79; exact absurd h79.2.2 (by decide)
    subst hk0
    rw [if_pos (keq rfl)] at h79
    obtain ⟨-, hf0, -⟩ := z0 rfl
    have hf0' : f0.length < 2 ^ 62 := by have := hB.sc.2.2; omega
    have hbody : df.body.ser.length ≤ 2 ^ 24 := by simp [DefA.ser] at hcl; omega
    have hlate := late_ok (np := df.npw) hxl hx6 hnbd hbody (by omega) hB.sc.2.1 hf0'
    have hm73 := u73_ok (np := df.npw) hxl (2 ^ 24) 16777216 [df.body] ([21] ++ q.flatMap DefA.ser) (i + 6) f0 y1
      (by simpa [serL] using hx6) (by simpa using ⟨hnbd, hbody⟩) (by omega) hB.sc.2.1 hf0'
    have hmono := u73_mono (x := x) 16777216 f0 y1 (u (i + 6)) 1
    rw [show u [df.body].length = (1 : UInt64) from rfl] at hm73
    generalize u73 16777216 x f0 y1 (u (i + 6)) 1 = M at h79 hlate hm73 hmono
    obtain ⟨f1, w1, k1⟩ := M
    iota_only at h79
    dsimp only at hlate hm73 hmono
    by_cases hk1 : k1 = 1
    rotate_left
    · rw [if_neg (by simpa using hk1)] at h79; simp only [Prod.mk.injEq] at h79; exact absurd h79.2.2 (by decide)
    subst hk1
    rw [if_pos (keq rfl)] at h79
    dsimp (config := {iota := false, proj := false, etaStruct := .none, beta := false, eta := false}) only at h79
    simp only [Prod.mk.injEq] at h79
    obtain ⟨ea, eb, h74⟩ := h79
    subst ea eb
    have hm1 := (hm73 rfl).2
    try simp only at hm1
    have hL := hlate rfl h74
    have hB' : BI b t g s y w1 f1 := ⟨hB.lb, hB.lt, hB.lg, hB.ls, ⟨hB.sc.1, hm1, by rw [hmono.1]; exact hf0'⟩⟩
    have hd := def_ok hK (hdb df (by simp)) hx1 hi hB' hgA
    rw [hx3, e6] at hd hR
    generalize u48 x d (u (i + 6)) (u df.nslots) b t g s y w1 f1 = W at hR hd
    obtain ⟨e, g1, b1, t1, s1, y5, ok, f2, h2⟩ := W
    iota_only at hR
    simp only [Prod.mk.injEq] at hR
    obtain ⟨hk', ei, eb1, et1, eg1, es1, ey3, ey4, ey5⟩ := hR
    subst ei eb1 et1 eg1 es1 ey3 ey4 ey5
    by_cases hok : ok = 1
    · subst hok
      obtain ⟨he, hnum, A', hg1, hB1⟩ := hd rfl
      simp only at he hg1 hB1
      subst he
      rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))] at hk'
      by_cases h21 : (bget x (u (i + 6 + df.body.ser.length)) == 21) = true
      · have e1 : u (i + 6 + df.body.ser.length) + 1 = u (i + df.ser.length) := by
          rw [u1, uadd, ser_def_len]; congr 1; omega
        rw [e1] at h
        have ih := u61_ok hK n q _ b1 t1 g1 s1 f2 h2 y5 A' hx2 (fun d hd => hdb d (by simp [hd])) (by omega) hB1 hg1 h
        intro df' hdf'
        simp at hdf'; rcases hdf' with rfl | hdf'
        · rw [numOkD_eq]; rw [numC] at hnum
          simp only [Bool.and_eq_true] at hnum ⊢
          exact ⟨⟨hnum.1, hL⟩, hnum.2⟩
        · exact ih df' hdf'
      · rw [if_neg h21] at hk'; exact absurd hk' (by decide)
    · rw [if_neg (by simpa using hok)] at hk'; exact absurd hk' (by decide)

theorem len_le_ser : ∀ p : List DefA, p.length ≤ (p.flatMap DefA.ser).length
  | [] => by simp
  | df :: p => by have := len_le_ser p; simp [DefA.ser] at this ⊢; omega

theorem u11_ok (p : List DefA) (hdb : ∀ d ∈ p, Templates.DB d) (hlen : (serialize p).length < 2 ^ 64) :
    u11 (serialize p) = 1 → NumSpec.numOkP p = true := by
  unfold u11
  rw [if_pos (by show (bget (2 :: p.flatMap DefA.ser) 0 == 2) = true; rfl)]
  by_cases hs : bsize (serialize p) < 8388608
  rotate_left
  · rw [if_neg hs]; intro h; exact absurd h (by decide)
  rw [if_pos hs]
  have hxl : (serialize p).length < 2 ^ 23 := by
    rw [bsize_u, show (8388608 : UInt64) = u (2 ^ 23) from rfl, ult hlen (by omega)] at hs; exact hs
  have hx1 : (serialize p).drop 1 = p.flatMap DefA.ser := by simp [serialize]
  have h60 := u60_ok hxl 16777216 p bnew 1 hx1 hdb (by omega) (by simp [serialize])
  rw [u1e] at h60
  generalize u60 16777216 (serialize p) bnew 1 = V at h60 ⊢
  obtain ⟨d, ok⟩ := V
  iota_only
  by_cases hok : ok = 1
  rotate_left
  · rw [if_neg (by simpa using hok)]; intro h; exact absurd h (by decide)
  subst hok
  rw [if_pos (keq (show ((1 : UInt64) == 1) = true from rfl))]
  have hd := h60 rfl; simp [bnew] at hd
  subst hd
  intro h
  have hpl : p.length < 2 ^ 23 := by
    have := len_le_ser p
    have e : (serialize p).length = (p.flatMap DefA.ser).length + 1 := rfl
    omega
  have hK := lk_tbl hxl p hpl hdb
  have := u61_ok hK 16777216 p 1 bnew bnew bnew bnew bnew bnew bnew [] hx1 hdb (by omega)
    ⟨by simp [bnew], by simp [bnew], by simp [bnew], by simp [bnew], by simp [bnew], by simp [bnew], by simp [bnew]⟩
    (by simp [encG, bnew]) (by rw [u1e]; exact h)
  unfold NumSpec.numOkP
  simp only [List.all_eq_true]
  exact this

/-- **the numeral check is sound**: if `C.u10` accepts the serialized program, every def's numerals mean what Lean's
mean (`NumSpec.numOkP`), and `C.u10` returns its input unchanged -/
theorem u10_sound (p : List ParSpec.DefA) (hdb : ∀ d ∈ p, Templates.DB d) (hlen : (ParSpec.serialize p).length < 2 ^ 64)
    (h : C.u10 (ParSpec.serialize p) ≠ []) :
    NumSpec.numOkP p = true ∧ C.u10 (ParSpec.serialize p) = ParSpec.serialize p := by
  unfold C.u10 at h ⊢
  by_cases h11 : (u11 (serialize p) == 1) = true
  · rw [if_pos h11]
    exact ⟨u11_ok p hdb hlen (by simpa using h11), rfl⟩
  · rw [if_neg h11] at h; exact absurd rfl h

end NumP
