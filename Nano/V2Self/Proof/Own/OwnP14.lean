/- Nano/V2Self/Proof/Own/OwnP14: CALL, PRIM, CONTINUE and BIN nodes = `OwnSpec.chk`. -/
import Nano.V2Self.Proof.Own.OwnP13
namespace OwnP
open C OwnSpec ParSpec

/-- an error in one step -/
theorem reach_err1 {W : WCx} {s f v : Buf} {A : AS} {P : SB → Prop} (hS : RS W s A) (h : bget (stp W (s, f, v)).1 1 = 1) :
    Reach W (s, f, v) P := reach_one hS (.inr h)

theorem o31_call {W : WCx} {s f v : Buf} {A : AS} (hS : RS W s A) (hB : Bnd W A) (hT : RT W) {i0 : Nat} {as : List Nd}
    {rest : List UInt64} (hi0 : i0 < 2 ^ 64) (hx : W.x.drop A.i = (Nd.call i0 as).ser ++ rest) :
    o31 W.x s f v W.t = if i0 < W.ps.length then
      (o3 (bset (bset s (u 0) (u (A.i + 3))) (u 11) (u 2)) (u 8) (u as.length) (u 3) (u i0) (u 0), (f, v))
      else (o5 s, (f, v)) := by
  have h0 := hdr0 hB hx (k := 0) (by simp [Nd.ser])
  have h1 := hdr0 hB hx (k := 1) (by simp [Nd.ser])
  have h2 := hdr0 hB hx (k := 2) (by simp [Nd.ser])
  rw [show u A.i + u 0 = u A.i from u_add _ 0] at h0
  simp only [Nd.ser, List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2
  unfold o31
  have r0 := (regs hS).1
  have r13 := (regs hS).2.2.2.2.2.2.2.2.2.2
  have hnd := hT.2.1
  simp only [lit] at r0 r13 h0 h1 h2 ⊢
  rw [u_add, show i0.toUInt64 = u i0 from rfl] at h1
  rw [u_add, show as.length.toUInt64 = u as.length from rfl] at h2
  simp only [r0, h0, u_add, h1, h2, r13]
  simp only [show (u 8 == u 1) = false from rfl, show (u 8 == u 2) = false from rfl, show (u 8 == u 3) = false from rfl,
    show (u 8 == u 4) = false from rfl, show (u 8 == u 5) = false from rfl, show (u 8 == u 6) = false from rfl,
    show (u 8 == u 8) = true from rfl, Bool.false_eq_true, if_false, if_true, u_lt' hi0 (show W.ps.length < 2 ^ 64 by omega)]

theorem getElem?_getD' {α : Type} {l : List α} {i : Nat} (h : i < l.length) (d : α) : l[i]? = some (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem sim_call {W : WCx} {i0 : Nat} {as : List Nd} (hsim : ∀ c ∈ as, SimOK W c) {A : AS} {s f v : Buf}
    {rest : List UInt64} (hSt : St W s f v A) (hp : A.ph = 0) (hi0 : i0 < 2 ^ 64)
    (hx : W.x.drop A.i = (Nd.call i0 as).ser ++ rest) : Reach W (s, f, v) (Done W A (.call i0 as)) := by
  have hS := hSt.1; have hB := hSt.2.2.2.2; have hT := hSt.2.2.2.1
  have h31 := o31_call hS hB hT (f := f) (v := v) hi0 hx
  by_cases hc : i0 < W.ps.length
  rotate_left
  · apply reach_err1 hS
    rw [stp_eq, o30_ph0 hS hp, h31, if_neg hc]; exact err_o5 (by have := hS.1; omega)
  rw [if_pos hc] at h31
  have hxl := drop_len hx (by simp [Nd.ser]); simp only [Nd.ser, List.length_cons] at hxl
  have hx1 : W.x.drop (A.i + 3) = serL as ++ rest :=
    drop_hdr (hdr := [8, i0.toUInt64, as.length.toUInt64]) (by simpa [Nd.ser] using hx) rfl
  have hnd := hT.2.1
  have hrs := hT.1
  apply reach_mono (sim_list hsim hSt hp (δ := 3) (g := 8) (d := 3) (a := i0) (by omega) (by omega) (by omega)
    ⟨by simp, by simp, fun _ => hc⟩ h31 hx1 (by omega) (by omega) (by omega) (by omega) (fun _ => W.rs.getD i0 [])
    (fun A' s f v r' acc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
      have := fin_call h1 h2 h3 h4 h5 h6 h8 h9 h10; rw [h7] at this; exact this))
  intro σ ⟨F', acc, F2, hl, hfin, hσ⟩
  refine ⟨F2, W.rs.getD i0 [], ?_, ?_⟩
  · have hds : dsOf W ⟨8, as.length, 0, 3, 0, 0, i0, 0⟩ = some (W.ps.getD i0 []) := by simp [dsOf]
    rw [hds] at hl hfin
    simp only [chk, WCx.oc, getElem?_getD' hc [], getElem?_getD' (show i0 < W.rs.length by omega) []]
    have hl' : lstA { ps := W.ps, rs := W.rs, K := W.K, npw := W.npw } as (some (W.ps.getD i0 [])) A.F [] = some (F', acc) := hl
    rw [hl']; simp only [Option.bind_some]; rw [hfin]; rfl
  · have e : A.i + (Nd.call i0 as).ser.length = A.i + 3 + (serL as).length := by simp [Nd.ser]; omega
    rw [e]; exact hσ

theorem o31_prim {W : WCx} {s f v : Buf} {A : AS} (hS : RS W s A) (hB : Bnd W A) {p : Nat} {as : List Nd}
    {rest : List UInt64} (hp64 : p < 2 ^ 64) (hx : W.x.drop A.i = (Nd.prim p as).ser ++ rest) :
    o31 W.x s f v W.t = if 0 < p ∧ p < 10 then
      (o3 (bset (bset s (u 0) (u (A.i + 2))) (u 11) (u 2)) (u 9) (o11 (u p)) (u 2) (u p) (u 0), (f, v))
      else (o5 s, (f, v)) := by
  have h0 := hdr0 hB hx (k := 0) (by simp [Nd.ser])
  have h1 := hdr0 hB hx (k := 1) (by simp [Nd.ser])
  rw [show u A.i + u 0 = u A.i from u_add _ 0] at h0
  simp only [Nd.ser, List.getD_cons_zero, List.getD_cons_succ] at h0 h1
  unfold o31
  have r0 := (regs hS).1
  simp only [lit] at r0 h0 h1 ⊢
  rw [u_add, show p.toUInt64 = u p from rfl] at h1
  simp only [r0, h0, u_add, h1]
  simp only [show (u 9 == u 1) = false from rfl, show (u 9 == u 2) = false from rfl, show (u 9 == u 3) = false from rfl,
    show (u 9 == u 4) = false from rfl, show (u 9 == u 5) = false from rfl, show (u 9 == u 6) = false from rfl,
    show (u 9 == u 8) = false from rfl, show (u 9 == u 9) = true from rfl, Bool.false_eq_true, if_false, if_true,
    u_lt' (show 0 < 2 ^ 64 by omega) hp64, u_lt' hp64 (show 10 < 2 ^ 64 by omega)]
  by_cases h1 : 0 < p <;> by_cases h2 : p < 10 <;> simp [h1, h2]

/-- prim nodes have the arity of their prim id -/
def primAr (p : Nat) (as : List Nd) : Prop := 1 ≤ p → p ≤ 9 → as.length = (dsP p).length

theorem sim_prim {W : WCx} {p : Nat} {as : List Nd} (hsim : ∀ c ∈ as, SimOK W c) {A : AS} {s f v : Buf}
    {rest : List UInt64} (hSt : St W s f v A) (hp : A.ph = 0) (hp64 : p < 2 ^ 64) (har : primAr p as)
    (hx : W.x.drop A.i = (Nd.prim p as).ser ++ rest) : Reach W (s, f, v) (Done W A (.prim p as)) := by
  have hS := hSt.1; have hB := hSt.2.2.2.2
  have h31 := o31_prim hS hB (f := f) (v := v) hp64 hx
  by_cases hc : 0 < p ∧ p < 10
  rotate_left
  · apply reach_err1 hS
    rw [stp_eq, o30_ph0 hS hp, h31, if_neg hc]; exact err_o5 (by have := hS.1; omega)
  rw [if_pos hc, o11_eq hc.2, ← har (by omega) (by omega)] at h31
  have hxl := drop_len hx (by simp [Nd.ser]); simp only [Nd.ser, List.length_cons] at hxl
  have hx1 : W.x.drop (A.i + 2) = serL as ++ rest :=
    drop_hdr (hdr := [9, p.toUInt64]) (by simpa [Nd.ser] using hx) rfl
  apply reach_mono (sim_list hsim hSt hp (δ := 2) (g := 9) (d := 2) (a := p) (by omega) (by omega) (by omega)
    ⟨by simp, fun _ => hc.2, by simp⟩ h31 hx1 (by omega) (by omega) (by omega) (by omega) (fun _ => [rk p])
    (fun A' s f v r' acc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
      have := fin_prim h1 h2 h3 h4 h5 (by rw [h7]; exact hc.2) h8 h9 h10; rw [h7] at this; exact this))
  intro σ ⟨F', acc, F2, hl, hfin, hσ⟩
  refine ⟨F2, [rk p], ?_, ?_⟩
  · have hds : dsOf W ⟨9, as.length, 0, 2, 0, 0, p, 0⟩ = some (dsP p) := by simp [dsOf]
    rw [hds] at hl hfin
    have hl' : lstA { ps := W.ps, rs := W.rs, K := W.K, npw := W.npw } as (some (dsP p)) A.F [] = some (F', acc) := hl
    simp only [chk, WCx.oc]; rw [hl']; simp only [Option.bind_some]; rw [hfin]; rfl
  · have e : A.i + (Nd.prim p as).ser.length = A.i + 2 + (serL as).length := by simp [Nd.ser]; omega
    rw [e]; exact hσ

theorem ser_head (e : Nd) (h : ∀ cs, e ≠ .pair cs) : e.ser.getD 0 0 ≠ 6 := by
  cases e <;> simp [Nd.ser] <;> first | decide | exact h _ rfl

theorem o31_cont {W : WCx} {s f v : Buf} {A : AS} (hS : RS W s A) (hB : Bnd W A) {e : Nd}
    {rest : List UInt64} (hx : W.x.drop A.i = (Nd.cont e).ser ++ rest) :
    o31 W.x s f v W.t = match e with
      | .pair cs => (o3 (bset (bset s (u 0) (u (A.i + 3))) (u 11) (u 2)) (u 11) (u cs.length) (u 4) (u 0) (u 0), (f, v))
      | _ => (o3 (bset (bset s (u 0) (u (A.i + 1))) (u 11) (u 2)) (u 11) (u 1) (u 4) (u 0) (u 0), (f, v)) := by
  have h0 := hdr0 hB hx (k := 0) (by simp [Nd.ser])
  have h1 := hdr0 hB hx (k := 1) (by have := ser_len_pos e; simp [Nd.ser]; omega)
  rw [show u A.i + u 0 = u A.i from u_add _ 0] at h0
  simp only [Nd.ser, List.getD_cons_zero, List.getD_cons_succ] at h0 h1
  unfold o31
  have r0 := (regs hS).1
  simp only [lit] at r0 h0 h1 ⊢
  rw [u_add] at h1
  simp only [r0, h0, u_add, h1]
  simp only [show (u 11 == u 1) = false from rfl, show (u 11 == u 2) = false from rfl, show (u 11 == u 3) = false from rfl,
    show (u 11 == u 4) = false from rfl, show (u 11 == u 5) = false from rfl, show (u 11 == u 6) = false from rfl,
    show (u 11 == u 8) = false from rfl, show (u 11 == u 9) = false from rfl, show (u 11 == u 10) = false from rfl,
    show (u 11 == u 11) = true from rfl, Bool.false_eq_true, if_false, if_true]
  cases e
  case pair cs =>
    have h2 := hdr0 hB hx (k := 2) (by simp [Nd.ser])
    simp only [Nd.ser, List.getD_cons_succ, List.getD_cons_zero] at h2 ⊢
    simp only [lit] at h2 ⊢; rw [u_add, show cs.length.toUInt64 = u cs.length from rfl] at h2
    simp only [show (u 6 == u 6) = true from rfl, if_true, h2]
  all_goals (simp only [Nd.ser, List.getD_cons_zero, lit]; rw [if_neg (by decide)])

theorem lstA_one {c : OwnSpec.Cx} {e : Nd} {ds : Option (List Nat)} {F F' : List Bool} {acc : List Nat}
    (h : lstA c [e] ds F [] = some (F', acc)) : chk c e F = some (F', acc) ∧ okAll ds F' 0 acc = true := by
  simp only [lstA, Option.bind_eq_some_iff] at h
  obtain ⟨x, hx, h2⟩ := h
  split at h2
  · simp at h2; obtain ⟨rfl, rfl⟩ := h2; exact ⟨hx, by simpa using ‹_›⟩
  · cases h2

theorem chk_cont_np (c : OwnSpec.Cx) (e : Nd) (h : ∀ cs, e ≠ .pair cs) (F : List Bool) :
    chk c (.cont e) F = (chk c e F).bind fun x => if okAll (some (stD c.K c.npw)) x.1 0 x.2 then
      (fin (some (stD c.K c.npw)) x.1 x.2).map fun y => (y.1, []) else none := by
  cases e <;> first | rfl | exact absurd rfl (h _)

theorem o31_cont_np {W : WCx} {s f v : Buf} {A : AS} (hS : RS W s A) (hB : Bnd W A) {e : Nd} (h : ∀ cs, e ≠ .pair cs)
    {rest : List UInt64} (hx : W.x.drop A.i = (Nd.cont e).ser ++ rest) :
    o31 W.x s f v W.t = (o3 (bset (bset s (u 0) (u (A.i + 1))) (u 11) (u 2)) (u 11) (u 1) (u 4) (u 0) (u 0), (f, v)) := by
  rw [o31_cont hS hB hx]; cases e <;> first | rfl | exact absurd rfl (h _)

theorem sim_cont {W : WCx} {e : Nd} (hsimE : SimOK W e) (hsimP : ∀ cs, e = .pair cs → ∀ c ∈ cs, SimOK W c) {A : AS}
    {s f v : Buf} {rest : List UInt64} (hSt : St W s f v A) (hp : A.ph = 0)
    (hx : W.x.drop A.i = (Nd.cont e).ser ++ rest) : Reach W (s, f, v) (Done W A (.cont e)) := by
  have hS := hSt.1; have hB := hSt.2.2.2.2
  have h31 := o31_cont hS hB (f := f) (v := v) hx
  have hxl := drop_len hx (by simp [Nd.ser]); simp only [Nd.ser, List.length_cons] at hxl
  have hfin : ∀ (A' : AS) (s f v : Buf) (r' : Fr) (acc : List Nat), St W s f v A' → A'.ph = 2 → A'.Φ = A.Φ ++ [r'] →
      r'.ok W → r'.g = 11 → r'.d = 4 → r'.a = 0 → r'.c = r'.n → A'.es = A.es ++ acc → A.es.length = r'.vb →
      Reach W (s, f, v) (fun σ => ∃ F2, fin (dsOf W r') A'.F acc = some (F2, strip acc) ∧
        Fin W A' A.Φ A.es F2 ((fun _ => []) acc) σ) :=
    fun A' s f v r' acc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => fin_cont h1 h2 h3 h4 h5 h8 h9 h10
  have hds : ∀ n, dsOf W ⟨11, n, 0, 4, 0, 0, 0, 0⟩ = some (stD W.K W.npw) := fun n => by simp [dsOf]
  by_cases hpe : ∃ cs, e = .pair cs
  · obtain ⟨cs, rfl⟩ := hpe
    simp only at h31
    have hx1 : W.x.drop (A.i + 3) = serL cs ++ rest :=
      drop_hdr (hdr := [11, 6, cs.length.toUInt64]) (by simpa [Nd.ser] using hx) rfl
    have hcs := serL_len_ge cs
    apply reach_mono (sim_list (hsimP cs rfl) hSt hp (δ := 3) (g := 11) (d := 4) (a := 0) (by omega) (by omega) (by omega)
      ⟨by simp, by simp, by simp⟩ h31 hx1 (by simp [Nd.ser] at hxl; omega) (by omega) (by omega) (by omega) (fun _ => []) hfin)
    intro σ ⟨F', acc, F2, hl, hfin2, hσ⟩
    refine ⟨F2, [], ?_, ?_⟩
    · rw [hds] at hl hfin2
      have hl' : lstA { ps := W.ps, rs := W.rs, K := W.K, npw := W.npw } cs (some (stD W.K W.npw)) A.F [] = some (F', acc) := hl
      simp only [chk, WCx.oc]; rw [hl']; simp only [Option.bind_some]; rw [hfin2]; rfl
    · have e : A.i + (Nd.cont (.pair cs)).ser.length = A.i + 3 + (serL cs).length := by simp [Nd.ser]; omega
      rw [e]; exact hσ
  · have hnp : ∀ cs, e ≠ .pair cs := fun cs h => hpe ⟨cs, h⟩
    have h31' := o31_cont_np hS hB hnp (f := f) (v := v) hx
    have hx1 : W.x.drop (A.i + 1) = serL [e] ++ rest :=
      drop_hdr (hdr := [11]) (by simpa [Nd.ser, serL_cons, serL] using hx) rfl
    have hel : (serL [e]).length = e.ser.length := by simp [serL_cons, serL]
    apply reach_mono (sim_list (cs := [e]) (fun c hc => by simp at hc; subst hc; exact hsimE) hSt hp (δ := 1) (g := 11)
      (d := 4) (a := 0) (by omega) (by omega) (by omega) ⟨by simp, by simp, by simp⟩ (by simpa using h31') hx1
      (by rw [hel]; omega) (by omega) (by omega) (by omega) (fun _ => []) hfin)
    intro σ ⟨F', acc, F2, hl, hfin2, hσ⟩
    rw [hds] at hl hfin2
    obtain ⟨hchk, hok⟩ := lstA_one hl
    refine ⟨F2, [], ?_, ?_⟩
    · rw [chk_cont_np _ _ hnp]
      have hchk' : chk W.oc e A.F = some (F', acc) := hchk
      rw [hchk']; simp only [Option.bind_some, WCx.oc]
      have hok' : okAll (some (stD W.K W.npw)) F' 0 acc = true := hok
      rw [if_pos hok', hfin2]; rfl
    · have e1 : A.i + (Nd.cont e).ser.length = A.i + 1 + (serL [e]).length := by rw [hel]; simp [Nd.ser]; omega
      rw [e1]; exact hσ

end OwnP
