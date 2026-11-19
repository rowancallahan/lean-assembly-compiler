/- Nano/V2Self/Proof/OwnP14: CALL, PRIM, CONTINUE and BIN nodes = `OwnSpec.chk`. -/
import Nano.V2Self.Proof.OwnP13
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

end OwnP
