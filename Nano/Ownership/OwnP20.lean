/- Nano/Ownership/OwnP20: LET node = `OwnSpec.chk`. -/
import Nano.Ownership.OwnP19
namespace OwnP
open C OwnSpec ParSpec

theorem o31_let {W : WCx} {s f v : Buf} {A : AS} (hS : RS W s A) (hB : Bnd W A) {sl w : Nat} {a b : Nd}
    {rest : List UInt64} (hx : W.x.drop A.i = (Nd.letE sl w a b).ser ++ rest) (hs : sl < 2 ^ 20) (hw : w < 2 ^ 20) :
    o31 W.x s f v W.t = (o3 (bset (bset s (u 0) (u (A.i + 3))) (u 11) (u 2)) (u 5) (u 2) (u 0) (u sl) (u w), (f, v)) := by
  have h0 := hdr0 hB hx (k := 0) (by simp [Nd.ser])
  have h1 := hdr0 hB hx (k := 1) (by simp [Nd.ser])
  have h2 := hdr0 hB hx (k := 2) (by simp [Nd.ser])
  rw [show u A.i + u 0 = u A.i from u_add _ 0] at h0
  simp only [Nd.ser, List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2
  unfold o31; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r0 := (regs hS).1
  simp only [lit] at r0 h0 h1 h2 ⊢
  rw [u_add, show sl.toUInt64 = u sl from rfl] at h1
  rw [u_add, show w.toUInt64 = u w from rfl] at h2
  simp only [r0, h0, u_add, h1, h2]
  simp only [show (u 5 == u 1) = false from rfl, show (u 5 == u 2) = false from rfl, show (u 5 == u 3) = false from rfl,
    show (u 5 == u 4) = false from rfl, show (u 5 == u 5) = true from rfl, Bool.false_eq_true, if_false, if_true,
    u_lt' (show 1048575 < 2 ^ 64 by omega) (show sl < 2 ^ 64 by omega),
    u_lt' (show 1048575 < 2 ^ 64 by omega) (show w < 2 ^ 64 by omega),
    show ¬ 1048575 < sl by omega, show ¬ 1048575 < w by omega, decide_false]

theorem sim_let {W : WCx} {sl w : Nat} {a b : Nd} (ha : SimOK W a) (hb : SimOK W b) (hs : sl < 2 ^ 20) (hw : w < 2 ^ 20)
    {A : AS} {s f v : Buf} {rest : List UInt64} (hSt : St W s f v A) (hp : A.ph = 0)
    (hx : W.x.drop A.i = (Nd.letE sl w a b).ser ++ rest) : Reach W (s, f, v) (Done W A (.letE sl w a b)) := by
  have hS := hSt.1; have hB := hSt.2.2.2.2
  have hxl := drop_len hx (by simp [Nd.ser]); simp only [Nd.ser, List.length_cons, List.length_append] at hxl
  have hx40 := hB.2.2.2.1
  have hesl := hB.2.2.2.2.2.2.2.1
  apply reach_trans (push_step hSt hp (o31_let hS hB (f := f) (v := v) hx hs hw) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega))
  intro σ1 h1
  apply reach_trans (ph2_next h1 rfl (Φ0 := A.Φ) rfl (by simp) (by simp) (by simp))
  intro σ2 h2
  have hxa : W.x.drop (A.i + 3) = a.ser ++ (b.ser ++ rest) :=
    drop_hdr (hdr := [5, sl.toUInt64, w.toUInt64]) (by simpa [Nd.ser] using hx) rfl
  apply reach_trans (ha _ σ2.1 σ2.2.1 σ2.2.2 _ h2 rfl (by simp) hxa)
  intro σ3 ⟨F1, ev, hca, h3⟩
  apply reach_trans (ph1_let_val h3 rfl (Φ0 := A.Φ) rfl (by simp [Fr.set]) (by simp [Fr.set]) (pre := A.es) (ev := ev) rfl
    (by simp [Fr.set]) (by simp [Fr.set]; omega) (by simp [Fr.set]; omega))
  intro σ4 ⟨F2, kv, htr, c1, c2, c3, c4, h4⟩
  simp only [Fr.set] at c1 c2 c3 c4
  apply reach_trans (ph2_next h4 rfl (Φ0 := A.Φ) rfl (by simp [Fr.set]) (by simp [Fr.set]) (by simp [Fr.set]))
  intro σ5 h5
  have hxb : W.x.drop (A.i + 3 + a.ser.length) = b.ser ++ rest := by rw [← List.drop_drop, hxa, List.drop_left]
  apply reach_trans (hb _ σ5.1 σ5.2.1 σ5.2.2 _ h5 rfl (by simp) hxb)
  intro σ6 ⟨Fb, eb, hcb, h6⟩
  apply reach_trans (ph1_let_body h6 rfl (Φ0 := A.Φ) rfl (by simp [Fr.set]) (by simp [Fr.set]) (pre := A.es) (eb := eb) rfl
    (by simp [Fr.set]))
  intro σ7 ⟨F', kb, htrb, h7⟩
  apply reach_mono (ph2_pop h7 rfl (Φ0 := A.Φ) rfl (by simp [Fr.set]) (by simp [Fr.set]))
  intro σ8 h8
  refine ⟨F', kb, ?_, ?_⟩
  · have hca' : chk W.oc a A.F = some (F1, ev) := hca
    have hcb' : chk W.oc b F2 = some (Fb, eb) := hcb
    simp only [chk, hca', Option.bind_some, htr]
    rw [if_pos ⟨c1, c2, c3, c4⟩]; simp only [hcb', Option.bind_some, htrb]
  · have e1 : A.i + (Nd.letE sl w a b).ser.length = A.i + 3 + a.ser.length + b.ser.length := by simp [Nd.ser]; omega
    rw [e1]; exact h8

end OwnP
