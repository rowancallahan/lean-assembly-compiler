/- Nano/V2Self/Proof/OwnP18: IF node = `OwnSpec.chk`. -/
import Nano.V2Self.Proof.OwnP17
namespace OwnP
open C OwnSpec ParSpec

theorem o31_ite {W : WCx} {s f v : Buf} {A : AS} (hS : RS W s A) (hB : Bnd W A) {c : Nat} {a b t e : Nd}
    {rest : List UInt64} (hx : W.x.drop A.i = (Nd.ite c a b t e).ser ++ rest) :
    o31 W.x s f v W.t = (o3 (bset (bset s (u 0) (u (A.i + 2))) (u 11) (u 2)) (u 4) (u 4) (u 1) (u 0) (u 0), (f, v)) := by
  have h0 := hdr0 hB hx (k := 0) (by simp [Nd.ser])
  rw [show u A.i + u 0 = u A.i from u_add _ 0] at h0
  simp only [Nd.ser, List.getD_cons_zero] at h0
  unfold o31
  have r0 := (regs hS).1
  simp only [lit] at r0 h0 ⊢
  simp only [r0, h0, u_add]
  simp only [show (u 4 == u 1) = false from rfl, show (u 4 == u 2) = false from rfl, show (u 4 == u 3) = false from rfl,
    show (u 4 == u 4) = true from rfl, Bool.false_eq_true, if_false, if_true]

theorem orF_comm (a b : List Bool) : orF a b = List.zipWith (· || ·) b a := by
  unfold orF; rw [List.zipWith_comm]; congr; funext x y; exact Bool.or_comm y x

theorem sim_ite {W : WCx} {c : Nat} {a b t e : Nd} (ha : SimOK W a) (hb : SimOK W b) (ht : SimOK W t) (he : SimOK W e)
    {A : AS} {s f v : Buf} {rest : List UInt64} (hSt : St W s f v A) (hp : A.ph = 0)
    (hx : W.x.drop A.i = (Nd.ite c a b t e).ser ++ rest) : Reach W (s, f, v) (Done W A (.ite c a b t e)) := by
  have hS := hSt.1; have hB := hSt.2.2.2.2
  have hxl := drop_len hx (by simp [Nd.ser]); simp only [Nd.ser, List.length_cons, List.length_append] at hxl
  have hx40 := hB.2.2.2.1
  have hesl := hB.2.2.2.2.2.2.2.1
  -- push
  apply reach_trans (push_step hSt hp (o31_ite hS hB (f := f) (v := v) hx) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega))
  intro σ1 h1
  -- the condition operands
  have hx1 : W.x.drop (A.i + 2) = serL [a, b] ++ (t.ser ++ e.ser ++ rest) :=
    drop_hdr (hdr := [4, c.toUInt64]) (by simpa [Nd.ser, serL_cons, serL] using hx) rfl
  apply reach_trans (lst_sim W [a, b] (fun x hx => by simp at hx; rcases hx with rfl | rfl <;> assumption) _ σ1.1 σ1.2.1
    σ1.2.2 _ A.Φ ⟨4, 4, 0, 1, A.es.length, A.es.length, 0, 0⟩ A.es [] h1 rfl rfl ⟨by simp, by simp, by simp⟩ (by simp)
    (by simp) (by simp) (by simp) (by simp) rfl hx1)
  intro σ2 ⟨F', acc, r1, hl, ⟨a1, a2, a4, a5, a6, a7⟩, hc1, h2⟩
  simp only at a1 a2 a4 a5 a6 a7 hc1
  -- condition end, snapshot
  apply reach_trans (ph2_if_cond h2 rfl (Φ0 := A.Φ) (r := r1) rfl ⟨by omega, by omega, by omega⟩ a1 a4 (by simpa using hc1)
    a2 (pre := A.es) (acc := acc) rfl (by rw [a5]))
  intro σ3 ⟨F2, hfin, h3⟩
  have hab : (serL [a, b]).length = a.ser.length + b.ser.length := by simp [serL_cons, serL]
  -- then-branch
  have hxt : W.x.drop (A.i + 2 + (serL [a, b]).length) = t.ser ++ (e.ser ++ rest) := by
    rw [← List.drop_drop, hx1, List.drop_left]; simp
  apply reach_trans (ht _ σ3.1 σ3.2.1 σ3.2.2 (e.ser ++ rest) h3 rfl (by simp) hxt)
  intro σ4 ⟨Ft0, et, hct, h4⟩
  apply reach_trans (ph1_if_then h4 rfl (Φ0 := A.Φ) (r := (r1.set 5 r1.vb).set 7 A.sn.length) rfl (by simp [Fr.set, a1])
    (by simp [Fr.set, hc1]) (sn0 := A.sn) (S := F2) rfl (by simp [Fr.set]) (pre := A.es) (et := et) rfl
    (by simp [Fr.set, a5]))
  intro σ5 ⟨Ft, kt, htr, h5⟩
  have hkl := (tr_len' _ _ _ _ htr).1
  -- else-branch
  apply reach_trans (ph2_next h5 rfl (Φ0 := A.Φ) (r := (((r1.set 5 r1.vb).set 7 A.sn.length).set 6
    (A.es ++ et).length).set 2 3) rfl (by simp [Fr.set, a2]) (by simp [Fr.set, a1]) (by simp [Fr.set]))
  intro σ6 h6
  have hxe : W.x.drop (A.i + 2 + (serL [a, b]).length + t.ser.length) = e.ser ++ rest := by
    rw [← List.drop_drop, hxt, List.drop_left]
  apply reach_trans (he _ σ6.1 σ6.2.1 σ6.2.2 rest h6 rfl (by simp) hxe)
  intro σ7 ⟨Fe0, ee, hce, h7⟩
  apply reach_trans (ph1_if_else h7 rfl (Φ0 := A.Φ) (r := ((((r1.set 5 r1.vb).set 7 A.sn.length).set 6
    (A.es ++ et).length).set 2 3).set 5 (A.es ++ kt).length) rfl (by simp [Fr.set, a1]) (by simp [Fr.set])
    (sn0 := A.sn) (S := Ft) rfl (by simp [Fr.set]) (pre := A.es) (kt := kt) (ee := ee) (by simp) (by simp [Fr.set, a5])
    (by simp [Fr.set]; omega) (by simp [Fr.set]))
  intro σ8 ⟨Fe, ke, k, htre, hj, h8⟩
  apply reach_mono (ph2_pop h8 rfl (Φ0 := A.Φ) rfl (by simp [Fr.set, a1]) (by simp [Fr.set, a2]))
  intro σ9 h9
  refine ⟨orF Ft Fe, k, ?_, ?_⟩
  · have hds : dsOf W ⟨4, 4, 0, 1, A.es.length, A.es.length, 0, 0⟩ = some [0, 0] := by simp [dsOf]
    rw [hds] at hl
    obtain ⟨a0, b0, h1', h2', h3', h4', rfl, rfl⟩ := lstA_two hl
    have hct' : chk W.oc t F2 = some (Ft0, et) := hct
    have hce' : chk W.oc e F2 = some (Fe0, ee) := hce
    have htwo : two a0 b0 = some (F2, strip (a0.2 ++ b0.2)) := by
      simp only [two, h3', h4', Bool.and_self, if_true]; exact hfin
    simp only [chk, h1', h2', Option.bind_some, htwo, hct', htr, hce', htre, hj, Option.map_some]
  · rw [orF_comm]
    have e1 : A.i + (Nd.ite c a b t e).ser.length = A.i + 2 + (serL [a, b]).length + t.ser.length + e.ser.length := by
      rw [hab]; simp [Nd.ser]; omega
    rw [e1]; exact h9

end OwnP
