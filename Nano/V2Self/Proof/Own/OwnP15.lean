/- Nano/V2Self/Proof/Own/OwnP15: BIN node = `OwnSpec.chk` (its operands as the argument list `[a, b]`). -/
import Nano.V2Self.Proof.Own.OwnP14
namespace OwnP
open C OwnSpec ParSpec

theorem lstA_two {c : OwnSpec.Cx} {a b : Nd} {ds : Option (List Nat)} {F F' : List Bool} {acc : List Nat}
    (h : lstA c [a, b] ds F [] = some (F', acc)) : ∃ a0 b0, chk c a F = some a0 ∧ chk c b a0.1 = some b0 ∧
      okAll ds a0.1 0 a0.2 = true ∧ okAll ds b0.1 a0.2.length b0.2 = true ∧ F' = b0.1 ∧ acc = a0.2 ++ b0.2 := by
  simp only [lstA, Option.bind_eq_some_iff] at h
  obtain ⟨a0, ha, h2⟩ := h
  split at h2
  · rename_i hoka
    simp only [Option.bind_eq_some_iff] at h2
    obtain ⟨b0, hb, h3⟩ := h2
    split at h3
    · rename_i hokb
      simp at h3; obtain ⟨rfl, rfl⟩ := h3
      exact ⟨a0, b0, ha, hb, hoka, by simpa using hokb, rfl, by simp⟩
    · cases h3
  · cases h2

theorem o31_bin {W : WCx} {s f v : Buf} {A : AS} (hS : RS W s A) (hB : Bnd W A) {op : Nat} {a b : Nd}
    {rest : List UInt64} (hx : W.x.drop A.i = (Nd.bin op a b).ser ++ rest) :
    o31 W.x s f v W.t = (o3 (bset (bset s (u 0) (u (A.i + 2))) (u 11) (u 2)) (u 3) (u [a, b].length) (u 1) (u 0) (u 0), (f, v)) := by
  have h0 := hdr0 hB hx (k := 0) (by simp [Nd.ser])
  rw [show u A.i + u 0 = u A.i from u_add _ 0] at h0
  simp only [Nd.ser, List.getD_cons_zero] at h0
  unfold o31; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r0 := (regs hS).1
  simp only [lit] at r0 h0 ⊢
  simp only [r0, h0, u_add]
  simp only [show (u 3 == u 1) = false from rfl, show (u 3 == u 2) = false from rfl, show (u 3 == u 3) = true from rfl,
    Bool.false_eq_true, if_false, if_true]
  rfl

theorem sim_bin {W : WCx} {op : Nat} {a b : Nd} (ha : SimOK W a) (hb : SimOK W b) {A : AS} {s f v : Buf}
    {rest : List UInt64} (hSt : St W s f v A) (hp : A.ph = 0)
    (hx : W.x.drop A.i = (Nd.bin op a b).ser ++ rest) : Reach W (s, f, v) (Done W A (.bin op a b)) := by
  have hS := hSt.1; have hB := hSt.2.2.2.2
  have h31 := o31_bin hS hB (f := f) (v := v) hx
  have hxl := drop_len hx (by simp [Nd.ser]); simp only [Nd.ser, List.length_cons, List.length_append] at hxl
  have hx1 : W.x.drop (A.i + 2) = serL [a, b] ++ rest :=
    drop_hdr (hdr := [3, op.toUInt64]) (by simpa [Nd.ser, serL_cons, serL] using hx) rfl
  have hel : (serL [a, b]).length = a.ser.length + b.ser.length := by simp [serL_cons, serL]
  have hfin : ∀ (A' : AS) (s f v : Buf) (r' : Fr) (acc : List Nat), St W s f v A' → A'.ph = 2 → A'.Φ = A.Φ ++ [r'] →
      r'.ok W → r'.g = 3 → r'.d = 1 → r'.a = 0 → r'.c = r'.n → A'.es = A.es ++ acc → A.es.length = r'.vb →
      Reach W (s, f, v) (fun σ => ∃ F2, fin (dsOf W r') A'.F acc = some (F2, strip acc) ∧
        Fin W A' A.Φ A.es F2 ((fun _ => [0]) acc) σ) :=
    fun A' s f v r' acc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => fin_bin h1 h2 h3 h4 h5 h8 h9 h10
  apply reach_mono (sim_list (cs := [a, b]) (fun c hc => by simp at hc; rcases hc with rfl | rfl <;> assumption) hSt hp
    (δ := 2) (g := 3) (d := 1) (a := 0) (by omega) (by omega) (by omega) ⟨by simp, by simp, by simp⟩ h31 hx1
    (by rw [hel]; omega) (by omega) (by omega) (by omega) (fun _ => [0]) hfin)
  intro σ ⟨F', acc, F2, hl, hfin2, hσ⟩
  have hds : dsOf W ⟨3, [a, b].length, 0, 1, 0, 0, 0, 0⟩ = some [0, 0] := by simp [dsOf]
  rw [hds] at hl hfin2
  obtain ⟨a0, b0, h1, h2, h3, h4, rfl, rfl⟩ := lstA_two hl
  refine ⟨F2, [0], ?_, ?_⟩
  · have h1' : chk W.oc a A.F = some a0 := h1
    have h2' : chk W.oc b a0.1 = some b0 := h2
    simp only [chk, h1', h2', Option.bind_some, two, h3, h4, Bool.and_self, if_true, hfin2, Option.map_some]
  · have e1 : A.i + (Nd.bin op a b).ser.length = A.i + 2 + (serL [a, b]).length := by rw [hel]; simp [Nd.ser]; omega
    rw [e1]; exact hσ

end OwnP
