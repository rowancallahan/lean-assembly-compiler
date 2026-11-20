/- Nano/V2Self/Proof/Own/OwnP13: phase-0 frame pushes (one per tag: `o31` = push) and the list-node simulations. -/
import Nano.V2Self.Proof.Own.OwnP12
namespace OwnP
open C OwnSpec ParSpec

theorem serL_len_ge : ∀ cs : List Nd, cs.length ≤ (serL cs).length
  | [] => by simp [serL]
  | n :: cs => by have := serL_len_ge cs; have := ser_len_pos n; simp [serL_cons]; omega

/-- a push step, given what `o31` does -/
theorem push_step {W : WCx} {s f v : Buf} {A : AS} (hSt : St W s f v A) (hp : A.ph = 0) {i' g n d a b : Nat}
    (h31 : o31 W.x s f v W.t = (o3 (bset (bset s (u 0) (u i')) (u 11) (u 2)) (u g) (u n) (u d) (u a) (u b), (f, v)))
    (hi : i' < 2 ^ 40) (hg : g < 2 ^ 40) (hn : n < 2 ^ 40) (hd : d < 2 ^ 40) (ha : a < 2 ^ 40) (hb : b < 2 ^ 40) :
    Reach W (s, f, v) (fun σ => St W σ.1 σ.2.1 σ.2.2
      { A with i := i', Φ := A.Φ ++ [⟨g, n, 0, d, A.es.length, A.es.length, a, b⟩], ph := 2 }) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  apply reach_one hS
  rw [stp_eq, o30_ph0 hS hp, h31]
  have hS1 := rs_ip hS i' 2
  have hb30 := hB.2.2.2.2.2.1
  rcases o3_ok hS1 hb30 g n d a b (by omega) (by omega) (by omega) (by omega) (by omega) with ⟨hq, hS2⟩ | herr
  · left
    simp only at hq
    refine ⟨hS2, hF, hV, hT, ?_⟩
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hB
    have hesl := b8
    refine ⟨b1, b2, b3, b4, hi, by simp; omega, b7, b8, b9, fun x hx => ?_, show 2 < 3 by omega⟩
    rcases List.mem_append.mp hx with h | h
    · exact b10 x h
    · simp at h; subst h; intro k hk
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with h | h | h | h | h | h | h | h <;>
        subst h <;> simp [Fr.fld] <;> omega
  · right; exact herr

theorem hdr0 {W : WCx} {A : AS} (hB : Bnd W A) {l rest : List UInt64} (hx : W.x.drop A.i = l ++ rest) {k : Nat}
    (hk : k < l.length) : bget W.x (u A.i + u k) = l.getD k 0 := by
  have hxl := drop_len hx (by omega); have hx40 := hB.2.2.2.1
  rw [u_add]; exact xw hx hk (by omega)

theorem o31_pair {W : WCx} {s f v : Buf} {A : AS} (hS : RS W s A) (hB : Bnd W A) {cs : List Nd} {rest : List UInt64}
    (hx : W.x.drop A.i = (Nd.pair cs).ser ++ rest) :
    o31 W.x s f v W.t = (o3 (bset (bset s (u 0) (u (A.i + 2))) (u 11) (u 2)) (u 6) (u cs.length) (u 0) (u 0) (u 0), (f, v)) := by
  have h0 := hdr0 hB hx (k := 0) (by simp [Nd.ser])
  have h1 := hdr0 hB hx (k := 1) (by simp [Nd.ser])
  rw [show u A.i + u 0 = u A.i from u_add _ 0] at h0
  simp only [Nd.ser, List.getD_cons_zero, List.getD_cons_succ] at h0 h1
  unfold o31; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r0 := (regs hS).1
  simp only [lit] at r0 h0 h1 ⊢
  rw [u_add, show cs.length.toUInt64 = u cs.length from rfl] at h1
  simp only [r0, h0, u_add, h1]
  simp only [show (u 6 == u 1) = false from rfl, show (u 6 == u 2) = false from rfl, show (u 6 == u 3) = false from rfl,
    show (u 6 == u 4) = false from rfl, show (u 6 == u 5) = false from rfl, show (u 6 == u 6) = true from rfl,
    Bool.false_eq_true, if_false, if_true]

theorem after_ok {W : WCx} {r r' : Fr} (h : r.after r') (hr : r.ok W) : r'.ok W := by
  obtain ⟨-, -, hd, -, ha, -⟩ := h
  obtain ⟨h1, h2, h3⟩ := hr
  exact ⟨by rw [hd]; exact h1, fun e => by rw [ha]; exact h2 (by rw [← hd]; exact e),
    fun e => by rw [ha]; exact h3 (by rw [← hd]; exact e)⟩

theorem after_ds {W : WCx} {r r' : Fr} (h : r.after r') : dsOf W r' = dsOf W r := by
  obtain ⟨-, -, hd, -, ha, -⟩ := h; unfold dsOf; rw [hd, ha]

theorem drop_hdr {x : Buf} {i k : Nat} {hdr l rest : List UInt64} (hx : x.drop i = hdr ++ l ++ rest) (hk : hdr.length = k) :
    x.drop (i + k) = l ++ rest := by
  rw [← List.drop_drop, hx, ← hk, List.append_assoc, List.drop_left]

theorem sim_pair {W : WCx} {cs : List Nd} (hsim : ∀ c ∈ cs, SimOK W c) {A : AS} {s f v : Buf} {rest : List UInt64}
    (hSt : St W s f v A) (hp : A.ph = 0) (hx : W.x.drop A.i = (Nd.pair cs).ser ++ rest) :
    Reach W (s, f, v) (Done W A (.pair cs)) := by
  have hB := hSt.2.2.2.2
  have hxl := drop_len hx (by simp [Nd.ser]); simp only [Nd.ser, List.length_cons] at hxl
  have hcs := serL_len_ge cs
  have hx40 := hB.2.2.2.1
  have hesl := hB.2.2.2.2.2.2.2.1
  apply reach_trans (push_step hSt hp (o31_pair hSt.1 hB hx) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  intro σ1 h1
  have hx1 : W.x.drop (A.i + 2) = serL cs ++ rest := drop_hdr (hdr := [6, cs.length.toUInt64]) (by simpa [Nd.ser] using hx) rfl
  apply reach_trans (lst_sim W cs hsim _ σ1.1 σ1.2.1 σ1.2.2 rest A.Φ ⟨6, cs.length, 0, 0, A.es.length, A.es.length, 0, 0⟩
    A.es [] h1 rfl rfl ⟨by simp, by simp, by simp⟩ (by simp) (by simp) (by simp) (by simp) (by simp) rfl hx1)
  intro σ2 ⟨F', acc', r', hl, haf, hc3, h2⟩
  have hok := after_ok (W := W) haf ⟨by simp, by simp, by simp⟩
  obtain ⟨a1, a2, a4, a5, a6, a7⟩ := haf
  apply reach_mono (fin_pair h2 rfl (Φ0 := A.Φ) (r := r') rfl hok (by rw [a1]) (by rw [hc3, a2]; simp) (pre := A.es) (acc := acc')
    rfl (by rw [a5]))
  intro σ3 ⟨F2, hfin, h3⟩
  refine ⟨F2, strip acc', ?_, ?_⟩
  · have hds : dsOf W ⟨6, cs.length, 0, 0, A.es.length, A.es.length, 0, 0⟩ = none := by simp [dsOf]
    simp only [hds] at hl
    simp only [chk]; rw [hl]; simp only [Option.bind_some]
    have : dsOf W r' = none := by unfold dsOf; rw [a4]; simp
    rw [this] at hfin; exact hfin
  · unfold Fin at h3
    have e : A.i + (Nd.pair cs).ser.length = A.i + 2 + (serL cs).length := by simp [Nd.ser]; omega
    rw [e]; exact h3

/-- any argument-list node: push (by `o31` as given), children, finish (as given) -/
theorem sim_list {W : WCx} {cs : List Nd} (hsim : ∀ c ∈ cs, SimOK W c) {A : AS} {s f v : Buf} {rest : List UInt64}
    (hSt : St W s f v A) (hp : A.ph = 0) {δ g d a : Nat} (hg5 : g ≠ 5) (hg10 : g ≠ 10) (hg4 : g ≠ 4)
    (hok : (⟨g, cs.length, 0, d, A.es.length, A.es.length, a, 0⟩ : Fr).ok W)
    (h31 : o31 W.x s f v W.t = (o3 (bset (bset s (u 0) (u (A.i + δ))) (u 11) (u 2)) (u g) (u cs.length) (u d) (u a) (u 0), (f, v)))
    (hx : W.x.drop (A.i + δ) = serL cs ++ rest) (hiδ : A.i + δ + (serL cs).length ≤ W.x.length) (hg : g < 2 ^ 40) (hd : d < 2 ^ 40) (ha : a < 2 ^ 40)
    (res : List Nat → List Nat)
    (hfin : ∀ (A' : AS) (s f v : Buf) (r' : Fr) (acc : List Nat), St W s f v A' → A'.ph = 2 → A'.Φ = A.Φ ++ [r'] →
      r'.ok W → r'.g = g → r'.d = d → r'.a = a → r'.c = r'.n → A'.es = A.es ++ acc → A.es.length = r'.vb →
      Reach W (s, f, v) (fun σ => ∃ F2, fin (dsOf W r') A'.F acc = some (F2, strip acc) ∧ Fin W A' A.Φ A.es F2 (res acc) σ)) :
    Reach W (s, f, v) (fun σ => ∃ F' acc F2, lstA W.oc cs (dsOf W ⟨g, cs.length, 0, d, 0, 0, a, 0⟩) A.F [] = some (F', acc) ∧
      fin (dsOf W ⟨g, cs.length, 0, d, 0, 0, a, 0⟩) F' acc = some (F2, strip acc) ∧
      St W σ.1 σ.2.1 σ.2.2 { A with i := A.i + δ + (serL cs).length, F := F2, es := A.es ++ res acc, ph := 1 }) := by
  have hB := hSt.2.2.2.2
  have hcs := serL_len_ge cs
  have hx40 := hB.2.2.2.1
  have hesl := hB.2.2.2.2.2.2.2.1
  apply reach_trans (push_step hSt hp h31 (by omega) hg (by omega) hd ha (by omega))
  intro σ1 h1
  apply reach_trans (lst_sim W cs hsim _ σ1.1 σ1.2.1 σ1.2.2 rest A.Φ ⟨g, cs.length, 0, d, A.es.length, A.es.length, a, 0⟩
    A.es [] h1 rfl rfl hok (by simpa using hg5) (by simpa using hg10) (fun h => absurd h (by simpa using hg4)) (by simp)
    (by simp) (by simp) hx)
  intro σ2 ⟨F', acc', r', hl, haf, hc3, h2⟩
  have hok' := after_ok haf hok
  have hds := after_ds (W := W) haf
  obtain ⟨a1, a2, a4, a5, a6, a7⟩ := haf
  apply reach_mono (hfin _ σ2.1 σ2.2.1 σ2.2.2 r' acc' h2 rfl rfl hok' (by rw [a1]) (by rw [a4]) (by rw [a6])
    (by rw [hc3, a2]; simp) (by simp) (by rw [a5]))
  intro σ3 ⟨F2, hfin2, h3⟩
  refine ⟨F', acc', F2, by exact hl, by rw [hds] at hfin2; exact hfin2, ?_⟩
  unfold Fin at h3
  exact h3
end OwnP
