/- Nano/V2Self/Proof/OwnP25: the def body at the root (no frames): a plain body is a node; a LOOP body pushes the loop
frame and walks its arms from fresh flags = `OwnSpec.defOk`'s body result. -/
import Nano.V2Self.Proof.OwnP24
namespace OwnP
open C OwnSpec ParSpec

/-- `defOk`'s body result -/
def rootR (c : OwnSpec.Cx) (F0 : List Bool) : Nd → Option (List Nat)
  | .loop z s =>
    (chk c z F0).bind fun z0 => (tr z0.1 z0.2).bind fun z1 =>
    (chk c s F0).bind fun s0 => (tr s0.1 s0.2).bind fun s1 => join z1.2 s1.2
  | b => (chk c b F0).bind fun x => (tr x.1 x.2).map fun (y : List Bool × List Nat) => y.2

theorem tr_id (F : List Bool) : ∀ (k : List Nat), (∀ e ∈ k, e ≤ 1) → tr F k = some (F, k)
  | [], _ => rfl
  | e :: k, h => by
    have he := h e (by simp)
    simp only [tr, show e < 4 by omega, he, if_true, tr_id F k (fun x hx => h x (by simp [hx])), Option.map_some]

theorem join_le {a b k : List Nat} (h : join a b = some k) (ha : ∀ e ∈ a, e ≤ 1) (hb : ∀ e ∈ b, e ≤ 1) : ∀ e ∈ k, e ≤ 1 := by
  unfold join at h
  split at h
  · simp at h; subst h; exact hb
  split at h
  · simp at h; subst h; exact ha
  split at h
  · simp at h; subst h; intro e he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    simp only [List.getElem_zipWith]
    exact Nat.max_le.mpr ⟨ha _ (List.getElem_mem _), hb _ (List.getElem_mem _)⟩
  · simp at h

/-- the body walked at the root: phase 1, no frames, entries `e` whose transfer is `defOk`'s result -/
def RootP (W : WCx) (A : AS) (b : Nd) (σ : SB) : Prop :=
  ∃ F' e, (∀ F'' ks, tr F' e = some (F'', ks) → rootR W.oc A.F b = some ks) ∧
    St W σ.1 σ.2.1 σ.2.2 { A with i := A.i + b.ser.length, F := F', es := A.es ++ e, ph := 1 }

theorem sim_root {W : WCx} {b : Nd} (hb : WFN b) (hnl : ∀ z st, b ≠ .loop z st) {A : AS} {s f v : Buf}
    {rest : List UInt64} (hSt : St W s f v A) (hp : A.ph = 0) (hx : W.x.drop A.i = b.ser ++ rest) :
    Reach W (s, f, v) (RootP W A b) := by
  have hd : Reach W (s, f, v) (Done W A b) := by
    cases b with
    | const c => exact sim_const hSt hp c hx
    | loc s0 w0 => exact sim_loc hSt hp hb.1 hb.2 hx
    | bin _ a b => exact sim_bin (sim_all W a hb.1) (sim_all W b hb.2) hSt hp hx
    | ite _ a b t e =>
      exact sim_ite (sim_all W a hb.1) (sim_all W b hb.2.1) (sim_all W t hb.2.2.1) (sim_all W e hb.2.2.2) hSt hp hx
    | letE _ _ a b => exact sim_let (sim_all W a hb.2.2.1) (sim_all W b hb.2.2.2) hb.1 hb.2.1 hSt hp hx
    | pair cs => exact sim_pair (sim_allL W cs hb) hSt hp hx
    | call _ as => exact sim_call (sim_allL W as hb.2) hSt hp hb.1 hx
    | prim _ as => exact sim_prim (sim_allL W as hb.2.2) hSt hp hb.1 hb.2.1 hx
    | loop z st => exact absurd rfl (hnl z st)
    | cont e => exact sim_cont (sim_all W e hb) (fun cs he => by subst he; exact sim_allL W cs hb) hSt hp hx
  apply reach_mono hd
  intro σ ⟨F', en, hc, hσ⟩
  refine ⟨F', en, fun F'' ks htr => ?_, hσ⟩
  have e1 : rootR W.oc A.F b = (chk W.oc b A.F).bind fun x => (tr x.1 x.2).map fun (y : List Bool × List Nat) => y.2 := by
    cases b <;> first | rfl | exact absurd rfl (hnl _ _)
  rw [e1, hc]; simp [htr]

theorem o31_rloop {W : WCx} {s f v : Buf} {A : AS} (hS : RS W s A) (hB : Bnd W A) (hΦ : A.Φ = []) {z st : Nd}
    {rest : List UInt64} (hx : W.x.drop A.i = (Nd.loop z st).ser ++ rest) :
    o31 W.x s f v W.t = (o3 (bset (bset s (u 0) (u (A.i + 1))) (u 11) (u 2)) (u 10) (u 2) (u 0) (u 0) (u 0), (f, v)) := by
  have h0 := hdr0 hB hx (k := 0) (by simp [Nd.ser])
  rw [show u A.i + u 0 = u A.i from u_add _ 0] at h0
  simp only [Nd.ser, List.getD_cons_zero] at h0
  have r4 := (regs hS).2.2.2.1
  rw [hΦ] at r4
  unfold o31
  have r0 := (regs hS).1
  simp only [lit] at r0 h0 r4 ⊢
  simp only [r0, h0, r4, u_add]
  simp only [show (u 10 == u 1) = false from rfl, show (u 10 == u 2) = false from rfl, show (u 10 == u 3) = false from rfl,
    show (u 10 == u 4) = false from rfl, show (u 10 == u 5) = false from rfl, show (u 10 == u 6) = false from rfl,
    show (u 10 == u 8) = false from rfl, show (u 10 == u 9) = false from rfl, show (u 10 == u 10) = true from rfl,
    show (u [].length == u 0) = true from rfl, Bool.false_eq_true, if_false, if_true]

theorem sim_rloop {W : WCx} {z st : Nd} (hz : WFN z) (hs : WFN st) {A : AS} {s f v : Buf} {rest : List UInt64}
    (hSt : St W s f v A) (hp : A.ph = 0) (hΦ : A.Φ = []) (hF : A.F = List.replicate W.ns false)
    (hx : W.x.drop A.i = (Nd.loop z st).ser ++ rest) : Reach W (s, f, v) (RootP W A (.loop z st)) := by
  have hS := hSt.1; have hB := hSt.2.2.2.2
  have hxl := drop_len hx (by simp [Nd.ser]); simp only [Nd.ser, List.length_cons, List.length_append] at hxl
  have hx40 := hB.2.2.2.1
  have hesl := hB.2.2.2.2.2.2.2.1
  apply reach_trans (push_step hSt hp (o31_rloop hS hB hΦ (f := f) (v := v) hx) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega))
  intro σ1 h1
  apply reach_trans (ph2_loop h1 rfl (Φ0 := A.Φ) rfl rfl (by simp))
  intro σ2 h2
  have hxz : W.x.drop (A.i + 1) = z.ser ++ (st.ser ++ rest) :=
    drop_hdr (hdr := [10]) (by simpa [Nd.ser] using hx) rfl
  apply reach_trans (sim_all W z hz _ σ2.1 σ2.2.1 σ2.2.2 _ h2 rfl (by simp) hxz)
  intro σ3 ⟨Fz0, ez, hcz, h3⟩
  apply reach_trans (ph1_loop_z h3 rfl (Φ0 := A.Φ) rfl (by simp [Fr.set]) (by simp [Fr.set]) (pre := A.es) (ez := ez) rfl
    (by simp [Fr.set]))
  intro σ4 ⟨Fz, kz, htz, h4⟩
  have hkz := tr_len' _ _ _ _ htz
  apply reach_trans (ph2_loop h4 rfl (Φ0 := A.Φ) rfl (by simp [Fr.set]) (by simp [Fr.set]))
  intro σ5 h5
  have hxs : W.x.drop (A.i + 1 + z.ser.length) = st.ser ++ rest := by rw [← List.drop_drop, hxz, List.drop_left]
  apply reach_trans (sim_all W st hs _ σ5.1 σ5.2.1 σ5.2.2 _ h5 rfl (by simp) hxs)
  intro σ6 ⟨Fs0, es0, hcs, h6⟩
  apply reach_trans (ph1_loop_s h6 rfl (Φ0 := A.Φ) rfl (by simp [Fr.set]) (by simp [Fr.set]) (pre := A.es) (kz := kz)
    (es := es0) (by simp) (by simp [Fr.set]) (by simp [Fr.set]; omega) (by simp [Fr.set]))
  intro σ7 ⟨Fs, ks, k, hts, hj, h7⟩
  have hks := tr_len' _ _ _ _ hts
  apply reach_mono (ph2_pop h7 rfl (Φ0 := A.Φ) rfl (by simp [Fr.set]) (by simp [Fr.set]))
  intro σ8 h8
  refine ⟨Fs, k, fun F'' ks' htr => ?_, ?_⟩
  · have hk1 := join_le hj hkz.2 hks.2
    rw [tr_id Fs k hk1] at htr; simp at htr; obtain ⟨-, rfl⟩ := htr
    have hcz' : chk W.oc z (List.replicate W.ns false) = some (Fz0, ez) := hcz
    have hcs' : chk W.oc st (List.replicate W.ns false) = some (Fs0, es0) := hcs
    simp only [rootR, hF, hcz', Option.bind_some, htz, hcs', hts, hj]
  · have e1 : A.i + (Nd.loop z st).ser.length = A.i + 1 + z.ser.length + st.ser.length := by simp [Nd.ser]; omega
    rw [e1, hΦ]; rw [hΦ] at h8; exact h8

end OwnP
