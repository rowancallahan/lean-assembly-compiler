/- Nano/Ownership/OwnP21: LOOP below a frame is an error; every well-formed node simulates `OwnSpec.chk`. -/
import Nano.Ownership.OwnP20
namespace OwnP
open C OwnSpec ParSpec

theorem sim_loop_in {W : WCx} {z st : Nd} {A : AS} {s f v : Buf} {rest : List UInt64} (hSt : St W s f v A)
    (hp : A.ph = 0) (hne : A.Φ ≠ []) (hx : W.x.drop A.i = (Nd.loop z st).ser ++ rest) :
    Reach W (s, f, v) (Done W A (.loop z st)) := by
  obtain ⟨hS, hF, hV, hT, hB⟩ := hSt
  obtain ⟨Φ0, r, hΦ⟩ := (List.eq_nil_or_concat A.Φ).resolve_left hne
  rw [List.concat_eq_append] at hΦ
  apply reach_one hS; right
  rw [stp_eq, o30_ph0 hS hp]
  have h0 := hdr0 hB hx (k := 0) (by simp [Nd.ser])
  rw [show u A.i + u 0 = u A.i from u_add _ 0] at h0
  simp only [Nd.ser, List.getD_cons_zero] at h0
  have hn := nfr_ne hS hB hΦ
  unfold o31; generalize hN : 16777216 = N; revert N; apply id; intro N hN
  have r0 := (regs hS).1
  simp only [lit] at r0 h0 hn ⊢
  simp only [r0, h0, hn]
  simp only [show (u 10 == u 1) = false from rfl, show (u 10 == u 2) = false from rfl, show (u 10 == u 3) = false from rfl,
    show (u 10 == u 4) = false from rfl, show (u 10 == u 5) = false from rfl, show (u 10 == u 6) = false from rfl,
    show (u 10 == u 8) = false from rfl, show (u 10 == u 9) = false from rfl, show (u 10 == u 10) = true from rfl,
    Bool.false_eq_true, if_false, if_true]
  exact err_o5 (by have := hS.1; omega)

mutual
/-- well-formed nodes: header numbers in range, primitive arities -/
def WFN : Nd → Prop
  | .const _ => True
  | .loc s w => s < 2 ^ 64 ∧ w < 2 ^ 64
  | .bin _ a b => WFN a ∧ WFN b
  | .ite _ a b t e => WFN a ∧ WFN b ∧ WFN t ∧ WFN e
  | .letE s w v b => s < 2 ^ 20 ∧ w < 2 ^ 20 ∧ WFN v ∧ WFN b
  | .pair cs => WFL cs
  | .call i as => i < 2 ^ 64 ∧ WFL as
  | .prim p as => p < 2 ^ 64 ∧ primAr p as ∧ WFL as
  | .loop _ _ => True
  | .cont e => WFN e
def WFL : List Nd → Prop
  | [] => True
  | n :: r => WFN n ∧ WFL r
end

mutual
theorem sim_all (W : WCx) : (n : Nd) → WFN n → SimOK W n
  | .const c, _ => fun _ _ _ _ _ hSt hp _ hx => sim_const hSt hp c hx
  | .loc s w, h => fun _ _ _ _ _ hSt hp _ hx => sim_loc hSt hp h.1 h.2 hx
  | .bin _ a b, h => fun _ _ _ _ _ hSt hp _ hx => sim_bin (sim_all W a h.1) (sim_all W b h.2) hSt hp hx
  | .ite _ a b t e, h => fun _ _ _ _ _ hSt hp _ hx =>
    sim_ite (sim_all W a h.1) (sim_all W b h.2.1) (sim_all W t h.2.2.1) (sim_all W e h.2.2.2) hSt hp hx
  | .letE _ _ a b, h => fun _ _ _ _ _ hSt hp _ hx => sim_let (sim_all W a h.2.2.1) (sim_all W b h.2.2.2) h.1 h.2.1 hSt hp hx
  | .pair cs, h => fun _ _ _ _ _ hSt hp _ hx => sim_pair (sim_allL W cs h) hSt hp hx
  | .call _ as, h => fun _ _ _ _ _ hSt hp _ hx => sim_call (sim_allL W as h.2) hSt hp h.1 hx
  | .prim _ as, h => fun _ _ _ _ _ hSt hp _ hx => sim_prim (sim_allL W as h.2.2) hSt hp h.1 h.2.1 hx
  | .loop _ _, _ => fun _ _ _ _ _ hSt hp hne hx => sim_loop_in hSt hp hne hx
  | .cont e, h => fun _ _ _ _ _ hSt hp _ hx =>
    sim_cont (sim_all W e h) (fun cs he => by subst he; exact sim_allL W cs h) hSt hp hx
theorem sim_allL (W : WCx) : (cs : List Nd) → WFL cs → ∀ c ∈ cs, SimOK W c
  | [], _ => fun _ hc => absurd hc (List.not_mem_nil)
  | n :: r, h => fun c hc => by
    rcases List.mem_cons.mp hc with heq | hc
    · exact heq ▸ sim_all W n h.1
    · exact sim_allL W r h.2 c hc
end

end OwnP
