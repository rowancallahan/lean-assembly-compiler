/- Nano/V2Self/Proof/MainConvX2: the cap half, layer 2 — when `Sem` stops at a full buffer (`.error .cap`), E's kinded
semantics reports `cap` given enough room (`ExC`).  The run up to the failing push is an ordinary successful run (the
success half: `NodeEx`, `NodeOK`), then the push's capacity check fails the same way. -/
import Nano.V2Self.Proof.MainConvX1

namespace NanoMain
open Templates

/-- with enough room, `S` stops with `cap` -/
def ExC {α : Type} (S : Nat → Hp → Except Fail α) (H : Hp) : Prop :=
  ∃ N, ∀ sp, H.top + N ≤ sp → sp < 2 ^ 62 → S sp H = .error .cap

theorem ok_of_toO {α : Type} {x : Except Fail α} {r : α} (h : toO x = some r) : x = .ok r := by
  cases x <;> simp_all [toO]

theorem exc_left {α β : Type} {S : Nat → Hp → Except Fail α} {f : Nat → α → Except Fail β} {H : Hp} (h : ExC S H) :
    ExC (fun sp H => (S sp H).bind (f sp)) H := by
  obtain ⟨N, hN⟩ := h; exact ⟨N, fun sp a b => by dsimp only; rw [hN sp a b]; rfl⟩

theorem exc_map {α β : Type} {S : Nat → Hp → Except Fail α} {f : α → β} {H : Hp} (h : ExC S H) :
    ExC (fun sp H => (S sp H).map f) H := by
  obtain ⟨N, hN⟩ := h; exact ⟨N, fun sp a b => by dsimp only; rw [hN sp a b]; rfl⟩

theorem exc_of_eq {α : Type} {S S' : Nat → Hp → Except Fail α} {H : Hp} (e : ∀ sp, S sp H = S' sp H) (h : ExC S H) :
    ExC S' H := by
  obtain ⟨N, hN⟩ := h; exact ⟨N, fun sp a b => by rw [← e]; exact hN sp a b⟩

/-- sequencing: `S` succeeds (success half), then `T` stops with `cap` -/
theorem exc_seq {α β : Type} {S : Nat → Hp → Except Fail α} {T : α → Nat → Hp → Except Fail β} {H : Hp} (c : Nat)
    (getH : α → Hp) (hS : Ex (fun sp H => toO (S sp H)) H) (hM : Mo (fun sp H => toO (S sp H)))
    (hT : ∀ sp r1, sp < 2 ^ 62 → S sp H = .ok r1 → ExC (fun sp' (_ : Hp) => T r1 sp' (getH r1)) (getH r1)) :
    ExC (fun sp H => (S sp H).bind fun r1 => T r1 (sp - c) (getH r1)) H := by
  obtain ⟨Na, ha⟩ := hS
  by_cases h0 : H.top + Na < 2 ^ 62
  · obtain ⟨r1, h1⟩ := ha (H.top + Na) (Nat.le_refl _) h0
    obtain ⟨Nb, hb⟩ := hT _ r1 h0 (ok_of_toO h1)
    refine ⟨Na + ((getH r1).top + Nb + c), fun sp hs hs' => ?_⟩
    have e1 := ok_of_toO (hM _ sp H r1 h1 (by omega) hs')
    simp only [e1]
    exact hb (sp - c) (by omega) (by omega)
  · exact ⟨Na, fun sp hs hs' => absurd (Nat.lt_of_le_of_lt hs hs') h0⟩

theorem val_cap {r : Out} (h : val r = .error .cap) : r = .error .cap := by
  unfold val at h; split at h <;> simp_all

/-! ## the kinded templates and E's semantics -/
section
variable (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n))
include hf

theorem svF_ok {e : ParSpec.Nd} {env : Env} {sp : Nat} {H : Hp} {r : List UInt64 × Hp} (h : sv K e env sp H = some r) :
    svF K fsX e env sp H = .ok r := by
  rw [← oW_sv K fsX hf] at h; exact ok_of_toO h

theorem svLF_ok {cs : List ParSpec.Nd} {env : Env} {sp : Nat} {H : Hp} {r : List UInt64 × Hp}
    (h : svL K cs env sp H = some r) : svLF K fsX cs env sp H = .ok r := by
  rw [← oW_svL K fsX hf] at h; exact ok_of_toO h

theorem svF_eq (e : ParSpec.Nd) (env : Env) (sp : Nat) (H : Hp) : toO (svF K fsX e env sp H) = sv K e env sp H :=
  congrFun (congrFun (congrFun (oW_sv K fsX hf e) env) sp) H
theorem svLF_eq (cs : List ParSpec.Nd) (env : Env) (sp : Nat) (H : Hp) :
    toO (svLF K fsX cs env sp H) = svL K cs env sp H :=
  congrFun (congrFun (congrFun (oW_svL K fsX hf cs) env) sp) H
theorem svF_ex {e : ParSpec.Nd} {env : Env} {H : Hp} (h : Ex (sv K e env) H) : Ex (fun sp H => toO (svF K fsX e env sp H)) H :=
  ex_of_eq (fun sp => (svF_eq K fsX hf e env sp H).symm) h
theorem svF_mo' (hFM : ∀ i args, Mo (K.fs i args)) (e : ParSpec.Nd) (env : Env) :
    Mo (fun sp H => toO (svF K fsX e env sp H)) := by
  intro sp sp' H r h h1 h2; dsimp only at h ⊢; rw [svF_eq K fsX hf] at h ⊢; exact sv_mo K hFM e env sp sp' H r h h1 h2
theorem svLF_ex {cs : List ParSpec.Nd} {env : Env} {H : Hp} (h : Ex (svL K cs env) H) :
    Ex (fun sp H => toO (svLF K fsX cs env sp H)) H :=
  ex_of_eq (fun sp => (svLF_eq K fsX hf cs env sp H).symm) h
theorem svLF_mo' (hFM : ∀ i args, Mo (K.fs i args)) (cs : List ParSpec.Nd) (env : Env) :
    Mo (fun sp H => toO (svLF K fsX cs env sp H)) := by
  intro sp sp' H r h h1 h2; dsimp only at h ⊢; rw [svLF_eq K fsX hf] at h ⊢; exact svL_mo K hFM cs env sp sp' H r h h1 h2
theorem pairF_eq (a b : ParSpec.Nd) (env : Env) (sp : Nat) (H : Hp) :
    toO (pairF 1 (svF K fsX a) (svF K fsX b) env sp H) = pairS 1 (sv K a) (sv K b) env sp H := by
  rw [← oW_sv K fsX hf a, ← oW_sv K fsX hf b, ← oW_pair]; rfl
theorem pairF_ex {a b : ParSpec.Nd} {env : Env} {H : Hp} (h : Ex (pairS 1 (sv K a) (sv K b) env) H) :
    Ex (fun sp H => toO (pairF 1 (svF K fsX a) (svF K fsX b) env sp H)) H := by
  exact ex_of_eq (fun sp => (pairF_eq K fsX hf a b env sp H).symm) h
theorem pairF_mo' (hFM : ∀ i args, Mo (K.fs i args)) (a b : ParSpec.Nd) (env : Env) :
    Mo (fun sp H => toO (pairF 1 (svF K fsX a) (svF K fsX b) env sp H)) := by
  intro sp sp' H r h h1 h2; dsimp only at h ⊢; rw [pairF_eq K fsX hf] at h ⊢; exact pairS_mo (sv_mo K hFM a) (sv_mo K hFM b) env sp sp' H r h h1 h2
end

/-- the value-mode cap claim -/
def NodeExC (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (oc : OwnSpec.Cx) (D : List Sig) (e : ParSpec.Nd) : Prop :=
  CtxOK cx D → (∀ s, oc.K.getD s 0 ≤ 2) → ∀ Γ ks F F' es env ew σ H, TyN D Γ none e ks →
    OwnSpec.chk oc e F = some (F', es) → EnvI σ oc.K F Γ env ew → AHeap K.hb K.κ H σ → H.top % 8 = 0 → K.hb ≤ H.top →
    R2 oc.K F → ev cx e env = .error .cap → ExC (svF K fsX e ew) H

theorem exc_const (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (oc : OwnSpec.Cx) (D : List Sig) (c : UInt64) :
    NodeExC cx K fsX oc D (.const c) := by
  intro _ _ Γ ks F F' es env ew σ H _ _ _ _ _ _ _ hev; simp [ev] at hev

theorem exc_loc (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (oc : OwnSpec.Cx) (D : List Sig) (s w : Nat) :
    NodeExC cx K fsX oc D (.loc s w) := by
  intro _ _ Γ ks F F' es env ew σ H _ _ _ _ _ _ _ hev
  simp only [ev] at hev; split at hev <;> simp_all

theorem err_inj {e : Stop} (h : (Except.error e : Except Stop (List W)) = .error .cap) : e = .cap := by cases h; rfl

theorem pairF_excL {wa : Nat} {SA SB : SemWX} {env : Env} {H : Hp} (h : ExC (SA env) H) : ExC (pairF wa SA SB env) H := by
  obtain ⟨N, hN⟩ := h; exact ⟨N, fun sp a b => by simp only [pairF, hN sp a b]; rfl⟩

theorem pairF_excR {wa : Nat} {SA SB : SemWX} {env : Env} {H : Hp} (hA : Ex (fun sp H => toO (SA env sp H)) H)
    (hM : Mo (fun sp H => toO (SA env sp H)))
    (hB : ∀ sp r1, sp < 2 ^ 62 → SA env sp H = .ok r1 → ExC (SB env) r1.2) : ExC (pairF wa SA SB env) H :=
  exc_seq (T := fun (r1 : List UInt64 × Hp) sp' H' =>
      (SB env sp' H').bind fun (r2 : List UInt64 × Hp) => (.ok (r1.1 ++ r2.1, r2.2) : Except Fail (List UInt64 × Hp)))
    (8 * wa) Prod.snd hA hM
    (fun sp r1 h0 h1 => by obtain ⟨N, hN⟩ := hB sp r1 h0 h1; exact ⟨N, fun sp' a b => by simp only [hN sp' a b]; rfl⟩)

/-- the operand pair of BIN / IF stops with `cap` when one of the operands does -/
theorem operands_exc {cx : Ctx} {K : SC} {fsX : Nat → SemDX} (hf : ∀ n, K.fs n = oD (fsX n)) {oc : OwnSpec.Cx}
    {D : List Sig} {a b : ParSpec.Nd}
    (hNa : NodeOK cx K oc D a) (hEa : NodeEx cx K oc D a) (hCa : NodeExC cx K fsX oc D a) (hCb : NodeExC cx K fsX oc D b)
    (hC : CtxOK cx D) (hK2 : ∀ s, oc.K.getD s 0 ≤ 2) (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args))
    {Γ : List (Option Kd)} {F : List Bool} {env : List W} {ew : Env} {σ : AH} {H : Hp}
    (ta : TyN D Γ none a [.w]) (tb : TyN D Γ none b [.w]) {a0 b0 : List Bool × List Nat}
    (hca : OwnSpec.chk oc a F = some a0) (hcb : OwnSpec.chk oc b a0.1 = some b0)
    (hE : EnvI σ oc.K F Γ env ew) (hA : AHeap K.hb K.κ H σ) (h8 : H.top % 8 = 0) (hhb : K.hb ≤ H.top) (hr : R2 oc.K F)
    (hev : val (ev cx a env) = .error .cap ∨ ∃ va, val (ev cx a env) = .ok va ∧ val (ev cx b env) = .error .cap) :
    ExC (pairF 1 (svF K fsX a) (svF K fsX b) ew) H := by
  rcases hev with ea | ⟨va, ea, eb⟩
  · exact pairF_excL (hCa hC hK2 Γ _ F _ _ env ew σ H ta hca hE hA h8 hhb hr (val_cap ea))
  · refine pairF_excR (svF_ex K fsX hf (hEa hC hK2 Γ _ F _ _ env ew σ H va ta hca hE hA h8 hhb hr (val_ok_of ea)))
        (svF_mo' K fsX hf hFM a ew) fun sp r1 _ h1 => ?_
    have h1' : sv K a ew sp H = some r1 := by rw [← svF_eq K fsX hf, h1]; rfl
    obtain ⟨σ1, v1, -, hA1, -, hE1, -, -, h81, hb1, -, -, -⟩ :=
      hNa hC hK2 Γ _ F _ _ env ew σ sp H r1.1 r1.2 ta hca hE hA h8 hhb hr h1'
    exact hCb hC hK2 Γ _ _ _ _ env ew σ1 r1.2 tb hcb hE1 hA1 h81 hb1 (hr.keep (chk_keep hK2 hW ta rfl _ _ _ hca).1)
      (val_cap eb)

theorem exc_bind_of {α β : Type} {S : Nat → Hp → Except Fail α} {T : Nat → Hp → Except Fail β} {g : Nat → α → Except Fail β}
    {H : Hp} (h : ExC S H) (e : ∀ sp, T sp H = (S sp H).bind (g sp)) : ExC T H := by
  obtain ⟨N, hN⟩ := h; exact ⟨N, fun sp a b => by rw [e, hN sp a b]; rfl⟩

/-- where a BIN / IF head's cap comes from -/
theorem head_cap {cx : Ctx} {a b : ParSpec.Nd} {env : List W} {β : Type}
    {k : List W → List W → Except Stop β} (hk : ∀ x y, k x y ≠ .error .cap)
    (h : (do let x ← val (ev cx a env); let y ← val (ev cx b env); k x y) = .error .cap) :
    val (ev cx a env) = .error .cap ∨ ∃ va, val (ev cx a env) = .ok va ∧ val (ev cx b env) = .error .cap := by
  simp only [bind, Except.bind] at h
  cases ea : val (ev cx a env) with
  | error e => rw [ea] at h; cases h; exact Or.inl rfl
  | ok va =>
    cases eb : val (ev cx b env) with
    | error e => rw [ea, eb] at h; cases h; exact Or.inr ⟨va, rfl, rfl⟩
    | ok vb => rw [ea, eb] at h; exact absurd h (hk va vb)

theorem exc_bin (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args)) (op : Nat) (a b : ParSpec.Nd) (hNa : NodeOK cx K oc D a)
    (hEa : NodeEx cx K oc D a) (hCa : NodeExC cx K fsX oc D a) (hCb : NodeExC cx K fsX oc D b) :
    NodeExC cx K fsX oc D (.bin op a b) := by
  intro hC hK2 Γ ks F F' es env ew σ H hT hc hE hA h8 hhb hr hev
  cases hT with
  | bin o1 o2 ta tb =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨a0, hca, b0, hcb, y, hy, -⟩ := hc
    simp only [ev] at hev
    have hh := head_cap (fun x y => by
      intro h
      split at h
      · simp only [bind, Except.bind] at h; split at h
        · rename_i e he; cases h; unfold binop at he; split at he <;> cases he
        · cases h
      · cases h) hev
    have hp := operands_exc hf hNa hEa hCa hCb hC hK2 hW hFM ta tb hca hcb hE hA h8 hhb hr hh
    simp only [svF]
    exact exc_bind_of hp (fun sp => rfl)

theorem exc_ite (cx : Ctx) (K : SC) (fsX : Nat → SemDX) (hf : ∀ n, K.fs n = oD (fsX n)) (oc : OwnSpec.Cx) (D : List Sig)
    (hW : RsW oc) (hFM : ∀ i args, Mo (K.fs i args)) (c : Nat) (a b t e : ParSpec.Nd) (hNa : NodeOK cx K oc D a)
    (hNb : NodeOK cx K oc D b) (hEa : NodeEx cx K oc D a) (hEb : NodeEx cx K oc D b) (hCa : NodeExC cx K fsX oc D a)
    (hCb : NodeExC cx K fsX oc D b) (hCt : NodeExC cx K fsX oc D t) (hCe : NodeExC cx K fsX oc D e) :
    NodeExC cx K fsX oc D (.ite c a b t e) := by
  intro hC hK2 Γ ks F F' es env ew σ H hT hc hE hA h8 hhb hr hev
  cases hT with
  | ite hc12 ta tb tt te =>
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨a0, hca, b0, hcb, y, hy, t0, h1, t1, h2, e0, h3, e1, h4, k, hj, hk⟩ := hc
    have hry : R2 oc.K y.1 := by
      obtain ⟨ka, ta'⟩ := chk_keep hK2 hW ta rfl _ _ _ hca
      obtain ⟨kb, tb'⟩ := chk_keep hK2 hW tb rfl _ _ _ hcb
      exact hr.keep ((ka.trans kb).trans (two_keep ta' tb' hy))
    have hev0 := hev
    simp only [ev, bind, Except.bind] at hev
    simp only [svF]
    cases ea : val (ev cx a env) with
    | error e' =>
      rw [ea] at hev; cases hev
      exact exc_bind_of (operands_exc hf hNa hEa hCa hCb hC hK2 hW hFM ta tb hca hcb hE hA h8 hhb hr (Or.inl ea))
        (fun sp => rfl)
    | ok va =>
      cases eb : val (ev cx b env) with
      | error e' =>
        rw [ea, eb] at hev; cases hev
        exact exc_bind_of (operands_exc hf hNa hEa hCa hCb hC hK2 hW hFM ta tb hca hcb hE hA h8 hhb hr
          (Or.inr ⟨va, ea, eb⟩)) (fun sp => rfl)
      | ok vb =>
        have hp := operands_ex hNa hEa hEb hC hK2 hW hFM ta tb hca hcb hE hA h8 hhb hr (val_ok_of ea) (val_ok_of eb)
        have := exc_seq (T := fun r1 sp' H' => match r1.1 with
            | [x, z] => if cmpF c x z then svF K fsX t ew sp' H' else svF K fsX e ew sp' H' | _ => .error .stuck) 0
          Prod.snd (pairF_ex K fsX hf hp) (pairF_mo' K fsX hf hFM a b ew) (fun sp r1 _ hr1 => by
            have hr1' : pairS 1 (sv K a) (sv K b) ew sp H = some (r1.1, r1.2) := by
              rw [← pairF_eq K fsX hf, hr1]; rfl
            obtain ⟨σ2, x1, x2, eva, evb, hu, hA2, hE2, -, -, h82, hb2, -⟩ := operands2 hNa hNb hC hK2 hW ta tb hca hcb hy
              hE hA h8 hhb hr hr1'
            have hev' : ev cx (ParSpec.Nd.ite c a b t e) env =
                (if (if c = 1 then x1 = x2 else x1 < x2) then ev cx t env else ev cx e env) := by
              rcases hc12 with rfl | rfl <;> simp [ev, eva, evb, val, bind, Except.bind]
            rw [hev'] at hev0
            simp only [hu]
            by_cases hcmp : cmpF c x1 x2
            · rw [if_pos ((cmpF_iff c hc12 x1 x2).1 hcmp)] at hev0
              obtain ⟨N, hN⟩ := hCt hC hK2 Γ ks _ _ _ env ew σ2 r1.2 tt h1 hE2 hA2 h82 hb2 hry hev0
              exact ⟨N, fun sp' a b => by simp only [hcmp, if_true]; exact hN sp' a b⟩
            · rw [if_neg (fun h => hcmp ((cmpF_iff c hc12 x1 x2).2 h))] at hev0
              obtain ⟨N, hN⟩ := hCe hC hK2 Γ ks _ _ _ env ew σ2 r1.2 te h3 hE2 hA2 h82 hb2 hry hev0
              exact ⟨N, fun sp' a b => by simp only [hcmp, if_false]; exact hN sp' a b⟩)
        exact exc_of_eq (fun sp => by simp only [Nat.sub_zero]; rfl) this

end NanoMain
