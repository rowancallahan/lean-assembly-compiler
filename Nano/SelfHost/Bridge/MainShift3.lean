/- Nano/SelfHost/Bridge/MainShift3: shift invariance, layer 3 — environments related through the kinds `Γ`, and the
node theorem: for a well-kinded node, E's kinded semantics at `hb` and at `hb + δ` simulate each other. -/
import Nano.SelfHost.Bridge.MainShift2

namespace NanoMain
open Templates

/-- slot words related by their known kinds -/
def ER (δ : Nat) (Γ : List (Option Kd)) (env env' : Env) : Prop :=
  ∀ k o, Γ[k]? = some (some o) → WR δ o (env k) (env' k)

theorem LR.get {δ : Nat} : ∀ {ks r r'}, LR δ ks r r' → ∀ i (hi : i < ks.length), WR δ ks[i] (r.getD i 0) (r'.getD i 0)
  | k :: ks, x :: r, x' :: r', h, 0, _ => by simpa using h.1
  | k :: ks, x :: r, x' :: r', h, i + 1, hi => by simpa using LR.get h.2 i (by simpa using hi)
  | [], _, _, _, i, hi => absurd hi (by simp)
  | _ :: _, [], _, h, _, _ | _ :: _, _ :: _, [], h, _, _ => by simp [LR] at h

theorem known_getS {Γ : List (Option Kd)} {s w : Nat} {ks : List Kd} (h : known Γ s w ks) (i : Nat) (hi : i < ks.length) :
    Γ[s + i]? = some (some ks[i]) := by
  obtain ⟨h1, h2⟩ := h
  have hl : ks.length = w := by have := congrArg List.length h2; simp at this; omega
  have := congrArg (·[i]?) h2
  simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_map] at this
  rw [if_pos (by omega)] at this
  rw [this, List.getElem?_eq_getElem hi]; rfl

theorem er_set {δ : Nat} {Γ : List (Option Kd)} {env env' : Env} {s : Nat} {vs : List Kd} {r r' : List UInt64}
    (he : ER δ Γ env env') (hr : LR δ vs r r') (hs : s + vs.length ≤ Γ.length) :
    ER δ (setK Γ s vs) (setW env s vs.length r) (setW env' s vs.length r') := by
  intro k o hk
  simp only [setK] at hk
  simp only [setW]
  by_cases h1 : s ≤ k ∧ k < s + vs.length
  · rw [if_pos h1, if_pos h1]
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)] at hk
    simp only [List.length_take, List.getElem?_map] at hk
    rw [show k - min s Γ.length = k - s by omega] at hk
    rw [List.getElem?_eq_getElem (show k - s < vs.length by omega)] at hk
    simp at hk; subst hk
    exact LR.get hr (k - s) (by omega)
  · rw [if_neg h1, if_neg h1]
    apply he k o
    by_cases h2 : k < s
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega),
        List.getElem?_take_of_lt h2] at hk; exact hk
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop] at hk
      simp only [List.length_append, List.length_take, List.length_map] at hk
      rw [show s + vs.length + (k - (min s Γ.length + vs.length)) = k by omega] at hk; exact hk

theorem er_arg {δ : Nat} {ps : List Kd} {n : Nat} {args args' : List UInt64} (h : LR δ ps args args') :
    ER δ (ps.map some ++ List.replicate n none) (argEnv ps.length args) (argEnv ps.length args') := by
  intro k o hk
  simp only [argEnv]
  by_cases hk2 : k < ps.length
  · rw [if_pos hk2, if_pos hk2]
    rw [List.getElem?_append_left (by simpa using hk2), List.getElem?_map, List.getElem?_eq_getElem hk2] at hk
    simp at hk; subst hk
    exact LR.get h k hk2
  · rw [List.getElem?_append_right (by simpa using hk2)] at hk
    simp [List.getElem?_replicate] at hk

/-! ## `wd` does not see the heap base -/
mutual
theorem wd_hb (K : SC) (h : Nat) : ∀ e : ParSpec.Nd, wd { K with hb := h } e = wd K e
  | .ite _ _ _ t _ => by simp only [wd]; rw [wd_hb K h t]
  | .letE _ _ _ b => by simp only [wd]; rw [wd_hb K h b]
  | .pair cs => by simp only [wd]; rw [wdL_hb K h cs]
  | .const _ | .loc _ _ | .bin _ _ _ | .call _ _ | .prim _ _ | .loop _ _ | .cont _ => by simp only [wd]
theorem wdL_hb (K : SC) (h : Nat) : ∀ cs : List ParSpec.Nd, wdL { K with hb := h } cs = wdL K cs
  | [] => by simp only [wdL]
  | c :: cs => by simp only [wdL]; rw [wd_hb K h c, wdL_hb K h cs]
end

theorem kinds_cases' {ps rs : List Kd} {p : Nat} (h : primK p ps = some rs) :
    (p = 1 ∧ ps = []) ∨ (p = 2 ∧ ps = [.w]) ∨ (p = 3 ∧ ps = []) ∨ (p = 4 ∧ ps = [.b, .w]) ∨ (p = 5 ∧ ps = []) ∨
    (p = 6 ∧ ps = [.b]) ∨ (p = 7 ∧ ps = [.b, .w]) ∨ (p = 8 ∧ ps = [.b, .w, .w]) ∨ (p = 9 ∧ ps = [.b, .w]) := by
  unfold primK at h; split at h <;> simp_all

/-- a value-mode expression's kinded tail semantics is its value semantics, exiting -/
theorem stF_none' (K : SC) (fsX : Nat → SemDX) {D : List Sig} : ∀ {Γ S e ks}, TyN D Γ S e ks → S = none →
    ∀ env sp H, stF K fsX e env sp H = exitF (svF K fsX e) env sp H
  | _, _, _, _, .const, _, _, _, _ => by simp only [stF]
  | _, _, _, _, .loc _, _, _, _, _ => by simp only [stF]
  | _, _, _, _, .bin _ _ _ _, _, _, _, _ => by simp only [stF]
  | _, _, _, _, .pair _, _, _, _, _ => by simp only [stF]
  | _, _, _, _, .call _ _, _, _, _, _ => by simp only [stF]
  | _, _, _, _, .prim _ _ _, _, _, _, _ => by simp only [stF]
  | _, _, _, _, .cont _, hS, _, _, _ => by cases hS
  | _, _, _, _, .ite (c := c) (a := a) (b := b) (t := t) (e := e) _ _ _ tt te, hS, env, sp, H => by
    simp only [stF, svF, ifTF, ifF, exitF]
    cases h : pairF 1 (svF K fsX a) (svF K fsX b) env sp H with
    | error x => rfl
    | ok r =>
      simp only [Except.bind]
      split
      · split
        · rw [stF_none' K fsX tt hS env sp]; rfl
        · rw [stF_none' K fsX te hS env sp]; rfl
      · rfl
  | _, _, _, _, .letE (s := s) (w := w) (v := v) (b := b) _ _ _ _ tb, hS, env, sp, H => by
    simp only [stF, svF, letTF, letF, exitF]
    cases h : svF K fsX v env sp H with
    | error x => rfl
    | ok r => simp only [Except.bind]; rw [stF_none' K fsX tb hS _ sp]; rfl

/-- the callees simulate each other on their signatures -/
def CallSh (δ hb : Nat) (D : List Sig) (fsX fsX' : Nat → SemDX) : Prop :=
  ∀ i ps rs, D[i]? = some (ps, rs) → SimD δ hb ps rs (fsX i) (fsX' i)

section
variable {δ : Nat} (K : SC) {D : List Sig} {fsX fsX' : Nat → SemDX} (hδ8 : δ % 8 = 0) (hδ : δ ≤ 2 ^ 32)
  (hC : CallSh δ K.hb D fsX fsX')
include hδ8 hδ hC

mutual
/-- **the node theorem**: a well-kinded node simulates itself across the shift -/
theorem sv_sh : ∀ {Γ S e ks}, TyN D Γ S e ks →
    Sim δ K.hb (ER δ Γ) (LR δ ks) (svF K fsX e) (svF { K with hb := K.hb + δ } fsX' e)
  | _, _, _, _, .const => by simp only [svF]; exact leafF_sim (fun _ _ _ => rfl)
  | Γ, _, _, ks, .loc (s := s) (w := w) hk => by
    simp only [svF]
    have hl : ks.length = w := by have := congrArg List.length hk.2; have := hk.1; simp at *; omega
    exact localF_sim w s ks hl (fun i hi env env' he => he (s + i) _ (known_getS hk i (by omega)))
  | _, _, _, _, .bin _ _ ta tb => by
    simp only [svF]
    exact fin2F_sim (pairF_sim (sv_sh ta) (sv_sh tb)) (alu_sh _)
  | _, _, _, _, .ite _ ta tb tt te => by
    simp only [svF]
    exact ifF_sim (pairF_sim (sv_sh ta) (sv_sh tb)) (sv_sh tt) (sv_sh te)
  | Γ, _, _, _, .letE (s := s) (vs := vs) hv hlen hsl _ tb => by
    simp only [svF]
    exact letF_sim (sv_sh hv) (sv_sh tb) (fun env env' r r' he hr => by
      have h2 : s + vs.length ≤ Γ.length := by rw [hlen]; exact hsl
      have := er_set he hr h2; rw [hlen] at this; exact this)
  | _, _, _, _, .pair tl => by simp only [svF]; exact svL_sh tl
  | _, _, _, _, .call tl hd => by simp only [svF]; exact callF_sim (svL_sh tl) (hC _ _ _ hd)
  | _, _, _, _, .prim tl hpk hnil => by
    rcases kinds_cases' hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp (config := { decide := true }) only [primK, Option.some.injEq] at hpk <;> subst hpk
    · simp (config := { decide := true }) only [svF, if_true, if_false]; exact leafF_sim (fun _ _ _ => rfl)
    · simp (config := { decide := true }) only [svF, if_true, if_false, primF1]
      exact fin1F_sim (svL_sh tl) (rd_sh _ _)
    · simp (config := { decide := true }) only [svF, if_true, if_false]; exact leafF_sim (fun _ _ _ => rfl)
    · simp (config := { decide := true }) only [svF, if_true, if_false, primF2F]
      exact fin2F_sim (svL_sh tl) (bpush_sh hδ8 hδ)
    · simp (config := { decide := true }) only [svF, if_true, if_false]; exact oneF_sim (bnew_sh _ hδ)
    · simp (config := { decide := true }) only [svF, if_true, if_false, primF1]
      exact fin1F_sim (svL_sh tl) bsize_sh
    · simp (config := { decide := true }) only [svF, if_true, if_false, primF2F]
      exact fin2F_sim (svL_sh tl) (bget_sh hδ)
    · simp (config := { decide := true }) only [svF, if_true, if_false]
      exact fin3F_sim (svL_sh tl) (bset_sh hδ8 hδ)
    · simp (config := { decide := true }) only [svF, if_true, if_false, primF2F]
      exact fin2F_sim (svL_sh tl) (bpush_sh hδ8 hδ)
  | _, _, _, _, .cont _ => fun _ _ _ _ _ _ _ _ _ _ => by simp only [svF]; exact rfl
theorem svL_sh : ∀ {Γ cs ks}, TyL D Γ cs ks →
    Sim δ K.hb (ER δ Γ) (LR δ ks) (svLF K fsX cs) (svLF { K with hb := K.hb + δ } fsX' cs)
  | _, _, _, .nil => by simp only [svLF]; exact nilF_sim
  | _, _, _, .cons (n := n) tn tr => by
    simp only [svLF]; rw [wd_hb K (K.hb + δ) n]
    exact pairF_sim (sv_sh tn) (svL_sh tr)
end

/-- **tail mode** (a loop's step arm) -/
theorem st_sh : ∀ {Γ sk e ks}, TyN D Γ (some sk) e ks →
    Sim δ K.hb (ER δ Γ) (TR δ ks sk) (stF K fsX e) (stF { K with hb := K.hb + δ } fsX' e)
  | _, _, _, _, .ite _ ta tb tt te => by
    simp only [stF]
    exact ifTF_sim (pairF_sim (sv_sh K hδ8 hδ hC ta) (sv_sh K hδ8 hδ hC tb)) (st_sh tt) (st_sh te)
  | Γ, _, _, _, .letE (s := s) (vs := vs) hv hlen hsl _ tb => by
    simp only [stF]
    exact letTF_sim (sv_sh K hδ8 hδ hC hv) (st_sh tb) (fun env env' r r' he hr => by
      have h2 : s + vs.length ≤ Γ.length := by rw [hlen]; exact hsl
      have := er_set he hr h2; rw [hlen] at this; exact this)
  | _, _, _, _, .cont te => by simp only [stF]; exact contF_sim (sv_sh K hδ8 hδ hC te)
  | _, _, _, _, h@(.const) => by simp only [stF]; exact exitF_sim (sv_sh K hδ8 hδ hC h)
  | _, _, _, _, h@(.loc _) => by simp only [stF]; exact exitF_sim (sv_sh K hδ8 hδ hC h)
  | _, _, _, _, h@(.bin _ _ _ _) => by simp only [stF]; exact exitF_sim (sv_sh K hδ8 hδ hC h)
  | _, _, _, _, h@(.pair _) => by simp only [stF]; exact exitF_sim (sv_sh K hδ8 hδ hC h)
  | _, _, _, _, h@(.call _ _) => by simp only [stF]; exact exitF_sim (sv_sh K hδ8 hδ hC h)
  | _, _, _, _, h@(.prim _ _ _) => by simp only [stF]; exact exitF_sim (sv_sh K hδ8 hδ hC h)

/-- a value-mode node in a loop's zero arm -/
theorem stz_sh {Γ : List (Option Kd)} {e : ParSpec.Nd} {ks sk : List Kd} (h : TyN D Γ none e ks) :
    Sim δ K.hb (ER δ Γ) (TR δ ks sk) (stF K fsX e) (stF { K with hb := K.hb + δ } fsX' e) := by
  intro env env' sp sp' H H' he hH hB hS
  rw [stF_none' K fsX h rfl, stF_none' _ fsX' h rfl]
  exact exitF_sim (sv_sh K hδ8 hδ hC h) env env' sp sp' H H' he hH hB hS

end

end NanoMain
