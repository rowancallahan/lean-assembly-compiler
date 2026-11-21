/- Nano/SelfHost/Bridge/MainConv1: the converse bridge, layer 1 — E's semantics only gains by more stack room: a success at
stack pointer `sp` is the same success at any `sp' ≥ sp` (below 2^62).  Results never depend on `sp`. -/
import Nano.SelfHost.Bridge.MainBridge15

namespace NanoMain
open Templates

/-- room-monotone: success at `sp` is the same success at every larger `sp'` -/
def Mo {α : Type} (S : Nat → Hp → Option α) : Prop :=
  ∀ sp sp' H r, S sp H = some r → sp ≤ sp' → sp' < 2 ^ 62 → S sp' H = some r

theorem leafS_mo (V : Env → UInt64) (env : Env) : Mo (leafS V env) := by
  intro sp sp' H r h hs hs'
  unfold leafS at h ⊢; split at h
  · rw [if_pos (by omega)]; exact h
  · cases h

theorem nilS_mo (env : Env) : Mo (nilS env) := fun _ _ _ _ h _ _ => h

theorem pairS_mo {wa : Nat} {SA SB : SemW} (ha : ∀ env, Mo (SA env)) (hb : ∀ env, Mo (SB env)) (env : Env) :
    Mo (pairS wa SA SB env) := by
  intro sp sp' H r h hs hs'
  simp only [pairS, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨r1, h1, r2, h2, he⟩ := h
  exact ⟨r1, ha env _ _ _ _ h1 hs hs', r2, hb env _ _ _ _ h2 (by omega) (by omega), he⟩

theorem localS_mo : ∀ (w k : Nat) (env : Env), Mo (localS k w env)
  | 0, k, env => nilS_mo env
  | w + 1, k, env => pairS_mo (fun e => leafS_mo _ e) (fun e => localS_mo w (k + 1) e) env

theorem one_mo {S : Env → Nat → Hp → Option (UInt64 × Hp)} (h : ∀ env, Mo (S env)) (env : Env) : Mo (one S env) := by
  intro sp sp' H r hr hs hs'
  simp only [one, Option.map_eq_some_iff] at hr ⊢
  obtain ⟨a, ha, e⟩ := hr; exact ⟨a, h env _ _ _ _ ha hs hs', e⟩

theorem bnewS_mo (κ : Nat) (env : Env) : Mo (bnewS κ env) := by
  intro sp sp' H r h hs hs'
  unfold bnewS at h ⊢; split at h
  · rename_i hc; rw [if_pos (by omega)]; exact h
  · cases h

theorem ifS_mo {c : Nat} {SP ST SE : SemW} (hp : ∀ env, Mo (SP env)) (ht : ∀ env, Mo (ST env))
    (he : ∀ env, Mo (SE env)) (env : Env) : Mo (ifS c SP ST SE env) := by
  intro sp sp' H r h hs hs'
  simp only [ifS, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨r1, h1, h2⟩ := h
  refine ⟨r1, hp env _ _ _ _ h1 hs hs', ?_⟩
  split at h2
  · rename_i hc
    split at h2
    · rename_i hcmp; simp only [hcmp, if_true]; exact ht env _ _ _ _ h2 hs hs'
    · rename_i hcmp; simp only [hcmp, if_false]; exact he env _ _ _ _ h2 hs hs'
  · cases h2

theorem letS_mo {k w : Nat} {SV SB : SemW} (hv : ∀ env, Mo (SV env)) (hb : ∀ env, Mo (SB env)) (env : Env) :
    Mo (letS k w SV SB env) := by
  intro sp sp' H r h hs hs'
  simp only [letS, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨r1, h1, h2⟩ := h
  exact ⟨r1, hv env _ _ _ _ h1 hs hs', hb _ _ _ _ _ h2 hs hs'⟩

/-- prim closings ignore `sp` -/
def Ind1 (F : UInt64 → Nat → Hp → Option (UInt64 × Hp)) : Prop := ∀ a sp sp' H, F a sp H = F a sp' H
def Ind2 (F : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) : Prop := ∀ a b sp sp' H, F a b sp H = F a b sp' H
def Ind3 (F : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) : Prop :=
  ∀ a b c sp sp' H, F a b c sp H = F a b c sp' H

theorem fin1S_mo {SP : SemW} {F : UInt64 → Nat → Hp → Option (UInt64 × Hp)} (hp : ∀ env, Mo (SP env)) (hF : Ind1 F)
    (env : Env) : Mo (fin1S SP F env) := by
  intro sp sp' H r h hs hs'
  simp only [fin1S, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨r1, h1, h2⟩ := h
  refine ⟨r1, hp env _ _ _ _ h1 hs hs', ?_⟩
  split at h2 <;> simp_all [hF _ (sp - 8) (sp' - 8)]
theorem fin2S_mo {SP : SemW} {F : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)} (hp : ∀ env, Mo (SP env))
    (hF : Ind2 F) (env : Env) : Mo (fin2S SP F env) := by
  intro sp sp' H r h hs hs'
  simp only [fin2S, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨r1, h1, h2⟩ := h
  refine ⟨r1, hp env _ _ _ _ h1 hs hs', ?_⟩
  split at h2 <;> simp_all [hF _ _ (sp - 16) (sp' - 16)]
theorem fin3S_mo {SP : SemW} {F : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)} (hp : ∀ env, Mo (SP env))
    (hF : Ind3 F) (env : Env) : Mo (fin3S SP F env) := by
  intro sp sp' H r h hs hs'
  simp only [fin3S, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨r1, h1, h2⟩ := h
  refine ⟨r1, hp env _ _ _ _ h1 hs hs', ?_⟩
  split at h2 <;> simp_all [hF _ _ _ (sp - 24) (sp' - 24)]

theorem callS_mo {pa : Nat} {SA : SemW} {g : List UInt64 → Nat → Hp → Option (List UInt64 × Hp)}
    (ha : ∀ env, Mo (SA env)) (hg : ∀ args, Mo (g args)) (env : Env) : Mo (callS pa SA g env) := by
  intro sp sp' H r h hs hs'
  simp only [callS, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨r1, h1, h2⟩ := h
  exact ⟨r1, ha env _ _ _ _ h1 hs hs', hg _ _ _ _ _ h2 (by omega) (by omega)⟩

theorem exitS_mo {S : SemW} (h : ∀ env, Mo (S env)) (env : Env) : Mo (exitS S env) := by
  intro sp sp' H r hr hs hs'
  simp only [exitS, Option.map_eq_some_iff] at hr ⊢
  obtain ⟨a, ha, e⟩ := hr; exact ⟨a, h env _ _ _ _ ha hs hs', e⟩
theorem contS_mo {S : SemW} (h : ∀ env, Mo (S env)) (env : Env) : Mo (contS S env) := by
  intro sp sp' H r hr hs hs'
  simp only [contS, Option.map_eq_some_iff] at hr ⊢
  obtain ⟨a, ha, e⟩ := hr; exact ⟨a, h env _ _ _ _ ha hs hs', e⟩
theorem ifTS_mo {c : Nat} {SP : SemW} {ST SE : SemT} (hp : ∀ env, Mo (SP env)) (ht : ∀ env, Mo (ST env))
    (he : ∀ env, Mo (SE env)) (env : Env) : Mo (ifTS c SP ST SE env) := by
  intro sp sp' H r h hs hs'
  simp only [ifTS, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨r1, h1, h2⟩ := h
  refine ⟨r1, hp env _ _ _ _ h1 hs hs', ?_⟩
  split at h2
  · split at h2
    · rename_i hcmp; simp only [hcmp, if_true]; exact ht env _ _ _ _ h2 hs hs'
    · rename_i hcmp; simp only [hcmp, if_false]; exact he env _ _ _ _ h2 hs hs'
  · cases h2
theorem letTS_mo {k w : Nat} {SV : SemW} {SB : SemT} (hv : ∀ env, Mo (SV env)) (hb : ∀ env, Mo (SB env)) (env : Env) :
    Mo (letTS k w SV SB env) := by
  intro sp sp' H r h hs hs'
  simp only [letTS, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨r1, h1, h2⟩ := h
  exact ⟨r1, hv env _ _ _ _ h1 hs hs', hb _ _ _ _ _ h2 hs hs'⟩

theorem loopGo_mo {p : Nat} {SZ SS : SemT} (hz : ∀ env, Mo (SZ env)) (hs : ∀ env, Mo (SS env)) :
    ∀ (n : Nat) (env : Env) (sp sp' : Nat) (H : Hp) (r : List UInt64 × Hp), loopGo p SZ SS sp n env H = some r →
      sp ≤ sp' → sp' < 2 ^ 62 → loopGo p SZ SS sp' n env H = some r
  | n, env, sp, sp', H, r, h, h1, h2 => by
    unfold loopGo at h ⊢
    split at h
    · rename_i h0; rw [if_pos h0]
      simp only [Option.bind_eq_some_iff] at h ⊢
      obtain ⟨r1, a, b⟩ := h; exact ⟨r1, hz env _ _ _ _ a h1 h2, b⟩
    · rename_i h0; rw [if_neg h0]
      cases n with
      | zero => cases h
      | succ n =>
        simp only [Option.bind_eq_some_iff] at h ⊢
        obtain ⟨r1, a, b⟩ := h
        refine ⟨r1, hs _ _ _ _ _ a h1 h2, ?_⟩
        split at b
        · exact b
        · exact loopGo_mo hz hs n _ sp sp' _ r b h1 h2

theorem loopS_mo {p : Nat} {SZ SS : SemT} (hz : ∀ env, Mo (SZ env)) (hs : ∀ env, Mo (SS env)) (env : Env) :
    Mo (loopS p SZ SS env) := fun sp sp' H r h h1 h2 => loopGo_mo hz hs _ env sp sp' H r h h1 h2

theorem rdF1_ind (c i) : Ind1 (rdF1 c i) := fun _ _ _ _ => rfl
theorem bsizeF_ind (hb) : Ind1 (bsizeF hb) := fun _ _ _ _ => rfl
theorem bgetF_ind (hb) : Ind2 (bgetF hb) := fun _ _ _ _ _ => rfl
theorem bpushF_ind (hb) : Ind2 (bpushF hb) := fun _ _ _ _ _ => rfl
theorem bsetF_ind (hb) : Ind3 (bsetF hb) := fun _ _ _ _ _ _ => rfl
theorem aluF2_ind (op) : Ind2 (aluF2 op) := fun _ _ _ _ _ => rfl

mutual
/-- **room monotonicity** of the node templates, given monotone callees -/
theorem sv_mo (K : SC) (hfs : ∀ i args, Mo (K.fs i args)) : ∀ (e : ParSpec.Nd) (env : Env), Mo (sv K e env)
  | .const _, env => by simp only [sv]; exact leafS_mo _ env
  | .loc s w, env => by simp only [sv]; exact localS_mo w s env
  | .bin op a b, env => by simp only [sv]; exact fin2S_mo (pairS_mo (sv_mo K hfs a) (sv_mo K hfs b)) (aluF2_ind op) env
  | .ite c a b t e, env => by simp only [sv]; exact ifS_mo (pairS_mo (sv_mo K hfs a) (sv_mo K hfs b)) (sv_mo K hfs t) (sv_mo K hfs e) env
  | .letE s w v b, env => by simp only [sv]; exact letS_mo (sv_mo K hfs v) (sv_mo K hfs b) env
  | .pair cs, env => by simp only [sv]; exact svL_mo K hfs cs env
  | .call i as, env => by simp only [sv]; exact callS_mo (svL_mo K hfs as) (hfs i) env
  | .prim pn as, env => by
    simp only [sv]
    split
    · exact leafS_mo _ env
    · split
      · exact one_mo (bnewS_mo K.κ) env
      · split
        · refine fin1S_mo (svL_mo K hfs as) ?_ env
          unfold primF1; split
          · exact rdF1_ind _ _
          · exact bsizeF_ind _
        · split
          · exact fin3S_mo (svL_mo K hfs as) (bsetF_ind _) env
          · refine fin2S_mo (svL_mo K hfs as) ?_ env
            unfold primF2; split
            · exact bgetF_ind _
            · exact bpushF_ind _
  | .loop z s, env => by simp only [sv]; exact loopS_mo (st_mo K hfs z) (st_mo K hfs s) env
  | .cont _, env => fun _ _ _ _ h => by simp [sv] at h
theorem st_mo (K : SC) (hfs : ∀ i args, Mo (K.fs i args)) : ∀ (e : ParSpec.Nd) (env : Env), Mo (st K e env)
  | .ite c a b t e, env => by simp only [st]; exact ifTS_mo (pairS_mo (sv_mo K hfs a) (sv_mo K hfs b)) (st_mo K hfs t) (st_mo K hfs e) env
  | .letE s w v b, env => by simp only [st]; exact letTS_mo (sv_mo K hfs v) (st_mo K hfs b) env
  | .cont e, env => by simp only [st]; exact contS_mo (sv_mo K hfs e) env
  | .const v, env => by simp only [st]; exact exitS_mo (sv_mo K hfs (.const v)) env
  | .loc s w, env => by simp only [st]; exact exitS_mo (sv_mo K hfs (.loc s w)) env
  | .bin op a b, env => by simp only [st]; exact exitS_mo (sv_mo K hfs (.bin op a b)) env
  | .pair cs, env => by simp only [st]; exact exitS_mo (sv_mo K hfs (.pair cs)) env
  | .call i as, env => by simp only [st]; exact exitS_mo (sv_mo K hfs (.call i as)) env
  | .prim p as, env => by simp only [st]; exact exitS_mo (sv_mo K hfs (.prim p as)) env
  | .loop z s, env => by simp only [st]; exact exitS_mo (sv_mo K hfs (.loop z s)) env
theorem svL_mo (K : SC) (hfs : ∀ i args, Mo (K.fs i args)) : ∀ (cs : List ParSpec.Nd) (env : Env), Mo (svL K cs env)
  | [], env => by simp only [svL]; exact nilS_mo env
  | c :: cs, env => by simp only [svL]; exact pairS_mo (sv_mo K hfs c) (svL_mo K hfs cs) env
end

theorem defS_mo {p nl : Nat} {Sb : SemW} (hb : ∀ env, Mo (Sb env)) (args : List UInt64) : Mo (defS p nl Sb args) := by
  intro sp sp' H r h h1 h2
  unfold defS at h ⊢; split at h
  · rw [if_pos (by omega)]; exact hb _ _ _ _ _ h (by omega) (by omega)
  · cases h

theorem semAt_mo (P : Templates.PC) (ds : List ParSpec.DefA) : ∀ (k : Nat) (args : List UInt64), Mo (semAt P ds k args)
  | k, args => by
    rw [semAt_eq]
    refine defS_mo (sv_mo _ (fun n a => ?_) _) args
    simp only [scAt]
    split
    · exact semAt_mo P ds n a
    · exact fun _ _ _ _ h => by simp [dflt] at h
termination_by k => k

end NanoMain
