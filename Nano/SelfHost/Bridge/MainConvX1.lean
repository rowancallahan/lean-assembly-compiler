/- Nano/SelfHost/Bridge/MainConvX1: the cap half, layer 1 — in E's kinded semantics (`SemX`: cap / room / stuck) every
outcome other than `room` is the same outcome at any larger stack pointer (below 2^62): a success stays the same
success, a `cap` or `stuck` stays.  So a `cap` or `stuck` at little room would persist with ample room. -/
import Nano.SelfHost.Bridge.MainConv8
import Nano.SelfHost.Bridge.SemX

namespace NanoMain
open Templates

/-- room-stable: an outcome other than `room` at `sp` is the outcome at every larger `sp'` -/
def MoX {α : Type} (S : Nat → Hp → Except Fail α) : Prop :=
  ∀ sp sp' H, sp ≤ sp' → sp' < 2 ^ 62 → S sp H ≠ .error .room → S sp' H = S sp H

theorem bindX {α β : Type} {x x' : Except Fail α} {f f' : α → Except Fail β}
    (hx : x ≠ .error .room → x' = x) (hf : ∀ a, f a ≠ .error .room → f' a = f a)
    (h : x.bind f ≠ .error .room) : x'.bind f' = x.bind f := by
  cases x with
  | error e =>
    have : x' = .error e := hx (fun h' => h (by rw [h']; rfl))
    rw [this]; rfl
  | ok a =>
    rw [hx (by simp)]
    exact hf a h

theorem mapX {α β : Type} {x x' : Except Fail α} (f : α → β) (hx : x ≠ .error .room → x' = x)
    (h : x.map f ≠ .error .room) : x'.map f = x.map f := by
  cases x with
  | error e => rw [hx (fun h' => h (by rw [h']; rfl))]
  | ok a => rw [hx (by simp)]

theorem leafF_mo (V : Env → UInt64) (env : Env) : MoX (leafF V env) := by
  intro sp sp' H h1 h2 h
  unfold leafF at h ⊢; split at h
  · rw [if_pos (by omega), if_pos ‹_›]
  · exact absurd rfl h

theorem nilF_mo (env : Env) : MoX (nilF env) := fun _ _ _ _ _ _ => rfl

theorem pairF_mo {wa : Nat} {SA SB : SemWX} (ha : ∀ env, MoX (SA env)) (hb : ∀ env, MoX (SB env)) (env : Env) :
    MoX (pairF wa SA SB env) := by
  intro sp sp' H h1 h2 h
  simp only [pairF] at h ⊢
  refine bindX (ha env _ _ _ h1 h2) (fun r1 hr => bindX (hb env _ _ _ (by omega) (by omega)) (fun _ _ => rfl) hr) h

theorem localF_mo : ∀ (w k : Nat) (env : Env), MoX (localF k w env)
  | 0, k, env => nilF_mo env
  | w + 1, k, env => pairF_mo (fun e => leafF_mo _ e) (fun e => localF_mo w (k + 1) e) env

theorem oneF_mo {S : Sem1X} (h : ∀ env, MoX (S env)) (env : Env) : MoX (oneF S env) := by
  intro sp sp' H h1 h2 hr
  simp only [oneF] at hr ⊢
  exact mapX _ (h env _ _ _ h1 h2) hr

theorem bnewF_mo (κ : Nat) (env : Env) : MoX (bnewF κ env) := by
  intro sp sp' H h1 h2 h
  simp only [bnewF] at h ⊢
  unfold bnewS at h ⊢; split at h
  · rename_i hc; rw [if_pos (by omega), if_pos hc]
  · exact absurd rfl h

theorem ifF_mo {c : Nat} {SP ST SE : SemWX} (hp : ∀ env, MoX (SP env)) (ht : ∀ env, MoX (ST env))
    (he : ∀ env, MoX (SE env)) (env : Env) : MoX (ifF c SP ST SE env) := by
  intro sp sp' H h1 h2 h
  simp only [ifF] at h ⊢
  refine bindX (hp env _ _ _ h1 h2) (fun r hr => ?_) h
  split at hr
  · split at hr
    · rename_i hcmp; simp only [hcmp, if_true] at hr ⊢; exact ht env _ _ _ h1 h2 hr
    · rename_i hcmp; simp only [hcmp] at hr ⊢; exact he env _ _ _ h1 h2 hr
  · rfl

theorem letF_mo {k w : Nat} {SV SB : SemWX} (hv : ∀ env, MoX (SV env)) (hb : ∀ env, MoX (SB env)) (env : Env) :
    MoX (letF k w SV SB env) := by
  intro sp sp' H h1 h2 h
  simp only [letF] at h ⊢
  exact bindX (hv env _ _ _ h1 h2) (fun r hr => hb _ _ _ _ h1 h2 hr) h

/-- prim closings ignore `sp` -/
def IndX1 (F : UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) : Prop := ∀ a sp sp' H, F a sp H = F a sp' H
def IndX2 (F : UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) : Prop := ∀ a b sp sp' H, F a b sp H = F a b sp' H
def IndX3 (F : UInt64 → UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)) : Prop :=
  ∀ a b c sp sp' H, F a b c sp H = F a b c sp' H

theorem fin1F_mo {SP : SemWX} {F : UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)} (hp : ∀ env, MoX (SP env))
    (hF : IndX1 F) (env : Env) : MoX (fin1F SP F env) := by
  intro sp sp' H h1 h2 h
  simp only [fin1F] at h ⊢
  refine bindX (hp env _ _ _ h1 h2) (fun r hr => ?_) h
  split <;> simp only [hF _ (sp' - 8) (sp - 8)]
theorem fin2F_mo {SP : SemWX} {F : UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)} (hp : ∀ env, MoX (SP env))
    (hF : IndX2 F) (env : Env) : MoX (fin2F SP F env) := by
  intro sp sp' H h1 h2 h
  simp only [fin2F] at h ⊢
  refine bindX (hp env _ _ _ h1 h2) (fun r hr => ?_) h
  split <;> simp only [hF _ _ (sp' - 16) (sp - 16)]
theorem fin3F_mo {SP : SemWX} {F : UInt64 → UInt64 → UInt64 → Nat → Hp → Except Fail (UInt64 × Hp)}
    (hp : ∀ env, MoX (SP env)) (hF : IndX3 F) (env : Env) : MoX (fin3F SP F env) := by
  intro sp sp' H h1 h2 h
  simp only [fin3F] at h ⊢
  refine bindX (hp env _ _ _ h1 h2) (fun r hr => ?_) h
  split <;> simp only [hF _ _ _ (sp' - 24) (sp - 24)]

theorem callF_mo {pa : Nat} {SA : SemWX} {g : SemDX} (ha : ∀ env, MoX (SA env)) (hg : ∀ args, MoX (g args))
    (env : Env) : MoX (callF pa SA g env) := by
  intro sp sp' H h1 h2 h
  simp only [callF] at h ⊢
  exact bindX (ha env _ _ _ h1 h2) (fun r hr => hg _ _ _ _ (by omega) (by omega) hr) h

theorem exitF_mo {S : SemWX} (h : ∀ env, MoX (S env)) (env : Env) : MoX (exitF S env) := by
  intro sp sp' H h1 h2 hr; simp only [exitF] at hr ⊢; exact mapX _ (h env _ _ _ h1 h2) hr
theorem contF_mo {S : SemWX} (h : ∀ env, MoX (S env)) (env : Env) : MoX (contF S env) := by
  intro sp sp' H h1 h2 hr; simp only [contF] at hr ⊢; exact mapX _ (h env _ _ _ h1 h2) hr
theorem ifTF_mo {c : Nat} {SP : SemWX} {ST SE : SemTX} (hp : ∀ env, MoX (SP env)) (ht : ∀ env, MoX (ST env))
    (he : ∀ env, MoX (SE env)) (env : Env) : MoX (ifTF c SP ST SE env) := by
  intro sp sp' H h1 h2 h
  simp only [ifTF] at h ⊢
  refine bindX (hp env _ _ _ h1 h2) (fun r hr => ?_) h
  split at hr
  · split at hr
    · rename_i hcmp; simp only [hcmp, if_true] at hr ⊢; exact ht env _ _ _ h1 h2 hr
    · rename_i hcmp; simp only [hcmp] at hr ⊢; exact he env _ _ _ h1 h2 hr
  · rfl
theorem letTF_mo {k w : Nat} {SV : SemWX} {SB : SemTX} (hv : ∀ env, MoX (SV env)) (hb : ∀ env, MoX (SB env))
    (env : Env) : MoX (letTF k w SV SB env) := by
  intro sp sp' H h1 h2 h
  simp only [letTF] at h ⊢
  exact bindX (hv env _ _ _ h1 h2) (fun r hr => hb _ _ _ _ h1 h2 hr) h

theorem loopGoF_mo {p : Nat} {SZ SS : SemTX} (hz : ∀ env, MoX (SZ env)) (hs : ∀ env, MoX (SS env)) :
    ∀ (n : Nat) (env : Env) (sp sp' : Nat) (H : Hp), sp ≤ sp' → sp' < 2 ^ 62 →
      loopGoF p SZ SS sp n env H ≠ .error .room → loopGoF p SZ SS sp' n env H = loopGoF p SZ SS sp n env H
  | n, env, sp, sp', H, h1, h2, h => by
    unfold loopGoF at h ⊢
    split at h
    · rename_i h0; simp only [h0, if_true]
      exact bindX (hz env _ _ _ h1 h2) (fun _ _ => rfl) h
    · rename_i h0; simp only [h0, if_false]
      cases n with
      | zero => rfl
      | succ n =>
        refine bindX (hs _ _ _ _ h1 h2) (fun r hr => ?_) h
        split
        · rfl
        · rename_i st hst
          simp only [hst] at hr
          exact loopGoF_mo hz hs n _ sp sp' _ h1 h2 hr

theorem loopF_mo {p : Nat} {SZ SS : SemTX} (hz : ∀ env, MoX (SZ env)) (hs : ∀ env, MoX (SS env)) (env : Env) :
    MoX (loopF p SZ SS env) := fun sp sp' H h1 h2 h => loopGoF_mo hz hs _ env sp sp' H h1 h2 h

theorem bpushFF_ind (hb : Nat) : IndX2 (bpushFF hb) := by
  intro a b sp sp' H; unfold bpushFF; split
  · rfl
  · split
    · rw [bpushF_ind hb a b sp sp' H]
    · rfl

theorem primF2F_ind (K : SC) (pn : Nat) : IndX2 (primF2F K pn) := by
  unfold primF2F; split
  · intro a b sp sp' H; simp only [bgetF_ind K.hb a b sp sp' H]
  · exact bpushFF_ind _

mutual
/-- **room stability** of the kinded node semantics, given room-stable callees -/
theorem svF_mo (K : SC) (fsX : Nat → SemDX) (hfs : ∀ i args, MoX (fsX i args)) :
    ∀ (e : ParSpec.Nd) (env : Env), MoX (svF K fsX e env)
  | .const _, env => by simp only [svF]; exact leafF_mo _ env
  | .loc s w, env => by simp only [svF]; exact localF_mo w s env
  | .bin op a b, env => by
    simp only [svF]
    exact fin2F_mo (pairF_mo (svF_mo K fsX hfs a) (svF_mo K fsX hfs b))
      (fun x y sp sp' H => by simp only [aluF2_ind op x y sp sp' H]) env
  | .ite c a b t e, env => by
    simp only [svF]
    exact ifF_mo (pairF_mo (svF_mo K fsX hfs a) (svF_mo K fsX hfs b)) (svF_mo K fsX hfs t) (svF_mo K fsX hfs e) env
  | .letE s w v b, env => by simp only [svF]; exact letF_mo (svF_mo K fsX hfs v) (svF_mo K fsX hfs b) env
  | .pair cs, env => by simp only [svF]; exact svLF_mo K fsX hfs cs env
  | .call i as, env => by simp only [svF]; exact callF_mo (svLF_mo K fsX hfs as) (hfs i) env
  | .prim pn as, env => by
    simp only [svF]
    split
    · exact leafF_mo _ env
    · split
      · exact oneF_mo (bnewF_mo K.κ) env
      · split
        · refine fin1F_mo (svLF_mo K fsX hfs as) (fun x sp sp' H => ?_) env
          unfold primF1; split
          · simp only [rdF1_ind K.c29 K.inp x sp sp' H]
          · simp only [bsizeF_ind K.hb x sp sp' H]
        · split
          · exact fin3F_mo (svLF_mo K fsX hfs as) (fun x y z sp sp' H => by simp only [bsetF_ind K.hb x y z sp sp' H]) env
          · exact fin2F_mo (svLF_mo K fsX hfs as) (primF2F_ind K pn) env
  | .loop z s, env => by simp only [svF]; exact loopF_mo (stF_mo K fsX hfs z) (stF_mo K fsX hfs s) env
  | .cont _, env => fun _ _ _ _ _ _ => by simp only [svF]
theorem stF_mo (K : SC) (fsX : Nat → SemDX) (hfs : ∀ i args, MoX (fsX i args)) :
    ∀ (e : ParSpec.Nd) (env : Env), MoX (stF K fsX e env)
  | .ite c a b t e, env => by
    simp only [stF]
    exact ifTF_mo (pairF_mo (svF_mo K fsX hfs a) (svF_mo K fsX hfs b)) (stF_mo K fsX hfs t) (stF_mo K fsX hfs e) env
  | .letE s w v b, env => by simp only [stF]; exact letTF_mo (svF_mo K fsX hfs v) (stF_mo K fsX hfs b) env
  | .cont e, env => by simp only [stF]; exact contF_mo (svF_mo K fsX hfs e) env
  | .const v, env => by simp only [stF]; exact exitF_mo (svF_mo K fsX hfs (.const v)) env
  | .loc s w, env => by simp only [stF]; exact exitF_mo (svF_mo K fsX hfs (.loc s w)) env
  | .bin op a b, env => by simp only [stF]; exact exitF_mo (svF_mo K fsX hfs (.bin op a b)) env
  | .pair cs, env => by simp only [stF]; exact exitF_mo (svF_mo K fsX hfs (.pair cs)) env
  | .call i as, env => by simp only [stF]; exact exitF_mo (svF_mo K fsX hfs (.call i as)) env
  | .prim p as, env => by simp only [stF]; exact exitF_mo (svF_mo K fsX hfs (.prim p as)) env
  | .loop z s, env => by simp only [stF]; exact exitF_mo (svF_mo K fsX hfs (.loop z s)) env
theorem svLF_mo (K : SC) (fsX : Nat → SemDX) (hfs : ∀ i args, MoX (fsX i args)) :
    ∀ (cs : List ParSpec.Nd) (env : Env), MoX (svLF K fsX cs env)
  | [], env => by simp only [svLF]; exact nilF_mo env
  | c :: cs, env => by simp only [svLF]; exact pairF_mo (svF_mo K fsX hfs c) (svLF_mo K fsX hfs cs) env
end

theorem defSF_mo {p nl : Nat} {Sb : SemWX} (hb : ∀ env, MoX (Sb env)) (args : List UInt64) : MoX (defSF p nl Sb args) := by
  intro sp sp' H h1 h2 h
  unfold defSF at h ⊢; split at h
  · rw [if_pos (by omega), if_pos ‹_›]; exact hb _ _ _ _ (by omega) (by omega) h
  · exact absurd rfl h

/-- **room stability of E's kinded semantics**: an outcome other than `room` is the same with more stack room -/
theorem semAtF_mo (P : Templates.PC) (ds : List ParSpec.DefA) : ∀ (k : Nat) (args : List UInt64), MoX (semAtF P ds k args)
  | k, args => by
    rw [semAtF]
    refine defSF_mo (svF_mo _ _ (fun n a => ?_) _) args
    split
    · exact semAtF_mo P ds n a
    · exact fun _ _ _ _ _ _ => rfl
termination_by k => k

end NanoMain
