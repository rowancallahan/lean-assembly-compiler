/- Nano/V2Self/Proof/MainBridge3: the Sem ⇐ sv bridge, layer 3 — invariants of one frame under O's ownership walk
(`OwnSpec.chk`): the environment invariant `EnvI`, the result invariant `ResI`, the heap change frame `Ch`. -/
import Nano.V2Self.Proof.MainBridge2
import Nano.V2Self.Proof.OwnSpec

namespace NanoMain
open Templates

/-- slot `s` is known in Γ -/
def Kn (Γ : List (Option Kd)) (s : Nat) : Prop := ∃ kd, Γ[s]? = some (some kd)

/-- slot `s` can be read: a word slot, or a live buffer slot -/
def Rd (Kk : List Nat) (F : List Bool) (s : Nat) : Prop := Kk.getD s 0 = 0 ∨ OwnSpec.dead F s = false

/-- **frame invariant**: readable known slots hold related values (words in word slots); a live OWNED buffer slot's
block is held by no other readable buffer slot -/
structure EnvI (σ : AH) (Kk : List Nat) (F : List Bool) (Γ : List (Option Kd)) (env : List W) (ew : Env) : Prop where
  len : env.length = Γ.length
  ty : EnvOK env Γ
  val : ∀ s, Kn Γ s → Rd Kk F s → ∃ v, env[s]? = some v ∧ VR σ v (ew s) ∧ (Kk.getD s 0 = 0 → ∃ x, v = .w x)
  dist : ∀ s t ls lt, s ≠ t → Kn Γ s → Kn Γ t → Kk.getD s 0 = 1 → Kk.getD t 0 ≠ 0 →
    OwnSpec.dead F s = false → OwnSpec.dead F t = false → env[s]? = some (.b ls) → env[t]? = some (.b lt) → ew s ≠ ew t

/-- slot `s` was consumed: live in `F`, dead in `F'` -/
def Cons (F F' : List Bool) (s : Nat) : Prop := OwnSpec.dead F s = false ∧ OwnSpec.dead F' s = true

/-- **change frame**: an existing block changes only if a buffer slot consumed between F and F' points to it -/
def Ch (σ σ' : AH) (Γ : List (Option Kd)) (F F' : List Bool) (env : List W) (ew : Env) : Prop :=
  ∀ a, (σ a).isSome → (∀ s l, Kn Γ s → Cons F F' s → env[s]? = some (.b l) → (ew s).toNat ≠ a) → σ' a = σ a

/-- no owned buffer entry of the list sits at address `u` -/
def OwnFree : List Nat → List W → List UInt64 → UInt64 → Prop
  | e :: es, x :: v, u' :: vs, u => (e = 1 → ∀ l, x = .b l → u' ≠ u) ∧ OwnFree es v vs u
  | _, _, _, _ => True

/-- **result invariant** for entries `es` (OwnSpec): < 4 related; 0 a word; 1 a buffer that no readable live buffer
slot holds and no later owned buffer entry repeats; a tagged entry = slot (e/4 − 1)'s value and word, of that kind -/
def ResI (σ : AH) (Kk : List Nat) (F : List Bool) (Γ : List (Option Kd)) (env : List W) (ew : Env) :
    List Nat → List W → List UInt64 → Prop
  | [], [], [] => True
  | e :: es, x :: v, u :: vs =>
    (e < 4 → VR σ x u) ∧ (e = 0 → ∃ y, x = .w y) ∧
    (e = 1 → ∀ l, x = .b l →
      (∀ s ls, Kn Γ s → Kk.getD s 0 ≠ 0 → OwnSpec.dead F s = false → env[s]? = some (.b ls) → ew s ≠ u) ∧
      OwnFree es v vs u) ∧
    (4 ≤ e → u = ew (e / 4 - 1) ∧ env[e / 4 - 1]? = some x ∧ e % 4 = Kk.getD (e / 4 - 1) 0 ∧ Kn Γ (e / 4 - 1)) ∧
    ResI σ Kk F Γ env ew es v vs
  | _, _, _ => False

theorem ResI.len {σ Kk F Γ env ew} : ∀ {es : List Nat} {v : List W} {vs : List UInt64},
    ResI σ Kk F Γ env ew es v vs → es.length = v.length ∧ v.length = vs.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, h => by have := ResI.len h.2.2.2.2; simp [this.1, this.2]
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by simp [ResI] at h

theorem leafS_some {V : Env → UInt64} {ew : Env} {sp : Nat} {H H' : Hp} {vs : List UInt64}
    (h : leafS V ew sp H = some (vs, H')) : vs = [V ew] ∧ H' = H := by
  unfold leafS at h; split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩
  · cases h

theorem localS_some : ∀ (w s : Nat) {ew : Env} {sp : Nat} {H H' : Hp} {vs : List UInt64},
    localS s w ew sp H = some (vs, H') → vs = (List.range w).map (fun j => ew (s + j)) ∧ H' = H
  | 0, s, ew, sp, H, H', vs, h => by
    simp only [localS, nilS, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | w + 1, s, ew, sp, H, H', vs, h => by
    simp only [localS, pairS, Option.bind_eq_some_iff] at h
    obtain ⟨⟨u1, H1⟩, h1, ⟨u2, H2⟩, h2, he⟩ := h
    obtain ⟨rfl, rfl⟩ := leafS_some h1
    obtain ⟨rfl, rfl⟩ := localS_some w (s + 1) h2
    simp only [Option.some.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    refine ⟨?_, rfl⟩
    rw [List.range_succ_eq_map]; simp [Nat.add_comm, Nat.add_left_comm]

/-- dead flags only grow -/
def Mono (F F' : List Bool) : Prop := ∀ s, OwnSpec.dead F s = true → OwnSpec.dead F' s = true

theorem Mono.refl (F : List Bool) : Mono F F := fun _ h => h
theorem Mono.trans {F F1 F2 : List Bool} (h1 : Mono F F1) (h2 : Mono F1 F2) : Mono F F2 := fun s h => h2 s (h1 s h)

theorem Ch.trans {σ σ1 σ2 : AH} {Γ : List (Option Kd)} {F F1 F2 : List Bool} {env : List W} {ew : Env}
    (h1 : Ch σ σ1 Γ F F1 env ew) (h2 : Ch σ1 σ2 Γ F1 F2 env ew) (m1 : Mono F F1) (m2 : Mono F1 F2) :
    Ch σ σ2 Γ F F2 env ew := by
  intro a ha hn
  have e1 : σ1 a = σ a := h1 a ha fun s l hk hc hl => hn s l hk ⟨hc.1, m2 s hc.2⟩ hl
  rw [← e1]
  refine h2 a (by rw [e1]; exact ha) fun s l hk hc hl => hn s l hk ⟨?_, hc.2⟩ hl
  cases hd : OwnSpec.dead F s
  · rfl
  · have := m1 s hd; rw [hc.1] at this; cases this

theorem Ch.refl (σ : AH) (Γ F env ew) : Ch σ σ Γ F F env ew := fun _ _ _ => rfl

end NanoMain
