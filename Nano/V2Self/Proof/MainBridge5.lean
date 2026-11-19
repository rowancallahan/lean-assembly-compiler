/- Nano/V2Self/Proof/MainBridge5: the TRANSFER of a value (`OwnSpec.tr`: let value, branch / body result): owned
pinned slots are consumed and their entries become owned results; all invariants carry over. -/
import Nano.V2Self.Proof.MainBridge4

namespace NanoMain
open Templates

/-- every pinned OWNED entry's slot is live in `F` -/
def TagLive (F : List Bool) : List Nat → Prop
  | e :: es => (4 ≤ e → e % 4 = 1 → OwnSpec.dead F (e / 4 - 1) = false) ∧ TagLive F es
  | [] => True

/-- no owned buffer entry, plain or pinned, sits at address `u` -/
def OwnFreeT : List Nat → List W → List UInt64 → UInt64 → Prop
  | e :: es, x :: v, u' :: vs, u => ((e = 1 ∨ (4 ≤ e ∧ e % 4 = 1)) → ∀ l, x = .b l → u' ≠ u) ∧ OwnFreeT es v vs u
  | _, _, _, _ => True

theorem TagLive.mono {F F1 : List Bool} (m : Mono F1 F) : ∀ {es : List Nat}, TagLive F es → TagLive F1 es
  | [], _ => trivial
  | _ :: _, ⟨h, t⟩ => ⟨fun a b => live_of_mono m (h a b), TagLive.mono m t⟩

theorem ownFreeT_of {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {u : UInt64} (ne : ∀ s ls, Kn Γ s → Kk.getD s 0 ≠ 0 → OwnSpec.dead F s = false → env[s]? = some (.b ls) → ew s ≠ u) :
    ∀ {es : List Nat} {v : List W} {vs : List UInt64}, ResI σ Kk F Γ env ew es v vs → TagLive F es →
      OwnFree es v vs u → OwnFreeT es v vs u
  | [], [], [], _, _, _ => trivial
  | e :: es, x :: v, u' :: vs, ⟨_, _, _, c4, cR⟩, ⟨t1, tT⟩, ⟨o1, oT⟩ => by
    refine ⟨fun he l hl => ?_, ownFreeT_of ne cR tT oT⟩
    rcases he with he | ⟨h4, h1⟩
    · exact o1 he l hl
    · obtain ⟨e1, e2, e3, hk⟩ := c4 h4
      rw [e1]; exact ne _ l hk (by omega) (t1 h4 h1) (by rw [e2, hl])
  | [], _ :: _, _, h, _, _ | [], [], _ :: _, h, _, _ | _ :: _, [], _, h, _, _ | _ :: _, _ :: _, [], h, _, _ => by
    simp [ResI] at h

theorem ownFree_slot {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {s : Nat} {ls : List UInt64} (hk : Kn Γ s) (k0 : Kk.getD s 0 ≠ 0) (ds : OwnSpec.dead F s = false)
    (es' : env[s]? = some (.b ls)) : ∀ {es : List Nat} {v : List W} {vs : List UInt64},
      ResI σ Kk F Γ env ew es v vs → OwnFree es v vs (ew s)
  | [], [], [], _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨_, _, c3, _, cR⟩ =>
    ⟨fun h1 l hl => fun q => (c3 h1 l hl).1 s ls hk k0 ds es' q.symm, ownFree_slot hk k0 ds es' cR⟩
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by simp [ResI] at h

theorem tr_spec {σ : AH} {Kk : List Nat} {Γ : List (Option Kd)} {env : List W} {ew : Env} (hK2 : ∀ s, Kk.getD s 0 ≤ 2) :
    ∀ (es : List Nat) (v : List W) (vs : List UInt64) (F F1 : List Bool) (es1 : List Nat),
    ResI σ Kk F Γ env ew es v vs → EnvI σ Kk F Γ env ew → OwnSpec.tr F es = some (F1, es1) →
    Mono F F1 ∧ ResI σ Kk F1 Γ env ew es1 v vs ∧ (∀ e ∈ es1, e ≤ 1) ∧ TagLive F es ∧
      ∀ u, OwnFreeT es v vs u → OwnFree es1 v vs u
  | [], [], [], F, F1, es1, _, _, h => by
    simp only [OwnSpec.tr, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨Mono.refl _, trivial, by simp, trivial, fun _ _ => trivial⟩
  | e :: es, x :: v, u0 :: vs, F, F1, es1, hR, hE, h => by
    obtain ⟨c1, c2, c3, c4, cR⟩ := hR
    simp only [OwnSpec.tr] at h
    split at h
    · -- plain entry
      rename_i he4
      split at h
      · rename_i he1
        obtain ⟨⟨F2, es2⟩, ht, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        obtain ⟨m, rR, r3, rT, rF⟩ := tr_spec hK2 es v vs F F2 es2 cR hE ht
        refine ⟨m, ⟨c1, c2, fun h1 l hl => ⟨fun s ls k1 k2 d hs => (c3 h1 l hl).1 s ls k1 k2 (live_of_mono m d) hs, ?_⟩,
          fun h4 => absurd h4 (by omega), rR⟩, ?_, ⟨fun h4 => absurd h4 (by omega), rT⟩, fun u hu => ⟨fun h1 l hl => hu.1 (.inl h1) l hl, rF u hu.2⟩⟩
        · subst h1; subst hl
          exact rF u0 (ownFreeT_of (c3 rfl l rfl).1 cR rT (c3 rfl l rfl).2)
        · intro y hy; rcases List.mem_cons.1 hy with rfl | hy; omega; exact r3 y hy
      · cases h
    · split at h
      · -- pinned word
        rename_i hn4 h0
        obtain ⟨⟨F2, es2⟩, ht, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        obtain ⟨m, rR, r3, rT, rF⟩ := tr_spec hK2 es v vs F F2 es2 cR hE ht
        obtain ⟨e1, e2, e3, hk⟩ := c4 (by omega)
        obtain ⟨w0, ew0, vr, wd⟩ := hE.val _ hk (.inl (by omega))
        rw [e2] at ew0; cases ew0
        obtain ⟨y, rfl⟩ := wd (by omega)
        refine ⟨m, ⟨fun _ => by rw [e1]; exact vr, fun _ => ⟨y, rfl⟩, fun h1 => absurd h1 (by omega),
          fun h4 => absurd h4 (by omega), rR⟩, ?_, ⟨fun _ h1 => absurd h1 (by omega), rT⟩,
          fun u hu => ⟨fun h1 => absurd h1 (by omega), rF u hu.2⟩⟩
        intro z hz; rcases List.mem_cons.1 hz with rfl | hz; omega; exact r3 z hz
      · split at h
        · -- pinned owned
          rename_i hn4 hn0 h1
          obtain ⟨Fh, hc, h⟩ := Option.bind_eq_some_iff.1 h
          obtain ⟨⟨F2, es2⟩, ht, he⟩ := Option.map_eq_some_iff.1 h
          simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
          obtain ⟨d0, d1, mh, dk⟩ := consume_spec hc
          obtain ⟨m, rR, r3, rT, rF⟩ := tr_spec hK2 es v vs Fh F2 es2 (ResI.mono mh cR) (hE.mono mh) ht
          obtain ⟨e1, e2, e3, hk⟩ := c4 (by omega)
          have hks : Kk.getD (e / 4 - 1) 0 = 1 := by omega
          obtain ⟨w0, ew0, vr, -⟩ := hE.val _ hk (.inr d0)
          rw [e2] at ew0; cases ew0
          -- the consumed slot's block differs from every live buffer slot and every tail owned entry
          have neS : ∀ t lt, Kn Γ t → Kk.getD t 0 ≠ 0 → OwnSpec.dead F t = false → env[t]? = some (.b lt) →
              t ≠ e / 4 - 1 → ∀ l, x = .b l → ew t ≠ ew (e / 4 - 1) := by
            intro t lt kt k0 dt et hne l hl
            exact fun q => hE.dist (e / 4 - 1) t l lt (Ne.symm hne) hk kt hks k0 d0 dt (by rw [e2, hl]) et q.symm
          refine ⟨mh.trans m, ⟨fun _ => by rw [e1]; exact vr, fun h0 => absurd h0 (by omega), fun _ l hl => ⟨?_, ?_⟩,
            fun h4 => absurd h4 (by omega), rR⟩, ?_, ⟨fun _ _ => d0, rT.mono mh⟩, fun u hu => ⟨?_, rF u hu.2⟩⟩
          · intro t lt kt k0 dt et
            have hne : t ≠ e / 4 - 1 := by
              intro q; subst q; have := m _ d1; rw [dt] at this; cases this
            rw [e1]; exact neS t lt kt k0 (live_of_mono (mh.trans m) dt) et hne l hl
          · rw [e1]
            apply rF
            refine ownFreeT_of (F := Fh) (fun t lt kt k0 dt et => ?_) (ResI.mono mh cR) rT ?_
            · have hne : t ≠ e / 4 - 1 := by intro q; subst q; rw [d1] at dt; cases dt
              exact neS t lt kt k0 (live_of_mono mh dt) et hne l hl
            · exact ResI.mono mh cR |> fun _ => ownFree_slot hk (by omega) d0 (by rw [e2, hl]) cR |>
                fun h => by
                  clear rF rR rT ht
                  exact h
          · intro z hz; rcases List.mem_cons.1 hz with rfl | hz; omega; exact r3 z hz
          · intro h1' l' hl'; exact hu.1 (.inr ⟨by omega, by omega⟩) l' hl'
        · cases h
  | [], _ :: _, _, _, _, _, h, _, _ | [], [], _ :: _, _, _, _, h, _, _ | _ :: _, [], _, _, _, _, h, _, _
  | _ :: _, _ :: _, [], _, _, _, h, _, _ => by simp [ResI] at h

end NanoMain
