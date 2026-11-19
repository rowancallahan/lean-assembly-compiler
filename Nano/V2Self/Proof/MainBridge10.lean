/- Nano/V2Self/Proof/MainBridge10: the Sem ⇐ sv bridge — CALL, against a callee contract `DefR` (proved per def later). -/
import Nano.V2Self.Proof.MainBridge9

namespace NanoMain
open Templates

/-! ## arguments by index -/

/-- any argument entry that passed `ok1` is related to its word (its slot, if a pin, is readable) -/
theorem arg_vr {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {es : List Nat} {v : List W} {vs : List UInt64} (hR : ResI σ Kk F Γ env ew es v vs) (hE : EnvI σ Kk F Γ env ew)
    (hr : R2 Kk F) {i e : Nat} {x : W} {u : UInt64} {G : List Bool} {d : Nat} (he : es[i]? = some e)
    (hv : v[i]? = some x) (hu : vs[i]? = some u) (hok : OwnSpec.ok1 G e d = true)
    (hlive : OwnSpec.own e = true → OwnSpec.dead F (e / 4 - 1) = false) : VR σ x u := by
  rcases Nat.lt_or_ge e 4 with h4 | h4
  · exact (resI_idx i hR he hv hu).1 h4
  · obtain ⟨ua, ex, ek, kn⟩ := resI_tag i hR he hv hu h4
    have rd : Rd Kk F (e / 4 - 1) := by
      unfold OwnSpec.ok1 at hok
      rw [if_neg (by omega)] at hok
      by_cases h0 : e % 4 = 0
      · exact .inl (by omega)
      · rw [if_neg h0] at hok
        by_cases h1 : e % 4 = 1
        · exact .inr (hlive (by simp [OwnSpec.own, h1]; omega))
        · rw [if_neg h1] at hok
          by_cases h2 : e % 4 = 2
          · exact .inr (hr _ (by omega))
          · rw [if_neg h2] at hok; cases hok
    obtain ⟨y, hy, vr, -⟩ := hE.val _ kn rd
    rw [ex] at hy; cases hy
    rw [ua]; exact vr

/-- an owned argument (destination 1) at index `i`: its block is no live buffer slot's after `fin`, and a pre-existing
block was a consumed slot's -/
theorem own_idx {σ σ1 : AH} {Kk : List Nat} {F x1 F2 : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {ds : List Nat} {es : List Nat} {v : List W} {vs : List UInt64} (hR1 : ResI σ1 Kk x1 Γ env ew es v vs)
    (hE1 : EnvI σ1 Kk x1 Γ env ew) (hS1 : Src σ Γ F x1 env ew es v vs) (hM1 : Mono F x1)
    (hf : OwnSpec.finC (some ds) x1 0 es = some F2) {i : Nat} (hd0 : OwnSpec.dest (some ds) i = 1)
    {e0 : Nat} {l : List UInt64} {a : UInt64} {G : List Bool} (he0 : es[i]? = some e0) (hv0 : v[i]? = some (.b l))
    (hu0 : vs[i]? = some a) (hok : OwnSpec.ok1 G e0 1 = true) :
    σ1 a.toNat = some l ∧
    (∀ s ls, Kn Γ s → Kk.getD s 0 ≠ 0 → OwnSpec.dead F2 s = false → env[s]? = some (.b ls) → ew s ≠ a) ∧
    ((σ a.toNat).isSome → ∃ j l', Kn Γ j ∧ Cons F F2 j ∧ env[j]? = some (.b l') ∧ ew j = a) := by
  have mf := finC_mono _ _ _ _ hf
  rcases Nat.lt_or_ge e0 4 with h4 | h4
  · have e1 : e0 = 1 := by
      have := (ok1_one hok).1 h4
      rcases Nat.lt_or_ge e0 1 with h0 | h0
      · obtain ⟨y, hy⟩ := (resI_idx i hR1 he0 hv0 hu0).2.1 (by omega); cases hy
      · omega
    subst e1
    obtain ⟨c1, -, c3⟩ := resI_idx i hR1 he0 hv0 hu0
    refine ⟨c1 (by omega), fun s ls k1 k2 d hs => c3 rfl l rfl s ls k1 k2 (live_of_mono mf d) hs, fun hs => ?_⟩
    obtain ⟨j, l', a1, b, c, d⟩ := src_idx i hS1 he0 hv0 hu0 hs
    exact ⟨j, l', a1, ⟨b.1, mf j b.2⟩, c, d⟩
  · obtain ⟨ua, ex, ek, kn⟩ := resI_tag i hR1 he0 hv0 hu0 h4
    have h1 : e0 % 4 = 1 := by
      have := (ok1_one hok).2 h4
      rcases Nat.lt_or_ge (e0 % 4) 1 with h0 | h0
      · obtain ⟨y, hy, -, wd⟩ := hE1.val _ kn (.inl (by omega))
        rw [ex] at hy; cases hy; obtain ⟨z, hz⟩ := wd (by omega); cases hz
      · omega
    have ho : OwnSpec.own e0 = true := by simp [OwnSpec.own, h1]; omega
    obtain ⟨d0, d1⟩ := finC_own1 _ _ _ _ hf i e0 he0 ho (by simpa using hd0)
    obtain ⟨y, hy, vr, -⟩ := hE1.val _ kn (.inr d0)
    rw [ex] at hy; cases hy
    refine ⟨by rw [ua]; exact vr, fun s ls k1 k2 d hs => ?_, fun _ => ⟨e0 / 4 - 1, l, kn, ⟨live_of_mono hM1 d0, d1⟩, ex, ua.symm⟩⟩
    have hne : e0 / 4 - 1 ≠ s := fun q => by subst q; rw [d1] at d; cases d
    rw [ua]
    exact fun q => hE1.dist (e0 / 4 - 1) s l ls hne kn k1 (by omega) k2 d0 (live_of_mono mf d) ex hs q.symm

/-- two owned pins at transfer destinations name different slots -/
theorem finC_two {ds : Option (List Nat)} : ∀ (F F2 : List Bool) (o : Nat) (es : List Nat),
    OwnSpec.finC ds F o es = some F2 → ∀ i i' e e', i < i' → es[i]? = some e → es[i']? = some e' →
    OwnSpec.own e = true → OwnSpec.own e' = true → OwnSpec.dest ds (o + i) = 1 → OwnSpec.dest ds (o + i') = 1 →
    e / 4 - 1 ≠ e' / 4 - 1
  | F, F2, _, [], _, i, _, e, _, _, he, _, _, _, _, _ => by simp at he
  | F, F2, o, x :: es, h, 0, i' + 1, e, e', _, he, he', ho, ho', hd, hd' => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst he
    simp only [List.getElem?_cons_succ] at he'
    simp only [Nat.add_zero] at hd
    simp only [OwnSpec.finC] at h
    rw [if_pos (by simp [ho, hd])] at h
    obtain ⟨F1, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨-, c1, -, -⟩ := consume_spec h1
    obtain ⟨d0, -⟩ := finC_own1 _ _ _ _ h i' e' he' ho' (by rwa [show o + (i' + 1) = o + 1 + i' by omega] at hd')
    intro q; rw [q, d0] at c1; cases c1
  | F, F2, o, x :: es, h, i + 1, i' + 1, e, e', hi, he, he', ho, ho', hd, hd' => by
    simp only [List.getElem?_cons_succ] at he he'
    rw [show o + (i + 1) = o + 1 + i by omega] at hd
    rw [show o + (i' + 1) = o + 1 + i' by omega] at hd'
    simp only [OwnSpec.finC] at h
    split at h
    · obtain ⟨F1, -, h⟩ := Option.bind_eq_some_iff.1 h
      exact finC_two _ _ _ _ h i i' e e' (by omega) he he' ho ho' hd hd'
    · exact finC_two _ _ _ _ h i i' e e' (by omega) he he' ho ho' hd hd'
  | _, _, _, _ :: _, _, _, 0, _, _, hi, _, _, _, _, _, _ => by omega

theorem dest_some {P : List Nat} {j d : Nat} (h : P[j]? = some d) : OwnSpec.dest (some P) j = d := by
  simp [OwnSpec.dest, List.getD_eq_getElem?_getD, h]

theorem get_of_len {α β : Type} {a : List α} {b : List β} (hl : a.length = b.length) {j : Nat} {y : β} (h : b[j]? = some y) :
    ∃ x, a[j]? = some x := by
  have : j < b.length := (List.getElem?_eq_some_iff.1 h).1
  exact ⟨a[j]'(by omega), List.getElem?_eq_getElem (by omega)⟩

/-- a buffer-valued pin at any destination names a readable slot of kind ≠ 0 -/
theorem pin_live {σ : AH} {Kk : List Nat} {x1 yF : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {P es : List Nat} {v : List W} {vs : List UInt64} (hR1 : ResI σ Kk x1 Γ env ew es v vs)
    (hE1 : EnvI σ Kk x1 Γ env ew) (hr1 : R2 Kk x1) (hfc : OwnSpec.finC (some P) x1 0 es = some yF)
    (hfb : OwnSpec.finB (some P) yF 0 es = true) {j e : Nat} {l : List UInt64} {u : UInt64} {G : List Bool}
    (he : es[j]? = some e) (hv : v[j]? = some (.b l)) (hu : vs[j]? = some u)
    (hG : OwnSpec.ok1 G e (OwnSpec.dest (some P) j) = true) (h4 : 4 ≤ e) :
    OwnSpec.dead x1 (e / 4 - 1) = false ∧ Kk.getD (e / 4 - 1) 0 ≠ 0 ∧
      (e % 4 = 1 → OwnSpec.dest (some P) j = 1 ∨ (OwnSpec.dest (some P) j = 2 ∧ OwnSpec.dead yF (e / 4 - 1) = false)) := by
  obtain ⟨ua, ex, ek, kn⟩ := resI_tag j hR1 he hv hu h4
  have mf := finC_mono _ _ _ _ hfc
  unfold OwnSpec.ok1 at hG
  rw [if_neg (by omega)] at hG
  by_cases h0 : e % 4 = 0
  · exfalso
    obtain ⟨y, hy, -, wd⟩ := hE1.val _ kn (.inl (by omega))
    rw [ex] at hy; cases hy; obtain ⟨z, hz⟩ := wd (by omega); cases hz
  · rw [if_neg h0] at hG
    by_cases h1 : e % 4 = 1
    · rw [if_pos h1] at hG
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hG
      have ho : OwnSpec.own e = true := by simp [OwnSpec.own, h1]; omega
      rcases hG.1 with hd | hd
      · exact ⟨(finC_own1 _ _ _ _ hfc j e he ho (by simpa using hd)).1, by omega, fun _ => .inl hd⟩
      · have := finB_own2 0 es hfb j e he ho (by simpa using hd)
        exact ⟨live_of_mono mf this, by omega, fun _ => .inr ⟨hd, this⟩⟩
    · rw [if_neg h1] at hG
      by_cases h2 : e % 4 = 2
      · exact ⟨hr1 _ (by omega), by omega, fun h => absurd h h1⟩
      · rw [if_neg h2] at hG; cases hG

/-- an owned argument's block differs from every other buffer argument's -/
theorem args_distinct {σ : AH} {Kk : List Nat} {x1 yF : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {P es : List Nat} {v : List W} {vs : List UInt64} (hR1 : ResI σ Kk x1 Γ env ew es v vs)
    (hE1 : EnvI σ Kk x1 Γ env ew) (hr1 : R2 Kk x1) (hfc : OwnSpec.finC (some P) x1 0 es = some yF)
    (hfb : OwnSpec.finB (some P) yF 0 es = true)
    (hok : ∀ i e, es[i]? = some e → ∃ G, OwnSpec.ok1 G e (OwnSpec.dest (some P) i) = true) :
    ∀ (j j' : Nat) (l l' : List UInt64) (u u' : UInt64), j ≠ j' → P[j]? = some 1 → v[j]? = some (W.b l) →
      v[j']? = some (W.b l') → vs[j]? = some u → vs[j']? = some u' → u ≠ u' := by
  intro j j' l l' u u' hne hP hv hv' hu hu'
  have ln := hR1.len
  obtain ⟨e, he⟩ := get_of_len ln.1 hv
  obtain ⟨e', he'⟩ := get_of_len ln.1 hv'
  obtain ⟨G, hG⟩ := hok j e he
  obtain ⟨G', hG'⟩ := hok j' e' he'
  have dj := dest_some hP
  have mf := finC_mono _ _ _ _ hfc
  rcases Nat.lt_or_ge e 4 with h4 | h4
  · -- a plain owned temporary
    rw [dj] at hG
    have e1 : e = 1 := by
      have := (ok1_one hG).1 h4
      rcases Nat.lt_or_ge e 1 with h0 | h0
      · obtain ⟨y, hy⟩ := (resI_idx j hR1 he hv hu).2.1 (by omega); cases hy
      · omega
    subst e1
    obtain ⟨-, -, c3⟩ := resI_idx j hR1 he hv hu
    rcases Nat.lt_or_ge e' 4 with h4' | h4'
    · have e1' : e' = 1 := by
        unfold OwnSpec.ok1 at hG'; rw [if_pos h4'] at hG'
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hG'
        rcases hG' with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · obtain ⟨y, hy⟩ := (resI_idx j' hR1 he' hv' hu').2.1 rfl; cases hy
        · rfl
      subst e1'
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact resI_pair j j' hR1 h he he' hv hv' hu hu'
      · exact Ne.symm (resI_pair j' j hR1 h he' he hv' hv hu' hu)
    · obtain ⟨ua, ex, -, kn⟩ := resI_tag j' hR1 he' hv' hu' h4'
      obtain ⟨d', k0, -⟩ := pin_live hR1 hE1 hr1 hfc hfb he' hv' hu' hG' h4'
      rw [ua]; exact Ne.symm (c3 rfl l rfl _ l' kn k0 d' ex)
  · -- an owned pin of slot k
    obtain ⟨ua, ex, ek, kn⟩ := resI_tag j hR1 he hv hu h4
    obtain ⟨d0, k0, hown⟩ := pin_live hR1 hE1 hr1 hfc hfb he hv hu hG h4
    have h1 : e % 4 = 1 := by
      rw [dj] at hG; have := (ok1_one hG).2 h4
      rcases Nat.lt_or_ge (e % 4) 1 with h0 | h0
      · exact absurd (by omega : Kk.getD (e / 4 - 1) 0 = 0) k0
      · omega
    have ho : OwnSpec.own e = true := by simp [OwnSpec.own, h1]; omega
    obtain ⟨-, dk⟩ := finC_own1 _ _ _ _ hfc j e he ho (by simpa using dj)
    rcases Nat.lt_or_ge e' 4 with h4' | h4'
    · have e1' : e' = 1 := by
        unfold OwnSpec.ok1 at hG'; rw [if_pos h4'] at hG'
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hG'
        rcases hG' with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · obtain ⟨y, hy⟩ := (resI_idx j' hR1 he' hv' hu').2.1 rfl; cases hy
        · rfl
      subst e1'
      obtain ⟨-, -, c3⟩ := resI_idx j' hR1 he' hv' hu'
      rw [ua]; exact c3 rfl l' rfl _ l kn k0 d0 ex
    · obtain ⟨ua', ex', ek', kn'⟩ := resI_tag j' hR1 he' hv' hu' h4'
      obtain ⟨d0', k0', hown'⟩ := pin_live hR1 hE1 hr1 hfc hfb he' hv' hu' hG' h4'
      have hkk : e / 4 - 1 ≠ e' / 4 - 1 := by
        intro q
        by_cases h1' : e' % 4 = 1
        · rcases hown' h1' with hd' | ⟨-, dl⟩
          · have ho' : OwnSpec.own e' = true := by simp [OwnSpec.own, h1']; omega
            rcases Nat.lt_or_gt_of_ne hne with h | h
            · exact finC_two _ _ _ _ hfc j j' e e' h he he' ho ho' (by simpa using dj) (by simpa using hd') q
            · exact finC_two _ _ _ _ hfc j' j e' e h he' he ho' ho (by simpa using hd') (by simpa using dj) q.symm
          · rw [← q, dk] at dl; cases dl
        · rw [← q] at ek'; omega
      rw [ua, ua']
      exact hE1.dist _ _ l l' hkk kn kn' (by omega) k0' d0 d0' ex ex'

end NanoMain
