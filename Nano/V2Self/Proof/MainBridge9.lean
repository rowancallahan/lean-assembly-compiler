/- Nano/V2Self/Proof/MainBridge9: the Sem ⇐ sv bridge — prims (RD, ISIZE/LEN, BNEW, BSIZE, BGET, PUT/BPUSH, BSET). -/
import Nano.V2Self.Proof.MainBridge8
import Nano.V2Self.Proof.MainBridge

namespace NanoMain
open Templates

/-! ## the end of an argument list (`fin`) -/

theorem finC_mono {ds : Option (List Nat)} : ∀ (F F2 : List Bool) (o : Nat) (es : List Nat),
    OwnSpec.finC ds F o es = some F2 → Mono F F2
  | F, F2, _, [], h => by simp only [OwnSpec.finC, Option.some.injEq] at h; subst h; exact Mono.refl _
  | F, F2, o, e :: es, h => by
    simp only [OwnSpec.finC] at h
    split at h
    · obtain ⟨F1, h1, h⟩ := Option.bind_eq_some_iff.1 h
      exact (consume_spec h1).2.2.1.trans (finC_mono _ _ _ _ h)
    · exact finC_mono _ _ _ _ h

theorem finC_none1 {ds : Option (List Nat)} : ∀ (F F2 : List Bool) (o : Nat) (es : List Nat),
    (∀ i, i < es.length → OwnSpec.dest ds (o + i) ≠ 1) → OwnSpec.finC ds F o es = some F2 → F2 = F
  | F, F2, _, [], _, h => by simp only [OwnSpec.finC, Option.some.injEq] at h; exact h.symm
  | F, F2, o, e :: es, hd, h => by
    simp only [OwnSpec.finC] at h
    rw [if_neg (by have := hd 0 (by simp); simp_all)] at h
    exact finC_none1 _ _ _ _ (fun i hi => by have := hd (i + 1) (by simp; omega); rwa [Nat.add_assoc, Nat.add_comm 1]) h

theorem finC_cons {ds : Option (List Nat)} : ∀ (F F2 : List Bool) (o : Nat) (es : List Nat),
    OwnSpec.finC ds F o es = some F2 → ∀ s, OwnSpec.dead F s = false → OwnSpec.dead F2 s = true →
    ∃ i e, es[i]? = some e ∧ OwnSpec.own e = true ∧ OwnSpec.dest ds (o + i) = 1 ∧ e / 4 - 1 = s
  | F, F2, _, [], h, s, d0, d1 => by
    simp only [OwnSpec.finC, Option.some.injEq] at h; subst h; rw [d0] at d1; cases d1
  | F, F2, o, e :: es, h, s, d0, d1 => by
    simp only [OwnSpec.finC] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨F1, h1, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨-, c1, -, c3⟩ := consume_spec h1
      by_cases hs : s = e / 4 - 1
      · exact ⟨0, e, rfl, hc.1, by simpa using hc.2, hs.symm⟩
      · obtain ⟨i, e', a, b, c, d⟩ := finC_cons _ _ _ _ h s (by rw [c3 s hs, d0]) d1
        exact ⟨i + 1, e', by simpa using a, b, by rwa [show o + (i + 1) = o + 1 + i by omega], d⟩
    · obtain ⟨i, e', a, b, c, d⟩ := finC_cons _ _ _ _ h s d0 d1
      exact ⟨i + 1, e', by simpa using a, b, by rwa [show o + (i + 1) = o + 1 + i by omega], d⟩

theorem finC_own1 {ds : Option (List Nat)} : ∀ (F F2 : List Bool) (o : Nat) (es : List Nat),
    OwnSpec.finC ds F o es = some F2 → ∀ i e, es[i]? = some e → OwnSpec.own e = true → OwnSpec.dest ds (o + i) = 1 →
    OwnSpec.dead F (e / 4 - 1) = false ∧ OwnSpec.dead F2 (e / 4 - 1) = true
  | F, F2, _, [], _, i, e, he, _, _ => by simp at he
  | F, F2, o, x :: es, h, 0, e, he, ho, hd => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst he
    simp only [Nat.add_zero] at hd
    simp only [OwnSpec.finC] at h
    rw [if_pos (by simp [ho, hd])] at h
    obtain ⟨F1, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨c0, c1, -, -⟩ := consume_spec h1
    exact ⟨c0, finC_mono _ _ _ _ h _ c1⟩
  | F, F2, o, x :: es, h, i + 1, e, he, ho, hd => by
    simp only [List.getElem?_cons_succ] at he
    rw [show o + (i + 1) = o + 1 + i by omega] at hd
    simp only [OwnSpec.finC] at h
    split at h
    · obtain ⟨F1, h1, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨a, b⟩ := finC_own1 _ _ _ _ h i e he ho hd
      exact ⟨live_of_mono (consume_spec h1).2.2.1 a, b⟩
    · exact finC_own1 _ _ _ _ h i e he ho hd

theorem finB_own2 {ds : Option (List Nat)} {F : List Bool} : ∀ (o : Nat) (es : List Nat), OwnSpec.finB ds F o es = true →
    ∀ i e, es[i]? = some e → OwnSpec.own e = true → OwnSpec.dest ds (o + i) = 2 → OwnSpec.dead F (e / 4 - 1) = false
  | _, [], _, i, e, he, _, _ => by simp at he
  | o, x :: es, h, 0, e, he, ho, hd => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst he
    simp only [Nat.add_zero] at hd
    simp only [OwnSpec.finB, Bool.and_eq_true] at h
    simpa [ho, hd] using h.1
  | o, x :: es, h, i + 1, e, he, ho, hd => by
    simp only [List.getElem?_cons_succ] at he
    simp only [OwnSpec.finB, Bool.and_eq_true] at h
    exact finB_own2 (o + 1) es h.2 i e he ho (by rwa [show o + (i + 1) = o + 1 + i by omega] at hd)

theorem fin_some {l : List Nat} {F F2 : List Bool} {es es2 : List Nat} (h : OwnSpec.fin (some l) F es = some (F2, es2)) :
    es.length = l.length ∧ OwnSpec.finC (some l) F 0 es = some F2 ∧ OwnSpec.finB (some l) F2 0 es = true := by
  simp only [OwnSpec.fin, Option.bind_eq_some_iff] at h
  split at h
  · rename_i hl
    obtain ⟨F3, h3, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simpa using hl, h3, by assumption⟩
    · simp at h
  · simp at h

/-! ## arguments -/

theorem resI_tag {σ Kk F Γ env ew} : ∀ {es : List Nat} {v : List W} {vs : List UInt64} (i : Nat),
    ResI σ Kk F Γ env ew es v vs → ∀ {e x u}, es[i]? = some e → v[i]? = some x → vs[i]? = some u → 4 ≤ e →
    u = ew (e / 4 - 1) ∧ env[e / 4 - 1]? = some x ∧ e % 4 = Kk.getD (e / 4 - 1) 0 ∧ Kn Γ (e / 4 - 1)
  | _ :: _, _ :: _, _ :: _, 0, h, _, _, _, he, hx, hu, h4 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at he hx hu; subst he hx hu; exact h.2.2.2.1 h4
  | _ :: _, _ :: _, _ :: _, i + 1, h, _, _, _, he, hx, hu, h4 => by
    simp only [List.getElem?_cons_succ] at he hx hu; exact resI_tag i h.2.2.2.2 he hx hu h4
  | [], _, _, _, _, _, _, _, he, _, _, _ => by simp at he
  | _ :: _, [], _, _, _, _, _, _, _, hx, _, _ => by simp at hx
  | _ :: _, _ :: _, [], _, _, _, _, _, _, _, hu, _ => by simp at hu

/-- a buffer argument at a transfer or borrow destination is its block in `σ` -/
theorem arg_buf {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {es : List Nat} {v : List W} {vs : List UInt64} (hR : ResI σ Kk F Γ env ew es v vs) (hE : EnvI σ Kk F Γ env ew)
    (hr : R2 Kk F) {i e : Nat} {l : List UInt64} {a : UInt64} {G : List Bool} {d : Nat} (he : es[i]? = some e)
    (hv : v[i]? = some (.b l)) (hu : vs[i]? = some a) (hok : OwnSpec.ok1 G e d = true) (hd : d = 1 ∨ d = 2)
    (hlive : OwnSpec.own e = true → OwnSpec.dead F (e / 4 - 1) = false) : σ a.toNat = some l := by
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
    obtain ⟨y, hy, vr, wd⟩ := hE.val _ kn rd
    rw [ex] at hy; cases hy
    rw [ua]; exact vr

/-- an argument at a word destination is that word -/
theorem arg_word {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {es : List Nat} {v : List W} {vs : List UInt64} (hR : ResI σ Kk F Γ env ew es v vs) (hE : EnvI σ Kk F Γ env ew)
    {i e : Nat} {x : W} {u : UInt64} {G : List Bool} (he : es[i]? = some e) (hv : v[i]? = some x) (hu : vs[i]? = some u)
    (hok : OwnSpec.ok1 G e 0 = true) : x = .w u := by
  rcases ok1_word hok with h0 | ⟨h4, h0⟩
  · subst h0
    obtain ⟨c1, c2, -⟩ := resI_idx i hR he hv hu
    obtain ⟨y, rfl⟩ := c2 rfl
    have := c1 (by omega); simp only [VR] at this; rw [this]
  · obtain ⟨ua, ex, ek, kn⟩ := resI_tag i hR he hv hu h4
    obtain ⟨y, hy, vr, wd⟩ := hE.val _ kn (.inl (by omega))
    rw [ex] at hy; cases hy
    obtain ⟨z, rfl⟩ := wd (by omega)
    simp only [VR] at vr; rw [ua, vr]

end NanoMain
