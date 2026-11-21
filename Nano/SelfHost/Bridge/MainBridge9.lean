/- Nano/SelfHost/Bridge/MainBridge9: the Sem ⇐ sv bridge — prims (RD, ISIZE/LEN, BNEW, BSIZE, BGET, PUT/BPUSH, BSET). -/
import Nano.SelfHost.Bridge.MainBridge8
import Nano.SelfHost.Bridge.MainBridge

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

/-! ## the owned buffer argument of PUT / BPUSH / BSET -/

/-- the transferred block `a` (argument 0, destination 1): no live buffer slot holds it after `fin`, and if it existed
before the node it is the block of a slot consumed by the node -/
theorem own0 {σ σ1 : AH} {Kk : List Nat} {F x1 F2 : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    {ds : List Nat} {es : List Nat} {v : List W} {vs : List UInt64} (hR1 : ResI σ1 Kk x1 Γ env ew es v vs)
    (hE1 : EnvI σ1 Kk x1 Γ env ew) (hS1 : Src σ Γ F x1 env ew es v vs) (hM1 : Mono F x1)
    (hf : OwnSpec.finC (some ds) x1 0 es = some F2) (hd0 : OwnSpec.dest (some ds) 0 = 1)
    {e0 : Nat} {l : List UInt64} {a : UInt64} {G : List Bool} (he0 : es[0]? = some e0) (hv0 : v[0]? = some (.b l))
    (hu0 : vs[0]? = some a) (hok : OwnSpec.ok1 G e0 1 = true) :
    σ1 a.toNat = some l ∧
    (∀ s ls, Kn Γ s → Kk.getD s 0 ≠ 0 → OwnSpec.dead F2 s = false → env[s]? = some (.b ls) → ew s ≠ a) ∧
    ((σ a.toNat).isSome → ∃ j l', Kn Γ j ∧ Cons F F2 j ∧ env[j]? = some (.b l') ∧ ew j = a) := by
  have mf := finC_mono _ _ _ _ hf
  rcases Nat.lt_or_ge e0 4 with h4 | h4
  · have e1 : e0 = 1 := by
      have := (ok1_one hok).1 h4
      rcases Nat.lt_or_ge e0 1 with h0 | h0
      · obtain ⟨y, hy⟩ := (resI_idx 0 hR1 he0 hv0 hu0).2.1 (by omega); cases hy
      · omega
    subst e1
    obtain ⟨c1, -, c3⟩ := resI_idx 0 hR1 he0 hv0 hu0
    refine ⟨c1 (by omega), fun s ls k1 k2 d hs => c3 rfl l rfl s ls k1 k2 (live_of_mono mf d) hs, fun hs => ?_⟩
    obtain ⟨j, l', a1, b, c, d⟩ := src_idx 0 hS1 he0 hv0 hu0 hs
    exact ⟨j, l', a1, ⟨b.1, mf j b.2⟩, c, d⟩
  · obtain ⟨ua, ex, ek, kn⟩ := resI_tag 0 hR1 he0 hv0 hu0 h4
    have h1 : e0 % 4 = 1 := by
      have := (ok1_one hok).2 h4
      rcases Nat.lt_or_ge (e0 % 4) 1 with h0 | h0
      · obtain ⟨y, hy, -, wd⟩ := hE1.val _ kn (.inl (by omega))
        rw [ex] at hy; cases hy; obtain ⟨z, hz⟩ := wd (by omega); cases hz
      · omega
    have ho : OwnSpec.own e0 = true := by simp [OwnSpec.own, h1]; omega
    obtain ⟨d0, d1⟩ := finC_own1 _ _ _ _ hf 0 e0 he0 ho (by simpa using hd0)
    obtain ⟨y, hy, vr, -⟩ := hE1.val _ kn (.inr d0)
    rw [ex] at hy; cases hy
    refine ⟨by rw [ua]; exact vr, fun s ls k1 k2 d hs => ?_, fun _ => ⟨e0 / 4 - 1, l, kn, ⟨live_of_mono hM1 d0, d1⟩, ex, ua.symm⟩⟩
    have hne : e0 / 4 - 1 ≠ s := fun q => by subst q; rw [d1] at d; cases d
    rw [ua]
    exact fun q => hE1.dist (e0 / 4 - 1) s l ls hne kn k1 (by omega) k2 d0 (live_of_mono mf d) ex hs q.symm

theorem VR.upd_ne {σ : AH} {a : Nat} {l' : List UInt64} {x : W} {u : UInt64} (h : VR σ x u)
    (hn : ∀ l, x = .b l → u.toNat ≠ a) : VR (upd σ a l') x u := by
  cases x with
  | w y => exact h
  | b l => show (if u.toNat = a then some l' else σ u.toNat) = some l; rw [if_neg (hn l rfl)]; exact h

/-- the frame after a block update that no readable buffer slot holds -/
theorem EnvI.upd {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {env : List W} {ew : Env}
    (hE : EnvI σ Kk F Γ env ew) {a : UInt64} (l' : List UInt64)
    (hn : ∀ s ls, Kn Γ s → Kk.getD s 0 ≠ 0 → OwnSpec.dead F s = false → env[s]? = some (.b ls) → ew s ≠ a) :
    EnvI (upd σ a.toNat l') Kk F Γ env ew where
  len := hE.len
  ty := hE.ty
  val s ks hr := by
    obtain ⟨y, hy, vr, wd⟩ := hE.val s ks hr
    refine ⟨y, hy, VR.upd_ne vr fun l hl q => ?_, wd⟩
    subst hl
    have k0 : Kk.getD s 0 ≠ 0 := fun k0 => by obtain ⟨z, hz⟩ := wd k0; cases hz
    have live : OwnSpec.dead F s = false := by rcases hr with h | h; exact absurd h k0; exact h
    exact hn s l ks k0 live hy (UInt64.toNat_inj.1 q)
  dist := hE.dist

/-! ## PRIM -/

/-- E's frame constants agree with the `Sem` context -/
structure CtxR (cx : Ctx) (K : SC) : Prop where
  κ : K.κ = cx.κ
  c29 : K.c29 = UInt64.ofNat cx.inp.length
  inp : K.inp = inpW cx.inp
  inl : cx.inp.length < 2 ^ 64

theorem kinds_cases {ps rs : List Kd} {p : Nat} (h : primK p ps = some rs) :
    (p = 1 ∧ ps = []) ∨ (p = 2 ∧ ps = [.w]) ∨ (p = 3 ∧ ps = []) ∨ (p = 4 ∧ ps = [.b, .w]) ∨ (p = 5 ∧ ps = []) ∨
    (p = 6 ∧ ps = [.b]) ∨ (p = 7 ∧ ps = [.b, .w]) ∨ (p = 8 ∧ ps = [.b, .w, .w]) ∨ (p = 9 ∧ ps = [.b, .w]) := by
  unfold primK at h; split at h <;> simp_all

theorem kOf_w {v : List W} (h : kOf v = [.w]) : ∃ x, v = [.w x] := by
  match v, h with | [.w x], _ => exact ⟨x, rfl⟩
theorem kOf_b {v : List W} (h : kOf v = [.b]) : ∃ l, v = [.b l] := by
  match v, h with | [.b l], _ => exact ⟨l, rfl⟩
theorem kOf_bw {v : List W} (h : kOf v = [.b, .w]) : ∃ l x, v = [.b l, .w x] := by
  match v, h with | [.b l, .w x], _ => exact ⟨l, x, rfl⟩
theorem kOf_bww {v : List W} (h : kOf v = [.b, .w, .w]) : ∃ l x y, v = [.b l, .w x, .w y] := by
  match v, h with | [.b l, .w x, .w y], _ => exact ⟨l, x, y, rfl⟩

theorem len3 {α : Type} {l : List α} (h : l.length = 3) : ∃ a b c, l = [a, b, c] := by
  match l, h with | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
theorem len2 {α : Type} {l : List α} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with | [a, b], _ => exact ⟨a, b, rfl⟩

theorem bufAt_of {hb κ : Nat} {H : Hp} {σ : AH} (hA : AHeap hb κ H σ) {a : UInt64} {l : List UInt64}
    (h : σ a.toNat = some l) : BufAt hb κ H a l := by
  have := (hA.1 _ _ h).2; rwa [UInt64.ofNat_toNat] at this

theorem node_prim (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hW : RsW oc) (hX : CtxR cx K) (p : Nat)
    (as : List ParSpec.Nd) (hN : ∀ n ∈ as, NodeOK cx K oc D n) : NodeOK cx K oc D (ParSpec.Nd.prim p as) := by
  intro hC hK2 Γ ks F F' es env ew σ sp H vs H' hT hc hE hA h8 hhb hr hs
  cases hT with
  | prim tl hpk hnil =>
    rename_i ps
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hc
    obtain ⟨⟨x1, x2⟩, hl, ⟨yF, yE⟩, hf, he⟩ := hc
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨-, hk⟩ := evL_ok hC tl env hE.ty
    obtain ⟨-, hfc, hfb⟩ := fin_some hf
    rcases kinds_cases hpk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- 1
      have h0 : as = [] := hnil (by decide)
      subst h0
      simp only [OwnSpec.lstA, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
      simp only [OwnSpec.finC, Option.some.injEq] at hfc; subst hfc
      simp (config := { decide := true }) only [sv, if_true, if_false] at hs
      obtain ⟨rfl, rfl⟩ := leafS_some hs
      refine ⟨σ, [.w cx.inp.length.toUInt64], by simp [ev, evL, prim, bind, Except.bind, pure, Except.pure], hA, ?_, hE,
        Ch.refl _ _ _ _ _, Mono.refl _, h8, hhb, by simp [Src, OwnSpec.rk], by simp [OwnSpec.rk], Grow.refl _⟩
      simp [ResI, VR, OwnSpec.rk, hX.c29, Nat.toUInt64_eq]
    · -- 2 RD
      simp (config := { decide := true }) only [sv, if_true, if_false] at hs
      unfold fin1S at hs
      obtain ⟨⟨ua, H1⟩, hsl, hrest⟩ := Option.bind_eq_some_iff.1 hs
      obtain ⟨σ1, v, esN, hesA, evl, hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hN tl hl hE hA h8 hhb hr hsl
      simp only [List.nil_append] at hesA; subst hesA
      have kv := hk v evl
      have ln := hR1.len
      obtain ⟨x, rfl⟩ := kOf_w kv
      obtain ⟨u0, rfl⟩ := List.length_eq_one_iff.1 (show ua.length = 1 by simp at ln; omega)
      obtain ⟨e0, rfl⟩ := List.length_eq_one_iff.1 (show x2.length = 1 by simp at ln; omega)
      obtain ⟨G, hG⟩ := hok 0 e0 rfl
      have := arg_word hR1 hE1 (i := 0) rfl rfl rfl (by simpa [OwnSpec.dest, OwnSpec.dsP] using hG)
      cases this
      simp (config := { decide := true }) only [primF1, if_true, hX.c29, hX.inp, rd_agree _ hX.inl, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      have := finC_none1 _ _ _ _ (fun i hi => by simp at hi; subst hi; simp [OwnSpec.dest, OwnSpec.dsP]) hfc; subst this
      refine ⟨σ1, [.w (cx.inp.getD x.toNat 0).toUInt64], by simp [ev, evl, prim, bind, Except.bind, pure, Except.pure],
        hA1, ?_, hE1, hCh1, hM1, h81, hb1, by simp [Src, OwnSpec.rk], by simp [OwnSpec.rk], hGr⟩
      simp [ResI, VR, OwnSpec.rk]
    · -- 3
      have h0 : as = [] := hnil (by decide)
      subst h0
      simp only [OwnSpec.lstA, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
      simp only [OwnSpec.finC, Option.some.injEq] at hfc; subst hfc
      simp (config := { decide := true }) only [sv, if_true, if_false] at hs
      obtain ⟨rfl, rfl⟩ := leafS_some hs
      refine ⟨σ, [.w cx.inp.length.toUInt64], by simp [ev, evL, prim, bind, Except.bind, pure, Except.pure], hA, ?_, hE,
        Ch.refl _ _ _ _ _, Mono.refl _, h8, hhb, by simp [Src, OwnSpec.rk], by simp [OwnSpec.rk], Grow.refl _⟩
      simp [ResI, VR, OwnSpec.rk, hX.c29, Nat.toUInt64_eq]
    · -- 4 PUT
      simp (config := { decide := true }) only [sv, if_true, if_false] at hs
      unfold fin2S at hs
      obtain ⟨⟨ua, H1⟩, hsl, hrest⟩ := Option.bind_eq_some_iff.1 hs
      obtain ⟨σ1, v, esN, hesA, evl, hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hN tl hl hE hA h8 hhb hr hsl
      simp only [List.nil_append] at hesA; subst hesA
      have kv := hk v evl
      have ln := hR1.len
      have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
      obtain ⟨l, x, rfl⟩ := kOf_bw kv
      obtain ⟨a, xw, rfl⟩ := len2 (show ua.length = 2 by simp at ln; omega)
      obtain ⟨e0, e1, rfl⟩ := len2 (show x2.length = 2 by simp at ln; omega)
      obtain ⟨G, hG⟩ := hok 0 e0 rfl
      obtain ⟨G1, hG1⟩ := hok 1 e1 rfl
      simp only [OwnSpec.dest, OwnSpec.dsP, List.length_nil, Nat.zero_add] at hG hG1
      simp at hG hG1
      have hx := W.w.inj (arg_word hR1 hE1 (i := 1) rfl rfl rfl hG1); subst x
      have hd : OwnSpec.dest (some (OwnSpec.dsP 4)) 0 = 1 := by simp [OwnSpec.dest, OwnSpec.dsP]
      obtain ⟨hσ, hn, hsrc⟩ := own0 hR1 hE1 hS1 hM1 hfc hd (e0 := e0) (l := l) (a := a) rfl rfl rfl hG
      have hB := bufAt_of hA1 hσ
      have hlt : l.length < K.κ := by
        obtain ⟨-, -, -, -, b5, b6, -⟩ := id hB
        have h7 : (7 : Nat) ≠ 4 := by decide
        simp only [primF2, if_neg h7.symm] at hrest
        cases h' : bpushF K.hb a xw (sp - 16) H1 with
        | none => rw [h'] at hrest; cases hrest
        | some r =>
          unfold bpushF at h'
          rw [bufInfo_at hB, Option.bind_some, toNat_ofNat_lt (show l.length < 2 ^ 64 by omega),
            toNat_ofNat_lt (show K.κ < 2 ^ 64 by omega)] at h'
          split at h'
          · omega
          · cases h'
      obtain ⟨H2, hp, hB2, ht2, hfr2⟩ := bpush_at hB hlt xw (sp - 16)
      simp (config := { decide := true }) only [primF2, if_false, hp, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      have hev : ev cx (ParSpec.Nd.prim 4 as) env = .ok (.inl [.b (l ++ [xw])]) := by
        simp [ev, evl, prim, push, bind, Except.bind, pure, Except.pure, ← hX.κ, hlt]
      have mf := finC_mono _ _ _ _ hfc
      have rk1 : OwnSpec.rk 4 = 1 := by decide
      refine ⟨upd σ1 a.toNat (l ++ [xw]), [.b (l ++ [xw])], hev,
        aheap_update hA1 hσ (by rwa [UInt64.ofNat_toNat]) ht2 (by rwa [UInt64.ofNat_toNat]), ?_,
        (hE1.mono mf).upd _ hn, fun a' ha hn' => ?_, hM1.trans mf, by rw [ht2]; exact h81, by rw [ht2]; exact hb1, ?_,
        by simp [rk1], hGr.trans (grow_upd _ _ _)⟩
      · rw [rk1]
        exact ⟨fun _ => by simp [VR, upd], fun h => absurd h (by decide), fun _ l' hl' => ⟨hn, trivial⟩,
          fun h => absurd h (by decide), trivial⟩
      · have e1 : σ1 a' = σ a' := (hCh1.weak mf) a' ha hn'
        simp only [upd]; split
        · rename_i q; subst q
          obtain ⟨j, l', kj, cj, ej, wj⟩ := hsrc ha
          exact absurd (congrArg UInt64.toNat wj) (hn' j l' kj cj ej)
        · exact e1
      · rw [rk1]; exact ⟨fun _ _ _ hs => hsrc hs, trivial⟩
    · -- 5 BNEW
      have h0 : as = [] := hnil (by decide)
      subst h0
      simp only [OwnSpec.lstA, Option.some.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
      simp only [OwnSpec.finC, Option.some.injEq] at hfc; subst hfc
      simp (config := { decide := true }) only [sv, if_true, if_false, one, Option.map_eq_some_iff, Prod.mk.injEq] at hs
      obtain ⟨⟨a, H2⟩, hb, rfl, rfl⟩ := hs
      obtain ⟨hB, htop, hat, hfr⟩ := bnew_at hhb h8 hb
      obtain ⟨hA', hfresh⟩ := aheap_new hA hB htop hat hfr
      have hn : ∀ s ls, Kn Γ s → oc.K.getD s 0 ≠ 0 → OwnSpec.dead F s = false → env[s]? = some (.b ls) → ew s ≠ a := by
        intro s ls ks k0 d hs q
        obtain ⟨y, hy, vr, -⟩ := hE.val s ks (.inr d)
        rw [hs] at hy; cases hy
        simp only [VR] at vr; rw [q, hfresh] at vr; cases vr
      refine ⟨upd σ a.toNat [], [.b []], by simp [ev, evL, prim, bind, Except.bind, pure, Except.pure], hA', ?_,
        hE.upd [] hn, fun a' ha _ => ?_, Mono.refl _, by show H2.top % 8 = 0; omega, by show K.hb ≤ H2.top; omega, ?_,
        by simp [OwnSpec.rk], grow_upd _ _ _⟩
      · refine ⟨fun _ => by simp [VR, upd], fun h => by simp [OwnSpec.rk] at h, fun _ l hl => ⟨?_, trivial⟩,
          fun h => by simp [OwnSpec.rk] at h, trivial⟩
        cases hl; exact hn
      · simp only [upd]; split
        · rename_i q; subst q; rw [hfresh] at ha; cases ha
        · rfl
      · exact ⟨fun _ _ _ hs => (by rw [hfresh] at hs; simp at hs), trivial⟩
    · -- 6 BSIZE
      simp (config := { decide := true }) only [sv, if_true, if_false] at hs
      unfold fin1S at hs
      obtain ⟨⟨ua, H1⟩, hsl, hrest⟩ := Option.bind_eq_some_iff.1 hs
      obtain ⟨σ1, v, esN, hesA, evl, hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hN tl hl hE hA h8 hhb hr hsl
      simp only [List.nil_append] at hesA; subst hesA
      have kv := hk v evl
      have ln := hR1.len
      have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
      obtain ⟨l, rfl⟩ := kOf_b kv
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 (show ua.length = 1 by simp at ln; omega)
      obtain ⟨e0, rfl⟩ := List.length_eq_one_iff.1 (show x2.length = 1 by simp at ln; omega)
      obtain ⟨G, hG⟩ := hok 0 e0 rfl
      simp only [OwnSpec.dest, OwnSpec.dsP, List.length_nil, Nat.add_zero] at hG
      have := finC_none1 _ _ _ _ (fun i hi => by simp at hi; subst hi; simp [OwnSpec.dest, OwnSpec.dsP]) hfc; subst this
      have hσ := arg_buf hR1 hE1 hr1 (i := 0) rfl rfl rfl hG (.inr rfl)
        (fun ho => finB_own2 0 _ hfb 0 e0 rfl ho (by simp [OwnSpec.dest, OwnSpec.dsP]))
      simp (config := { decide := true }) only [primF1, if_false, bsize_at (bufAt_of hA1 hσ), Option.map_some,
        Option.some.injEq, Prod.mk.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      refine ⟨σ1, [.w l.length.toUInt64], by simp [ev, evl, prim, bind, Except.bind, pure, Except.pure],
        hA1, ?_, hE1, hCh1, hM1, h81, hb1, by simp [Src, OwnSpec.rk], by simp [OwnSpec.rk], hGr⟩
      simp [ResI, VR, OwnSpec.rk, Nat.toUInt64_eq]
    · -- 7 BGET
      simp (config := { decide := true }) only [sv, if_true, if_false] at hs
      unfold fin2S at hs
      obtain ⟨⟨ua, H1⟩, hsl, hrest⟩ := Option.bind_eq_some_iff.1 hs
      obtain ⟨σ1, v, esN, hesA, evl, hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hN tl hl hE hA h8 hhb hr hsl
      simp only [List.nil_append] at hesA; subst hesA
      have kv := hk v evl
      have ln := hR1.len
      have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
      obtain ⟨l, i, rfl⟩ := kOf_bw kv
      obtain ⟨a, iw, rfl⟩ := len2 (show ua.length = 2 by simp at ln; omega)
      obtain ⟨e0, e1, rfl⟩ := len2 (show x2.length = 2 by simp at ln; omega)
      obtain ⟨G, hG⟩ := hok 0 e0 rfl
      obtain ⟨G1, hG1⟩ := hok 1 e1 rfl
      simp only [OwnSpec.dest, OwnSpec.dsP, List.length_nil, Nat.zero_add] at hG hG1
      simp at hG hG1
      have hx := W.w.inj (arg_word hR1 hE1 (i := 1) rfl rfl rfl hG1); subst i
      have := finC_none1 _ _ _ _ (fun j hi => by
        simp at hi; rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp [OwnSpec.dest, OwnSpec.dsP]) hfc
      subst this
      have hσ := arg_buf hR1 hE1 hr1 (i := 0) rfl rfl rfl hG (.inr rfl)
        (fun ho => finB_own2 0 _ hfb 0 e0 rfl ho (by simp [OwnSpec.dest, OwnSpec.dsP]))
      simp (config := { decide := true }) only [primF2, if_true, bget_at (bufAt_of hA1 hσ), Option.map_some,
        Option.some.injEq, Prod.mk.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      refine ⟨σ1, [.w (l.getD iw.toNat 0)], by simp [ev, evl, prim, bind, Except.bind, pure, Except.pure],
        hA1, ?_, hE1, hCh1, hM1, h81, hb1, by simp [Src, OwnSpec.rk], by simp [OwnSpec.rk], hGr⟩
      simp [ResI, VR, OwnSpec.rk]
    · -- 8 BSET
      simp (config := { decide := true }) only [sv, if_true, if_false] at hs
      unfold fin3S at hs
      obtain ⟨⟨ua, H1⟩, hsl, hrest⟩ := Option.bind_eq_some_iff.1 hs
      obtain ⟨σ1, v, esN, hesA, evl, hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hN tl hl hE hA h8 hhb hr hsl
      simp only [List.nil_append] at hesA; subst hesA
      have kv := hk v evl
      have ln := hR1.len
      have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
      obtain ⟨l, i, x, rfl⟩ := kOf_bww kv
      obtain ⟨a, iw, xw, rfl⟩ := len3 (show ua.length = 3 by simp at ln; omega)
      obtain ⟨e0, e1, e2, rfl⟩ := len3 (show x2.length = 3 by simp at ln; omega)
      obtain ⟨G, hG⟩ := hok 0 e0 rfl
      obtain ⟨G1, hG1⟩ := hok 1 e1 rfl
      obtain ⟨G2, hG2⟩ := hok 2 e2 rfl
      simp only [OwnSpec.dest, OwnSpec.dsP, List.length_nil, Nat.zero_add] at hG hG1 hG2
      simp at hG hG1 hG2
      have hx := W.w.inj (arg_word hR1 hE1 (i := 1) rfl rfl rfl hG1); subst i
      have hx := W.w.inj (arg_word hR1 hE1 (i := 2) rfl rfl rfl hG2); subst x
      have hd : OwnSpec.dest (some (OwnSpec.dsP 8)) 0 = 1 := by simp [OwnSpec.dest, OwnSpec.dsP]
      obtain ⟨hσ, hn, hsrc⟩ := own0 hR1 hE1 hS1 hM1 hfc hd (e0 := e0) (l := l) (a := a) rfl rfl rfl hG
      have hB := bufAt_of hA1 hσ
      obtain ⟨H2, hp, hB2, ht2, hfr2⟩ := bset_at hB iw xw (sp - 24)
      simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      have hev : ev cx (ParSpec.Nd.prim 8 as) env = .ok (.inl [.b (l.set iw.toNat xw)]) := by
        simp [ev, evl, prim, bind, Except.bind, pure, Except.pure]
      have mf := finC_mono _ _ _ _ hfc
      have rk1 : OwnSpec.rk 8 = 1 := by decide
      refine ⟨upd σ1 a.toNat (l.set iw.toNat xw), [.b (l.set iw.toNat xw)], hev,
        aheap_update hA1 hσ (by rwa [UInt64.ofNat_toNat]) ht2 (by rwa [UInt64.ofNat_toNat]), ?_,
        (hE1.mono mf).upd _ hn, fun a' ha hn' => ?_, hM1.trans mf, by rw [ht2]; exact h81, by rw [ht2]; exact hb1, ?_,
        by simp [rk1], hGr.trans (grow_upd _ _ _)⟩
      · rw [rk1]
        exact ⟨fun _ => by simp [VR, upd], fun h => absurd h (by decide), fun _ l' hl' => ⟨hn, trivial⟩,
          fun h => absurd h (by decide), trivial⟩
      · have e1 : σ1 a' = σ a' := (hCh1.weak mf) a' ha hn'
        simp only [upd]; split
        · rename_i q; subst q
          obtain ⟨j, l', kj, cj, ej, wj⟩ := hsrc ha
          exact absurd (congrArg UInt64.toNat wj) (hn' j l' kj cj ej)
        · exact e1
      · rw [rk1]; exact ⟨fun _ _ _ hs => hsrc hs, trivial⟩
    · -- 9 BPUSH
      simp (config := { decide := true }) only [sv, if_true, if_false] at hs
      unfold fin2S at hs
      obtain ⟨⟨ua, H1⟩, hsl, hrest⟩ := Option.bind_eq_some_iff.1 hs
      obtain ⟨σ1, v, esN, hesA, evl, hA1, hR1, hE1, hCh1, hM1, h81, hb1, hS1, -, hGr, hok⟩ :=
        lst_ok cx K oc D hC hK2 hW as hN tl hl hE hA h8 hhb hr hsl
      simp only [List.nil_append] at hesA; subst hesA
      have kv := hk v evl
      have ln := hR1.len
      have hr1 : R2 oc.K x1 := hr.keep (lstA_keep hK2 hW tl _ _ _ _ _ hl (fun _ h => by simp at h)).1
      obtain ⟨l, x, rfl⟩ := kOf_bw kv
      obtain ⟨a, xw, rfl⟩ := len2 (show ua.length = 2 by simp at ln; omega)
      obtain ⟨e0, e1, rfl⟩ := len2 (show x2.length = 2 by simp at ln; omega)
      obtain ⟨G, hG⟩ := hok 0 e0 rfl
      obtain ⟨G1, hG1⟩ := hok 1 e1 rfl
      simp only [OwnSpec.dest, OwnSpec.dsP, List.length_nil, Nat.zero_add] at hG hG1
      simp at hG hG1
      have hx := W.w.inj (arg_word hR1 hE1 (i := 1) rfl rfl rfl hG1); subst x
      have hd : OwnSpec.dest (some (OwnSpec.dsP 9)) 0 = 1 := by simp [OwnSpec.dest, OwnSpec.dsP]
      obtain ⟨hσ, hn, hsrc⟩ := own0 hR1 hE1 hS1 hM1 hfc hd (e0 := e0) (l := l) (a := a) rfl rfl rfl hG
      have hB := bufAt_of hA1 hσ
      have hlt : l.length < K.κ := by
        obtain ⟨-, -, -, -, b5, b6, -⟩ := id hB
        have h7 : (7 : Nat) ≠ 9 := by decide
        simp only [primF2, if_neg h7.symm] at hrest
        cases h' : bpushF K.hb a xw (sp - 16) H1 with
        | none => rw [h'] at hrest; cases hrest
        | some r =>
          unfold bpushF at h'
          rw [bufInfo_at hB, Option.bind_some, toNat_ofNat_lt (show l.length < 2 ^ 64 by omega),
            toNat_ofNat_lt (show K.κ < 2 ^ 64 by omega)] at h'
          split at h'
          · omega
          · cases h'
      obtain ⟨H2, hp, hB2, ht2, hfr2⟩ := bpush_at hB hlt xw (sp - 16)
      simp (config := { decide := true }) only [primF2, if_false, hp, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      have hev : ev cx (ParSpec.Nd.prim 9 as) env = .ok (.inl [.b (l ++ [xw])]) := by
        simp [ev, evl, prim, push, bind, Except.bind, pure, Except.pure, ← hX.κ, hlt]
      have mf := finC_mono _ _ _ _ hfc
      have rk1 : OwnSpec.rk 9 = 1 := by decide
      refine ⟨upd σ1 a.toNat (l ++ [xw]), [.b (l ++ [xw])], hev,
        aheap_update hA1 hσ (by rwa [UInt64.ofNat_toNat]) ht2 (by rwa [UInt64.ofNat_toNat]), ?_,
        (hE1.mono mf).upd _ hn, fun a' ha hn' => ?_, hM1.trans mf, by rw [ht2]; exact h81, by rw [ht2]; exact hb1, ?_,
        by simp [rk1], hGr.trans (grow_upd _ _ _)⟩
      · rw [rk1]
        exact ⟨fun _ => by simp [VR, upd], fun h => absurd h (by decide), fun _ l' hl' => ⟨hn, trivial⟩,
          fun h => absurd h (by decide), trivial⟩
      · have e1 : σ1 a' = σ a' := (hCh1.weak mf) a' ha hn'
        simp only [upd]; split
        · rename_i q; subst q
          obtain ⟨j, l', kj, cj, ej, wj⟩ := hsrc ha
          exact absurd (congrArg UInt64.toNat wj) (hn' j l' kj cj ej)
        · exact e1
      · rw [rk1]; exact ⟨fun _ _ _ hs => hsrc hs, trivial⟩

end NanoMain
