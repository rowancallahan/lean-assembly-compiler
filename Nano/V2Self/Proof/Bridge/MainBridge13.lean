/- Nano/V2Self/Proof/Bridge/MainBridge13: the Sem ⇐ sv bridge — the fuel loop (E's `loopGo` ↔ `Sem`'s `loopRun`). -/
import Nano.V2Self.Proof.Bridge.MainBridge12

namespace NanoMain
open Templates

/-- tail mode kills only owned slots too -/
theorem chk_keep_tail {oc : OwnSpec.Cx} {D : List Sig} (hK2 : ∀ s, oc.K.getD s 0 ≤ 2) (hW : RsW oc) :
    ∀ {Γ S e ks}, TyN D Γ S e ks → ∀ F F' es, OwnSpec.chk oc e F = some (F', es) → Keep oc.K F F' ∧ TagsOK oc.K es
  | Γ, _, _, _, .const, F, F', es, h => chk_keep hK2 hW (D := D) (Γ := Γ) (S := none) .const rfl F F' es h
  | _, _, _, _, .loc hk, F, F', es, h => chk_keep hK2 hW (D := D) (S := none) (.loc hk) rfl F F' es h
  | _, _, _, _, .bin o1 o2 ta tb, F, F', es, h => chk_keep hK2 hW (D := D) (S := none) (.bin o1 o2 ta tb) rfl F F' es h
  | _, _, _, _, .pair tl, F, F', es, h => chk_keep hK2 hW (D := D) (S := none) (.pair tl) rfl F F' es h
  | _, _, _, _, .call tl hd, F, F', es, h => chk_keep hK2 hW (D := D) (S := none) (.call tl hd) rfl F F' es h
  | _, _, _, _, .prim tl hp hn, F, F', es, h => chk_keep hK2 hW (D := D) (S := none) (.prim tl hp hn) rfl F F' es h
  | _, _, _, _, .ite _ ta tb tt te, F, F', es, h => by
    simp only [OwnSpec.chk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨a0, ha, b0, hb, y, hy, t0, h1, t1, h2, e0, h3, e1, h4, k, hj, hk⟩ := h
    simp only [Prod.mk.injEq] at hk; obtain ⟨rfl, rfl⟩ := hk
    obtain ⟨ka, ta'⟩ := chk_keep hK2 hW ta rfl _ _ _ ha
    obtain ⟨kb, tb'⟩ := chk_keep hK2 hW tb rfl _ _ _ hb
    have ky := (ka.trans kb).trans (two_keep ta' tb' hy)
    obtain ⟨kt, tt'⟩ := chk_keep_tail hK2 hW tt _ _ _ h1
    obtain ⟨ke, te'⟩ := chk_keep_tail hK2 hW te _ _ _ h3
    obtain ⟨kt1, lt1⟩ := tr_keep _ _ _ _ tt' h2
    obtain ⟨ke1, le1⟩ := tr_keep _ _ _ _ te' h4
    exact ⟨keep_orF (ky.trans (kt.trans kt1)) (ky.trans (ke.trans ke1)), tags_plain (join_plain lt1 le1 hj)⟩
  | _, _, _, _, .letE tv _ _ _ tb, F, F', es, h => by
    simp only [OwnSpec.chk, Option.bind_eq_some_iff] at h
    obtain ⟨v0, hv, v1, hv1, h⟩ := h
    split at h
    · obtain ⟨b0, hb0, hb1⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨kv, tv'⟩ := chk_keep hK2 hW tv rfl _ _ _ hv
      obtain ⟨kv1, -⟩ := tr_keep _ _ _ _ tv' hv1
      obtain ⟨kb, tb'⟩ := chk_keep_tail hK2 hW tb _ _ _ hb0
      obtain ⟨kb1, lb1⟩ := tr_keep _ _ _ _ tb' hb1
      exact ⟨((kv.trans kv1).trans kb).trans kb1, tags_plain lb1⟩
    · cases h
  | _, _, _, _, .cont te, F, F', es, h => by
    unfold OwnSpec.chk at h
    split at h
    · cases te with
      | pair hl =>
        obtain ⟨⟨x1, x2⟩, hx, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨y, hy, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        obtain ⟨k1, t1⟩ := lstA_keep hK2 hW hl _ _ _ _ _ hx (fun _ h => by simp at h)
        exact ⟨k1.trans (fin_keep t1 hy).1, by simp [TagsOK]⟩
    · obtain ⟨⟨x1, x2⟩, hx, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · obtain ⟨y, hy, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
        obtain ⟨k1, t1⟩ := chk_keep hK2 hW te rfl _ _ _ hx
        exact ⟨k1.trans (fin_keep t1 hy).1, by simp [TagsOK]⟩
      · cases h

/-- a slot killed from all-live flags is owned -/
theorem cons_owned {Kk : List Nat} {F F' : List Bool} (hk : Keep Kk F F') {j : Nat} (hc : Cons F F' j) :
    Kk.getD j 0 = 1 := by
  refine Classical.byContradiction fun h => ?_
  have := hk j h hc.2; rw [hc.1] at this; cases this

/-! ## the def-level frame: blocks that existed at the call and are not owned arguments' stay -/

def Frame0 (σ0 σ : AH) (OA : UInt64 → Prop) : Prop :=
  ∀ a, (σ0 a).isSome → (∀ u, OA u → u.toNat ≠ a) → σ a = σ0 a

/-- owned slots hold blocks fresh since the call or owned arguments' -/
def OwnSt (σ0 : AH) (OA : UInt64 → Prop) (Kk : List Nat) (Γ : List (Option Kd)) (env : List W) (ew : Env) : Prop :=
  ∀ j l, Kn Γ j → Kk.getD j 0 = 1 → env[j]? = some (.b l) → σ0 (ew j).toNat = none ∨ OA (ew j)

/-- results in the callee contract's form -/
def ResR (σ0 σ' : AH) (OA : UInt64 → Prop) (R : List Nat) (v : List W) (vs : List UInt64) : Prop :=
  v.length = R.length ∧ vs.length = R.length ∧
  (∀ (j e : Nat) (x : W) (u : UInt64), R[j]? = some e → v[j]? = some x → vs[j]? = some u → VR σ' x u ∧
    (e = 0 → ∃ y, x = .w y) ∧ (e = 1 → ∀ l, x = .b l → σ0 u.toNat = none ∨ OA u)) ∧
  (∀ (j j' : Nat) (l l' : List UInt64) (u u' : UInt64), j ≠ j' → R[j]? = some 1 → R[j']? = some 1 →
    v[j]? = some (W.b l) → v[j']? = some (W.b l') → vs[j]? = some u → vs[j']? = some u' → u ≠ u')

theorem frame_step {σ0 σ σ' : AH} {OA : UInt64 → Prop} {Kk : List Nat} {Γ : List (Option Kd)} {F0 Fx : List Bool}
    {env : List W} {ew : Env} (hF : Frame0 σ0 σ OA) (hCh : Ch σ σ' Γ F0 Fx env ew) (hk : Keep Kk F0 Fx)
    (hO : OwnSt σ0 OA Kk Γ env ew) : Frame0 σ0 σ' OA := by
  intro a ha hn
  have e1 := hF a ha hn
  rw [← e1]
  refine hCh a (by rw [e1]; exact ha) fun t l kt ct et hq => ?_
  rcases hO t l kt (cons_owned hk ct) et with h | h
  · rw [← hq, h] at ha; cases ha
  · exact hn _ h hq

theorem res_step {σ0 σ σ' : AH} {OA : UInt64 → Prop} {Kk : List Nat} {Γ : List (Option Kd)} {F0 Fx : List Bool}
    {env : List W} {ew : Env} {R : List Nat} {v : List W} {vs : List UInt64} (hR : ResI σ' Kk Fx Γ env ew R v vs)
    (h1 : ∀ e ∈ R, e ≤ 1) (hS : Src σ Γ F0 Fx env ew R v vs) (hk : Keep Kk F0 Fx) (hO : OwnSt σ0 OA Kk Γ env ew)
    (hG : Grow σ0 σ) : ResR σ0 σ' OA R v vs := by
  have ln := hR.len
  refine ⟨ln.1.symm, by omega, fun j e x u he hx hu => ?_, fun j j' l l' u u' hne a b c d f g => ?_⟩
  · obtain ⟨c1, c2, -⟩ := resI_idx j hR he hx hu
    have := h1 e (List.mem_of_getElem? he)
    refine ⟨c1 (by omega), c2, fun e1 l hl => ?_⟩
    subst hl
    by_cases hs : (σ u.toNat).isSome
    · obtain ⟨i, l', ki, ci, ei, wi⟩ := src_idx j hS (by rw [he, e1]) hx hu hs
      rw [← wi]; exact hO i l' ki (cons_owned hk ci) ei
    · left
      cases h0 : σ0 u.toNat with
      | none => rfl
      | some _ => exact absurd (hG _ (by rw [h0]; rfl)) hs
  · rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact resI_pair j j' hR h a b c d f g
    · exact Ne.symm (resI_pair j' j hR h b a d c g f)

/-! ## the loop counter (slot 0) -/

theorem envI_slot0 {σ : AH} {Kk : List Nat} {F : List Bool} {Γ : List (Option Kd)} {x : W} {env : List W} {ew ew' : Env}
    (hE : EnvI σ Kk F Γ (x :: env) ew) {y : UInt64} (hΓ : Γ[0]? = some (some .w)) (h0 : ew' 0 = y)
    (hk : ∀ k, k ≠ 0 → ew' k = ew k) : EnvI σ Kk F Γ (.w y :: env) ew' where
  len := by have := hE.len; simpa using this
  ty := by
    have t := hE.ty
    cases t with
    | cons r t' =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hΓ
      exact .cons (fun k hk => by rw [hΓ] at hk; cases hk; rfl) t'
  val k kn hr := by
    rcases k with _ | k
    · exact ⟨.w y, rfl, by simp [VR, h0], fun _ => ⟨y, rfl⟩⟩
    · obtain ⟨z, hz, vr, wd⟩ := hE.val (k + 1) kn hr
      exact ⟨z, hz, by rw [hk (k + 1) (by omega)]; exact vr, wd⟩
  dist a b la lb hab ka kb k1 k0 da db ea eb := by
    rcases a with _ | a
    · cases ea
    rcases b with _ | b
    · cases eb
    rw [hk (a + 1) (by omega), hk (b + 1) (by omega)]
    exact hE.dist (a + 1) (b + 1) la lb hab ka kb k1 k0 da db ea eb

/-! ## a CONTINUE re-establishes the loop head's frame invariant -/

theorem stD_get {Kk : List Nat} {npw i : Nat} (hi : i < npw - 1) (hl : npw ≤ Kk.length) :
    (OwnSpec.stD Kk npw)[i]? = some (if Kk.getD (1 + i) 0 = 2 then 3 else Kk.getD (1 + i) 0) := by
  simp only [OwnSpec.stD, List.getElem?_map, List.getElem?_take_of_lt hi, List.getElem?_drop]
  rw [List.getElem?_eq_getElem (show 1 + i < Kk.length by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 1 + i < Kk.length by omega)]

theorem loopΓ_get (sk : List Kd) (m : Nat) :
    ∀ k, (some Kd.w :: sk.map some ++ List.replicate m none)[k]? =
      if k = 0 then some (some .w) else if k < 1 + sk.length then (sk[k - 1]?).map some
      else if k < 1 + sk.length + m then some none else none := by
  intro k
  rcases k with _ | k
  · simp
  · simp only [List.cons_append, List.getElem?_cons_succ, Nat.succ_ne_zero, if_false]
    by_cases h1 : k < sk.length
    · rw [List.getElem?_append_left (by simpa using h1), if_pos (by omega)]; simp
    · rw [List.getElem?_append_right (by simp; omega), if_neg (by omega)]
      simp only [List.length_map, List.getElem?_replicate]
      by_cases h2 : k - sk.length < m
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem envI_cont {σ : AH} {Kk : List Nat} {F : List Bool} {sk : List Kd} {m : Nat} {env1 st : List W} {ew1 : Env}
    {ws : List UInt64} (hlen : Kk.length = 1 + sk.length + m)
    (ht : EnvOK env1 (some Kd.w :: sk.map some ++ List.replicate m none)) (h0 : env1[0]? = some (.w (ew1 0)))
    (hk : kOf st = sk) (hA : ArgsR σ (OwnSpec.stD Kk (1 + sk.length)) st ws) :
    EnvI σ Kk F (some Kd.w :: sk.map some ++ List.replicate m none) (env1.take 1 ++ st ++ env1.drop (1 + st.length))
      (setW ew1 1 sk.length ws) := by
  have hst : st.length = sk.length := by rw [← hk, kOf_length]
  have hl1 := ht.length_eq
  simp only [List.length_cons, List.length_append, List.length_map, List.length_replicate] at hl1
  obtain ⟨env', e1, he'⟩ := setSlots_ok (vs := st) (s := 1) ht (by simp; omega)
  have he2 : env' = env1.take 1 ++ st ++ env1.drop (1 + st.length) := by
    simp only [setSlots] at e1; rw [if_pos (by omega)] at e1; cases e1; rfl
  subst he2
  rw [hk, setK_loop1] at he'
  have hP : ∀ i, i < sk.length → (OwnSpec.stD Kk (1 + sk.length))[i]? =
      some (if Kk.getD (1 + i) 0 = 2 then 3 else Kk.getD (1 + i) 0) := fun i hi => stD_get (by omega) (by omega)
  have hkn : ∀ k, Kn (some Kd.w :: sk.map some ++ List.replicate m none) k → k < 1 + sk.length := by
    intro k ⟨kd, h⟩
    rw [loopΓ_get] at h
    by_cases a : k = 0
    · omega
    · rw [if_neg a] at h
      by_cases b : k < 1 + sk.length
      · exact b
      · rw [if_neg b] at h; split at h <;> simp at h
  refine ⟨he'.length_eq, he', fun k kn hr => ?_, fun a b la lb hab ka kb k1 k0 da db ea eb => ?_⟩
  · have hk1 := hkn k kn
    rcases k with _ | i
    · refine ⟨.w (ew1 0), by rw [ss_out (by omega) (by omega)]; exact h0, by simp [VR, setW], fun _ => ⟨_, rfl⟩⟩
    · have hi : i < sk.length := by omega
      have e' : (env1.take 1 ++ st ++ env1.drop (1 + st.length))[i + 1]? = st[i]? := by
        rw [show i + 1 = 1 + i by omega]; exact ss_in (by omega) (by omega)
      obtain ⟨x, hx⟩ : ∃ x, st[i]? = some x := ⟨st[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have hw : ws.length = sk.length := by
        have := hA.2.1; rw [this]; simp [OwnSpec.stD]; omega
      obtain ⟨u, hu⟩ : ∃ u, ws[i]? = some u := ⟨ws[i]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have ew' : setW ew1 1 sk.length ws (i + 1) = u := by
        rw [show i + 1 = 1 + i by omega, setW_in _ _ _ _ _ hi, List.getD_eq_getElem?_getD, hu]; rfl
      refine ⟨x, by rw [e', hx], by rw [ew']; exact hA.2.2.1 i x u hx hu, fun h0' => ?_⟩
      have := hP i hi
      rw [show 1 + i = i + 1 by omega, h0'] at this
      exact hA.2.2.2.1 i x (by simpa using this) hx
  · have ha := hkn a ka
    have hb := hkn b kb
    rcases a with _ | a
    · rw [ss_out (by omega) (by omega), h0] at ea; cases ea
    rcases b with _ | b
    · rw [ss_out (by omega) (by omega), h0] at eb; cases eb
    have ea' : st[a]? = some (.b la) := by
      rw [show a + 1 = 1 + a by omega, ss_in (by omega) (by omega)] at ea; exact ea
    have eb' : st[b]? = some (.b lb) := by
      rw [show b + 1 = 1 + b by omega, ss_in (by omega) (by omega)] at eb; exact eb
    have hw : ws.length = sk.length := by
      have := hA.2.1; rw [this]; simp [OwnSpec.stD]; omega
    have pa := hP a (by omega)
    rw [show 1 + a = a + 1 by omega, k1] at pa
    simp only [show (1 : Nat) ≠ 2 by decide, if_false] at pa
    rw [show a + 1 = 1 + a by omega, show b + 1 = 1 + b by omega, setW_in _ _ _ _ _ (by omega),
      setW_in _ _ _ _ _ (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show a < ws.length by omega), List.getElem?_eq_getElem (show b < ws.length by omega)]
    exact hA.2.2.2.2 a b la lb ws[a] ws[b] (by omega) pa ea' eb' (List.getElem?_eq_getElem _)
      (List.getElem?_eq_getElem _)

/-! ## the loop -/

theorem dec_word {a : UInt64} {N : Nat} (h : a.toNat = N + 1) : a - 1 = UInt64.ofNat N := by
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_sub, h]
  simp [UInt64.toNat_ofNat']
  have : N + 1 < 2 ^ 64 := h ▸ a.toNat_lt
  omega

/-- the loop head's invariant (relative to the call's heap `σ0` and owned-argument blocks `OA`) -/
structure LI (σ0 : AH) (OA : UInt64 → Prop) (Kk : List Nat) (Γ0 : List (Option Kd)) (F0 : List Bool) (hb κ : Nat)
    (σ : AH) (H : Hp) (env : List W) (ew : Env) : Prop where
  E : EnvI σ Kk F0 Γ0 env ew
  A : AHeap hb κ H σ
  t8 : H.top % 8 = 0
  tb : hb ≤ H.top
  G : Grow σ0 σ
  Fr : Frame0 σ0 σ OA
  Os : OwnSt σ0 OA Kk Γ0 env ew

theorem r2_init {Kk : List Nat} {n : Nat} (hl : Kk.length = n) : R2 Kk (List.replicate n false) := by
  intro s hs
  have : s < Kk.length := by
    refine Nat.lt_of_not_le fun h => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h] at hs; simp at hs
  simp [OwnSpec.dead, List.getD_eq_getElem?_getD, List.getElem?_replicate, show s < n by omega]

theorem loop_run (cx : Ctx) (K : SC) (oc : OwnSpec.Cx) (D : List Sig) (hRs : RsOK oc D) (hW : RsW oc)
    (hX : CtxR cx K) (hCR : CallR cx K oc D) (hC : CtxOK cx D) (hK2 : ∀ s, oc.K.getD s 0 ≤ 2)
    {sk : List Kd} {m : Nat} {ks : List Kd} {z s : ParSpec.Nd} {z0 z1 s0 s1 : List Bool × List Nat} {R : List Nat}
    (hlen : oc.K.length = 1 + sk.length + m) (hp : K.p = 1 + sk.length) (hnpw : oc.npw = 1 + sk.length)
    (tz : TyN D (some Kd.w :: sk.map some ++ List.replicate m none) none z ks)
    (ts : TyN D (some Kd.w :: sk.map some ++ List.replicate m none) (some sk) s ks)
    (hz0 : OwnSpec.chk oc z (List.replicate (1 + sk.length + m) false) = some z0) (hz1 : OwnSpec.tr z0.1 z0.2 = some z1)
    (hs0 : OwnSpec.chk oc s (List.replicate (1 + sk.length + m) false) = some s0) (hs1 : OwnSpec.tr s0.1 s0.2 = some s1)
    (hj : OwnSpec.join z1.2 s1.2 = some R) (σ0 : AH) (OA : UInt64 → Prop) (sp : Nat) (vs : List UInt64) (H' : Hp) :
    ∀ N σ H env ew, LI σ0 OA oc.K (some Kd.w :: sk.map some ++ List.replicate m none)
      (List.replicate (1 + sk.length + m) false) K.hb K.κ σ H env ew → (ew 0).toNat = N → env[0]? = some (.w (ew 0)) →
      loopGo K.p (st K z) (st K s) sp N ew H = some (vs, H') →
      ∃ σ' v, loopRun (ev cx z) (ev cx s) N env = .ok v ∧ AHeap K.hb K.κ H' σ' ∧ H'.top % 8 = 0 ∧ K.hb ≤ H'.top ∧
        Grow σ0 σ' ∧ Frame0 σ0 σ' OA ∧ ResR σ0 σ' OA R v vs := by
  have hr0 := r2_init (Kk := oc.K) hlen
  obtain ⟨kz0, tz0⟩ := chk_keep hK2 hW tz rfl _ _ _ hz0
  obtain ⟨kz1, lz1⟩ := tr_keep _ _ _ _ tz0 hz1
  obtain ⟨ks0, ts0⟩ := chk_keep_tail hK2 hW ts _ _ _ hs0
  obtain ⟨ks1, ls1⟩ := tr_keep _ _ _ _ ts0 hs1
  have lz : z1.2.length = ks.length := by rw [tr_len _ _ _ _ hz1]; exact chk_len hRs tz rfl _ _ _ hz0
  have ls : s1.2 = [] ∨ s1.2.length = ks.length := by
    rw [← List.length_eq_zero_iff, tr_len _ _ _ _ hs1, List.length_eq_zero_iff]; exact chk_len_tail hRs ts _ _ _ hs0
  intro N
  induction N with
  | zero =>
    intro σ H env ew hI h0 he0 hg
    have hz : ew 0 = 0 := UInt64.toNat_inj.1 (by simpa using h0)
    rw [loopGo, if_pos hz, st_none K tz rfl] at hg
    simp only [exitS, Option.bind_eq_some_iff, Option.map_eq_some_iff, exitOnly] at hg
    obtain ⟨⟨r, H2⟩, ⟨⟨vs', H3⟩, hsv, he⟩, hx⟩ := hg
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simp only [Option.some.injEq, Prod.mk.injEq] at hx; obtain ⟨hx1, hx2⟩ := hx; subst vs' H3
    obtain ⟨σ', v, evz, hA', hR, hE', hCh, hM, h8', hb', hS, -, hG⟩ :=
      node_all cx K oc D hRs hW hX hCR z hC hK2 _ ks _ _ _ env ew σ sp H vs H' tz hz0 hI.E hI.A hI.t8 hI.tb hr0 hsv
    obtain ⟨m2, hR2, r2, -, -⟩ := tr_spec hK2 _ v vs _ _ _ hR hE' hz1
    obtain ⟨-, hS2⟩ := tr_src _ _ _ _ _ _ hR hM hS hz1
    have hRR : ResI σ' oc.K z1.1 (some Kd.w :: sk.map some ++ List.replicate m none) env ew R v vs ∧
        ∀ x ∈ R, x ≤ 1 := by
      by_cases h0 : s1.2 = []
      · rw [h0] at hj; rw [join_nil_r hj]; exact ⟨hR2, r2⟩
      · exact resI_join hR2 r2 (tr_le1 _ _ _ _ hs1) (by rcases ls with h | h <;> simp_all) hj
    have hSR : Src σ (some Kd.w :: sk.map some ++ List.replicate m none) (List.replicate (1 + sk.length + m) false)
        z1.1 env ew R v vs := by
      by_cases h0 : s1.2 = []
      · rw [h0] at hj; rw [join_nil_r hj]; exact hS2
      · exact src_join hR2 hS2 r2 (tr_le1 _ _ _ _ hs1) hj
    have kz := kz0.trans kz1
    exact ⟨σ', v, by simp [loopRun, evz, val], hA', h8', hb', hI.G.trans hG,
      frame_step hI.Fr (hCh.weak m2) kz hI.Os, res_step hRR.1 hRR.2 hSR kz hI.Os hI.G⟩
  | succ N ih =>
    intro σ H env ew hI h0 he0 hg
    have hnz : ew 0 ≠ 0 := fun q => by rw [q] at h0; simp at h0
    rw [loopGo, if_neg hnz] at hg
    simp only [Option.bind_eq_some_iff] at hg
    obtain ⟨⟨r, H2⟩, hss, hrest⟩ := hg
    -- the decremented frame
    obtain ⟨x0, tl, rfl⟩ : ∃ x0 tl, env = x0 :: tl := by
      cases env with | nil => simp at he0 | cons x0 tl => exact ⟨x0, tl, rfl⟩
    have hdec : decE ew 0 = UInt64.ofNat N := by simp only [decE, if_true]; exact dec_word h0
    have hE1 := envI_slot0 (y := UInt64.ofNat N) hI.E (by simp) hdec (fun k hk => by simp [decE, hk])
    have hO1 : OwnSt σ0 OA oc.K (some Kd.w :: sk.map some ++ List.replicate m none) (.w (UInt64.ofNat N) :: tl)
        (decE ew) := by
      intro j l kj k1 ej
      rcases j with _ | j
      · cases ej
      · have := hI.Os (j + 1) l kj k1 ej; simpa [decE] using this
    obtain ⟨σ2, out, evs, hA2, hE2, hCh2, hM2, h82, hb2, hG2, hout⟩ :=
      tail_all cx K oc D hRs hW hX hCR s hC hK2 _ sk ks _ _ _ _ _ σ sp H r H2 ts hs0 hE1 hI.A hI.t8 hI.tb hr0 hss
    have hss1 : setSlots (x0 :: tl) 0 [.w (UInt64.ofNat N)] = .ok (.w (UInt64.ofNat N) :: tl) := by
      simp [setSlots]
    have hFr := frame_step hI.Fr hCh2 ks0 hO1
    rcases hout with ⟨v, vs', rfl, rfl, hR3, hS3, -⟩ | ⟨st', ws, rfl, rfl, hst⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hrest; obtain ⟨hx1, hx2⟩ := hrest; subst vs' H2
      obtain ⟨m4, hR4, r4, -, -⟩ := tr_spec hK2 _ v vs _ _ _ hR3 hE2 hs1
      obtain ⟨-, hS4⟩ := tr_src _ _ _ _ _ _ hR3 hM2 hS3 hs1
      have kv := (ev_ok hC ts _ hE1.ty).2.1 v evs
      have lv : s1.2.length = ks.length := by rw [tr_len _ _ _ _ hs1, hR3.len.1, ← kOf_length, kv]
      obtain ⟨hRR, hR1⟩ := resI_join_r hR4 (tr_le1 _ _ _ _ hz1) r4 (by omega) hj
      have hSR := src_join_r hR4 hS4 (tr_le1 _ _ _ _ hz1) r4 hj
      refine ⟨σ2, v, ?_, hA2, h82, hb2, hI.G.trans hG2, hFr, res_step hRR hR1 hSR (ks0.trans ks1) hO1 hI.G⟩
      simp [loopRun, hss1, evs, bind, Except.bind, pure, Except.pure]
    · -- CONTINUE: the next head
      have kst := (ev_ok hC ts _ hE1.ty).2.2 st' evs
      obtain ⟨sk', hsk, kst⟩ := kst
      cases hsk
      have hst_len : st'.length = sk.length := by rw [← kst, kOf_length]
      have hl1 := hE1.len
      simp only [List.length_cons, List.length_append, List.length_map, List.length_replicate] at hl1
      have hss2 : setSlots (.w (UInt64.ofNat N) :: tl) 1 st' =
          .ok ((.w (UInt64.ofNat N) :: tl).take 1 ++ st' ++ (.w (UInt64.ofNat N) :: tl).drop (1 + st'.length)) := by
        simp only [setSlots]; rw [if_pos (by simp; omega)]
      have hA' : ArgsR σ2 (OwnSpec.stD oc.K (1 + sk.length)) st' ws := by rw [← hnpw]; exact hst.1
      have hEn := envI_cont (F := List.replicate (1 + sk.length + m) false) (ew1 := decE ew) hlen hE1.ty
        (by simp [hdec]) kst hA'
      simp only at hrest
      rw [show K.p - 1 = sk.length by omega] at hrest
      have hw0 : setW (decE ew) 1 sk.length ws 0 = UInt64.ofNat N := by rw [setW_out _ _ _ _ _ (by omega), hdec]
      have hIn : LI σ0 OA oc.K (some Kd.w :: sk.map some ++ List.replicate m none)
          (List.replicate (1 + sk.length + m) false) K.hb K.κ σ2 H2
          ((.w (UInt64.ofNat N) :: tl).take 1 ++ st' ++ (.w (UInt64.ofNat N) :: tl).drop (1 + st'.length))
          (setW (decE ew) 1 sk.length ws) := by
        refine ⟨hEn, hA2, h82, hb2, hI.G.trans hG2, hFr, fun j l kj k1 ej => ?_⟩
        have hj1 : j < 1 + sk.length := by
          obtain ⟨kd, h⟩ := kj
          rw [loopΓ_get] at h
          by_cases a : j = 0
          · omega
          · rw [if_neg a] at h
            by_cases b : j < 1 + sk.length
            · exact b
            · rw [if_neg b] at h; split at h <;> simp at h
        rcases j with _ | i
        · simp at ej
        · have hi : i < sk.length := by omega
          have es' : st'[i]? = some (.b l) := by
            rw [show i + 1 = 1 + i by omega, ss_in (by simp; omega) (by omega)] at ej; exact ej
          have hw : ws.length = sk.length := by
            have := hA'.2.1; rw [this]; simp [OwnSpec.stD]; omega
          have wi : setW (decE ew) 1 sk.length ws (i + 1) = ws[i]'(by omega) := by
            rw [show i + 1 = 1 + i by omega, setW_in _ _ _ _ _ hi, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show i < ws.length by omega)]; rfl
          rw [wi]
          have pi := stD_get (Kk := oc.K) (npw := 1 + sk.length) (i := i) (by omega) (by omega)
          rw [show 1 + i = i + 1 by omega, k1] at pi
          simp only [show (1 : Nat) ≠ 2 by decide, if_false] at pi
          by_cases hs : (σ (ws[i]'(by omega)).toNat).isSome
          · obtain ⟨j', l', kj', cj', ej', wj'⟩ := hst.2.1 i l _ (by rw [← hnpw] at pi; exact pi) es'
              (List.getElem?_eq_getElem _) hs
            rw [← wj']
            exact hO1 j' l' kj' (cons_owned ks0 cj') ej'
          · left
            cases h0 : σ0 (ws[i]'(by omega)).toNat with
            | none => rfl
            | some _ => exact absurd (hI.G _ (by rw [h0]; rfl)) hs
      obtain ⟨σ', v, hlr, hA', h8', hb', hG', hFr', hRR⟩ :=
        ih σ2 H2 _ _ hIn (by rw [hw0]; exact toNat_ofNat_lt (by have := (ew 0).toNat_lt; omega))
          (by simp [hw0]) hrest
      refine ⟨σ', v, ?_, hA', h8', hb', hG', hFr', hRR⟩
      simp only [loopRun, hss1, evs, bind, Except.bind, hss2]; exact hlr

end NanoMain
