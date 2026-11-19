/- Nano/V2Self/Proof/MainBridge13: the Sem ⇐ sv bridge — the fuel loop (E's `loopGo` ↔ `Sem`'s `loopRun`). -/
import Nano.V2Self.Proof.MainBridge12

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

end NanoMain
