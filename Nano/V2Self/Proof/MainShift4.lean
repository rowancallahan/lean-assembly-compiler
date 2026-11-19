/- Nano/V2Self/Proof/MainShift4: shift invariance, layer 4 — defs, the program (`semAtF` by strong induction), and
E's `ShiftInv`: whether C's main run runs out of room does not depend on where the 8-aligned work block lies. -/
import Nano.V2Self.Proof.MainShift3
import Nano.V2Self.Proof.RunsShift
import Nano.V2Self.Proof.MainTyP

namespace NanoMain
open Templates

/-! ## `svF` does not read the `fs` field -/
mutual
theorem wd_fs (K : SC) (f) : ∀ e : ParSpec.Nd, wd { K with fs := f } e = wd K e
  | .ite _ _ _ t _ => by simp only [wd]; rw [wd_fs K f t]
  | .letE _ _ _ b => by simp only [wd]; rw [wd_fs K f b]
  | .pair cs => by simp only [wd]; rw [wdL_fs K f cs]
  | .const _ | .loc _ _ | .bin _ _ _ | .call _ _ | .prim _ _ | .loop _ _ | .cont _ => by simp only [wd]
theorem wdL_fs (K : SC) (f) : ∀ cs : List ParSpec.Nd, wdL { K with fs := f } cs = wdL K cs
  | [] => by simp only [wdL]
  | c :: cs => by simp only [wdL]; rw [wd_fs K f c, wdL_fs K f cs]
end

mutual
theorem svF_fs (K : SC) (fsX : Nat → SemDX) (f) : ∀ e : ParSpec.Nd, svF { K with fs := f } fsX e = svF K fsX e
  | .const _ => by simp only [svF]
  | .loc _ _ => by simp only [svF]
  | .bin op a b => by simp only [svF]; rw [svF_fs K fsX f a, svF_fs K fsX f b]
  | .ite c a b t e => by simp only [svF]; rw [svF_fs K fsX f a, svF_fs K fsX f b, svF_fs K fsX f t, svF_fs K fsX f e]
  | .letE s w v b => by simp only [svF]; rw [svF_fs K fsX f v, svF_fs K fsX f b]
  | .pair cs => by simp only [svF]; rw [svLF_fs K fsX f cs]
  | .call id as => by simp only [svF]; rw [svLF_fs K fsX f as]
  | .prim pn as => by simp only [svF]; rw [svLF_fs K fsX f as]; rfl
  | .loop z s => by simp only [svF]; rw [stF_fs K fsX f z, stF_fs K fsX f s]
  | .cont _ => by simp only [svF]
theorem stF_fs (K : SC) (fsX : Nat → SemDX) (f) : ∀ e : ParSpec.Nd, stF { K with fs := f } fsX e = stF K fsX e
  | .ite c a b t e => by simp only [stF]; rw [svF_fs K fsX f a, svF_fs K fsX f b, stF_fs K fsX f t, stF_fs K fsX f e]
  | .letE s w v b => by simp only [stF]; rw [svF_fs K fsX f v, stF_fs K fsX f b]
  | .cont e => by simp only [stF]; rw [svF_fs K fsX f e]
  | .const _ => by simp only [stF]; rw [svF_fs K fsX f (.const _)]
  | .loc _ _ => by simp only [stF]; rw [svF_fs K fsX f (.loc _ _)]
  | .bin op a b => by simp only [stF]; rw [svF_fs K fsX f (.bin op a b)]
  | .pair cs => by simp only [stF]; rw [svF_fs K fsX f (.pair cs)]
  | .call id as => by simp only [stF]; rw [svF_fs K fsX f (.call id as)]
  | .prim pn as => by simp only [stF]; rw [svF_fs K fsX f (.prim pn as)]
  | .loop z s => by simp only [stF]; rw [svF_fs K fsX f (.loop z s)]
theorem svLF_fs (K : SC) (fsX : Nat → SemDX) (f) : ∀ cs : List ParSpec.Nd, svLF { K with fs := f } fsX cs = svLF K fsX cs
  | [] => by simp only [svLF]
  | c :: cs => by simp only [svLF]; rw [svF_fs K fsX f c, svLF_fs K fsX f cs, wd_fs K f c]
end

/-! ## a def -/
theorem def_sh {δ : Nat} (K : SC) {D : List Sig} {fsX fsX' : Nat → SemDX} (hδ8 : δ % 8 = 0) (hδ : δ ≤ 2 ^ 32)
    (hC : CallSh δ K.hb D fsX fsX') (d : ParSpec.DefA) (sg : Sig) (hTy : TyDef D d sg) (hp : K.p = d.npw) :
    SimD δ K.hb sg.1 sg.2 (defSF d.npw d.nslots (svF K fsX d.body))
      (defSF d.npw d.nslots (svF { K with hb := K.hb + δ } fsX' d.body)) := by
  obtain ⟨t1, -, -, t4⟩ := hTy
  refine defSF_sim (RE0 := ER δ (sg.1.map some ++ List.replicate (d.nslots - d.npw) none)) ?_
    (fun args args' h => by rw [t1]; exact er_arg h)
  generalize d.body = body at t4 ⊢
  cases t4 with
  | plain tb => exact sv_sh K hδ8 hδ hC tb
  | loop hΓ tz ts =>
    rename_i z s sk n
    rw [hΓ] at tz ts ⊢
    have h0 : ∀ env env', ER δ (some Kd.w :: sk.map some ++ List.replicate n none) env env' → env' 0 = env 0 :=
      fun env env' he => he 0 .w rfl
    have hdec : ∀ env env', ER δ (some Kd.w :: sk.map some ++ List.replicate n none) env env' →
        ER δ (some Kd.w :: sk.map some ++ List.replicate n none) (decE env) (decE env') := by
      intro env env' he k o hk
      simp only [decE]
      by_cases k0 : k = 0
      · subst k0; simp at hk; subst hk; simp only [WR]; rw [h0 env env' he]
      · rw [if_neg k0, if_neg k0]; exact he k o hk
    have hsl : sk.length + 1 = K.p := by
      have hf : ∀ l : List Kd, ((l.map some).filter Option.isSome).length = l.length := by
        intro l; induction l <;> simp [*]
      have := congrArg (fun l => (l.filter Option.isSome).length) hΓ
      simp [List.filter_append] at this
      rw [hf, hf] at this
      rw [hp, t1]; omega
    have hset : ∀ env env' st st', ER δ (some Kd.w :: sk.map some ++ List.replicate n none) env env' →
        LR δ sk st st' → ER δ (some Kd.w :: sk.map some ++ List.replicate n none) (setW env 1 (K.p - 1) st)
          (setW env' 1 (K.p - 1) st') := by
      intro env env' st st' he hr
      have := er_set (s := 1) he hr (by simp; omega)
      rw [show K.p - 1 = sk.length by omega]
      have e : setK (some Kd.w :: sk.map some ++ List.replicate n none) 1 sk =
          some Kd.w :: sk.map some ++ List.replicate n none := by
        simp only [setK]
        rw [show 1 + sk.length = sk.length + 1 by omega, List.cons_append, List.drop_succ_cons,
          List.drop_left' (by simp)]
        simp
      rw [e] at this; exact this
    intro env env' sp sp' H H' he hH hB hS
    simp only [svF, loopF]
    rw [h0 env env' he]
    exact loopGoF_sim (stz_sh K hδ8 hδ hC tz) (st_sh K hδ8 hδ hC ts) h0 hdec hset _ env env' sp sp' H H' he hH hB hS

/-! ## the program -/
theorem semAtF_sh {δ : Nat} (P : Templates.PC) (ds : List ParSpec.DefA) (sigs : List Sig) (hTy : TyProg ds sigs)
    (hδ8 : δ % 8 = 0) (hδ : δ ≤ 2 ^ 32) :
    ∀ k sg, sigs[k]? = some sg → SimD δ P.hb sg.1 sg.2 (semAtF P ds k) (semAtF { P with hb := P.hb + δ } ds k) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro sg hsg
    obtain ⟨hsl, hts, -⟩ := hTy
    have hk : k < ds.length := by rw [← hsl]; exact (List.getElem?_eq_some_iff.1 hsg).1
    have hd : ds[k]? = some (dA ds k) := by
      simp [dA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    have hT := hts k (dA ds k) sg hd hsg
    rw [semAtF, semAtF]
    have e2 : ∀ f, svF (scAt { P with hb := P.hb + δ } ds k) f = svF { scAt P ds k with hb := P.hb + δ } f :=
      fun f => funext fun b => svF_fs { scAt P ds k with hb := P.hb + δ } f (scAt { P with hb := P.hb + δ } ds k).fs b
    rw [e2]
    refine def_sh (scAt P ds k) hδ8 hδ ?_ (dA ds k) sg hT rfl
    intro i ps rs hi
    have hik : i < k := by
      have := (List.getElem?_eq_some_iff.1 hi).1; simp at this; omega
    rw [List.getElem?_take_of_lt hik] at hi
    simp only [dif_pos hik]
    exact ih i hik (ps, rs) hi

/-- C's main run at `hb` and at `hb + δ` reach the same failure, or both succeed -/
theorem rs_out {ts : List UInt64} {p : List ParSpec.DefA} (hp : ParSpec.ParsesProgram ts p) (x : List UInt8) (T : Buf)
    (hb δ u : Nat) (h8 : hb % 8 = 0) (hδ8 : δ % 8 = 0) (h31 : 2 ^ 31 ≤ hb) (hu : hb + δ + u ≤ 2 ^ 32) :
    OutR (LR δ [.b]) δ hb ⟨hb, fun _ => none⟩ (RS p x T hb u) (RS p x T (hb + δ) u) := by
  obtain ⟨sigs, hTy⟩ := refParse_ty hp
  have hlast := hTy.2.2
  have hsl := hTy.1
  have hk : sigs[p.length - 1]? = some ([], [.b]) := by
    rw [List.getLast?_eq_getElem?] at hlast; rw [← hsl]; exact hlast
  have hP : (pcOf κC hb (UInt64.ofNat x.length) (inpW x) T).hb = hb := rfl
  have := semAtF_sh (δ := δ) (pcOf κC hb (UInt64.ofNat x.length) (inpW x) T) p sigs hTy hδ8 (by omega)
    (p.length - 1) _ hk [] [] (hb + u) (hb + δ + u) ⟨hb, fun _ => none⟩ ⟨hb + δ, fun _ => none⟩ trivial
    ⟨rfl, fun _ _ => rfl⟩ ⟨by first | omega | (rw [hP]; omega) | (dsimp only; omega), Nat.le_refl _, by first | omega | (rw [hP]; omega) | (dsimp only; omega)⟩ (.inl ⟨by first | omega | (rw [hP]; omega) | (dsimp only; omega), by first | omega | (rw [hP]; omega) | (dsimp only; omega)⟩)
  exact this

/-- **E's shift invariance**: running out of room does not depend on where the 8-aligned work block lies -/
theorem shiftInv : ShiftInv := by
  intro ts p hp hts hL x hx T hb hb' u h8 h8' h31 h31' hu hu'
  have key : ∀ a δ, a % 8 = 0 → δ % 8 = 0 → 2 ^ 31 ≤ a → a + δ + u ≤ 2 ^ 32 →
      (RS p x T a u = .error .room ↔ RS p x T (a + δ) u = .error .room) := by
    intro a δ ha hδ h1 h2
    have ho := rs_out hp x T a δ u ha hδ h1 h2
    revert ho
    cases RS p x T a u with
    | error f =>
      cases RS p x T (a + δ) u with
      | error f' => intro ho; simp only [OutR] at ho; subst ho; exact Iff.rfl
      | ok r' => intro ho; simp [OutR] at ho
    | ok r =>
      cases RS p x T (a + δ) u with
      | error f' => intro ho; obtain ⟨_, _⟩ := r; simp [OutR] at ho
      | ok r' => intro _; constructor <;> intro h <;> cases h
  rcases Nat.le_total hb hb' with h | h
  · obtain ⟨δ, rfl⟩ := Nat.exists_eq_add_of_le h
    exact key hb δ h8 (by omega) h31 (by omega)
  · obtain ⟨δ, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (key hb' δ h8' (by omega) h31' (by omega)).symm

end NanoMain
