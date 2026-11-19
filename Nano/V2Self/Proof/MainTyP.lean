/- Nano/V2Self/Proof/MainTyP: ParSpec's parser only produces WELL-KINDED programs (`NanoMain.TyProg`), hence (with
`MainTy.sem_ok`) `ParsesProgram ts p → Sem κ p inp ≠ .error .stuck`. -/
import Nano.V2Self.Proof.MainTy

namespace NanoMain
open ParSpec

def _root_.ParSpec.Sh.kinds : Sh → List Kd
  | .uw => [.w] | .bf => [.b] | .ls => [.b] | .nt => [.w] | .p a b => a.kinds ++ b.kinds
def _root_.ParSpec.Ps.kinds : Ps → List Kd | .inp => [] | .fuel => [.w] | .sh s => s.kinds
/-- `ty` describes values of kinds `ks` (`bot`: a CONTINUE, any) -/
def _root_.ParSpec.Ty.fits : Ty → List Kd → Prop
  | .s sh, ks => ks = sh.kinds | .lit, ks => ks = [.w] | .inp, ks => ks = [] | .bot, _ => True
def sigOf (d : DefI) : Sig := (d.params.flatMap Ps.kinds, d.res.kinds)
def selfK (cx : Cx) : Option (List Kd) := cx.self.map fun (_, sps) => sps.flatMap Ps.kinds
/-- the CONTINUE kinds `S` are right for a parse with tail flag `tl` -/
def SOK (cx : Cx) (tl : Bool) (S : Option (List Kd)) : Prop := tl = false ∨ cx.self = none ∨ S = selfK cx

/-- every binding of the parse environment lies below the slot counter and is known in `Γ` -/
def EnvT (env : List (List Nat × Nat × Ps)) (Γ : List (Option Kd)) (nx : Nat) : Prop :=
  (∀ e ∈ env, e.2.1 + e.2.2.width ≤ nx ∧ e.2.1 + e.2.2.width ≤ Γ.length ∧
    ∀ s, e.2.2 = .sh s → known Γ e.2.1 s.width s.kinds) ∧
  ∀ k, nx ≤ k → k < Γ.length → Γ[k]? = some none

theorem _root_.ParSpec.Sh.kinds_length : ∀ s : Sh, s.kinds.length = s.width
  | .uw => rfl | .bf => rfl | .ls => rfl | .nt => rfl
  | .p a b => by simp [Sh.kinds, Sh.width, a.kinds_length, b.kinds_length]

theorem _root_.ParSpec.Ps.kinds_length : ∀ p : Ps, p.kinds.length = p.width
  | .inp => rfl | .fuel => rfl | .sh s => s.kinds_length

theorem tyMatch_fits : ∀ (p : Ps) (t : Ty), tyMatch p t = true → t.fits p.kinds
  | .inp, .inp, _ => rfl
  | .sh s, .s t, h => by simp [tyMatch] at h; subst h; rfl
  | .sh .uw, .lit, _ => rfl
  | .fuel, .s .nt, _ => rfl
  | .fuel, .lit, _ => rfl
  | .inp, .s _, h | .inp, .lit, h | .inp, .bot, h => by simp [tyMatch] at h
  | .fuel, .inp, h | .fuel, .bot, h => by simp [tyMatch] at h
  | .fuel, .s .uw, h | .fuel, .s .bf, h | .fuel, .s .ls, h | .fuel, .s (.p _ _), h => by simp [tyMatch] at h
  | .sh _, .inp, h | .sh _, .bot, h => by simp [tyMatch] at h
  | .sh .bf, .lit, h | .sh .ls, .lit, h | .sh .nt, .lit, h | .sh (.p _ _), .lit, h => by simp [tyMatch] at h

theorem primSig_ok : ∀ t pid ps rs, primSig t = some (pid, ps, rs) → primK pid (ps.flatMap Ps.kinds) = some rs.kinds := by
  intro t pid ps rs h
  unfold primSig at h
  split at h <;> cases h <;> rfl

theorem primSig_noarg {t pid ps rs} (h : primSig t = some (pid, ps, rs)) (h0 : pid = 1 ∨ pid = 3 ∨ pid = 5)
    (as : List Nd) : dropInp ps as = [] := by
  unfold primSig at h
  split at h <;> cases h <;> simp at h0 <;>
    (match as with | [] => rfl | a :: _ => simp [dropInp, List.zip])

theorem findEnv_mem {env n slot p} (h : findEnv env n = some (slot, p)) : (n, slot, p) ∈ env := by
  unfold findEnv at h
  cases hf : env.find? (fun e => e.1 == n) with
  | none => simp [hf] at h
  | some e =>
    simp [hf] at h
    have hm := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    simp at he
    obtain ⟨a, b, c⟩ := e; simp at h he; subst he; obtain ⟨rfl, rfl⟩ := h; exact hm

theorem findDef_get {defs : List DefI} {n i d} (h : findDef defs n = some (i, d)) : defs[i]? = some d := by
  unfold findDef at h
  cases hf : defs.zipIdx.find? (fun e => e.1.name == n) with
  | none => simp [hf] at h
  | some e =>
    simp [hf] at h
    have hm := List.mem_of_find?_eq_some hf
    obtain ⟨a, b⟩ := e; simp at h; obtain ⟨rfl, rfl⟩ := h
    rw [List.mem_zipIdx_iff_getElem?] at hm; simpa using hm

theorem setK_length {Γ : List (Option Kd)} {s : Nat} {ks : List Kd} (h : s + ks.length ≤ Γ.length) :
    (setK Γ s ks).length = Γ.length := by
  simp [setK]; omega

theorem known_setK_below {Γ : List (Option Kd)} {a w s : Nat} {ks ks' : List Kd} (hk : known Γ a w ks) (has : a + w ≤ s)
    (hs : s + ks'.length ≤ Γ.length) : known (setK Γ s ks') a w ks := by
  obtain ⟨h1, h2⟩ := hk
  refine ⟨by rw [setK_length hs]; exact h1, ?_⟩
  rw [← h2]; unfold setK
  rw [List.append_assoc, List.drop_append_of_le_length (by simp; omega), List.take_append_of_le_length (by simp; omega)]
  rw [List.drop_take, List.take_take]; congr 1; omega

theorem known_setK_at {Γ : List (Option Kd)} {s : Nat} {ks : List Kd} (hs : s + ks.length ≤ Γ.length) :
    known (setK Γ s ks) s ks.length ks := by
  refine ⟨by rw [setK_length hs]; exact hs, ?_⟩
  unfold setK
  have : (List.take s Γ).length = s := by simp; omega
  rw [List.append_assoc, List.drop_append_of_le_length (by omega)]
  rw [List.drop_eq_nil_of_le (by omega), List.nil_append, List.take_append_of_le_length (by simp)]
  exact List.take_of_length_le (by simp)

theorem EnvT.mono {env Γ nx nx'} (h : EnvT env Γ nx) (hle : nx ≤ nx') : EnvT env Γ nx' :=
  ⟨fun e he => let ⟨a, b, c⟩ := h.1 e he; ⟨by omega, b, c⟩, fun k hk hl => h.2 k (by omega) hl⟩

theorem setK_get_above {Γ : List (Option Kd)} {s : Nat} {ks : List Kd} (h : s + ks.length ≤ Γ.length) (k : Nat)
    (hk : s + ks.length ≤ k) : (setK Γ s ks)[k]? = Γ[k]? := by
  unfold setK
  have h1 : (List.take s Γ ++ ks.map some).length = s + ks.length := by simp; omega
  rw [List.getElem?_append_right (by omega), h1, List.getElem?_drop]; congr 1; omega

theorem EnvT.push {env Γ nx s} (x : List Nat) (sh : Sh) (h : EnvT env Γ nx) (hs : nx ≤ s) (hΓ : s + sh.width ≤ Γ.length) :
    EnvT ((x, s, .sh sh) :: env) (setK Γ s sh.kinds) (s + sh.width) := by
  have hΓ' : s + sh.kinds.length ≤ Γ.length := by rw [Sh.kinds_length]; exact hΓ
  refine ⟨fun e he => ?_, fun k hk hl => ?_⟩
  rotate_left
  · rw [setK_get_above hΓ' k (by rw [Sh.kinds_length]; exact hk)]
    exact h.2 k (by omega) (by rw [setK_length hΓ'] at hl; exact hl)
  rcases List.mem_cons.1 he with rfl | he
  · refine ⟨Nat.le_refl _, by rw [setK_length hΓ']; exact hΓ, fun s' e' => ?_⟩
    cases e'; have := known_setK_at hΓ'; rwa [Sh.kinds_length] at this
  · obtain ⟨a, b, c⟩ := h.1 e he
    exact ⟨by omega, by rw [setK_length hΓ']; exact b, fun s' e' => known_setK_below (c s' e') (by rw [e'] at a; simp [Ps.width] at a; omega) hΓ'⟩

/-- the non-input arguments, kinds of the parameters -/
theorem dropInp_ty {D : List Sig} {Γ} : ∀ (ps : List Ps) (as : List (Nd × Ty)), as.length = ps.length →
    (∀ i (h1 : i < ps.length) (h2 : i < as.length), as[i].2.fits ps[i].kinds ∧ ∀ ks, as[i].2.fits ks → TyN D Γ none as[i].1 ks) →
    TyL D Γ (dropInp ps (as.map (·.1))) (ps.flatMap Ps.kinds)
  | [], [], _, _ => by simp [dropInp]; exact .nil
  | p :: ps, a :: as, hl, h => by
    have h0 := h 0 (by simp) (by simp)
    have ih := dropInp_ty (D := D) (Γ := Γ) ps as (by simpa using hl) (fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2))
    simp only [List.getElem_cons_zero] at h0
    have hd : dropInp (p :: ps) ((a :: as).map (·.1)) = (match p with | .inp => [] | _ => [a.1]) ++ dropInp ps (as.map (·.1)) := by
      cases p <;> simp [dropInp, List.zip]
    rw [hd, List.flatMap_cons]
    cases p with
    | inp => have : Ps.kinds .inp = [] := rfl; simpa [this] using ih
    | fuel => exact .cons (h0.2 _ h0.1) ih
    | sh s => exact .cons (h0.2 _ h0.1) ih
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

theorem mkPairFlat_ty {D : List Sig} {Γ} {cs : List Nd} {ks : List Kd} (h : TyL D Γ cs ks) (hn : cs ≠ []) :
    TyN D Γ none (mkPairFlat cs) ks := by
  match cs, h with
  | [c], .cons h1 .nil => simpa [mkPairFlat] using h1
  | c :: d :: r, h => exact .pair h

theorem setK_append (Γ : List (Option Kd)) (s : Nat) (a b : List Kd) (h : s + a.length + b.length ≤ Γ.length) :
    setK Γ s (a ++ b) = setK (setK Γ s a) (s + a.length) b := by
  unfold setK
  have h1 : (List.take s Γ ++ a.map some).length = s + a.length := by simp; omega
  have e1 : List.take (s + a.length) (List.take s Γ ++ a.map some ++ List.drop (s + a.length) Γ) = List.take s Γ ++ a.map some :=
    List.take_left' h1
  have e2 : List.drop (s + a.length + b.length) (List.take s Γ ++ a.map some ++ List.drop (s + a.length) Γ) =
      List.drop (s + a.length + b.length) Γ := by
    rw [show s + a.length + b.length = (List.take s Γ ++ a.map some).length + b.length by rw [h1],
      List.drop_append, List.drop_drop, h1]; congr 1; simp; omega
  rw [e1, e2]; simp only [List.length_append, List.map_append, List.append_assoc, Nat.add_assoc]

theorem tyShape_fits {t : Ty} {s : Sh} (h : tyShape t = some s) : t.fits s.kinds := by
  cases t with
  | s s' => simp [tyShape] at h; obtain ⟨-, rfl⟩ := h; rfl
  | lit => simp [tyShape] at h; subst h; rfl
  | inp => simp [tyShape] at h
  | bot => simp [tyShape] at h

theorem isU_fits {t : Ty} (h : isU t = true) : t.fits [.w] := by
  cases t with
  | s s' => cases s' <;> simp [isU] at h; rfl
  | lit => rfl
  | inp => simp [isU] at h
  | bot => simp [isU] at h

theorem join_fits {a b t : Ty} {ks : List Kd} (h : a.join b = some t) (hk : t.fits ks) : a.fits ks ∧ b.fits ks := by
  unfold Ty.join at h
  split at h
  · cases h; exact ⟨trivial, hk⟩
  · cases h; exact ⟨hk, trivial⟩
  · cases h; simp [Ty.fits] at hk ⊢; simp [hk, Sh.kinds]
  · cases h; simp [Ty.fits] at hk ⊢; simp [hk, Sh.kinds]
  · split at h
    · cases h; subst_vars; exact ⟨hk, hk⟩
    · cases h

/-- the statements, by parser function (`D` = signatures of the defs in scope) -/
def PE (f : Nat) : Prop := ∀ cx tl ts nx e ty r nx', pExpr f cx tl ts nx = some (e, ty, r, nx') → nx ≤ nx' ∧
  ∀ Γ, EnvT cx.env Γ nx → nx' ≤ Γ.length → ∀ S ks, SOK cx tl S → ty.fits ks → TyN (cx.defs.map sigOf) Γ S e ks
def PB (f : Nat) : Prop := ∀ cx tl minp ts nx e ty r nx', pBin f cx tl minp ts nx = some (e, ty, r, nx') → nx ≤ nx' ∧
  ∀ Γ, EnvT cx.env Γ nx → nx' ≤ Γ.length → ∀ S ks, SOK cx tl S → ty.fits ks → TyN (cx.defs.map sigOf) Γ S e ks
def Opf (ts : List Tok) : Prop := ∃ t r', ts = .k t :: r' ∧ (opInfo t).isSome = true
def PL (f : Nat) : Prop := ∀ cx minp a ta ts nx e ty r nx', pLoop f cx minp a ta ts nx = some (e, ty, r, nx') → nx ≤ nx' ∧
  ∀ Γ (Q : Option (List Kd) → Prop), EnvT cx.env Γ nx → nx' ≤ Γ.length →
    (∀ S ks, Q S → ta.fits ks → TyN (cx.defs.map sigOf) Γ S a ks) →
    (Opf ts → ∀ ks, ta.fits ks → TyN (cx.defs.map sigOf) Γ none a ks) →
    ∀ S ks, Q S → ty.fits ks → TyN (cx.defs.map sigOf) Γ S e ks
def PA (f : Nat) : Prop := ∀ cx tl ts nx e ty r nx', pApp f cx tl ts nx = some (e, ty, r, nx') → nx ≤ nx' ∧
  ∀ Γ, EnvT cx.env Γ nx → nx' ≤ Γ.length → ∀ S ks, SOK cx tl S → ty.fits ks → TyN (cx.defs.map sigOf) Γ S e ks
def PC (f : Nat) : Prop := ∀ cx n ts nx e ty r nx', pCallDef f cx n ts nx = some (e, ty, r, nx') → nx ≤ nx' ∧
  ∀ Γ, EnvT cx.env Γ nx → nx' ≤ Γ.length → ∀ S ks, ty.fits ks → TyN (cx.defs.map sigOf) Γ S e ks
def PG (f : Nat) : Prop := ∀ cx ps ts nx as r nx', pArgs f cx ps ts nx = some (as, r, nx') → nx ≤ nx' ∧ as.length = ps.length ∧
  ∀ Γ, EnvT cx.env Γ nx → nx' ≤ Γ.length → ∀ i (h1 : i < ps.length) (h2 : i < as.length),
    as[i].2.fits ps[i].kinds ∧ ∀ ks, as[i].2.fits ks → TyN (cx.defs.map sigOf) Γ none as[i].1 ks
def PT (f : Nat) : Prop := ∀ cx tl ts nx e ty r nx', pAtom f cx tl ts nx = some (e, ty, r, nx') → nx ≤ nx' ∧
  ∀ Γ, EnvT cx.env Γ nx → nx' ≤ Γ.length → ∀ S ks, SOK cx tl S → ty.fits ks → TyN (cx.defs.map sigOf) Γ S e ks
def PU (f : Nat) : Prop := ∀ cx ts nx e sh r nx', pTup f cx ts nx = some (e, sh, r, nx') → nx ≤ nx' ∧
  ∀ Γ, EnvT cx.env Γ nx → nx' ≤ Γ.length → ∀ S, TyN (cx.defs.map sigOf) Γ S e sh.kinds

theorem pE_step (f : Nat) (hB : PB f) (hE : PE f) : PE (f + 1) := by
  intro cx tl ts nx e ty r nx' h
  unfold pExpr at h
  split at h
  · cases h
  · rename_i cx tl nx _ _ _ _ _ f0 x r0 heq
    simp at heq; subst heq
    obtain ⟨⟨v, tv, r1, nx1⟩, hv, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · rename_i _ _ s r2 hs
      obtain ⟨⟨b, tb, r3, nx3⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨m1, t1⟩ := hE _ _ _ _ _ _ _ _ hv
      obtain ⟨m2, t2⟩ := hE _ _ _ _ _ _ _ _ hb
      refine ⟨by omega, fun Γ hΓ hl S ks hS hk => ?_⟩
      have hw : nx1 + s.width ≤ Γ.length := by omega
      refine TyN.letE (vs := s.kinds) (t1 Γ hΓ (by omega) none _ (.inl rfl) (tyShape_fits hs)) (Sh.kinds_length s) hw
        (fun k h1 h2 => hΓ.2 k (by omega) (by omega)) ?_
      exact t2 _ (EnvT.push x s (hΓ.mono m1) (Nat.le_refl _) hw) (by rw [setK_length (by rw [Sh.kinds_length]; exact hw)]; omega) S ks hS hk
    · cases h
  · rename_i cx tl nx _ _ _ _ _ f0 x y r0 heq
    simp at heq; subst heq
    obtain ⟨⟨v, tv, r1, nx1⟩, hv, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · rename_i _ _ l rr r2 hs
      obtain ⟨⟨b, tb, r3, nx3⟩, hb, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨m1, t1⟩ := hE _ _ _ _ _ _ _ _ hv
      obtain ⟨m2, t2⟩ := hE _ _ _ _ _ _ _ _ hb
      refine ⟨by omega, fun Γ hΓ hl S ks hS hk => ?_⟩
      have hw : nx1 + l.width + rr.width ≤ Γ.length := by omega
      have hl1 : nx1 + l.kinds.length + rr.kinds.length ≤ Γ.length := by rw [Sh.kinds_length, Sh.kinds_length]; exact hw
      refine TyN.letE (vs := l.kinds ++ rr.kinds) (t1 Γ hΓ (by omega) none _ (.inl rfl) (tyShape_fits hs))
        (by simp [Sh.kinds_length]) (by omega) (fun k h1 h2 => hΓ.2 k (by omega) (by omega)) ?_
      rw [setK_append _ _ _ _ hl1, Sh.kinds_length]
      have hL1 : (setK Γ nx1 l.kinds).length = Γ.length := setK_length (by rw [Sh.kinds_length]; omega)
      have e1 := EnvT.push x l (hΓ.mono m1) (Nat.le_refl _) (by omega)
      have e2 := EnvT.push y rr e1 (Nat.le_refl _) (by rw [hL1]; omega)
      refine t2 _ e2 ?_ S ks hS hk
      rw [setK_length (by rw [hL1, Sh.kinds_length]; omega), hL1]; omega
    · cases h
  · rename_i cx tl nx _ _ _ _ _ f0 r0 heq
    simp at heq; subst heq
    obtain ⟨⟨a, ta, r1, nx1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · rename_i _ _ c r2 hua
      split at h
      · rename_i hc
        obtain ⟨⟨b, tb, r3, nx2⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
        simp only at h
        split at h
        · rename_i _ _ r4 hub
          obtain ⟨⟨t, tt, r5, nx3⟩, ht, h⟩ := Option.bind_eq_some_iff.1 h
          simp only at h
          split at h
          · rename_i r6
            obtain ⟨⟨el, te, r7, nx4⟩, hel, h⟩ := Option.bind_eq_some_iff.1 h
            obtain ⟨ty', hj, he⟩ := Option.map_eq_some_iff.1 h
            simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
            obtain ⟨m1, t1⟩ := hB _ _ _ _ _ _ _ _ _ ha
            obtain ⟨m2, t2⟩ := hB _ _ _ _ _ _ _ _ _ hb
            obtain ⟨m3, t3⟩ := hE _ _ _ _ _ _ _ _ ht
            obtain ⟨m4, t4⟩ := hE _ _ _ _ _ _ _ _ hel
            refine ⟨by omega, fun Γ hΓ hl S ks hS hk => ?_⟩
            obtain ⟨k1, k2⟩ := join_fits hj hk
            refine TyN.ite (by split <;> simp) (t1 Γ hΓ (by omega) none _ (.inl rfl) (isU_fits hua))
              (t2 Γ (hΓ.mono m1) (by omega) none _ (.inl rfl) (isU_fits hub))
              (t3 Γ (hΓ.mono (by omega)) (by omega) S ks hS k1) (t4 Γ (hΓ.mono (by omega)) hl S ks hS k2)
          · cases h
        · cases h
      · cases h
    · cases h
  · rename_i cx tl ts nx _ _ _ _ _ f0 heq _ _ _
    simp at heq; subst heq
    obtain ⟨m, t⟩ := hB _ _ _ _ _ _ _ _ _ h
    exact ⟨m, t⟩

theorem sok_false (cx : Cx) (S : Option (List Kd)) : SOK cx false S := .inl rfl

theorem pB_step (f : Nat) (hA : PA f) (hL : PL f) : PB (f + 1) := by
  intro cx tl minp ts nx e ty r nx' h
  unfold pBin at h
  obtain ⟨⟨a, ta, r1, nx1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
  simp only at h
  obtain ⟨m1, t1⟩ := hA _ _ _ _ _ _ _ _ ha
  split at h
  · rename_i _ c r2
    split at h
    · rename_i hop
      obtain ⟨⟨a', ta', r1', nx1'⟩, ha', h⟩ := Option.bind_eq_some_iff.1 h
      simp only at h
      obtain ⟨m2, t2⟩ := hA _ _ _ _ _ _ _ _ ha'
      obtain ⟨m3, t3⟩ := hL _ _ _ _ _ _ _ _ _ _ h
      refine ⟨by omega, fun Γ hΓ hl S ks hS hk => ?_⟩
      exact t3 Γ (SOK cx true) (hΓ.mono m2) hl (fun S ks _ hk => t2 Γ hΓ (by omega) S ks (sok_false _ _) hk)
        (fun _ ks hk => t2 Γ hΓ (by omega) none ks (sok_false _ _) hk) S ks hS hk
    · rename_i hop
      obtain ⟨m3, t3⟩ := hL _ _ _ _ _ _ _ _ _ _ h
      refine ⟨by omega, fun Γ hΓ hl S ks hS hk => ?_⟩
      exact t3 Γ (SOK cx true) (hΓ.mono m1) hl (fun S ks hS hk => t1 Γ hΓ (by omega) S ks hS hk)
        (fun ⟨t, r', he, ho⟩ => by simp at he; obtain ⟨rfl, -⟩ := he; simp_all) S ks hS hk
  · rename_i _ hn
    obtain ⟨m3, t3⟩ := hL _ _ _ _ _ _ _ _ _ _ h
    refine ⟨by omega, fun Γ hΓ hl S ks hS hk => ?_⟩
    refine t3 Γ (SOK cx tl) (hΓ.mono m1) hl (fun S ks hS hk => t1 Γ hΓ (by omega) S ks hS hk) ?_ S ks hS hk
    rintro ⟨t, r', rfl, ho⟩ ks hk
    cases tl
    · exact t1 Γ hΓ (by omega) none ks (sok_false _ _) hk
    · exact (hn t r' rfl rfl).elim

theorem opInfo_rng {t op p : Nat} (h : opInfo t = some (op, p)) : 1 ≤ op ∧ op ≤ 8 := by
  unfold opInfo at h; split at h <;> cases h <;> decide

theorem pL_step (f : Nat) (hB : PB f) (hL : PL f) : PL (f + 1) := by
  intro cx minp a ta ts nx e ty r nx' h
  unfold pLoop at h
  split at h
  · rename_i _ t r0
    split at h
    · rename_i op p hop
      have hrng := opInfo_rng hop
      have hO : Opf (Tok.k t :: r0) := ⟨t, r0, rfl, by simp [hop]⟩
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact ⟨Nat.le_refl _, fun Γ Q _ _ ha _ => ha⟩
      · split at h
        · rename_i hu
          split at h
          · split at h
            · rename_i k r'
              obtain ⟨m3, t3⟩ := hL _ _ _ _ _ _ _ _ _ _ h
              refine ⟨m3, fun Γ Q hΓ hl ha ha0 S ks hS hk => ?_⟩
              have hbin : ∀ S, TyN (cx.defs.map sigOf) Γ S (.bin op a (.const (UInt64.ofNat k))) [.w] :=
                fun S => .bin hrng.1 hrng.2 (ha0 hO _ (isU_fits hu)) .const
              exact t3 Γ Q hΓ hl (fun S ks _ hk => by cases hk; exact hbin S) (fun _ ks hk => by cases hk; exact hbin none) S ks hS hk
            · cases h
          · obtain ⟨⟨b, tb, r', nx2⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
            simp only at h
            split at h
            · rename_i hub
              obtain ⟨m2, t2⟩ := hB _ _ _ _ _ _ _ _ _ hb
              obtain ⟨m3, t3⟩ := hL _ _ _ _ _ _ _ _ _ _ h
              refine ⟨by omega, fun Γ Q hΓ hl ha ha0 S ks hS hk => ?_⟩
              have hbin : ∀ S, TyN (cx.defs.map sigOf) Γ S (.bin op a b) [.w] :=
                fun S => .bin hrng.1 hrng.2 (ha0 hO _ (isU_fits hu)) (t2 Γ hΓ (by omega) none _ (sok_false _ _) (isU_fits hub))
              exact t3 Γ Q (hΓ.mono m2) hl (fun S ks _ hk => by cases hk; exact hbin S) (fun _ ks hk => by cases hk; exact hbin none) S ks hS hk
            · cases h
        · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨Nat.le_refl _, fun Γ Q _ _ ha _ => ha⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, fun Γ Q _ _ ha _ => ha⟩

theorem pC_step (f : Nat) (hG : PG f) : PC (f + 1) := by
  intro cx n ts nx e ty r nx' h
  unfold pCallDef at h
  split at h
  · rename_i id d hd
    obtain ⟨⟨as, r1, nx1⟩, ha, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    obtain ⟨m1, hl1, t1⟩ := hG _ _ _ _ _ _ _ ha
    refine ⟨m1, fun Γ hΓ hl S ks hk => ?_⟩
    cases hk
    exact .call (ps := (sigOf d).1) (dropInp_ty _ _ hl1 (t1 Γ hΓ hl)) (by simp [findDef_get hd]; rfl)
  · cases h

theorem pG_step (f : Nat) (hT : PT f) (hG : PG f) : PG (f + 1) := by
  intro cx ps ts nx as r nx' h
  unfold pArgs at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, rfl, fun _ _ _ i h1 => by simp at h1⟩
  · rename_i f0 p ps0 heq
    simp at heq; subst heq
    obtain ⟨⟨a, ta, r1, nx1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    split at h
    · rename_i hm
      obtain ⟨⟨as0, r2, nx2⟩, has, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨m1, t1⟩ := hT _ _ _ _ _ _ _ _ ha
      obtain ⟨m2, hl2, t2⟩ := hG _ _ _ _ _ _ _ has
      refine ⟨by omega, by simp [hl2], fun Γ hΓ hl i h1 h2 => ?_⟩
      cases i with
      | zero => exact ⟨tyMatch_fits _ _ hm, fun ks hk => t1 Γ hΓ (by omega) none ks (.inl rfl) hk⟩
      | succ i => exact t2 Γ (hΓ.mono m1) hl i (by simpa using h1) (by simpa using h2)
    · cases h

theorem pA_step (f : Nat) (hT : PT f) (hG : PG f) (hC : PC f) : PA (f + 1) := by
  intro cx tl ts nx e ty r nx' h
  unfold pApp at h
  split at h
  · cases h
  · rename_i f0 t r0 heq
    simp at heq; subst heq
    split at h
    · rename_i pid ps rs hp
      obtain ⟨⟨as, r1, nx1⟩, ha, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨m1, hl1, t1⟩ := hG _ _ _ _ _ _ _ ha
      refine ⟨m1, fun Γ hΓ hl S ks hS hk => ?_⟩
      cases hk
      exact .prim (dropInp_ty _ _ hl1 (t1 Γ hΓ hl)) (primSig_ok _ _ _ _ hp) (fun h0 => primSig_noarg hp h0 _)
    · exact hT _ _ _ _ _ _ _ _ h
  · rename_i cx tl nx _ _ _ _ _ f0 n r0 heq
    simp at heq; subst heq
    split at h
    · exact hT _ _ _ _ _ _ _ _ h
    · split at h
      · rename_i sn sps hself
        split at h
        · split at h
          · split at h
            · rename_i fn r1
              split at h
              · obtain ⟨⟨as, r2, nx2⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
                simp only at h
                split at h
                · cases h
                · rename_i _ hne
                  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                  obtain ⟨m1, hl1, t1⟩ := hG _ _ _ _ _ _ _ ha
                  refine ⟨m1, fun Γ hΓ hl S ks hS hk => ?_⟩
                  rcases hS with hS | hS | hS
                  · simp_all
                  · simp_all
                  · have hS' : S = some (sps.flatMap Ps.kinds) := by simp [hS, selfK, hself]
                    subst hS'
                    have := dropInp_ty (D := cx.defs.map sigOf) (Γ := Γ) _ _ hl1 (t1 Γ hΓ hl)
                    exact .cont (mkPairFlat_ty this (by intro e; exact hne e))
              · cases h
            · cases h
          · cases h
        · exact hC _ _ _ _ _ _ _ _ h |>.imp id fun h Γ hΓ hl S ks _ hk => h Γ hΓ hl S ks hk
      · exact hC _ _ _ _ _ _ _ _ h |>.imp id fun h Γ hΓ hl S ks _ hk => h Γ hΓ hl S ks hk
  · rename_i cx tl ts nx _ _ _ _ _ f0 heq _ _
    simp at heq; subst heq
    exact hT _ _ _ _ _ _ _ _ h

theorem pU_step (f : Nat) (hE : PE f) (hU : PU f) : PU (f + 1) := by
  intro cx ts nx e sh r nx' h
  unfold pTup at h
  split at h
  · cases h
  · rename_i cx nx _ _ _ _ f0 r0 heq
    simp at heq; subst heq
    obtain ⟨⟨e1, t1, r1, nx1⟩, he1, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    obtain ⟨m1, k1⟩ := hE _ _ _ _ _ _ _ _ he1
    split at h
    · rename_i s r2 hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨m1, fun Γ hΓ hl S => k1 Γ hΓ hl S _ (.inl rfl) (tyShape_fits hs)⟩
    · rename_i s r2 hs
      obtain ⟨⟨rest, sr, r3, nx3⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨m2, k2⟩ := hU _ _ _ _ _ _ _ hr
      refine ⟨by omega, fun Γ hΓ hl S => ?_⟩
      have := TyL.cons (k1 Γ hΓ (by omega) none _ (.inl rfl) (tyShape_fits hs)) (TyL.cons (k2 Γ (hΓ.mono m1) hl none) .nil)
      simp only [List.append_nil] at this
      exact .pair this
    · cases h
  · cases h

theorem pT_step (f : Nat) (hE : PE f) (hU : PU f) : PT (f + 1) := by
  intro cx tl ts nx e ty r nx' h
  unfold pAtom at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, fun Γ hΓ hl S ks hS hk => by cases hk; exact .const⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, fun Γ hΓ hl S ks hS hk => by cases hk; exact .prim .nil rfl (fun _ => rfl)⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact ⟨Nat.le_refl _, fun Γ hΓ hl S ks hS hk => by cases hk; exact .prim .nil rfl (fun _ => rfl)⟩
  · rename_i cx tl nx _ _ _ _ _ f0 n r0 heq
    split at h
    · rename_i slot s hf
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      refine ⟨Nat.le_refl _, fun Γ hΓ hl S ks hS hk => ?_⟩
      cases hk
      exact .loc ((hΓ.1 _ (findEnv_mem hf)).2.2 s rfl)
    · rename_i slot hf
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      refine ⟨Nat.le_refl _, fun Γ hΓ hl S ks hS hk => ?_⟩
      cases hk
      have := (hΓ.1 _ (findEnv_mem hf)).2.1
      exact .loc ⟨by simpa [Ps.width] using this, by simp⟩
    · cases h
    · split at h
      · rename_i id d hd
        split at h
        · rename_i hp
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          refine ⟨Nat.le_refl _, fun Γ hΓ hl S ks hS hk => ?_⟩
          cases hk
          have hp' : d.params = [] := by simpa using hp
          exact .call (ps := []) .nil (by simp [findDef_get hd, sigOf, hp'])
        · cases h
      · cases h
  · rename_i cx tl nx _ _ _ _ _ f0 r0 heq
    simp at heq; subst heq
    obtain ⟨⟨e1, t1, r1, nx1⟩, he1, h⟩ := Option.bind_eq_some_iff.1 h
    simp only at h
    obtain ⟨m1, k1⟩ := hE _ _ _ _ _ _ _ _ he1
    split at h
    · rename_i r2
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨m1, k1⟩
    · obtain ⟨⟨e2, t2, r2, nx2⟩, he2, h⟩ := Option.bind_eq_some_iff.1 h
      simp only at h
      obtain ⟨m2, k2⟩ := hE _ _ _ _ _ _ _ _ he2
      split at h
      · rename_i s1 hs
        obtain ⟨⟨rest, st, r3, nx3⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
        obtain ⟨m3, k3⟩ := hU _ _ _ _ _ _ _ hr
        refine ⟨by omega, fun Γ hΓ hl S ks hS hk => ?_⟩
        cases hk
        have := TyL.cons (k2 Γ hΓ (by omega) none _ (.inl rfl) (tyShape_fits hs)) (TyL.cons (k3 Γ (hΓ.mono m2) hl none) .nil)
        simp only [List.append_nil] at this
        exact .pair this
      · cases h
    · cases h
  · cases h

theorem p_all : ∀ f, PE f ∧ PB f ∧ PL f ∧ PA f ∧ PC f ∧ PG f ∧ PT f ∧ PU f
  | 0 => by
    refine ⟨fun _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ _ _ h => ?_,
      fun _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ h => ?_, fun _ _ _ _ _ _ _ _ h => ?_,
      fun _ _ _ _ _ _ _ h => ?_⟩
    · rw [pExpr.eq_1] at h; cases h
    · rw [pBin.eq_1] at h; cases h
    · rw [pLoop.eq_1] at h; cases h
    · rw [pApp.eq_1] at h; cases h
    · rw [pCallDef.eq_1] at h; cases h
    · rw [pArgs.eq_1] at h; cases h
    · rw [pAtom.eq_1] at h; cases h
    · rw [pTup.eq_1] at h; cases h
  | f + 1 => by
    obtain ⟨hE, hB, hL, hA, hC, hG, hT, hU⟩ := p_all f
    exact ⟨pE_step f hB hE, pB_step f hA hL, pL_step f hB hL, pA_step f hT hG hC, pC_step f hG, pG_step f hT hG,
      pT_step f hE hU, pU_step f hE hU⟩

/-- every binding names a parameter `ps[i]` at its packed slot -/
def Lay (ps : List Ps) (start : Nat) (env : List (List Nat × Nat × Ps)) : Prop :=
  ∀ e ∈ env, ∃ i, ∃ h : i < ps.length, ps[i] = e.2.2 ∧ e.2.1 = start + ((ps.take i).flatMap Ps.kinds).length

theorem Lay.nil (ps start) : Lay ps start [] := fun _ h => by simp at h

theorem Lay.cons_ps {ps : List Ps} {start env} (p : Ps) (h : Lay ps (start + p.width) env) : Lay (p :: ps) start env := by
  intro e he
  obtain ⟨i, hi, h1, h2⟩ := h e he
  refine ⟨i + 1, by simp; omega, by simpa using h1, ?_⟩
  simp [h2, Ps.kinds_length]; omega

theorem Lay.append_ps {ps : List Ps} {start env} (qs : List Ps) (h : Lay ps start env) : Lay (ps ++ qs) start env := by
  intro e he
  obtain ⟨i, hi, h1, h2⟩ := h e he
  refine ⟨i, by simp; omega, by rw [List.getElem_append_left hi]; exact h1, ?_⟩
  rw [List.take_append_of_le_length (by omega)]; exact h2

theorem Lay.prepend_ps {ps : List Ps} {start env} (qs : List Ps) (h : Lay ps (start + (qs.flatMap Ps.kinds).length) env) :
    Lay (qs ++ ps) start env := by
  induction qs generalizing start with
  | nil => simpa using h
  | cons q qs ih =>
    have := ih (start := start + q.width) (by simp [Ps.kinds_length] at h ⊢; rw [Nat.add_assoc]; exact h)
    exact Lay.cons_ps q this

theorem mkEnv_lay : ∀ (start : Nat) (ps : List Ps) (ns : List (List Nat)) env, mkEnv start ps ns = some env → Lay ps start env
  | _, [], [], env, h => by simp [mkEnv] at h; subst h; exact Lay.nil _ _
  | start, p :: ps, n :: ns, env, h => by
    simp only [mkEnv, Option.map_eq_some_iff] at h
    obtain ⟨env', h1, rfl⟩ := h
    have ih := Lay.cons_ps p (mkEnv_lay (start + p.width) ps ns env' h1)
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨0, by simp, rfl, by simp⟩
    · exact ih e he
  | _, [], _ :: _, _, h | _, _ :: _, [], _, h => by simp [mkEnv] at h

theorem go_lay (p : Ps) : ∀ (ns : List (List Nat)) (s : Nat) e ps s', bindSlots.go p s ns = (e, ps, s') →
    Lay ps s e ∧ s' = s + (ps.flatMap Ps.kinds).length
  | [], s, e, ps, s', h => by simp [bindSlots.go] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨Lay.nil _ _, by simp⟩
  | n :: l, s, e, ps, s', h => by
    rcases hgo : bindSlots.go p (s + p.width) l with ⟨e1, ps1, s1⟩
    obtain ⟨ih1, ih2⟩ := go_lay p l (s + p.width) e1 ps1 s1 hgo
    simp only [bindSlots.go, hgo] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨?_, by rw [ih2, List.flatMap_cons, List.length_append, Ps.kinds_length]; omega⟩
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact ⟨0, by simp, rfl, by simp⟩
    · exact Lay.cons_ps p ih1 e he

theorem bindSlots_lay : ∀ (groups : List (List (List Nat) × TyR)) (start : Nat) (used : Bool) e ps s',
    bindSlots start used groups = (e, ps, s') → Lay ps start e ∧ s' = start + (ps.flatMap Ps.kinds).length
  | [], start, used, e, ps, s', h => by
    simp [bindSlots] at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact ⟨Lay.nil _ _, by simp⟩
  | (ns, t) :: g, start, used, e, ps, s', h => by
    unfold bindSlots at h
    rcases hp : pickPs used (ns.length == 1) t with ⟨p, used'⟩
    rcases hgo : bindSlots.go p start ns with ⟨e1, ps1, s1⟩
    obtain ⟨g1, g2⟩ := go_lay p ns start e1 ps1 s1 hgo
    rcases hb : bindSlots s1 used' g with ⟨e2, ps2, s2⟩
    obtain ⟨b1, b2⟩ := bindSlots_lay g s1 used' e2 ps2 s2 hb
    simp only [hp, hgo, hb] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨?_, ?_⟩
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact Lay.append_ps _ g1 e he
      · rw [g2] at b1; exact Lay.prepend_ps _ b1 e he
    · rw [b2, g2]; simp; omega

theorem flatMap_split (ps : List Ps) (i : Nat) (hi : i < ps.length) :
    ps.flatMap Ps.kinds = (ps.take i).flatMap Ps.kinds ++ ps[i].kinds ++ (ps.drop (i + 1)).flatMap Ps.kinds := by
  conv => lhs; rw [← List.take_append_drop i ps]
  rw [List.drop_eq_getElem_cons hi, List.flatMap_append, List.flatMap_cons, List.append_assoc]

theorem lay_envT {ps : List Ps} {start env} (hL : Lay ps start env) (pre : List (Option Kd)) (n : Nat) (hpre : pre.length = start) :
    EnvT env.reverse (pre ++ (ps.flatMap Ps.kinds).map some ++ List.replicate n none) (start + (ps.flatMap Ps.kinds).length) := by
  refine ⟨fun e he => ?_, fun k hk hl => ?_⟩
  rotate_left
  · have h1 : (pre ++ (ps.flatMap Ps.kinds).map some).length = start + (ps.flatMap Ps.kinds).length := by simp [hpre]
    rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
    simp only [List.length_append, List.length_replicate, List.length_map] at hl h1
    rw [if_pos (by simp only [List.length_append, List.length_map]; omega)]
  generalize hpost : List.replicate n (none : Option Kd) = post
  rw [List.mem_reverse] at he
  obtain ⟨i, hi, h1, h2⟩ := hL e he
  have hs := flatMap_split ps i hi
  generalize (ps.take i).flatMap Ps.kinds = A at hs h2
  generalize (ps.drop (i + 1)).flatMap Ps.kinds = B at hs
  generalize hK : ps[i].kinds = K at hs
  have hw : e.2.2.width = K.length := by rw [← hK, Ps.kinds_length, h1]
  rw [hs]
  have hl : (pre ++ (A ++ K ++ B).map some ++ post).length = start + A.length + K.length + B.length + post.length := by
    simp only [List.length_append, List.length_map]; omega
  refine ⟨?_, ?_, fun s hsh => ⟨?_, ?_⟩⟩
  · simp only [List.length_append]; omega
  · rw [hl]; omega
  · rw [hl]; rw [hsh] at hw; simp only [Ps.width] at hw; omega
  have hk : s.kinds = K := by rw [← hK, h1, hsh]; rfl
  have hΓ : pre ++ (A ++ K ++ B).map some ++ post = (pre ++ A.map some) ++ (K.map some ++ (B.map some ++ post)) := by
    simp only [List.map_append, List.append_assoc]
  rw [h2, hΓ, List.drop_left' (by simp; omega), ← Sh.kinds_length, hk, List.take_left' (by simp)]

theorem tyOk_fits {res : Sh} {t : Ty} (h : tyOk res t = true) : t.fits res.kinds := by
  cases t with
  | s s => simp [tyOk] at h; subst h; rfl
  | lit => simp [tyOk] at h; subst h; rfl
  | inp => simp [tyOk] at h
  | bot => simp [tyOk] at h

theorem join_s {a : Ty} {res x : Sh} (h : a.join (.s res) = some (.s x)) : x = res := by
  cases a with
  | bot => simp [Ty.join] at h; exact h.symm
  | lit => unfold Ty.join at h; split at h <;> simp_all
  | s a => unfold Ty.join at h; split at h <;> simp_all
  | inp => unfold Ty.join at h; split at h <;> simp_all

theorem foldl_add (l : List Nat) (a : Nat) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih]; omega

theorem width_sum (ps : List Ps) : (ps.map Ps.width).foldl (· + ·) 0 = (ps.flatMap Ps.kinds).length := by
  rw [foldl_add]; induction ps with
  | nil => rfl
  | cons p ps ih => simp [Ps.kinds_length] at ih ⊢

theorem pDef_ok (fuel : Nat) (defs : List DefI) (ts : List Tok) (di : DefI) (da : DefA) (r : List Tok)
    (h : pDef fuel defs ts = some (di, da, r)) :
    TyDef (defs.map sigOf) da (sigOf di) ∧ da.id = defs.length ∧ (di.resLst = true → di.res = .ls) := by
  obtain ⟨hE, -⟩ := p_all fuel
  unfold pDef at h
  split at h
  · rename_i name ts0
    split at h
    · cases h
    · split at h
      · rename_i r0
        obtain ⟨⟨tys, r1⟩, ha, h⟩ := Option.bind_eq_some_iff.1 h
        simp only at h
        split at h
        · rename_i resT revSt hrev
          split at h
          · cases h
          · split at h
            · rename_i r2
              obtain ⟨⟨zn, r3⟩, hz, h⟩ := Option.bind_eq_some_iff.1 h
              simp only at h
              split at h
              · cases h
              · obtain ⟨envZ, hZ, h⟩ := Option.bind_eq_some_iff.1 h
                obtain ⟨⟨z, tz, r4, nx1⟩, hpz, h⟩ := Option.bind_eq_some_iff.1 h
                simp only at h
                split at h
                · cases h
                · rename_i hokz
                  split at h
                  · rename_i nb r5
                    obtain ⟨⟨sn, r6⟩, hs, h⟩ := Option.bind_eq_some_iff.1 h
                    simp only at h
                    split at h
                    · cases h
                    · obtain ⟨envS, hS, h⟩ := Option.bind_eq_some_iff.1 h
                      obtain ⟨⟨sb, ts', r7, nx2⟩, hps, h⟩ := Option.bind_eq_some_iff.1 h
                      simp only at h
                      split at h
                      · rename_i x hj
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl, rfl⟩ := h
                        generalize stateKinds false revSt.reverse = ps at hZ hS hpz hps ⊢
                        generalize trRes resT = res at hokz hj ⊢
                        have hx := join_s hj; subst hx
                        simp only [width_sum] at hpz hps ⊢
                        generalize hL : ps.flatMap Ps.kinds = L at hpz hps ⊢
                        obtain ⟨mz, tzz⟩ := hE _ _ _ _ _ _ _ _ hpz
                        obtain ⟨ms, tss⟩ := hE _ _ _ _ _ _ _ _ hps
                        refine ⟨⟨by simp [sigOf, Ps.kinds, hL]; omega, by show 1 + L.length ≤ nx2; omega,
                          by simp [sigOf, Sh.kinds_length], ?_⟩, trivial, by simp⟩
                        simp only [sigOf, List.flatMap_cons, Ps.kinds, hL]
                        have hΓ : ([Kd.w] ++ L).map some ++ List.replicate (nx2 - (1 + L.length)) none =
                            [some Kd.w] ++ L.map some ++ List.replicate (nx2 - (1 + L.length)) none := by simp
                        rw [hΓ]
                        have eZ := lay_envT (mkEnv_lay 1 ps zn envZ hZ) [some Kd.w] (nx2 - (1 + L.length)) rfl
                        have eS := lay_envT (mkEnv_lay 1 ps sn envS hS) [some Kd.w] (nx2 - (1 + L.length)) rfl
                        rw [hL] at eZ eS
                        have hlen : ([some Kd.w] ++ L.map some ++ List.replicate (nx2 - (1 + L.length)) none).length = nx2 := by
                          simp only [List.length_append, List.length_map, List.length_replicate, List.length_singleton]; omega
                        refine TyB.loop (sk := L) (n := nx2 - (1 + L.length)) (by simp) ?_ ?_
                        · exact tzz _ eZ (by omega) none _ (.inl rfl) (tyOk_fits (by simpa using hokz))
                        · refine tss _ ?_ (by omega) (some L) _ (.inr (.inr (by simp [selfK, hL]))) (join_fits hj rfl).1
                          refine ⟨fun e he => ?_, (eS.mono (by omega)).2⟩
                          rcases List.mem_cons.1 he with rfl | he
                          · exact ⟨by simp [Ps.width]; omega, by rw [hlen]; simp [Ps.width]; omega, fun s hs => by cases hs⟩
                          · exact (eS.mono (by omega)).1 e he
                      · cases h
                  · cases h
            · cases h
        · cases h
      · obtain ⟨⟨groups, r1⟩, hb, h⟩ := Option.bind_eq_some_iff.1 h
        simp only at h
        split at h
        · rename_i r2
          obtain ⟨⟨resT, r3⟩, ht, h⟩ := Option.bind_eq_some_iff.1 h
          simp only at h
          split at h
          · rename_i r4
            rcases hbs : bindSlots 0 false groups with ⟨env, ps, npw⟩
            obtain ⟨hlay, hnpw⟩ := bindSlots_lay groups 0 false env ps npw hbs
            simp only [hbs] at h
            split at h
            · cases h
            · obtain ⟨⟨b, tb, r5, nx⟩, hpe, h⟩ := Option.bind_eq_some_iff.1 h
              simp only at h
              split at h
              · cases h
              · rename_i hok
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                simp only [Bool.not_eq_true', Bool.not_eq_false] at hok
                obtain ⟨m, t⟩ := hE _ _ _ _ _ _ _ _ hpe
                refine ⟨⟨by simp [sigOf, hnpw], m, by simp [sigOf, Sh.kinds_length], ?_⟩, rfl, fun hr => ?_⟩
                · have he := lay_envT hlay [] (nx - npw) rfl
                  rw [← hnpw] at he
                  simp only [List.nil_append] at he
                  exact .plain <| t _ he (by simp only [List.length_append, List.length_map, List.length_replicate]; omega) none _ (.inl rfl) (tyOk_fits (by simpa using hok))
                · cases resT <;> simp_all [trRes]
          · cases h
        · cases h
  · cases h

theorem pDefs_ok (fuel : Nat) : ∀ (f : Nat) (defs : List DefI) (ts : List Tok) (ds : List DefI) (as : List DefA),
    pDefs fuel f defs ts = some (ds, as) → ∃ nw : List DefI, ds = defs ++ nw ∧ nw.length = as.length ∧
      (∀ (i : Nat) d di, as[i]? = some d → nw[i]? = some di → TyDef ((defs ++ nw.take i).map sigOf) d (sigOf di)) ∧
      (∀ di ∈ nw, di.resLst = true → di.res = .ls)
  | 0, _, _, _, _, h => by simp [pDefs] at h
  | f + 1, defs, [], ds, as, h => by
    simp [pDefs] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], by simp, rfl, by simp, by simp⟩
  | f + 1, defs, t :: ts, ds, as, h => by
    simp only [pDefs] at h
    obtain ⟨⟨di, da, r⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨ds', as'⟩, hr, he⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    obtain ⟨t1, -, t3⟩ := pDef_ok fuel defs _ di da r hd
    obtain ⟨nw, rfl, hl, ht, hm⟩ := pDefs_ok fuel f (defs ++ [di]) r ds' as' hr
    refine ⟨di :: nw, by simp, by simp [hl], fun i d di' h1 h2 => ?_, fun d' hd' => ?_⟩
    rotate_left
    · rcases List.mem_cons.1 hd' with rfl | hd'
      · exact t3
      · exact hm d' hd'
    cases i with
    | zero => simp at h1 h2; subst h1; subst h2; simpa using t1
    | succ i =>
      have := ht i d di' (by simpa using h1) (by simpa using h2)
      simpa [List.take_succ_cons] using this

theorem refParse_ty {ts : List UInt64} {p : List DefA} (h : refParse ts = some p) : ∃ sigs, TyProg p sigs := by
  unfold refParse at h
  obtain ⟨toks, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨ds, as⟩, hd, h⟩ := Option.bind_eq_some_iff.1 h
  simp only at h
  split at h
  · rename_i d hl
    split at h
    · rename_i hm
      cases h
      obtain ⟨nw, rfl, hlen, ht, hm'⟩ := pDefs_ok _ _ _ _ _ _ hd
      refine ⟨ds.map sigOf, by simp [hlen], fun i d' sg h1 h2 => ?_, ?_⟩
      · rw [List.getElem?_map] at h2
        cases h3 : ds[i]? with
        | none => simp [h3] at h2
        | some di =>
          simp [h3] at h2; subst h2
          have := ht i d' di h1 h3
          simpa [List.map_take] using this
      · rw [List.getLast?_map, hl]
        simp [isMain] at hm
        obtain ⟨⟨-, hp⟩, hr⟩ := hm
        have := hm' d (List.mem_of_getLast? hl) hr
        simp [sigOf, hp, Ps.kinds, this, Sh.kinds]
    · cases h
  · cases h

theorem parsed_not_stuck {ts : List UInt64} {p : List DefA} (h : ParsesProgram ts p) (κ : Nat) (inp : List UInt8) :
    Sem κ p inp ≠ .error .stuck := by
  obtain ⟨sigs, hs⟩ := refParse_ty h
  exact sem_ok κ p sigs hs inp

/-- **the end-to-end theorem with progress**: as `compiler_correct`, and the meaning never gets stuck, so for every input
the emitted code's run shows the program's output, the capacity trap, or (below the work bound) out-of-memory -/
theorem compiler_correct' (HP : ParStage) (HG : GenStage) (x : List UInt8) (hx : x.length ≤ 2 ^ 20) (h : mC x ≠ []) :
    ∃ ts p, LexSpec.Lexes x ts ∧ ParsesProgram ts p ∧ ImplementsC (mC x) (Sem κC p) ∧
      ∀ inp, Sem κC p inp ≠ .error .stuck := by
  obtain ⟨ts, p, h1, h2, h3⟩ := compiler_correct HP HG x hx h
  exact ⟨ts, p, h1, h2, h3, parsed_not_stuck h2 κC⟩

end NanoMain
