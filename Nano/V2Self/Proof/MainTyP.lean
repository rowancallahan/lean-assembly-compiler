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
  ∀ e ∈ env, e.2.1 + e.2.2.width ≤ nx ∧ e.2.1 + e.2.2.width ≤ Γ.length ∧
    ∀ s, e.2.2 = .sh s → known Γ e.2.1 s.width s.kinds

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
  fun e he => let ⟨a, b, c⟩ := h e he; ⟨by omega, b, c⟩

theorem EnvT.push {env Γ nx s} (x : List Nat) (sh : Sh) (h : EnvT env Γ nx) (hs : nx ≤ s) (hΓ : s + sh.width ≤ Γ.length) :
    EnvT ((x, s, .sh sh) :: env) (setK Γ s sh.kinds) (s + sh.width) := by
  have hΓ' : s + sh.kinds.length ≤ Γ.length := by rw [Sh.kinds_length]; exact hΓ
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · refine ⟨Nat.le_refl _, by rw [setK_length hΓ']; exact hΓ, fun s' e' => ?_⟩
    cases e'; have := known_setK_at hΓ'; rwa [Sh.kinds_length] at this
  · obtain ⟨a, b, c⟩ := h e he
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
      refine TyN.letE (vs := s.kinds) (t1 Γ hΓ (by omega) none _ (.inl rfl) (tyShape_fits hs)) (Sh.kinds_length s) hw ?_
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
        (by simp [Sh.kinds_length]) (by omega) ?_
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

end NanoMain
