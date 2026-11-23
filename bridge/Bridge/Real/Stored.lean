/- Bridge.Real.Stored: what an ACCEPTED stream stores, in the form the transfer kit reads.

All against REAL con-leche (no trimmed copies).  Source of facts: `Cached.checkDecls_consts`
(Model/StreamConsts.lean:764): every def/thm record of the accepted stream is stored under its name with
`AnnotOf declared stored`, i.e. `stored.resetMeta = declared.zeta.resetMeta`.  Here: inversion of `resetMeta`
for the binder-free parts, so a stored type `∀ x₁…xₙ, @Eq S a b` comes back with the DECLARED `S a b`
(only the binder data of the `∀`s may differ; transfer does not read it). -/
import ConLeche.MainTheorem
import ConLeche.Model.StreamConsts
import Bridge.Transfer

namespace Bridge.Real
open ConLeche ConLeche.SetModel SetTheory

universe w

/-- Binder-free terms: no λ/∀/let/proj/fvar.  `resetMeta` cannot change them. -/
def BF : Expr → Prop
  | .bvar _ | .sort _ | .const _ _ | .lit _ => True
  | .app f a => BF f ∧ BF a
  | _ => False

theorem BF.rm : ∀ {e : Expr}, BF e → e.resetMeta = e
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, ⟨hf, ha⟩ => by simp only [Expr.resetMeta, hf.rm, ha.rm]

/-- If `e'.resetMeta = e` and `e` is binder-free then `e' = e`. -/
theorem BF.inv : ∀ {e : Expr}, BF e → ∀ {e' : Expr}, e'.resetMeta = e → e' = e
  | .bvar _, _, e', h | .sort _, _, e', h | .const _ _, _, e', h | .lit _, _, e', h => by
      cases e' <;> simp_all [Expr.resetMeta]
  | .app f a, ⟨hf, ha⟩, e', h => by
      cases e' <;> simp only [Expr.resetMeta, reduceCtorEq] at h
      case app f' a' =>
        obtain ⟨h1, h2⟩ := Expr.app.inj h
        rw [hf.inv h1, ha.inv h2]

/-- `∀`-telescope with binder data erased to a list of domains. -/
def piD : List Expr → Expr → Expr
  | [], b => b
  | T :: Ts, b => .forallE T (piD Ts b) ⟨.never⟩

/-- Inversion along a `∀` telescope of binder-free domains: the stored term is the same telescope with some
binder data. -/
theorem piD_inv : ∀ (Ts : List Expr) {b e : Expr}, (∀ T ∈ Ts, BF T) → BF b →
    e.resetMeta = piD Ts b → ∃ ms : List BinderMeta, ms.length = Ts.length ∧ e = piN (Ts.zip ms) b
  | [], b, e, _, hb, h => ⟨[], rfl, hb.inv h⟩
  | T :: Ts, b, e, hT, hb, h => by
      cases e <;> simp only [Expr.resetMeta, piD, reduceCtorEq] at h
      case forallE T' B' m' =>
        obtain ⟨h1, h2, -⟩ := Expr.forallE.inj h
        obtain ⟨ms, hl, rfl⟩ := piD_inv Ts (fun T h => hT T (List.mem_cons_of_mem _ h)) hb h2
        refine ⟨m' :: ms, by simp [hl], ?_⟩
        rw [(hT T List.mem_cons_self).inv h1]; rfl

/-- `resetMeta` of a declared telescope with binder-free parts. -/
theorem piD_rm : ∀ (Ts : List Expr) (ms : List BinderMeta) {b : Expr}, ms.length = Ts.length →
    (∀ T ∈ Ts, BF T) → BF b → (piN (Ts.zip ms) b).resetMeta = piD Ts b
  | [], [], b, _, _, hb => hb.rm
  | T :: Ts, m :: ms, b, hl, hT, hb => by
      simp only [List.zip_cons_cons, piN, Expr.resetMeta, piD]
      rw [(hT T List.mem_cons_self).rm, piD_rm Ts ms (by simpa using hl)
        (fun T h => hT T (List.mem_cons_of_mem _ h)) hb]

/-- `zeta` is the identity on let-free telescopes of binder-free parts. -/
theorem BF.zeta : ∀ {e : Expr}, BF e → e.zeta = e
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, ⟨hf, ha⟩ => by simp only [Expr.zeta, hf.zeta, ha.zeta]

theorem piN_zeta : ∀ (Ts : List (Expr × BinderMeta)) {b : Expr}, (∀ p ∈ Ts, BF p.1) → BF b →
    (piN Ts b).zeta = piN Ts b
  | [], b, _, hb => hb.zeta
  | (T, m) :: Ts, b, hT, hb => by
      simp only [piN, Expr.zeta]
      rw [(hT (T, m) List.mem_cons_self).zeta, piN_zeta Ts (fun p h => hT p (List.mem_cons_of_mem _ h)) hb]

/-- **A stored def/thm of the accepted stream, by its DECLARED type.**  The record `pd` declares `cv`, whose type
is a telescope `∀ (x : T₁) … (xₙ : Tₙ), b` (any binder data) with binder-free parts.  Then `env` finds `cv.name`,
with `cv`'s level parameters and a type that is the same telescope (only binder data may differ). -/
theorem stored_tele (V : Type w) [SetTheory V] {pins : List NatOpPinSet} {ds : Array Declaration} {env : Env}
    (accepted : Cached.checkDecls .verified pins ds = .ok env)
    {pd : Declaration} (hmem : pd ∈ ds) {cv : ConstantVal} (hcv : Cached.Declaration.Declares pd cv)
    (Ts : List Expr) (ms : List BinderMeta) (b : Expr) (hl : ms.length = Ts.length)
    (hty : cv.type = piN (Ts.zip ms) b) (hT : ∀ T ∈ Ts, BF T) (hb : BF b) :
    ∃ c ms', env.find? cv.name = some c ∧ c.toConstantVal.levelParams = cv.levelParams ∧
      ms'.length = Ts.length ∧ c.toConstantVal.type = piN (Ts.zip ms') b := by
  obtain ⟨c, hf, hlp, han⟩ := Cached.checkDecls_consts V accepted hmem hcv
  have hT' : ∀ p ∈ Ts.zip ms, BF p.1 := fun p hp => hT p.1 (List.of_mem_zip hp).1
  unfold AnnotOf at han
  rw [hty, piN_zeta _ hT' hb, piD_rm Ts ms hl hT hb] at han
  obtain ⟨ms', hl', he⟩ := piD_inv Ts hT hb han
  exact ⟨c, ms', hf, hlp, hl', he⟩

end Bridge.Real
