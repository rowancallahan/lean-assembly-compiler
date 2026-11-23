/- MiniBind: binders on top of MiniDenotes (standalone, no imports).  Copies from con-leche (ConLeche/Denotes.lean):
`push` :118, rules `bvar` :137, `app` :151, `lam` :157 (BinderMeta dropped; `regime φ m.pw` is the parameter `r`),
`proj_fst`/`proj_snd` :171/:176 (the `env.findProj?` side condition dropped).  `let` has no Denotes rule: it is the
redex `app (lam ty body) v`.  Model facts are hypotheses (`Facts`), each with the con-leche lemma that would give it:
* `beta`  = `app_lamR_pos` (SetModel/Ops.lean:206): `r ≠ 0 → a ∈ A → app (lamR r A F) a = F a`.
* `fst/snd` = `sfst_spair`/`ssnd_spair` (SetTheory/Derive/Sigma.lean:85/93), if `Prod.mk` denotes `spair`.
* `dec`, `mem`, `onlyEnc`: the domain constant `T` denotes exactly the encodings (`lam` quantifies over ALL x ∈ A,
  not just encodings, so `onlyEnc` is needed).  `r ≠ 0`: graph regime, i.e. `pw.holds φ₁ = false` (binder body not a Prop).
Everything is stated at one fixed φ (= φ₁), which is why `φ` does not appear. -/
namespace MiniBind

inductive Literal | natVal (n : Nat)
inductive Expr
  | bvar (i : Nat) | const (n : String) | app (f a : Expr) | lam (ty body : Expr) | proj (i : Nat) (e : Expr)
  | lit (l : Literal)

def natLitToConstructor : Nat → Expr
  | 0 => .const "Nat.zero"
  | k + 1 => .app (.const "Nat.succ") (.lit (.natVal k))

def push {V : Type} (x : V) (ρ : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => ρ i

variable {V : Type} (app : V → V → V) (lamR : Nat → V → (V → V) → V) (mem : V → V → Prop)
  (sfst ssnd : V → V) (r : Nat)

inductive Denotes (cval : String → V) : (Nat → V) → Expr → V → Prop
  | bvar {ρ i} : Denotes cval ρ (.bvar i) (ρ i)
  | const {ρ n} : Denotes cval ρ (.const n) (cval n)
  | app {ρ f a F X} : Denotes cval ρ f F → Denotes cval ρ a X → Denotes cval ρ (.app f a) (app F X)
  | lam {ρ ty body A F} (hA : Denotes cval ρ ty A) (hF : ∀ x, mem x A → Denotes cval (push x ρ) body (F x))
      (hP : r = 0 → ∀ x, mem x A → F x = F x) : Denotes cval ρ (.lam ty body) (lamR r A F)
  | projFst {ρ e P} : Denotes cval ρ e P → Denotes cval ρ (.proj 0 e) (sfst P)
  | projSnd {ρ e P} : Denotes cval ρ e P → Denotes cval ρ (.proj 1 e) (ssnd P)
  | natLit {ρ n X} : Denotes cval ρ (natLitToConstructor n) X → Denotes cval ρ (.lit (.natVal n)) X

/-! ## intrinsically typed source -/
inductive Ty | nat | prod (a b : Ty)
@[reducible] def Ty.den : Ty → Type | .nat => Nat | .prod a b => a.den × b.den
def Ty.name : Ty → String | .nat => "Nat" | .prod a b => "Prod " ++ a.name ++ " " ++ b.name

inductive Var : List Ty → Ty → Type
  | zero {Γ t} : Var (t :: Γ) t
  | succ {Γ s t} : Var Γ t → Var (s :: Γ) t
def Var.idx : Var Γ t → Nat | .zero => 0 | .succ v => v.idx + 1

inductive Tm : List Ty → Ty → Type
  | var {Γ t} : Var Γ t → Tm Γ t
  | lit {Γ} (n : Nat) : Tm Γ .nat
  | add {Γ} (a b : Tm Γ .nat) : Tm Γ .nat
  | let_ {Γ s t} (v : Tm Γ s) (b : Tm (s :: Γ) t) : Tm Γ t
  | pair {Γ s t} (a : Tm Γ s) (b : Tm Γ t) : Tm Γ (.prod s t)
  | fst {Γ s t} (p : Tm Γ (.prod s t)) : Tm Γ s
  | snd {Γ s t} (p : Tm Γ (.prod s t)) : Tm Γ t
  | natCase {Γ t} (n : Tm Γ .nat) (z : Tm Γ t) (s : Tm (.nat :: Γ) t) : Tm Γ t

abbrev Env (Γ : List Ty) := ∀ {t}, Var Γ t → t.den
def Env.cons (v : s.den) (σ : Env Γ) : Env (s :: Γ) := fun {t} x => match x with
  | .zero => v
  | .succ x => σ x

def eval : Tm Γ t → Env Γ → t.den
  | .var x, σ => σ x
  | .lit n, _ => n
  | .add a b, σ => eval a σ + eval b σ
  | .let_ v b, σ => eval b (σ.cons (eval v σ))
  | .pair a b, σ => (eval a σ, eval b σ)
  | .fst p, σ => (eval p σ).1
  | .snd p, σ => (eval p σ).2
  | .natCase n z s, σ => match eval n σ with | 0 => eval z σ | k + 1 => eval s (σ.cons k)

def tr : Tm Γ t → Expr
  | .var x => .bvar x.idx
  | .lit n => .lit (.natVal n)
  | .add a b => .app (.app (.const "Nat.add") (tr a)) (tr b)
  | .let_ (s := s) v b => .app (.lam (.const s.name) (tr b)) (tr v)
  | .pair a b => .app (.app (.const "Prod.mk") (tr a)) (tr b)
  | .fst p => .proj 0 (tr p)
  | .snd p => .proj 1 (tr p)
  | .natCase (t := t) n z s =>
    .app (.app (.app (.app (.const "Nat.casesOn") (.lam (.const "Nat") (.const t.name))) (tr n)) (tr z))
      (.lam (.const "Nat") (tr s))

variable (cval : String → V)
def enc : Nat → V | 0 => cval "Nat.zero" | n + 1 => app (cval "Nat.succ") (enc n)
def encT : (t : Ty) → t.den → V
  | .nat, n => enc app cval n
  | .prod a b, (x, y) => app (app (cval "Prod.mk") (encT a x)) (encT b y)

theorem lit_denotes (ρ : Nat → V) : ∀ n, Denotes app lamR mem sfst ssnd r cval ρ (.lit (.natVal n)) (enc app cval n)
  | 0 => .natLit .const
  | n + 1 => .natLit (.app .const (lit_denotes ρ n))

/-- `dec t` is a decoder, only its values on encodings matter (it makes `F` below total).  Needs `Inhabited` nowhere:
it is a parameter whose spec is `dec_enc`. -/
structure Facts (dec : ∀ t : Ty, V → t.den) : Prop where
  add : ∀ a b, app (app (cval "Nat.add") (enc app cval a)) (enc app cval b) = enc app cval (a + b)
  /-- `Nat.casesOn` at a constant motive: iota on encodings (`M` = the motive's denotation, arbitrary) -/
  cases0 : ∀ M z f, app (app (app (app (cval "Nat.casesOn") M) (enc app cval 0)) z) f = z
  casesS : ∀ M z f k, app (app (app (app (cval "Nat.casesOn") M) (enc app cval (k + 1))) z) f = app f (enc app cval k)
  fst : ∀ x y, sfst (app (app (cval "Prod.mk") x) y) = x
  snd : ∀ x y, ssnd (app (app (cval "Prod.mk") x) y) = y
  beta : r ≠ 0 → ∀ A F a, mem a A → app (lamR r A F) a = F a
  memEnc : ∀ t v, mem (encT app cval t v) (cval t.name)
  onlyEnc : ∀ t x, mem x (cval t.name) → ∃ v, x = encT app cval t v
  dec_enc : ∀ t v, dec t (encT app cval t v) = v

def Rel (σ : Env Γ) (ρ : Nat → V) : Prop := ∀ {t} (x : Var Γ t), ρ x.idx = encT app cval t (σ x)

theorem Rel.cons {σ : Env Γ} {ρ} (h : Rel app cval σ ρ) (v : s.den) :
    Rel app cval (σ.cons v) (push (encT app cval s v) ρ) := by
  intro t x; cases x with
  | zero => rfl
  | succ x => exact h x

theorem lam_den (dec : ∀ t : Ty, V → t.den) (H : Facts app lamR mem sfst ssnd r cval dec)
    {Γ s t} (b : Tm (s :: Γ) t) (σ : Env Γ) (ρ : Nat → V) (h : Rel app cval σ ρ)
    (ihb : ∀ (σ : Env (s :: Γ)) (ρ : Nat → V), Rel app cval σ ρ →
      Denotes app lamR mem sfst ssnd r cval ρ (tr b) (encT app cval t (eval b σ))) :
    Denotes app lamR mem sfst ssnd r cval ρ (.lam (.const s.name) (tr b))
      (lamR r (cval s.name) fun x => encT app cval t (eval b (σ.cons (dec s x)))) := by
  refine Denotes.lam .const (fun x hx => ?_) (fun _ _ _ => rfl)
  obtain ⟨w, rfl⟩ := H.onlyEnc s x hx
  simp only [H.dec_enc]
  exact ihb _ _ (h.cons app cval w)

theorem sound (hr : r ≠ 0) (dec : ∀ t : Ty, V → t.den) (H : Facts app lamR mem sfst ssnd r cval dec) :
    ∀ {Γ t} (e : Tm Γ t) (σ : Env Γ) (ρ : Nat → V), Rel app cval σ ρ →
      Denotes app lamR mem sfst ssnd r cval ρ (tr e) (encT app cval t (eval e σ)) := by
  intro Γ t e
  induction e with
  | var x => intro σ ρ h; exact (h x) ▸ .bvar
  | lit n => intro σ ρ _; exact lit_denotes app lamR mem sfst ssnd r cval ρ n
  | add a b iha ihb =>
    intro σ ρ h
    have := Denotes.app (Denotes.app (Denotes.const (n := "Nat.add")) (iha σ ρ h)) (ihb σ ρ h)
    simp only [encT] at this; rw [H.add] at this; exact this
  | let_ v b ihv ihb =>
    rename_i s t
    intro σ ρ h
    have key := Denotes.app (lam_den app lamR mem sfst ssnd r cval dec H b σ ρ h ihb) (ihv σ ρ h)
    rw [H.beta hr _ _ _ (H.memEnc s _)] at key
    simp only [H.dec_enc] at key
    exact key
  | pair a b iha ihb =>
    intro σ ρ h
    exact .app (.app .const (iha σ ρ h)) (ihb σ ρ h)
  | fst p ih =>
    intro σ ρ h
    have := Denotes.projFst (sfst := sfst) (ssnd := ssnd) (ih σ ρ h)
    simp only [eval, tr]
    generalize eval p σ = pr at this ⊢
    obtain ⟨x, y⟩ := pr
    simp only [encT, H.fst] at this; exact this
  | snd p ih =>
    intro σ ρ h
    have := Denotes.projSnd (sfst := sfst) (ssnd := ssnd) (ih σ ρ h)
    simp only [eval, tr]
    generalize eval p σ = pr at this ⊢
    obtain ⟨x, y⟩ := pr
    simp only [encT, H.snd] at this; exact this
  | natCase n z f ihn ihz ihf =>
    rename_i t
    intro σ ρ h
    have hM : Denotes app lamR mem sfst ssnd r cval ρ (.lam (.const "Nat") (.const t.name))
        (lamR r (cval "Nat") fun _ => cval t.name) := .lam .const (fun _ _ => .const) (fun _ _ _ => rfl)
    have hn := ihn σ ρ h
    have hz := ihz σ ρ h
    have hf := lam_den app lamR mem sfst ssnd r cval dec H f σ ρ h ihf
    simp only [tr, eval]
    generalize eval n σ = m at hn ⊢
    cases m with
    | zero =>
      have := Denotes.app (Denotes.app (Denotes.app (Denotes.app (Denotes.const (n := "Nat.casesOn")) hM) hn) hz) hf
      simp only [encT] at this; rw [H.cases0] at this; exact this
    | succ k =>
      have := Denotes.app (Denotes.app (Denotes.app (Denotes.app (Denotes.const (n := "Nat.casesOn")) hM) hn) hz) hf
      simp only [encT] at this; rw [H.casesS, H.beta hr _ _ (enc app cval k) (H.memEnc .nat k)] at this
      have e := H.dec_enc .nat k; simp only [encT] at e; simp only [e] at this; exact this

end MiniBind
#print axioms MiniBind.sound
