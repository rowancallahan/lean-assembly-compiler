/- HeadTyping (typing lemma, piece P3): typing of head constants from the con-leche-SHAPED `Model.mem`,
with real level assignments (`Level.substFn`), standalone, no imports.  dwijayuda/con-leche @ 3b37939.

Copied: `Level` (Kernel/Expr.lean:39), `eval`/`substFn` (Verify/Level.lean:26,34), `push` (Denotes.lean:118),
`Denotes` rules bvar 137 / sort 140 / const 144 / app 151 / pi 168, `Model.mem` (Denotes.lean:265).
Trimmed/assumed: `pi` is the graph regime only (regime ≠ 0 ASSUMED for the binders read here);
`SetTheory` = `mem`/`univ`/`app`/`piSet` with `app_mem` (con-leche `app_mem_piR`) as a class field;
`ConstantInfo` = name/levelParams/type; `Env.find?` = list lookup.

Proved (sorry-free):
* `head_has`      `.const n us` at φ denotes a member of ⟦stored type of n⟧ READ AT ψ = substFn φ ps us.
* `Denotes.shift` under `CvalParams` (proposed field, Universe.lean) a term whose levels have equal values
                  at φ and ψ denotes the same set at both — now including `∀`.  This moves argument terms
                  from the ambient φ to a head's ψ.
* `cons_typed`    worked case `List.cons.{0}` : needs NO `CvalParams` (its type only mentions `List.{u}`,
                  read at ψ, which is what `List.{0}` denotes at φ).
* `sel_typed`     worked case of a polymorphic head whose type mentions a LEVEL-FREE constant
                  (`sel.{u} : (α : Sort u) → Nat → α → α`, the shape of ite / Nat.casesOn / OfNat.ofNat):
                  here `CvalParams` is used, to identify `cval Nat ψ` with `cval Nat φ`. -/
namespace HeadTyping
open Lean (Name)
universe w

inductive Level | zero | succ (u : Level) | max (u v : Level) | imax (u v : Level) | param (n : Name)

namespace Level
def eval (φ : Name → Nat) : Level → Nat
  | .zero => 0
  | .succ l => eval φ l + 1
  | .max l r => Max.max (eval φ l) (eval φ r)
  | .imax l r => if eval φ r = 0 then 0 else Max.max (eval φ l) (eval φ r)
  | .param n => φ n

def substFn (φ : Name → Nat) : List Name → List Level → Name → Nat
  | k :: ks, v :: vs, n => if k = n then eval φ v else substFn φ ks vs n
  | _, _, n => φ n

theorem substFn_self (ψ : Name → Nat) (p : Name) : substFn ψ [p] [.param p] = ψ := by
  funext n; by_cases h : p = n <;> simp [substFn, eval, h]

theorem substFn_agree {φ ψ : Name → Nat} : ∀ (ps : List Name) (us : List Level),
    us.length = ps.length → (∀ u ∈ us, eval φ u = eval ψ u) →
    ∀ p ∈ ps, substFn φ ps us p = substFn ψ ps us p
  | [], _, _, _, _, hp => nomatch hp
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | k :: ks, u :: us, hl, h, p, hp => by
    by_cases hk : k = p
    · simp only [substFn, hk, ite_true]; exact h u (by simp)
    · simp only [substFn, hk, ite_false]
      refine substFn_agree ks us (by simpa using hl) (fun u hu => h u (by simp [hu])) p ?_
      cases hp with
      | head => exact absurd rfl hk
      | tail _ h => exact h
end Level

class SetTheory (V : Type w) where
  mem : V → V → Prop
  univ : Nat → V
  app : V → V → V
  piSet : V → (V → V) → V
  app_mem : ∀ {f A B x}, mem f (piSet A B) → mem x A → mem (app f x) (B x)
open SetTheory

inductive Expr
  | bvar (i : Nat)
  | sort (u : Level)
  | const (n : Name) (us : List Level)
  | app (f a : Expr)
  | forallE (ty body : Expr)

structure ConstantInfo where
  name : Name
  levelParams : List Name
  type : Expr

structure Env where consts : List ConstantInfo
def Env.find? (env : Env) (n : Name) : Option ConstantInfo := env.consts.find? (·.name == n)

theorem Env.find?_spec {env : Env} {n : Name} {ci : ConstantInfo} (h : env.find? n = some ci) :
    ci ∈ env.consts ∧ ci.name = n := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

variable {V : Type w} [SetTheory V]

def push (x : V) (ρ : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => ρ i

inductive Denotes (cval : Name → (Name → Nat) → V) (env : Env) (φ : Name → Nat) :
    (Nat → V) → Expr → V → Prop
  | bvar {ρ : Nat → V} {i : Nat} : Denotes cval env φ ρ (.bvar i) (ρ i)
  | sort {ρ : Nat → V} {u : Level} : Denotes cval env φ ρ (.sort u) (univ (Level.eval φ u))
  | const {ρ : Nat → V} {n : Name} {us : List Level} {ci : ConstantInfo}
      (hf : env.find? n = some ci) (hlen : us.length = ci.levelParams.length) :
      Denotes cval env φ ρ (.const n us) (cval n (Level.substFn φ ci.levelParams us))
  | app {ρ : Nat → V} {f a : Expr} {F X : V}
      (hf : Denotes cval env φ ρ f F) (ha : Denotes cval env φ ρ a X) :
      Denotes cval env φ ρ (.app f a) (app F X)
  | pi {ρ : Nat → V} {ty body : Expr} {A : V} {B : V → V}
      (hA : Denotes cval env φ ρ ty A)
      (hB : ∀ x, mem x A → Denotes cval env φ (push x ρ) body (B x)) :
      Denotes cval env φ ρ (.forallE ty body) (piSet A B)

structure Model (V : Type w) [SetTheory V] (env : Env) where
  cval : Name → (Name → Nat) → V
  mem : ∀ c ∈ env.consts, ∀ (φ : Name → Nat) (ρ : Nat → V),
    ∃ T, Denotes cval env φ ρ c.type T ∧ SetTheory.mem (cval c.name φ) T

/-- `c` is a member of what `ty` denotes at `φ`, `ρ` -/
def Has (cval : Name → (Name → Nat) → V) (env : Env) (φ : Name → Nat) (ρ : Nat → V) (c : V) (ty : Expr) :
    Prop := ∃ T, Denotes cval env φ ρ ty T ∧ mem c T

/-- **Head typing.**  A constant used at levels `us` under `φ` denotes a member of its stored type read at
the shifted assignment `substFn φ ps us` — no syntactic level instantiation is involved. -/
theorem head_has {env : Env} (m : Model V env) {φ : Name → Nat} {ρ : Nat → V} {n : Name}
    {us : List Level} {H : V} (h : Denotes m.cval env φ ρ (.const n us) H) :
    ∃ ci, env.find? n = some ci ∧
      Has m.cval env (Level.substFn φ ci.levelParams us) ρ H ci.type := by
  cases h with
  | const hf hlen =>
    obtain ⟨hmem, hname⟩ := Env.find?_spec hf
    obtain ⟨T, hT, hm⟩ := m.mem _ hmem (Level.substFn φ _ us) ρ
    rw [hname] at hm
    exact ⟨_, hf, T, hT, hm⟩

/-! ## binder-free type expressions, and application -/

def simple : Expr → Prop
  | .bvar _ | .sort _ | .const _ _ => True
  | .app f a => simple f ∧ simple a
  | _ => False

def den (cval : Name → (Name → Nat) → V) (env : Env) (φ : Name → Nat) (ρ : Nat → V) : Expr → V
  | .bvar i => ρ i
  | .sort u => univ (Level.eval φ u)
  | .const n us => match env.find? n with
    | some ci => cval n (Level.substFn φ ci.levelParams us)
    | none => univ 0
  | .app f a => app (den cval env φ ρ f) (den cval env φ ρ a)
  | _ => univ 0

variable {cval : Name → (Name → Nat) → V} {env : Env}

theorem D_den {φ : Name → Nat} {ρ : Nat → V} {e : Expr} {T : V} (h : Denotes cval env φ ρ e T) :
    simple e → T = den cval env φ ρ e := by
  induction h with
  | bvar => intro _; rfl
  | sort => intro _; rfl
  | const hf _ => intro _; simp only [den, hf]
  | app _ _ ihf iha => intro hs; rw [ihf hs.1, iha hs.2]; rfl
  | pi _ _ _ _ => intro hs; exact hs.elim

theorem Has.mem_den {φ : Name → Nat} {ρ : Nat → V} {c : V} {ty : Expr} (h : Has cval env φ ρ c ty)
    (hs : simple ty) : mem c (den cval env φ ρ ty) := by
  obtain ⟨T, hT, hm⟩ := h
  rw [← D_den hT hs]; exact hm

theorem Has.app' {φ : Name → Nat} {ρ : Nat → V} {f : V} {t b : Expr}
    (h : Has cval env φ ρ f (.forallE t b)) (hs : simple t) {x : V}
    (hx : mem x (den cval env φ ρ t)) : Has cval env φ (push x ρ) (app f x) b := by
  obtain ⟨T, hT, hm⟩ := h
  cases hT with
  | pi hA hB =>
    have hx' := hx
    rw [← D_den hA hs] at hx'
    exact ⟨_, hB x hx', app_mem hm hx'⟩

/-! ## the shift lemma, with `∀` -/

def CvalParams (cval : Name → (Name → Nat) → V) (env : Env) : Prop :=
  ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ ci.levelParams, ψ₁ p = ψ₂ p) → cval n ψ₁ = cval n ψ₂

def Agree (φ ψ : Name → Nat) : Expr → Prop
  | .bvar _ => True
  | .sort u => Level.eval φ u = Level.eval ψ u
  | .const _ us => ∀ u ∈ us, Level.eval φ u = Level.eval ψ u
  | .app f a => Agree φ ψ f ∧ Agree φ ψ a
  | .forallE t b => Agree φ ψ t ∧ Agree φ ψ b

theorem Denotes.shift {φ ψ : Name → Nat} (hext : CvalParams cval env) {ρ : Nat → V} {e : Expr} {v : V}
    (h : Denotes cval env φ ρ e v) : Agree φ ψ e → Denotes cval env ψ ρ e v := by
  induction h with
  | bvar => intro _; exact .bvar
  | sort => intro ha; simp only [Agree] at ha; rw [ha]; exact .sort
  | const hf hlen =>
    intro ha
    rw [hext _ _ hf _ _ (Level.substFn_agree _ _ hlen ha)]
    exact .const hf hlen
  | app _ _ ihf iha => intro ha; exact .app (ihf ha.1) (iha ha.2)
  | pi _ _ ihA ihB => intro ha; exact .pi (ihA ha.1) (fun x hx => ihB x hx ha.2)

/-! ## worked case 1: `List.cons.{0}` — no `CvalParams` needed -/

/-- `List.cons.{u} : (α : Type u) → α → List.{u} α → List.{u} α` -/
def consTy (p : Name) (List' : Name) : Expr :=
  .forallE (.sort (.succ (.param p))) (.forallE (.bvar 0)
    (.forallE (.app (.const List' [.param p]) (.bvar 1)) (.app (.const List' [.param p]) (.bvar 2))))

theorem cons_typed (m : Model V env) {φ : Name → Nat} {ρ : Nat → V} {p lN cN : Name}
    {cl cc : ConstantInfo}
    (hlist : env.find? lN = some cl) (hlps : cl.levelParams = [p])
    (hcons : env.find? cN = some cc) (hcps : cc.levelParams = [p]) (hcty : cc.type = consTy p lN)
    {H A a l : V} (hH : Denotes m.cval env φ ρ (.const cN [.zero]) H)
    (hA : mem A (univ 1)) (ha : mem a A)
    (hl : mem l (app (m.cval lN (Level.substFn φ [p] [.zero])) A)) :
    mem (app (app (app H A) a) l) (app (m.cval lN (Level.substFn φ [p] [.zero])) A) := by
  obtain ⟨ci, hf, hh⟩ := head_has m hH
  rw [hcons] at hf; cases hf
  rw [hcps, hcty] at hh
  have e1 : Level.eval (Level.substFn φ [p] [.zero]) (.succ (.param p)) = 1 := by
    simp [Level.eval, Level.substFn]
  have h1 := hh.app' (x := A) trivial (by simpa [den, e1] using hA)
  have h2 := h1.app' (x := a) trivial (by simpa [den, push] using ha)
  have h3 := h2.app' (x := l) ⟨trivial, trivial⟩
    (by simpa [den, push, hlist, hlps, Level.substFn_self] using hl)
  have h4 := h3.mem_den ⟨trivial, trivial⟩
  simpa [den, push, hlist, hlps, Level.substFn_self] using h4

/-! ## worked case 2: a polymorphic head whose type mentions a level-free constant — `CvalParams` used -/

/-- `sel.{u} : (α : Sort u) → Nat → α → α` -/
def selTy (p : Name) (Nat' : Name) : Expr :=
  .forallE (.sort (.param p)) (.forallE (.const Nat' []) (.forallE (.bvar 1) (.bvar 2)))

theorem sel_typed (m : Model V env) (hext : CvalParams m.cval env) {φ : Name → Nat} {ρ : Nat → V}
    {p nN sN : Name} {cn cs : ConstantInfo}
    (hnat : env.find? nN = some cn) (hnps : cn.levelParams = [])
    (hsel : env.find? sN = some cs) (hsps : cs.levelParams = [p]) (hsty : cs.type = selTy p nN)
    {H A k t : V} (hH : Denotes m.cval env φ ρ (.const sN [.succ .zero]) H)
    (hA : mem A (univ 1)) (hk : mem k (m.cval nN φ)) (ht : mem t A) :
    mem (app (app (app H A) k) t) A := by
  obtain ⟨ci, hf, hh⟩ := head_has m hH
  rw [hsel] at hf; cases hf
  rw [hsps, hsty] at hh
  have e1 : Level.eval (Level.substFn φ [p] [.succ .zero]) (.param p) = 1 := by
    simp [Level.eval, Level.substFn]
  -- the level-free `Nat` is read at ψ inside the head's type, but the scrutinee was typed at φ:
  have eN : m.cval nN (Level.substFn (Level.substFn φ [p] [.succ .zero]) [] []) = m.cval nN φ :=
    hext nN cn hnat _ _ (by rw [hnps]; intro q hq; exact nomatch hq)
  have h1 := hh.app' (x := A) trivial (by simpa [den, e1] using hA)
  have h2 := h1.app' (x := k) trivial (by simpa [den, hnat, hnps, eN] using hk)
  have h3 := h2.app' (x := t) trivial (by simpa [den, push] using ht)
  have h4 := h3.mem_den trivial
  simpa [den, push] using h4

end HeadTyping

#print axioms HeadTyping.head_has
#print axioms HeadTyping.Denotes.shift
#print axioms HeadTyping.cons_typed
#print axioms HeadTyping.sel_typed
