/- Bridge.MiniModel: the transfer kit (task 2) and the typing method (task 3), PROVED against a standalone trimmed
copy of con-leche's `Denotes`/`Model` (con-leche is not built tonight, owner decision).  Transfer.lean is the
same development written against the real con-leche API (draft, never compiled); this file is the compiled twin.

What is copied, and how it is trimmed (dwijayuda/con-leche @ 3b37939):
* `E`: ConLeche/Kernel/Expr.lean:328 (`bvar sort const app lam forallE lit`); levels are concrete `Nat`s (nano emits
  only concrete levels), `BinderMeta` is reduced to the `pw : Bool` the checker would compute (regime 0 iff `pw`).
* `D`: ConLeche/Denotes.lean:134, rules bvar 137, sort 140, const 144, app 151, lam 157, pi 165, natLit 184.
  `const` denotes `cval n ls` (con-leche: `cval n (Level.substFn φ ps us)`).  DIVERGENCE: with concrete levels
  this hides con-leche's φ-dependence of level-free constants inside level-polymorphic heads (see notes §11).
* `Model`: ConLeche/Denotes.lean:270 (`mem`, `eq_equality`; `false_empty` unused).  A stored constant is a name and
  its type as a function of the level arguments.
* the set operations are abstract (`SetOps`); the laws used are HYPOTHESES (`SetLaws`), each one a con-leche
  theorem, cited at its field.

STATUS: proved, no sorry. -/

namespace Bridge.Mini

/-! ## trimmed terms and set interface -/

inductive E | bvar (i : Nat) | sort (u : Nat) | const (n : String) (ls : List Nat) | app (f a : E)
  | lam (t b : E) (pw : Bool) | forallE (t b : E) (pw : Bool) | lit (k : Nat)

def natLitToConstructor : Nat → E    -- ConLeche/Kernel/CoreDefs.lean:123
  | 0 => .const "Nat.zero" []
  | k + 1 => .app (.const "Nat.succ" []) (.lit k)

structure SetOps (V : Type) where
  mem : V → V → Prop
  app : V → V → V
  pt : V
  univ : Nat → V
  lamR : Nat → V → (V → V) → V
  piR : Nat → V → (V → V) → V
  eqv : V → V → V

/-- the con-leche lemmas used, as hypotheses (`univZero = univ 0`: SetTheory/Derive/Univ.lean:37) -/
structure SetLaws {V : Type} (O : SetOps V) : Prop where
  /-- SetModel/Ops.lean:206 -/
  app_lamR_pos : ∀ {v A a} {F : V → V}, v ≠ 0 → O.mem a A → O.app (O.lamR v A F) a = F a
  /-- SetModel/Ops.lean:72 -/
  lamR_zero : ∀ {A} {F : V → V}, O.lamR 0 A F = O.pt
  /-- SetTheory/Derive/Graphs.lean:56 -/
  app_pt : ∀ a, O.app O.pt a = O.pt
  /-- SetModel/Ops.lean:174 -/
  app_mem_piR : ∀ {v A f a} {B : V → V}, O.mem f (O.piR v A B) → O.mem a A →
    (v = 0 → ∀ x, O.mem x A → O.mem (B x) (O.univ 0)) → O.mem (O.app f a) (B a)
  /-- SetTheory/Derive/Pt.lean:168 -/
  eq_of_mem_eqv : ∀ {a x y}, O.mem a (O.eqv x y) → x = y
  /-- SetTheory/Derive/Univ.lean:50 -/
  univ_mem_univ : ∀ n, O.mem (O.univ n) (O.univ (n + 1))
  /-- SetModel/Ops.lean:88 -/
  lamR_congr : ∀ {v A} {F F' : V → V}, (∀ x, O.mem x A → F x = F' x) → O.lamR v A F = O.lamR v A F'
  /-- SetModel/Ops.lean:134 -/
  lamR_mem : ∀ {v A} {F B : V → V}, (∀ x, O.mem x A → O.mem (F x) (B x)) → O.mem (O.lamR v A F) (O.piR v A B)
  /-- SetModel/Ops.lean:79 -/
  piR_congr : ∀ {v A} {B B' : V → V}, (∀ x, O.mem x A → B x = B' x) → O.piR v A B = O.piR v A B'

def regime (pw : Bool) : Nat := if pw then 0 else 1

def push {V : Type} (x : V) (ρ : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => ρ i

section
variable {V : Type} (O : SetOps V) (cval : String → List Nat → V)

inductive D : (Nat → V) → E → V → Prop
  | bvar {ρ i} : D ρ (.bvar i) (ρ i)
  | sort {ρ u} : D ρ (.sort u) (O.univ u)
  | const {ρ n ls} : D ρ (.const n ls) (cval n ls)
  | app {ρ f a F X} : D ρ f F → D ρ a X → D ρ (.app f a) (O.app F X)
  | lam {ρ t b pw A} {F : V → V} : D ρ t A → (∀ x, O.mem x A → D (push x ρ) b (F x)) →
      (regime pw = 0 → ∀ x, O.mem x A → F x = O.pt) → D ρ (.lam t b pw) (O.lamR (regime pw) A F)
  | pi {ρ t b pw A} {B : V → V} : D ρ t A → (∀ x, O.mem x A → D (push x ρ) b (B x)) →
      (regime pw = 0 → ∀ x, O.mem x A → O.mem (B x) (O.univ 0)) → D ρ (.forallE t b pw) (O.piR (regime pw) A B)
  | natLit {ρ k X} : D ρ (natLitToConstructor k) X → D ρ (.lit k) X
end

variable {V : Type} {O : SetOps V} (L : SetLaws O)
include L

/-- ConLeche/Denotes.lean:197 (`Denotes_functional`), re-proved for the trimmed relation -/
theorem D_functional {cval : String → List Nat → V} {ρ : Nat → V} {e : E} {v w : V}
    (hv : D O cval ρ e v) (hw : D O cval ρ e w) : v = w := by
  induction hv generalizing w with
  | bvar => cases hw; rfl
  | sort => cases hw; rfl
  | const => cases hw; rfl
  | app _ _ ihf iha => cases hw with | app hf ha => rw [ihf hf, iha ha]
  | lam _ _ _ ihA ihF =>
    cases hw with
    | lam hA hF _ => obtain rfl := ihA hA; exact L.lamR_congr fun x hx => ihF x hx (hF x hx)
  | pi _ _ _ ihA ihB =>
    cases hw with
    | pi hA hB _ => obtain rfl := ihA hA; exact L.piR_congr fun x hx => ihB x hx (hB x hx)
  | natLit _ ih => cases hw with | natLit h => exact ih h

/-! ## the model -/

/-- a stored constant: name and type (as a function of the level arguments) -/
abbrev Const := String × (List Nat → E)

/-- ConLeche/Denotes.lean:270, trimmed (`false_empty` unused here) -/
structure Model (O : SetOps V) (env : List Const) where
  cval : String → List Nat → V
  mem : ∀ c ∈ env, ∀ ls ρ, ∃ T, D O cval ρ (c.2 ls) T ∧ O.mem (cval c.1 ls) T
  eq_equality : ∀ u ρ Ev A a b, D O cval ρ (.const "Eq" [u]) Ev → O.mem A (O.univ u) → O.mem a A → O.mem b A →
    O.app (O.app (O.app Ev A) a) b = O.eqv a b

omit L in
theorem app_inv {cval : String → List Nat → V} {ρ : Nat → V} {f a : E} {R : V}
    (h : D O cval ρ (.app f a) R) : ∃ F X, D O cval ρ f F ∧ D O cval ρ a X ∧ R = O.app F X := by
  cases h with | app hf ha => exact ⟨_, _, hf, ha, rfl⟩

omit L in
theorem pi_inv {cval : String → List Nat → V} {ρ : Nat → V} {t b : E} {pw : Bool} {P : V}
    (h : D O cval ρ (.forallE t b pw) P) :
    ∃ A B, D O cval ρ t A ∧ (∀ x, O.mem x A → D O cval (push x ρ) b (B x)) ∧
      (regime pw = 0 → ∀ x, O.mem x A → O.mem (B x) (O.univ 0)) ∧ P = O.piR (regime pw) A B := by
  cases h with | pi hA hB hP => exact ⟨_, _, hA, hB, hP, rfl⟩

omit L in
theorem lam_inv {cval : String → List Nat → V} {ρ : Nat → V} {t b : E} {pw : Bool} {P : V}
    (h : D O cval ρ (.lam t b pw) P) :
    ∃ A F, D O cval ρ t A ∧ (∀ x, O.mem x A → D O cval (push x ρ) b (F x)) ∧
      (regime pw = 0 → ∀ x, O.mem x A → F x = O.pt) ∧ P = O.lamR (regime pw) A F := by
  cases h with | lam hA hF hP => exact ⟨_, _, hA, hF, hP, rfl⟩

/-! ## typing steps -/

/-- **application typing**, both regimes -/
theorem mem_app {cval : String → List Nat → V} {ρ : Nat → V} {t b : E} {pw : Bool} {P F A X : V}
    (hP : D O cval ρ (.forallE t b pw) P) (hF : O.mem F P) (hA : D O cval ρ t A) (hX : O.mem X A) :
    ∃ Bx, D O cval (push X ρ) b Bx ∧ O.mem (O.app F X) Bx := by
  obtain ⟨A', B, hA', hB, h0, rfl⟩ := pi_inv hP
  obtain rfl := D_functional L hA hA'
  exact ⟨B X, hB X hX, L.app_mem_piR hF hX h0⟩

/-- same, with the fibre's denotation given -/
theorem mem_app' {cval : String → List Nat → V} {ρ : Nat → V} {t b : E} {pw : Bool} {P F A X Bx : V}
    (hP : D O cval ρ (.forallE t b pw) P) (hF : O.mem F P) (hA : D O cval ρ t A) (hX : O.mem X A)
    (hB : D O cval (push X ρ) b Bx) : O.mem (O.app F X) Bx := by
  obtain ⟨Bx', hB', hm⟩ := mem_app L hP hF hA hX
  rwa [D_functional L hB hB']

/-- **beta, both regimes** (a `let` emitted as a redex) -/
theorem beta {cval : String → List Nat → V} {ρ : Nat → V} {t b v : E} {pw : Bool} {A X R : V}
    (hR : D O cval ρ (.app (.lam t b pw) v) R) (hA : D O cval ρ t A) (hv : D O cval ρ v X) (hX : O.mem X A) :
    D O cval (push X ρ) b R := by
  obtain ⟨Lv, X', hL, hv', rfl⟩ := app_inv hR
  obtain rfl := D_functional L hv hv'
  obtain ⟨A', F, hA', hF, hP, rfl⟩ := lam_inv hL
  obtain rfl := D_functional L hA hA'
  by_cases hr : regime pw = 0
  · rw [hr, L.lamR_zero, L.app_pt, ← hP hr X hX]; exact hF X hX
  · rw [L.app_lamR_pos hr hX]; exact hF X hX

/-! ## transfer, n binders -/

variable {env : List Const}

def Inhab (M : Model O env) (ρ : Nat → V) (e : E) : Prop := ∃ P, D O M.cval ρ e P ∧ ∃ y, O.mem y P

omit L in
theorem inhab_const (M : Model O env) {c : Const} (hc : c ∈ env) (ls : List Nat) (ρ : Nat → V) :
    Inhab M ρ (c.2 ls) := by
  obtain ⟨T, hT, hm⟩ := M.mem c hc ls ρ; exact ⟨T, hT, _, hm⟩

theorem Inhab.pi {M : Model O env} {ρ : Nat → V} {t b : E} {pw : Bool} {A x : V}
    (h : Inhab M ρ (.forallE t b pw)) (hA : D O M.cval ρ t A) (hx : O.mem x A) : Inhab M (push x ρ) b := by
  obtain ⟨P, hP, y, hy⟩ := h
  obtain ⟨Bx, hB, hm⟩ := mem_app L hP hy hA hx
  exact ⟨Bx, hB, _, hm⟩

def eqE (u : Nat) (S a b : E) : E := .app (.app (.app (.const "Eq" [u]) S) a) b

theorem Inhab.eq {M : Model O env} {ρ : Nat → V} {u : Nat} {S a b : E} {Sv av bv : V}
    (h : Inhab M ρ (eqE u S a b)) (hS : D O M.cval ρ S Sv) (ha : D O M.cval ρ a av) (hb : D O M.cval ρ b bv)
    (hSu : O.mem Sv (O.univ u)) (hav : O.mem av Sv) (hbv : O.mem bv Sv) : av = bv := by
  obtain ⟨P, hP, y, hy⟩ := h
  obtain ⟨F2, bv', h3, hb', rfl⟩ := app_inv hP
  obtain ⟨F1, av', h2, ha', rfl⟩ := app_inv h3
  obtain ⟨Ev, Sv', hE, hS', rfl⟩ := app_inv h2
  obtain rfl := D_functional L hS hS'
  obtain rfl := D_functional L ha ha'
  obtain rfl := D_functional L hb hb'
  rw [M.eq_equality u ρ _ _ _ _ hE hSu hav hbv] at hy
  exact L.eq_of_mem_eqv hy

def piN : List (E × Bool) → E → E
  | [], b => b
  | (t, pw) :: ts, b => .forallE t (piN ts b) pw

inductive Tele (M : Model O env) : (Nat → V) → List (E × Bool) → (Nat → V) → Prop
  | nil {ρ} : Tele M ρ [] ρ
  | cons {ρ ρ' t pw ts A x} : D O M.cval ρ t A → O.mem x A → Tele M (push x ρ) ts ρ' → Tele M ρ ((t, pw) :: ts) ρ'

theorem Inhab.piN {M : Model O env} : ∀ {ρ ρ' : Nat → V} {ts : List (E × Bool)} {b : E},
    Inhab M ρ (Mini.piN ts b) → Tele M ρ ts ρ' → Inhab M ρ' b
  | _, _, [], _, h, .nil => h
  | _, _, (_, _) :: _, _, h, .cons hA hx ht => Inhab.piN (Inhab.pi L h hA hx) ht

/-- **Transfer, n binders.**  A stored theorem `∀ (x₁ : T₁) … (xₙ : Tₙ), @Eq.{u} S a b`: at every telescope
instance, `⟦a⟧ = ⟦b⟧`, given the three membership facts `eq_equality` asks for. -/
theorem transferN (M : Model O env) {c : Const} (hc : c ∈ env) {ls : List Nat} {ts : List (E × Bool)}
    {u : Nat} {S a b : E} (hty : c.2 ls = piN ts (eqE u S a b)) (ρ : Nat → V) {ρ' : Nat → V}
    (ht : Tele M ρ ts ρ') {Sv av bv : V} (hS : D O M.cval ρ' S Sv) (ha : D O M.cval ρ' a av)
    (hb : D O M.cval ρ' b bv) (hSu : O.mem Sv (O.univ u)) (hav : O.mem av Sv) (hbv : O.mem bv Sv) : av = bv := by
  have h0 := inhab_const M hc ls ρ
  rw [hty] at h0
  exact (h0.piN L ht).eq L hS ha hb hSu hav hbv

/-! ## worked example: the `litU` fact (EvBridge `FactsW.litU`) from ONE stored theorem + typing

`br_lit : ∀ n : Nat, @OfNat.ofNat.{0} UInt64 n (UInt64.instOfNat n) = UInt64.ofNat n` (DENOTES_SPIKE §5 H1,
proved by `rfl`, accepted by con-leche).  The stored types below are Lean's, in the trimmed syntax; `pw` flags are
the regime the checker computes (all data binders: `false`). -/

def tNat : E := .const "Nat" []
def tU : E := .const "UInt64" []

/-- the constants the example reads, with their Lean types -/
structure LitEnv (env : List Const) : Prop where
  nat : ("Nat", fun _ => .sort 1) ∈ env
  zero : ("Nat.zero", fun _ => tNat) ∈ env
  succ : ("Nat.succ", fun _ => .forallE tNat tNat false) ∈ env
  u64 : ("UInt64", fun _ => .sort 1) ∈ env
  ofNat : ("UInt64.ofNat", fun _ => .forallE tNat tU false) ∈ env
  /-- `OfNat.{u} : Type u → Nat → Type u` -/
  cls : ("OfNat", fun ls => .forallE (.sort (ls.headD 0 + 1)) (.forallE tNat (.sort (ls.headD 0 + 1)) false) false) ∈ env
  /-- `OfNat.ofNat.{u} : {α : Type u} → (n : Nat) → [OfNat α n] → α` -/
  ofNatH : ("OfNat.ofNat", fun ls => .forallE (.sort (ls.headD 0 + 1)) (.forallE tNat
      (.forallE (.app (.app (.const "OfNat" [ls.headD 0]) (.bvar 1)) (.bvar 0)) (.bvar 2) false) false) false) ∈ env
  /-- `UInt64.instOfNat : (n : Nat) → OfNat UInt64 n` (nano emits it applied to the literal) -/
  inst : ("UInt64.instOfNat", fun _ => .forallE tNat (.app (.app (.const "OfNat" [0]) tU) (.bvar 0)) false) ∈ env
  brLit : ("br_lit", fun _ => piN [(tNat, false)] (eqE 1 tU
      (.app (.app (.app (.const "OfNat.ofNat" [0]) tU) (.bvar 0)) (.app (.const "UInt64.instOfNat" []) (.bvar 0)))
      (.app (.const "UInt64.ofNat" []) (.bvar 0)))) ∈ env

/-- the canonical numeral: what `succ^k zero` denotes -/
def natEnc (M : Model O env) : Nat → V
  | 0 => M.cval "Nat.zero" []
  | k + 1 => O.app (M.cval "Nat.succ" []) (natEnc M k)

omit L in
theorem lit_denotes (M : Model O env) (ρ : Nat → V) : ∀ k, D O M.cval ρ (.lit k) (natEnc M k)
  | 0 => .natLit .const
  | k + 1 => .natLit (.app .const (lit_denotes M ρ k))

/-- `mem` of a constant whose type is a closed constant `T`: the constant is in `⟦T⟧` -/
theorem mem_closed (M : Model O env) {n : String} {ty : List Nat → E} (hc : (n, ty) ∈ env) {ls : List Nat}
    {ρ : Nat → V} {Tv : V} (hT : D O M.cval ρ (ty ls) Tv) : O.mem (M.cval n ls) Tv := by
  obtain ⟨T, hT', hm⟩ := M.mem _ hc ls ρ
  rwa [D_functional L hT hT']

theorem natEnc_mem (M : Model O env) (H : LitEnv env) (ρ : Nat → V) :
    ∀ k, O.mem (natEnc M k) (M.cval "Nat" []) := by
  intro k
  induction k with
  | zero => exact mem_closed L M H.zero (ρ := ρ) .const
  | succ k ih =>
    have hs := mem_closed L M H.succ (ρ := ρ) (ls := [])
      (.pi .const (fun _ _ => .const) (fun h => by simp [regime] at h))
    exact mem_app' L (ρ := ρ) (.pi .const (fun _ _ => .const) (fun h => by simp [regime] at h)) hs .const ih .const

/-- **`FactsW.litU`, derived.**  The emitted UInt64 literal denotes the canonical encoding
`⟦UInt64.ofNat⟧ (natEnc k)`.  Uses: `br_lit` (transfer, one binder) and typing through the stored types of
`OfNat.ofNat`, `UInt64.instOfNat`, `UInt64.ofNat`, `Nat.zero/succ`. -/
theorem litU_fact (M : Model O env) (H : LitEnv env) (ρ : Nat → V) (k : Nat) {R : V}
    (hR : D O M.cval ρ (.app (.app (.app (.const "OfNat.ofNat" [0]) tU) (.lit k))
      (.app (.const "UInt64.instOfNat" []) (.lit k))) R) :
    R = O.app (M.cval "UInt64.ofNat" []) (natEnc M k) := by
  have dNat : ∀ ρ', D O M.cval ρ' tNat (M.cval "Nat" []) := fun _ => .const
  have dU : ∀ ρ', D O M.cval ρ' tU (M.cval "UInt64" []) := fun _ => .const
  have hx := natEnc_mem L M H ρ k
  obtain ⟨x, hxe⟩ : ∃ x, x = natEnc M k := ⟨_, rfl⟩
  rw [← hxe] at hx ⊢
  -- the transfer, at `push x ρ`
  have hpi : ∀ _ρ' : Nat → V, regime false = 0 → ∀ y, O.mem y (M.cval "Nat" []) →
      O.mem (M.cval "UInt64" []) (O.univ 0) := fun _ h => by simp [regime] at h
  -- typing of the right side: `UInt64.ofNat x ∈ ⟦UInt64⟧`
  have hOf := mem_closed L M H.ofNat (ls := []) (ρ := push x ρ) (.pi (dNat _) (fun _ _ => dU _) (hpi ρ))
  have hb : O.mem (O.app (M.cval "UInt64.ofNat" []) x) (M.cval "UInt64" []) :=
    mem_app' L (ρ := push x ρ) (.pi (dNat _) (fun _ _ => dU _) (hpi ρ)) hOf (dNat _) hx (dU _)
  -- typing of the left side, through `OfNat.ofNat`'s type at level 0
  have hUu : O.mem (M.cval "UInt64" []) (O.univ 1) := mem_closed L M H.u64 (ls := []) (ρ := ρ) .sort
  have hInst := mem_closed L M H.inst (ls := []) (ρ := push x ρ)
    (.pi (dNat _) (fun y _ => .app (.app .const (dU _)) .bvar) (fun h => by simp [regime] at h))
  have hIx : O.mem (O.app (M.cval "UInt64.instOfNat" []) x)
      (O.app (O.app (M.cval "OfNat" [0]) (M.cval "UInt64" [])) x) :=
    mem_app' L (.pi (dNat _) (fun y _ => .app (.app .const (dU _)) .bvar) (fun h => by simp [regime] at h))
      hInst (dNat _) hx (.app (.app .const (dU _)) .bvar)
  -- `OfNat.ofNat`'s type, denoted at `push x ρ` (its body only reads its own binders)
  have dTy : D O M.cval (push x ρ) (.forallE (.sort 1) (.forallE tNat
      (.forallE (.app (.app (.const "OfNat" [0]) (.bvar 1)) (.bvar 0)) (.bvar 2) false) false) false)
      (O.piR 1 (O.univ 1) fun α => O.piR 1 (M.cval "Nat" []) fun n =>
        O.piR 1 (O.app (O.app (M.cval "OfNat" [0]) α) n) fun _ => α) := by
    refine .pi .sort (fun α _ => .pi (dNat _) (fun n _ => .pi (.app (.app .const .bvar) .bvar) (fun _ _ => .bvar) ?_) ?_) ?_
    all_goals intro h; simp [regime] at h
  have hH := mem_closed L M H.ofNatH (ls := [0]) (ρ := push x ρ) dTy
  have h1 := L.app_mem_piR hH hUu (fun h => by simp at h)
  have h2 := L.app_mem_piR h1 hx (fun h => by simp at h)
  have h3 := L.app_mem_piR h2 hIx (fun h => by simp at h)
  -- the transfer gives `⟦lhs⟧ = ⟦rhs⟧` at `push x ρ`
  have key := transferN L M H.brLit (ls := []) (hty := rfl) ρ (.cons (dNat ρ) hx .nil)
    (dU _) (.app (.app (.app .const (dU _)) .bvar) (.app .const .bvar)) (.app .const .bvar) hUu h3 hb
  -- the emitted term at `ρ` (literal `k` for the binder) denotes the same set
  obtain ⟨F, I, hF, hI, rfl⟩ := app_inv hR
  obtain ⟨G, n1, hG, hn1, rfl⟩ := app_inv hF
  obtain ⟨Hd, Uv, hHd, hUv, rfl⟩ := app_inv hG
  obtain ⟨J, n2, hJ, hn2, rfl⟩ := app_inv hI
  cases hHd; cases hUv; cases hJ
  rw [D_functional L hn1 (lit_denotes M ρ k), D_functional L hn2 (lit_denotes M ρ k), ← hxe]
  exact key

end Bridge.Mini
