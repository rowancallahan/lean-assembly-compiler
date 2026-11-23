/- MiniTyping: the TYPING LEMMA of DENOTES_SPIKE.md §3/§7, standalone (no imports), against a trimmed copy
of con-leche's `Denotes` (dwijayuda/con-leche @ 3b37939), in the style of MiniDenotes.lean / EvSkeleton.lean.

What is proved (sorry-free):
* `Has.app`      a head whose type is a `∀` applied to an argument in the domain inhabits the body's type
                 ("heads applied to well-typed args stay well-typed"; this is `Model.mem` + `app_mem_piR`).
* `enc_mem`      for every value `v` of the slice (Nano/Expr/Eval.lean:9: UInt64, Nat, List UInt64,
                 List UInt8, pairs), `enc v ∈ ⟦ty v⟧` and `⟦ty v⟧ ∈ univ 1`.
* `tiny_typed`   in the tiny language of MiniDenotes (lit / add / iteEq), WHATEVER `tr e` denotes is in ⟦Nat⟧.

Trimmed / assumed (each is a real gap to the con-leche statement):
* `D` = `Denotes` (ConLeche/Denotes.lean:134) with rules bvar 137, sort 140, const 144, app 151, pi 168,
  natLit 184.  `pi` is the GRAPH regime only (`piS`); the regime-0 reading is dropped, i.e. it is ASSUMED that
  every data `∀` in a stored constructor type has `regime ≠ 0` (spike §3: decidable on the stored term).
* levels: `cval : String → List Nat → S` takes the instantiation directly and stored types are written already
  instantiated.  In con-leche the constant is read at `Level.substFn φ ps us`; identifying the two for
  level-free constants used under `List.{0}` AND `ite.{1}` needs `cval_params` (Universe.lean): the single
  assignment φ₁ does NOT cover the slice, because `u` is needed at 0 (List, Prod, OfNat, HAdd) and at 1 (ite,
  Nat.casesOn).
* the set theory: `app_mem` is con-leche's `app_mem_piR` at a nonzero regime, taken as a hypothesis.
* `Stored`: one field per constant = what `Model.mem` gives for that constant (its type denotes, and the
  constant is a member).  The types are hand-written here, NOT read from an exported env. -/
namespace MiniTyping

inductive E | bvar (i : Nat) | sort (k : Nat) | const (n : String) (ls : List Nat) | app (f a : E)
  | forallE (t b : E) | lit (k : Nat)

def natLitToConstructor : Nat → E    -- ConLeche/Kernel/CoreDefs.lean:123
  | 0 => .const "Nat.zero" []
  | k + 1 => .app (.const "Nat.succ" []) (.lit k)

def push {S : Type} (x : S) (ρ : Nat → S) : Nat → S    -- ConLeche/Denotes.lean:118
  | 0 => x
  | i + 1 => ρ i

section
variable {S : Type} (sapp : S → S → S) (mem : S → S → Prop) (piS : S → (S → S) → S) (univ : Nat → S)
  (cval : String → List Nat → S)

inductive D : (Nat → S) → E → S → Prop
  | bvar {ρ i} : D ρ (.bvar i) (ρ i)
  | sort {ρ k} : D ρ (.sort k) (univ k)
  | const {ρ n ls} : D ρ (.const n ls) (cval n ls)
  | app {ρ f a F X} : D ρ f F → D ρ a X → D ρ (.app f a) (sapp F X)
  | pi {ρ t b A B} : D ρ t A → (∀ x, mem x A → D (push x ρ) b (B x)) → D ρ (.forallE t b) (piS A B)
  | natLit {ρ k X} : D ρ (natLitToConstructor k) X → D ρ (.lit k) X

/-- `c` is a member of what the type expression `ty` denotes at `ρ` (the shape of `Model.mem`). -/
def Has (ρ : Nat → S) (c : S) (ty : E) : Prop := ∃ T, D sapp mem piS univ cval ρ ty T ∧ mem c T

/-- binder-free type expressions and their (functional) reading -/
def simple : E → Prop
  | .bvar _ | .sort _ | .const _ _ => True
  | .app f a => simple f ∧ simple a
  | _ => False

def den (ρ : Nat → S) : E → S
  | .bvar i => ρ i
  | .sort k => univ k
  | .const n ls => cval n ls
  | .app f a => sapp (den ρ f) (den ρ a)
  | _ => univ 0
end

variable {S : Type} {sapp : S → S → S} {mem : S → S → Prop} {piS : S → (S → S) → S} {univ : Nat → S}
  {cval : String → List Nat → S}

theorem D_den {ρ : Nat → S} {e : E} {T : S} (h : D sapp mem piS univ cval ρ e T) :
    simple e → T = den sapp univ cval ρ e := by
  induction h with
  | bvar => intro _; rfl
  | sort => intro _; rfl
  | const => intro _; rfl
  | app _ _ ihf iha => intro hs; rw [ihf hs.1, iha hs.2]; rfl
  | pi _ _ _ _ => intro hs; exact hs.elim
  | natLit _ _ => intro hs; exact hs.elim

theorem Has.mem_den {ρ : Nat → S} {c : S} {ty : E} (h : Has sapp mem piS univ cval ρ c ty)
    (hs : simple ty) : mem c (den sapp univ cval ρ ty) := by
  obtain ⟨T, hT, hm⟩ := h
  rw [← D_den hT hs]; exact hm

/-- **Heads applied to well-typed arguments stay well-typed.** -/
theorem Has.app (app_mem : ∀ {f A B x}, mem f (piS A B) → mem x A → mem (sapp f x) (B x))
    {ρ : Nat → S} {f : S} {t b : E} (h : Has sapp mem piS univ cval ρ f (.forallE t b)) :
    ∃ A, D sapp mem piS univ cval ρ t A ∧
      ∀ x, mem x A → Has sapp mem piS univ cval (push x ρ) (sapp f x) b := by
  obtain ⟨T, hT, hm⟩ := h
  cases hT with
  | pi hA hB => exact ⟨_, hA, fun x hx => ⟨_, hB x hx, app_mem hm hx⟩⟩

/-- the same with a binder-free domain: the domain is `den t` -/
theorem Has.app' (app_mem : ∀ {f A B x}, mem f (piS A B) → mem x A → mem (sapp f x) (B x))
    {ρ : Nat → S} {f : S} {t b : E} (h : Has sapp mem piS univ cval ρ f (.forallE t b)) (hs : simple t)
    {x : S} (hx : mem x (den sapp univ cval ρ t)) :
    Has sapp mem piS univ cval (push x ρ) (sapp f x) b := by
  obtain ⟨A, hA, h⟩ := h.app app_mem
  exact h x (by rw [D_den hA hs]; exact hx)

/-! ## the stored constants of the slice (what `Model.mem` gives), types written instantiated -/

abbrev c (n : String) (ls : List Nat := []) : E := .const n ls
abbrev arr (t b : E) : E := .forallE t b   -- non-dependent use: `b` closed
abbrev lst (a : E) : E := .app (c "List" [0]) a

structure Stored (sapp : S → S → S) (mem : S → S → Prop) (piS : S → (S → S) → S) (univ : Nat → S)
    (cval : String → List Nat → S) : Prop where
  app_mem : ∀ {f A B x}, mem f (piS A B) → mem x A → mem (sapp f x) (B x)
  nat : ∀ ρ, Has sapp mem piS univ cval ρ (cval "Nat" []) (.sort 1)
  u64 : ∀ ρ, Has sapp mem piS univ cval ρ (cval "UInt64" []) (.sort 1)
  u8 : ∀ ρ, Has sapp mem piS univ cval ρ (cval "UInt8" []) (.sort 1)
  zero : ∀ ρ, Has sapp mem piS univ cval ρ (cval "Nat.zero" []) (c "Nat")
  succ : ∀ ρ, Has sapp mem piS univ cval ρ (cval "Nat.succ" []) (arr (c "Nat") (c "Nat"))
  u64ofNat : ∀ ρ, Has sapp mem piS univ cval ρ (cval "UInt64.ofNat" []) (arr (c "Nat") (c "UInt64"))
  u8ofNat : ∀ ρ, Has sapp mem piS univ cval ρ (cval "UInt8.ofNat" []) (arr (c "Nat") (c "UInt8"))
  list : ∀ ρ, Has sapp mem piS univ cval ρ (cval "List" [0]) (arr (.sort 1) (.sort 1))
  nil : ∀ ρ, Has sapp mem piS univ cval ρ (cval "List.nil" [0]) (.forallE (.sort 1) (lst (.bvar 0)))
  cons : ∀ ρ, Has sapp mem piS univ cval ρ (cval "List.cons" [0])
    (.forallE (.sort 1) (.forallE (.bvar 0) (.forallE (lst (.bvar 1)) (lst (.bvar 2)))))
  prod : ∀ ρ, Has sapp mem piS univ cval ρ (cval "Prod" [0, 0]) (arr (.sort 1) (arr (.sort 1) (.sort 1)))
  pmk : ∀ ρ, Has sapp mem piS univ cval ρ (cval "Prod.mk" [0, 0])
    (.forallE (.sort 1) (.forallE (.sort 1) (.forallE (.bvar 1) (.forallE (.bvar 1)
      (.app (.app (c "Prod" [0, 0]) (.bvar 3)) (.bvar 2))))))
  -- the two heads of the tiny language
  add : ∀ ρ, Has sapp mem piS univ cval ρ (cval "Nat.add" []) (arr (c "Nat") (arr (c "Nat") (c "Nat")))
  iteEq : ∀ ρ, Has sapp mem piS univ cval ρ (cval "iteEq" [])
    (arr (c "Nat") (arr (c "Nat") (arr (c "Nat") (arr (c "Nat") (c "Nat")))))

section
variable (St : Stored sapp mem piS univ cval)
include St

theorem nat_univ : mem (cval "Nat" []) (univ 1) := (St.nat (fun _ => (cval "Nat" []))).mem_den trivial
theorem u64_univ : mem (cval "UInt64" []) (univ 1) := (St.u64 (fun _ => (cval "Nat" []))).mem_den trivial
theorem u8_univ : mem (cval "UInt8" []) (univ 1) := (St.u8 (fun _ => (cval "Nat" []))).mem_den trivial
theorem zero_mem : mem (cval "Nat.zero" []) (cval "Nat" []) := (St.zero (fun _ => (cval "Nat" []))).mem_den trivial
theorem succ_mem {x : S} (hx : mem x (cval "Nat" [])) : mem (sapp (cval "Nat.succ" []) x) (cval "Nat" []) :=
  ((St.succ (fun _ => (cval "Nat" []))).app' St.app_mem trivial hx).mem_den trivial
theorem u64ofNat_mem {x : S} (hx : mem x (cval "Nat" [])) : mem (sapp (cval "UInt64.ofNat" []) x) (cval "UInt64" []) :=
  ((St.u64ofNat (fun _ => (cval "Nat" []))).app' St.app_mem trivial hx).mem_den trivial
theorem u8ofNat_mem {x : S} (hx : mem x (cval "Nat" [])) : mem (sapp (cval "UInt8.ofNat" []) x) (cval "UInt8" []) :=
  ((St.u8ofNat (fun _ => (cval "Nat" []))).app' St.app_mem trivial hx).mem_den trivial
theorem add_mem {x y : S} (hx : mem x (cval "Nat" [])) (hy : mem y (cval "Nat" [])) : mem (sapp (sapp (cval "Nat.add" []) x) y) (cval "Nat" []) :=
  (((St.add (fun _ => (cval "Nat" []))).app' St.app_mem trivial hx).app' St.app_mem trivial hy).mem_den trivial
theorem iteEq_mem {a b t e : S} (ha : mem a (cval "Nat" [])) (hb : mem b (cval "Nat" [])) (ht : mem t (cval "Nat" [])) (he : mem e (cval "Nat" [])) :
    mem (sapp (sapp (sapp (sapp (cval "iteEq" []) a) b) t) e) (cval "Nat" []) :=
  (((((St.iteEq (fun _ => (cval "Nat" []))).app' St.app_mem trivial ha).app' St.app_mem trivial hb).app'
    St.app_mem trivial ht).app' St.app_mem trivial he).mem_den trivial

theorem list_univ {A : S} (hA : mem A (univ 1)) : mem (sapp (cval "List" [0]) A) (univ 1) :=
  ((St.list (fun _ => (cval "Nat" []))).app' St.app_mem trivial hA).mem_den trivial
theorem nil_mem {A : S} (hA : mem A (univ 1)) : mem (sapp (cval "List.nil" [0]) A) (sapp (cval "List" [0]) A) :=
  ((St.nil (fun _ => (cval "Nat" []))).app' St.app_mem trivial hA).mem_den ⟨trivial, trivial⟩
theorem cons_mem {A a l : S} (hA : mem A (univ 1)) (ha : mem a A) (hl : mem l (sapp (cval "List" [0]) A)) :
    mem (sapp (sapp (sapp (cval "List.cons" [0]) A) a) l) (sapp (cval "List" [0]) A) :=
  ((((St.cons (fun _ => (cval "Nat" []))).app' St.app_mem trivial hA).app' St.app_mem trivial ha).app' St.app_mem
    ⟨trivial, trivial⟩ hl).mem_den ⟨trivial, trivial⟩
theorem prod_univ {A B : S} (hA : mem A (univ 1)) (hB : mem B (univ 1)) : mem (sapp (sapp (cval "Prod" [0, 0]) A) B) (univ 1) :=
  (((St.prod (fun _ => (cval "Nat" []))).app' St.app_mem trivial hA).app' St.app_mem trivial hB).mem_den trivial
theorem mk_mem {A B a b : S} (hA : mem A (univ 1)) (hB : mem B (univ 1)) (ha : mem a A) (hb : mem b B) :
    mem (sapp (sapp (sapp (sapp (cval "Prod.mk" [0, 0]) A) B) a) b) (sapp (sapp (cval "Prod" [0, 0]) A) B) :=
  (((((St.pmk (fun _ => (cval "Nat" []))).app' St.app_mem trivial hA).app' St.app_mem trivial hB).app' St.app_mem
    trivial ha).app' St.app_mem trivial hb).mem_den ⟨⟨trivial, trivial⟩, trivial⟩
end

/-! ## the canonical encoding of values (DENOTES_SPIKE §2) and its typing -/

/-- values of the slice: Nano/Expr/Eval.lean:9 (verbatim, without the derived instances) -/
inductive V | w (v : UInt64) | n (v : Nat) | b (v : List UInt64) | l (v : List UInt8) | p (a b : V)

section
variable (sapp : S → S → S) (cval : String → List Nat → S)

def nat : Nat → S
  | 0 => cval "Nat.zero" []
  | k + 1 => sapp (cval "Nat.succ" []) (nat k)
def encL {α : Type} (T : S) (f : α → S) : List α → S
  | [] => sapp (cval "List.nil" [0]) T
  | a :: l => sapp (sapp (sapp (cval "List.cons" [0]) T) (f a)) (encL T f l)
def u64 (x : UInt64) : S := sapp (cval "UInt64.ofNat" []) (nat sapp cval x.toNat)
def u8 (x : UInt8) : S := sapp (cval "UInt8.ofNat" []) (nat sapp cval x.toNat)

/-- what the value's type denotes -/
def tyS : V → S
  | .w _ => cval "UInt64" []
  | .n _ => cval "Nat" []
  | .b _ => sapp (cval "List" [0]) (cval "UInt64" [])
  | .l _ => sapp (cval "List" [0]) (cval "UInt8" [])
  | .p a b => sapp (sapp (cval "Prod" [0, 0]) (tyS a)) (tyS b)

def enc : V → S
  | .w x => u64 sapp cval x
  | .n k => nat sapp cval k
  | .b xs => encL sapp cval (cval "UInt64" []) (u64 sapp cval) xs
  | .l xs => encL sapp cval (cval "UInt8" []) (u8 sapp cval) xs
  | .p a b => sapp (sapp (sapp (sapp (cval "Prod.mk" [0, 0]) (tyS sapp cval a)) (tyS sapp cval b)) (enc a)) (enc b)
end

section
variable (St : Stored sapp mem piS univ cval)
include St

theorem nat_mem : ∀ k, mem (nat sapp cval k) (cval "Nat" [])
  | 0 => zero_mem St
  | k + 1 => succ_mem St (nat_mem k)

theorem encL_mem {α : Type} {T : S} {f : α → S} (hT : mem T (univ 1)) (hf : ∀ a, mem (f a) T) :
    ∀ xs : List α, mem (encL sapp cval T f xs) (sapp (cval "List" [0]) T)
  | [] => nil_mem St hT
  | a :: l => cons_mem St hT (hf a) (encL_mem hT hf l)

/-- **Typing of values.**  The encoding of every value of the slice lies in the denotation of its type, and
that type is in `univ 1`. -/
theorem enc_mem : ∀ v : V, mem (enc sapp cval v) (tyS sapp cval v) ∧ mem (tyS sapp cval v) (univ 1)
  | .w _ => ⟨u64ofNat_mem St (nat_mem St _), u64_univ St⟩
  | .n k => ⟨nat_mem St k, nat_univ St⟩
  | .b xs => ⟨encL_mem St (u64_univ St) (fun _ => u64ofNat_mem St (nat_mem St _)) xs, list_univ St (u64_univ St)⟩
  | .l xs => ⟨encL_mem St (u8_univ St) (fun _ => u8ofNat_mem St (nat_mem St _)) xs, list_univ St (u8_univ St)⟩
  | .p a b =>
    have ha := enc_mem a
    have hb := enc_mem b
    ⟨mk_mem St ha.2 hb.2 ha.1 hb.1, prod_univ St ha.2 hb.2⟩

/-! ## the tiny language (MiniDenotes.lean): every denotation is in ⟦Nat⟧ -/

theorem lit_typed {ρ : Nat → S} : ∀ (k : Nat) (R : S), D sapp mem piS univ cval ρ (.lit k) R →
    mem R (cval "Nat" [])
  | 0, R, h => by
    cases h with
    | natLit h => cases h; exact zero_mem St
  | k + 1, R, h => by
    cases h with
    | natLit h =>
      cases h with
      | app hf ha => cases hf; exact succ_mem St (lit_typed k _ ha)
end

inductive T | lit (n : Nat) | add (a b : T) | ite (a b t e : T)

def tr : T → E
  | .lit n => .lit n
  | .add a b => .app (.app (.const "Nat.add" []) (tr a)) (tr b)
  | .ite a b t e => .app (.app (.app (.app (.const "iteEq" []) (tr a)) (tr b)) (tr t)) (tr e)

/-- **Typing for the tiny language**: whatever `tr e` denotes is a member of ⟦Nat⟧. -/
theorem tiny_typed (St : Stored sapp mem piS univ cval) {ρ : Nat → S} :
    ∀ (e : T) (R : S), D sapp mem piS univ cval ρ (tr e) R → mem R (cval "Nat" [])
  | .lit n, R, h => lit_typed St n R h
  | .add a b, R, h => by
    cases h with
    | app h1 hb => cases h1 with
      | app h0 ha => cases h0; exact add_mem St (tiny_typed St a _ ha) (tiny_typed St b _ hb)
  | .ite a b t e, R, h => by
    cases h with
    | app h3 he => cases h3 with
      | app h2 ht => cases h2 with
        | app h1 hb => cases h1 with
          | app h0 ha =>
            cases h0
            exact iteEq_mem St (tiny_typed St a _ ha) (tiny_typed St b _ hb) (tiny_typed St t _ ht)
              (tiny_typed St e _ he)

end MiniTyping

#print axioms MiniTyping.Has.app
#print axioms MiniTyping.enc_mem
#print axioms MiniTyping.tiny_typed
