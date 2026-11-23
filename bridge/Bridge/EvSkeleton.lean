/- Bridge.EvSkeleton: the Ev induction (DENOTES_SPIKE.md §3, task 5) against a STANDALONE trimmed copy of
con-leche's `Denotes` (as MiniDenotes.lean; built without con-leche, owner 2026-11-23).

Shape of the result (`ev_denotes`): if `Ev P env e v`, then whatever `tr e` denotes at `ρE env` is `enc v`
("uniqueness" form).  EXISTENCE of the denotation is not claimed here: in the real bridge it comes from
`Model.mem` (every subterm of a stored `f = body` theorem denotes), see Transfer.lean `Inhab.eq`.

The per-constant facts are the fields of `Facts`, ONE PER Ev RULE THAT TOUCHES A CONSTANT.  Each field is a
local statement about one head constant applied to denoted arguments; in the real bridge each is a transfer
from one or two stored theorems + typing (Transfer.lean).  The skeleton does the plumbing: application
spines, environments (`ρE`), binders (let as a beta-redex, Prod.casesOn, Nat.casesOn), argument lists and
calls (`strip`, `vs.reverse`).

STATUS: proved, no sorry (the `Facts` fields are HYPOTHESES, i.e. the open per-constant lemmas). -/
import Nano.Expr.Correct

namespace Bridge.Skel
open ExprSpec

/-! ## trimmed `Denotes` (con-leche ConLeche/Denotes.lean:134; rules bvar 137, const 144, app 151, lam 157,
natLit 184).  Levels are nano's `List Nat` and passed to `cval` (con-leche: `Level.substFn`); the set
operations `app`, `∈`, `lamR` are parameters; `lam`'s regime is dropped (Transfer.lean `beta` shows beta holds
in both regimes). -/

inductive E | bvar (i : Nat) | const (n : String) (ls : List Nat) | app (f a : E) | lam (t b : E)
  | forallE (t b : E) | lit (k : Nat)

def natLitToConstructor : Nat → E    -- ConLeche/Kernel/CoreDefs.lean:123
  | 0 => .const "Nat.zero" []
  | k + 1 => .app (.const "Nat.succ" []) (.lit k)

def push {S : Type} (x : S) (ρ : Nat → S) : Nat → S    -- ConLeche/Denotes.lean:118
  | 0 => x
  | i + 1 => ρ i

section
variable {S : Type} (sapp : S → S → S) (mem : S → S → Prop) (lamS : S → (S → S) → S)
  (cval : String → List Nat → S)

inductive D : (Nat → S) → E → S → Prop
  | bvar {ρ i} : D ρ (.bvar i) (ρ i)
  | const {ρ n ls} : D ρ (.const n ls) (cval n ls)
  | app {ρ f a F X} : D ρ f F → D ρ a X → D ρ (.app f a) (sapp F X)
  | lam {ρ t b A F} : D ρ t A → (∀ x, mem x A → D (push x ρ) b (F x)) → D ρ (.lam t b) (lamS A F)
  | natLit {ρ k X} : D ρ (natLitToConstructor k) X → D ρ (.lit k) X
end

/-- nano's Expr → the term language.  `let` is emitted as a beta-redex (allowed change, DENOTES_SPIKE §2). -/
def tr : X → E
  | .bv i => .bvar i
  | .c n ls => .const n ls
  | .app f a => .app (tr f) (tr a)
  | .lam t b => .lam (tr t) (tr b)
  | .pi t b => .forallE (tr t) (tr b)
  | .lt _ t v b => .app (.lam (tr t) (tr b)) (tr v)
  | .nat k => .lit k

theorem tr_apps (f : X) : ∀ as : List X, tr (apps f as) = (as.map tr).foldl E.app (tr f)
  | [] => rfl
  | a :: as => tr_apps (.app f a) as

variable {S : Type} {sapp : S → S → S} {mem : S → S → Prop} {lamS : S → (S → S) → S}
  {cval : String → List Nat → S}

/-- the variable environment of an Ev environment (head = bvar 0) -/
def ρE (enc : ExprSpec.V → S) (junk : S) (env : List ExprSpec.V) (i : Nat) : S :=
  (env[i]?.map enc).getD junk

theorem ρE_cons (enc : ExprSpec.V → S) (junk : S) (a : ExprSpec.V) (env : List ExprSpec.V) :
    ρE enc junk (a :: env) = push (enc a) (ρE enc junk env) := by
  funext i; cases i <;> rfl

/-- `List.Forall₂` (not in core): pointwise relation of two lists -/
inductive Fa2 {α β : Type} (r : α → β → Prop) : List α → List β → Prop
  | nil : Fa2 r [] []
  | cons {a b as bs} : r a b → Fa2 r as bs → Fa2 r (a :: as) (b :: bs)

theorem Fa2_map {α β γ : Type} {r : β → γ → Prop} {f : α → β} :
    ∀ {as : List α} {cs : List γ}, Fa2 r (as.map f) cs → Fa2 (fun a c => r (f a) c) as cs
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h t => .cons h (Fa2_map t)

/-! ## inversions -/

theorem D_app_inv {ρ : Nat → S} {f a : E} {R : S} (h : D sapp mem lamS cval ρ (.app f a) R) :
    ∃ F X, D sapp mem lamS cval ρ f F ∧ D sapp mem lamS cval ρ a X ∧ R = sapp F X := by
  cases h with
  | app hf ha => exact ⟨_, _, hf, ha, rfl⟩

theorem D_const_inv {ρ : Nat → S} {n : String} {ls : List Nat} {R : S}
    (h : D sapp mem lamS cval ρ (.const n ls) R) : R = cval n ls := by
  cases h; rfl

/-- peel a spine: `f a₁ … aₙ` denotes `F X₁ … Xₙ` -/
theorem D_foldl_inv {ρ : Nat → S} : ∀ (as : List E) (f : E) (R : S),
    D sapp mem lamS cval ρ (as.foldl E.app f) R →
    ∃ F Xs, D sapp mem lamS cval ρ f F ∧ Fa2 (D sapp mem lamS cval ρ) as Xs ∧ R = Xs.foldl sapp F
  | [], f, R, h => ⟨R, [], h, .nil, rfl⟩
  | a :: as, f, R, h => by
    obtain ⟨F', Xs, hF', hXs, rfl⟩ := D_foldl_inv as (.app f a) R h
    obtain ⟨F, X, hF, hX, rfl⟩ := D_app_inv hF'
    exact ⟨F, X :: Xs, hF, .cons hX hXs, rfl⟩

/-- split a spine `apps g (as ++ [a, b])`-style: `tr (apps g [a, b] …)` is two `app`s on `tr (apps g …)` -/
theorem tr_apps_append (g : X) (l r : List X) : tr (apps g (l ++ r)) = tr (apps (apps g l) r) := by
  simp [apps, List.foldl_append]

/-! ## the per-rule facts (open lemmas of the real bridge) -/

/-- What the model must give, one field per constant-touching Ev rule.  `H` is always what the head with its
type/instance arguments denotes; the value arguments are encodings (the IH has already been used). -/
structure Facts (sapp : S → S → S) (mem : S → S → Prop) (lamS : S → (S → S) → S)
    (cval : String → List Nat → S) (P : Prog) (enc : ExprSpec.V → S) (junk : S) : Prop where
  /-- `have x : t := v; b` as `(λ t. b) v`: beta + typing of the let value (`enc a ∈ ⟦t⟧`) -/
  letβ : ∀ {env nd t v b a R}, Ev P env v a →
    D sapp mem lamS cval (ρE enc junk env) (tr (.lt nd t v b)) R →
    D sapp mem lamS cval (ρE enc junk (a :: env)) (tr b) R
  litU : ∀ {ρ ls k i R}, D sapp mem lamS cval ρ (tr (apps (.c "OfNat.ofNat" ls) [.c "UInt64" [], .nat k, i])) R →
    R = enc (.w (UInt64.ofNat k))
  litN : ∀ {ρ ls k i R}, D sapp mem lamS cval ρ (tr (apps (.c "OfNat.ofNat" ls) [.c "Nat" [], .nat k, i])) R →
    R = enc (.n k)
  bin : ∀ {ρ n ls t1 t2 t3 i H x y z}, binV n x y = some z →
    D sapp mem lamS cval ρ (tr (apps (.c n ls) [t1, t2, t3, i])) H →
    sapp (sapp H (enc (.w x))) (enc (.w y)) = enc (.w z)
  /-- ite: `H` = ⟦ite T c d⟧; the condition is given by its `EvB` derivation -/
  ite : ∀ {env ls T c d bc H Xt Xe}, EvB P env c bc →
    D sapp mem lamS cval (ρE enc junk env) (tr (apps (.c "ite" ls) [T, c, d])) H →
    sapp (sapp H Xt) Xe = if bc then Xt else Xe
  pair : ∀ {ρ ls A B H x y}, D sapp mem lamS cval ρ (tr (apps (.c "Prod.mk" ls) [A, B])) H →
    sapp (sapp H (enc x)) (enc y) = enc (.p x y)
  /-- Prod.casesOn iota + beta twice (+ typing of the components) -/
  cases : ∀ {ρ ls A B M T1 T2 body H L x y R},
    D sapp mem lamS cval ρ (tr (apps (.c "Prod.casesOn" ls) [A, B, M])) H →
    D sapp mem lamS cval ρ (tr (.lam T1 (.lam T2 body))) L → R = sapp (sapp H (enc (.p x y))) L →
    D sapp mem lamS cval (push (enc y) (push (enc x) ρ)) (tr body) R
  natZ : ∀ {ρ ls M H Z L}, D sapp mem lamS cval ρ (tr (apps (.c "Nat.casesOn" ls) [M])) H →
    sapp (sapp (sapp H (enc (.n 0))) Z) L = Z
  /-- Nat.casesOn succ iota + beta (+ typing of `k`) -/
  natS : ∀ {ρ ls M T s H Z L k R}, D sapp mem lamS cval ρ (tr (apps (.c "Nat.casesOn" ls) [M])) H →
    D sapp mem lamS cval ρ (tr (.lam T s)) L → R = sapp (sapp (sapp H (enc (.n (k + 1)))) Z) L →
    D sapp mem lamS cval (push (enc (.n k)) ρ) (tr s) R
  nil : ∀ {ρ ls T R}, D sapp mem lamS cval ρ (tr (.app (.c "List.nil" ls) T)) R → R = enc (.l [])
  prim : ∀ {n : String} {vs : List ExprSpec.V} {r : ExprSpec.V}, ExprSpec.prim n vs = some r → (vs.map enc).foldl sapp (cval n []) = enc r
  /-- a program def: its stored equation `∀ xs, f xs = body` + typing of the arguments; `hb` is the
  induction hypothesis for the body (uniqueness), existence comes from `mem` -/
  call : ∀ {n : String} {vs : List ExprSpec.V} {body b : X} {r : ExprSpec.V}, P.lookup n = some body → strip vs.length body = some b →
    (∀ R, D sapp mem lamS cval (ρE enc junk vs.reverse) (tr b) R → R = enc r) →
    (vs.map enc).foldl sapp (cval n []) = enc r

/-! ## the induction -/

section
variable {P : Prog} {enc : ExprSpec.V → S} {junk : S} (F : Facts sapp mem lamS cval P enc junk)
include F

omit F in
theorem two_args {ρ : Nat → S} {g : X} {l : List X} {a b : X} {R : S}
    (h : D sapp mem lamS cval ρ (tr (apps g (l ++ [a, b]))) R) :
    ∃ H A B, D sapp mem lamS cval ρ (tr (apps g l)) H ∧ D sapp mem lamS cval ρ (tr a) A ∧
      D sapp mem lamS cval ρ (tr b) B ∧ R = sapp (sapp H A) B := by
  rw [tr_apps_append] at h
  obtain ⟨F1, B, h1, hb, rfl⟩ := D_app_inv h
  obtain ⟨H, A, hH, ha, rfl⟩ := D_app_inv h1
  exact ⟨H, A, B, hH, ha, hb, rfl⟩

mutual
theorem ev_denotes : ∀ {env e v}, Ev P env e v →
    ∀ R, D sapp mem lamS cval (ρE enc junk env) (tr e) R → R = enc v
  | env, _, v, .bv hi, R, h => by
    cases h; simp [ρE, hi]
  | env, _, _, .lt hv hb, R, h => ev_denotes hb R (F.letβ hv h)
  | _, _, _, .litU, R, h => F.litU h
  | _, _, _, .litN, R, h => F.litN h
  | _, _, _, .bin (t1 := t1) (t2 := t2) (t3 := t3) (i := i) hz ha hb, R, h => by
    obtain ⟨H, A, B, hH, hA, hB, rfl⟩ := two_args (l := [t1, t2, t3, i]) h
    rw [ev_denotes ha A hA, ev_denotes hb B hB]; exact F.bin hz hH
  | _, _, _, .iteT (T := T) (c := c) (d := d) hc ht, R, h => by
    obtain ⟨H, A, B, hH, hA, hB, rfl⟩ := two_args (l := [T, c, d]) h
    rw [F.ite hc hH]; exact ev_denotes ht A hA
  | _, _, _, .iteF (T := T) (c := c) (d := d) hc he, R, h => by
    obtain ⟨H, A, B, hH, hA, hB, rfl⟩ := two_args (l := [T, c, d]) h
    rw [F.ite hc hH]; exact ev_denotes he B hB
  | _, _, _, .mk (A := A) (B := B) ha hb, R, h => by
    obtain ⟨H, X1, X2, hH, h1, h2, rfl⟩ := two_args (l := [A, B]) h
    rw [ev_denotes ha X1 h1, ev_denotes hb X2 h2]; exact F.pair hH
  | _, _, _, .cases (A := A) (B := B) (M := M) hv hbody, R, h => by
    obtain ⟨H, X1, L, hH, h1, hL, rfl⟩ := two_args (l := [A, B, M]) h
    rw [ev_denotes hv X1 h1] at *
    exact ev_denotes hbody _ (by rw [ρE_cons, ρE_cons]; exact F.cases hH hL rfl)
  | _, _, _, .natZ (M := M) hd hz, R, h => by
    rw [show [M, _, _, _] = [M, _] ++ [_, _] from rfl] at h
    obtain ⟨H1, Z, L, hH1, hZ, hL, rfl⟩ := two_args h
    obtain ⟨H, X1, hH, h1, rfl⟩ := D_app_inv hH1
    rw [ev_denotes hd X1 h1, F.natZ hH]; exact ev_denotes hz Z hZ
  | _, _, _, .natS (M := M) hd hs, R, h => by
    rw [show [M, _, _, _] = [M, _] ++ [_, _] from rfl] at h
    obtain ⟨H1, Z, L, hH1, hZ, hL, rfl⟩ := two_args h
    obtain ⟨H, X1, hH, h1, rfl⟩ := D_app_inv hH1
    rw [ev_denotes hd X1 h1]
    exact ev_denotes hs _ (by rw [ρE_cons]; exact F.natS hH hL rfl)
  | _, _, _, .nil, R, h => F.nil h
  | _, _, _, .prim hl hp, R, h => by
    rw [tr_apps] at h
    obtain ⟨H, Xs, hH, hXs, rfl⟩ := D_foldl_inv _ _ _ h
    rw [D_const_inv hH, evL_denotes hl Xs (Fa2_map hXs)]; exact F.prim hp
  | _, _, _, .call hl hlook hstrip hb, R, h => by
    rw [tr_apps] at h
    obtain ⟨H, Xs, hH, hXs, rfl⟩ := D_foldl_inv _ _ _ h
    rw [D_const_inv hH, evL_denotes hl Xs (Fa2_map hXs)]
    exact F.call hlook hstrip (ev_denotes hb)

theorem evL_denotes : ∀ {env as vs}, EvL P env as vs →
    ∀ Xs, Fa2 (fun a X => D sapp mem lamS cval (ρE enc junk env) (tr a) X) as Xs → Xs = vs.map enc
  | _, _, _, .nil, _, .nil => rfl
  | _, _, _, .cons ha hl, _, .cons hX hXs => by
    rw [ev_denotes ha _ hX, evL_denotes hl _ hXs]; rfl
end

end


/-! ## `Facts.prim` and `Facts.bin` split per op (the form of DENOTES-S2's `BridgeOpsSet` lemmas: `len'_set`,
`len64_set`, `rd_set`, `put_set`, `bget_set`, `bset_set`, `bpush_set`; `bnew` is the constructor encoding) -/

structure PrimFacts (sapp : S → S → S) (cval : String → List Nat → S) (enc : ExprSpec.V → S) : Prop where
  rd : ∀ x i, sapp (sapp (cval "rd" []) (enc (.l x))) (enc (.w i)) = enc (.w (x.getD i.toNat 0).toUInt64)
  len : ∀ x, sapp (cval "len" []) (enc (.l x)) = enc (.w x.length.toUInt64)
  len' : ∀ x, sapp (cval "len'" []) (enc (.l x)) = enc (.n x.length)
  put : ∀ o v, sapp (sapp (cval "put" []) (enc (.l o))) (enc (.w v)) = enc (.l (o ++ [v.toUInt8]))
  bnew : cval "bnew" [] = enc (.b [])
  bsize : ∀ b, sapp (cval "bsize" []) (enc (.b b)) = enc (.w b.length.toUInt64)
  bget : ∀ b i, sapp (sapp (cval "bget" []) (enc (.b b))) (enc (.w i)) = enc (.w (b.getD i.toNat 0))
  bset : ∀ b i v, sapp (sapp (sapp (cval "bset" []) (enc (.b b))) (enc (.w i))) (enc (.w v)) =
    enc (.b (b.set i.toNat v))
  bpush : ∀ b v, sapp (sapp (cval "bpush" []) (enc (.b b))) (enc (.w v)) = enc (.b (b ++ [v]))

theorem PrimFacts.prim {enc : ExprSpec.V → S} (F : PrimFacts sapp cval enc) :
    ∀ {n : String} {vs : List ExprSpec.V} {r : ExprSpec.V}, ExprSpec.prim n vs = some r →
      (vs.map enc).foldl sapp (cval n []) = enc r := by
  intro n vs r h
  unfold ExprSpec.prim at h
  split at h <;> (try cases h) <;> simp only [List.map, List.foldl]
  · exact F.rd _ _
  · exact F.len _
  · exact F.len' _
  · exact F.put _ _
  · exact F.bnew
  · exact F.bsize _
  · exact F.bget _ _
  · exact F.bset _ _ _
  · exact F.bpush _ _

/-- one field per `.bin` op: the head (with its type and instance arguments) acts as the UInt64 op -/
structure BinFacts (sapp : S → S → S) (mem : S → S → Prop) (lamS : S → (S → S) → S)
    (cval : String → List Nat → S) (enc : ExprSpec.V → S) : Prop where
  op : ∀ {n ρ ls t1 t2 t3 i H} (f : UInt64 → UInt64 → UInt64), (∀ x y, binV n x y = some (f x y)) →
    D sapp mem lamS cval ρ (tr (apps (.c n ls) [t1, t2, t3, i])) H →
    ∀ x y, sapp (sapp H (enc (.w x))) (enc (.w y)) = enc (.w (f x y))

theorem binV_some {n : String} {x y z : UInt64} (h : binV n x y = some z) :
    ∃ f : UInt64 → UInt64 → UInt64, (∀ a b, binV n a b = some (f a b)) ∧ z = f x y := by
  unfold binV at h ⊢
  split at h <;> first
    | (cases h; exact ⟨_, fun _ _ => rfl, rfl⟩)
    | cases h

theorem BinFacts.bin {enc : ExprSpec.V → S} (F : BinFacts sapp mem lamS cval enc) :
    ∀ {ρ n ls t1 t2 t3 i H x y z}, binV n x y = some z →
      D sapp mem lamS cval ρ (tr (apps (.c n ls) [t1, t2, t3, i])) H →
      sapp (sapp H (enc (.w x))) (enc (.w y)) = enc (.w z) := by
  intro ρ n ls t1 t2 t3 i H x y z hz hH
  obtain ⟨f, hf, rfl⟩ := binV_some hz
  exact F.op f hf hH x y

end Bridge.Skel
