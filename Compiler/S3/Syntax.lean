/- **S3: the typed source calculus** (`Testing/notes/S3_CALCULUS.md`, `Testing/notes/IR_S3.md`).

A deeply embedded, first-order, monomorphic calculus that every front end can target, so that features compose in
one function:
* types `Ty`: 64-bit words (`UInt64`/`Int64` share them; the meaning of an operation fixes signedness), `Bool`, and
  user algebraic datatypes `d i` from the signature (constructors with word / Bool / datatype fields, no function
  fields); lists are datatypes `[[], [τ, d i]]`, structures are one-constructor datatypes;
* expressions `Expr S Γ τ`, typed by construction (de Bruijn variables `Var Γ τ`), in A-normal form: variables,
  literals, word primitives with their exact Lean meaning (`Prim`, `Cmp`), `let`, `if` on a `Bool`, constructors,
  exhaustive `match` (one arm per constructor, binding the fields), fully applied calls of named functions;
* programs `Prog`: signature + one body per function + `main` (bytes to bytes, as a byte list `d 0`).

Meaning: `Ev P env e v`, a big-step relation into universal values `V` (a word, or a constructor with fields), free of
pointers, registers, allocation and fuel; it is deterministic (`Ev.det`), and stuck (no derivation) only on
ill-formed values, which typed programs on encoded inputs never meet.  `⟦τ⟧` (`Ty.den`) is the Lean type a value of
type `τ` stands for (a datatype stands for its universal value; the bridge `Compiler/S3/Cert.lean` relates them to
the user's Lean types).  Recursion: the meaning is the least relation (no termination needed to state it); a
program's termination on its inputs is the per-function bridge's business (it is proved from the Lean function's
own termination, by functional induction); `WfCert` is the slot for a program-level certificate.

Pure Lean (core only). -/
import Spec.Code
import Spec.Top

namespace Proven.S3
set_option autoImplicit false

/-! ## types and signatures -/

inductive Ty where
  | w
  | b
  | d (i : Nat)
  deriving DecidableEq, Repr

structure Sig where
  /-- per datatype, per constructor, the field types -/
  dts : List (List (List Ty))
  /-- per function, the parameter types and the result type -/
  fns : List (List Ty × Ty)
  deriving Repr

/-- list lookup with a default, reducible (so that the types of generated programs compute by `whnfR`) -/
@[reducible] def lget {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | a :: _, 0 => a
  | _ :: l, n + 1 => lget d l n

/-- the constructors of datatype `i` -/
@[reducible] def Sig.dt (S : Sig) (i : Nat) : List (List Ty) := lget [] S.dts i
/-- the field types of constructor `j` of datatype `i` -/
@[reducible] def Sig.flds (S : Sig) (i j : Nat) : List Ty := lget [] (S.dt i) j
/-- the number of constructors of datatype `i` -/
@[reducible] def Sig.nc (S : Sig) (i : Nat) : Nat := (S.dt i).length
/-- the field types of constructor `j` of datatype `i`, for a constructor that exists -/
@[reducible] def Sig.fld (S : Sig) (i : Nat) (j : Fin (S.nc i)) : List Ty := (S.dt i)[j.val]'j.isLt
/-- the parameter types and the result type of function `f` -/
@[reducible] def Sig.fn (S : Sig) (f : Nat) : List Ty × Ty := lget ([], .w) S.fns f

/-! ## syntax -/

/-- a typed de Bruijn variable -/
inductive Var : List Ty → Ty → Type where
  | z {Γ : List Ty} {τ : Ty} : Var (τ :: Γ) τ
  | s {Γ : List Ty} {τ σ : Ty} : Var Γ τ → Var (σ :: Γ) τ
  deriving Repr

def Var.idx {Γ : List Ty} {τ : Ty} : Var Γ τ → Nat
  | .z => 0
  | .s x => x.idx + 1

/-- variables of the types `ts` -/
inductive Vars (Γ : List Ty) : List Ty → Type where
  | nil : Vars Γ []
  | cons {τ : Ty} {ts : List Ty} : Var Γ τ → Vars Γ ts → Vars Γ (τ :: ts)
  deriving Repr

def Vars.idxs {Γ ts : List Ty} : Vars Γ ts → List Nat
  | .nil => []
  | .cons x xs => x.idx :: xs.idxs

/-- word operations (meaning: `Prim.eval`, the meaning of the `UInt64` operation of the same name) -/
inductive Prim where
  | op (o : Proven.Op)
  | mul
  /-- unsigned division, `x / 0 = 0` (Lean's) -/
  | udiv
  /-- unsigned remainder, `x % 0 = x` (Lean's) -/
  | urem
  deriving DecidableEq, Repr

def Prim.eval : Prim → BitVec 64 → BitVec 64 → BitVec 64
  | .op o, x, y => o.eval x y
  | .mul, x, y => x * y
  | .udiv, x, y => x / y
  | .urem, x, y => x % y

/-- comparisons of words (a `Bool`) -/
inductive Cmp where | eq | ne | ult | ule | slt | sle
  deriving DecidableEq, Repr

def Cmp.eval : Cmp → BitVec 64 → BitVec 64 → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .ult, x, y => decide (x < y)
  | .ule, x, y => decide (x ≤ y)
  | .slt, x, y => x.slt y
  | .sle, x, y => x.sle y

/-- **expressions**, typed by construction, in A-normal form -/
inductive Expr (S : Sig) : List Ty → Ty → Type where
  | var {Γ : List Ty} {τ : Ty} (x : Var Γ τ) : Expr S Γ τ
  | lit {Γ : List Ty} (c : BitVec 64) : Expr S Γ .w
  | blit {Γ : List Ty} (c : Bool) : Expr S Γ .b
  | bin {Γ : List Ty} (o : Prim) (a b : Var Γ .w) : Expr S Γ .w
  | cmp {Γ : List Ty} (c : Cmp) (a b : Var Γ .w) : Expr S Γ .b
  | bnot {Γ : List Ty} (a : Var Γ .b) : Expr S Γ .b
  | let_ {Γ : List Ty} {σ τ : Ty} (e₁ : Expr S Γ σ) (e₂ : Expr S (σ :: Γ) τ) : Expr S Γ τ
  | ite {Γ : List Ty} {τ : Ty} (c : Var Γ .b) (e₁ e₂ : Expr S Γ τ) : Expr S Γ τ
  /-- constructor `j` of datatype `i` -/
  | mk {Γ : List Ty} (i j : Nat) (xs : Vars Γ (S.flds i j)) : Expr S Γ (.d i)
  /-- exhaustive `match`: arm `j` binds the fields of constructor `j` (field `0` is variable `0`) -/
  | cas {Γ : List Ty} {τ : Ty} {i : Nat} (x : Var Γ (.d i)) (arms : (j : Fin (S.nc i)) → Expr S (S.fld i j ++ Γ) τ) :
      Expr S Γ τ
  /-- a fully applied call of function `f` -/
  | call {Γ : List Ty} {τ : Ty} (f : Fin S.fns.length) (xs : Vars Γ (S.fn f).1) (h : (S.fn f).2 = τ) : Expr S Γ τ

/-- match arms as a list (`Alts.get` is the arms function of `cas`) -/
inductive Alts (S : Sig) (Γ : List Ty) (τ : Ty) : List (List Ty) → Type where
  | nil : Alts S Γ τ []
  | cons {fs : List Ty} {fss : List (List Ty)} : Expr S (fs ++ Γ) τ → Alts S Γ τ fss → Alts S Γ τ (fs :: fss)

def Alts.get {S : Sig} {Γ : List Ty} {τ : Ty} : {fss : List (List Ty)} → Alts S Γ τ fss → (j : Nat) →
    (h : j < fss.length) → Expr S (fss[j] ++ Γ) τ
  | _ :: _, .cons a _, 0, _ => a
  | _ :: _, .cons _ as, j + 1, h => as.get j (Nat.lt_of_succ_lt_succ h)

@[simp] theorem Alts.get_zero {S : Sig} {Γ : List Ty} {τ : Ty} {fs : List Ty} {fss : List (List Ty)}
    (a : Expr S (fs ++ Γ) τ) (as : Alts S Γ τ fss) (h : 0 < (fs :: fss).length) : (Alts.cons a as).get 0 h = a := rfl

@[simp] theorem Alts.get_succ {S : Sig} {Γ : List Ty} {τ : Ty} {fs : List Ty} {fss : List (List Ty)}
    (a : Expr S (fs ++ Γ) τ) (as : Alts S Γ τ fss) (j : Nat) (h : j + 1 < (fs :: fss).length) :
    (Alts.cons a as).get (j + 1) h = as.get j (Nat.lt_of_succ_lt_succ h) := rfl

/-- the arms of a `cas` on datatype `i` (the type `cas` expects, syntactically) -/
def Alts.arms {S : Sig} {Γ : List Ty} {τ : Ty} {i : Nat} (as : Alts S Γ τ (S.dt i)) :
    (j : Fin (S.nc i)) → Expr S (S.fld i j ++ Γ) τ := fun j => as.get j.val j.isLt

/-- the bodies of functions with signatures `fns` -/
inductive Bodies (S : Sig) : List (List Ty × Ty) → Type where
  | nil : Bodies S []
  | cons {fn : List Ty × Ty} {fns : List (List Ty × Ty)} : Expr S fn.1 fn.2 → Bodies S fns → Bodies S (fn :: fns)

def Bodies.get {S : Sig} : {fns : List (List Ty × Ty)} → Bodies S fns → (j : Nat) → j < fns.length →
    Expr S (lget ([], .w) fns j).1 (lget ([], .w) fns j).2
  | _ :: _, .cons b _, 0, _ => b
  | _ :: _, .cons _ bs, j + 1, h => bs.get j (Nat.lt_of_succ_lt_succ h)

@[simp] theorem Bodies.get_zero {S : Sig} {fn : List Ty × Ty} {fns : List (List Ty × Ty)} (b : Expr S fn.1 fn.2)
    (bs : Bodies S fns) (h : 0 < (fn :: fns).length) : (Bodies.cons b bs).get 0 h = b := rfl

@[simp] theorem Bodies.get_succ {S : Sig} {fn : List Ty × Ty} {fns : List (List Ty × Ty)} (b : Expr S fn.1 fn.2)
    (bs : Bodies S fns) (j : Nat) (h : j + 1 < (fn :: fns).length) :
    (Bodies.cons b bs).get (j + 1) h = bs.get j (Nat.lt_of_succ_lt_succ h) := rfl

/-- **programs**: a signature, one body per function, the entry `main` (a byte list to a byte list, datatype `0`
being byte lists `[[], [w, d 0]]`) -/
structure Prog where
  S : Sig
  bodies : Bodies S S.fns
  main : Fin S.fns.length

/-- the body of function `f` -/
def Prog.body (P : Prog) (f : Fin P.S.fns.length) : Expr P.S (P.S.fn f).1 (P.S.fn f).2 := P.bodies.get f.val f.isLt

/-! ## values and meaning -/

/-- universal values: a word (also `Bool`: `0`/`1`), or constructor `j` with its fields -/
inductive V where
  | w (x : BitVec 64)
  | c (j : Nat) (fs : List V)
  deriving Repr, Inhabited

/-- **`⟦τ⟧`**: what a value of type `τ` stands for -/
@[reducible] def Ty.den : Ty → Type
  | .w => BitVec 64
  | .b => Bool
  | .d _ => V

def Ty.toV : (τ : Ty) → τ.den → V
  | .w, x => .w x
  | .b, x => .w (if x then 1 else 0)
  | .d _, v => v

def bv (c : Bool) : BitVec 64 := if c then 1 else 0

def Vars.get {Γ ts : List Ty} (xs : Vars Γ ts) (env : List V) : Option (List V) := xs.idxs.mapM (env[·]?)

/-- **the meaning** of an expression in an environment (variable `k` is `env[k]`) -/
inductive Ev (P : Prog) : {Γ : List Ty} → {τ : Ty} → List V → Expr P.S Γ τ → V → Prop where
  | var {Γ τ env v} {x : Var Γ τ} : env[x.idx]? = some v → Ev P env (.var x) v
  | lit {Γ env c} : Ev P (Γ := Γ) env (.lit c) (.w c)
  | blit {Γ env c} : Ev P (Γ := Γ) env (.blit c) (.w (bv c))
  | bin {Γ env o x y} {a b : Var Γ .w} : env[a.idx]? = some (.w x) → env[b.idx]? = some (.w y) →
      Ev P env (.bin o a b) (.w (o.eval x y))
  | cmp {Γ env c x y} {a b : Var Γ .w} : env[a.idx]? = some (.w x) → env[b.idx]? = some (.w y) →
      Ev P env (.cmp c a b) (.w (bv (c.eval x y)))
  | bnot {Γ env x} {a : Var Γ .b} : env[a.idx]? = some (.w x) → Ev P env (.bnot a) (.w (x ^^^ 1))
  | let_ {Γ σ τ env v₁ v} {e₁ : Expr P.S Γ σ} {e₂ : Expr P.S (σ :: Γ) τ} : Ev P env e₁ v₁ → Ev P (v₁ :: env) e₂ v →
      Ev P env (.let_ e₁ e₂) v
  | iteT {Γ τ env x v} {c : Var Γ .b} {e₁ e₂ : Expr P.S Γ τ} : env[c.idx]? = some (.w x) → x ≠ 0 → Ev P env e₁ v →
      Ev P env (.ite c e₁ e₂) v
  | iteF {Γ τ env v} {c : Var Γ .b} {e₁ e₂ : Expr P.S Γ τ} : env[c.idx]? = some (.w 0) → Ev P env e₂ v →
      Ev P env (.ite c e₁ e₂) v
  | mk {Γ env i j vs} {xs : Vars Γ (P.S.flds i j)} : xs.get env = some vs → Ev P env (.mk i j xs) (.c j vs)
  | cas {Γ τ env i j fs v} {x : Var Γ (.d i)} {arms : (j : Fin (P.S.nc i)) → Expr P.S (P.S.fld i j ++ Γ) τ}
      (hj : j < P.S.nc i) : env[x.idx]? = some (.c j fs) → fs.length = (P.S.fld i ⟨j, hj⟩).length →
      Ev P (fs ++ env) (arms ⟨j, hj⟩) v → Ev P env (.cas x arms) v
  | call {Γ τ env vs v} {f : Fin P.S.fns.length} {xs : Vars Γ (P.S.fn f).1} {h : (P.S.fn f).2 = τ} :
      xs.get env = some vs → Ev P vs (P.body f) v → Ev P env (.call f xs h) v

/-- **the meaning is deterministic** -/
theorem Ev.det {P : Prog} {Γ : List Ty} {τ : Ty} {env : List V} {e : Expr P.S Γ τ} {v : V} (h : Ev P env e v) :
    ∀ {v'}, Ev P env e v' → v = v' := by
  induction h with
  | var h => intro v' h'; cases h'; rename_i h2; rw [h] at h2; exact Option.some.inj h2
  | lit => intro v' h'; cases h'; rfl
  | blit => intro v' h'; cases h'; rfl
  | bin ha hb => intro v' h'; cases h'; rename_i ha' hb'; rw [ha] at ha'; rw [hb] at hb'; cases ha'; cases hb'; rfl
  | cmp ha hb => intro v' h'; cases h'; rename_i ha' hb'; rw [ha] at ha'; rw [hb] at hb'; cases ha'; cases hb'; rfl
  | bnot ha => intro v' h'; cases h'; rename_i ha'; rw [ha] at ha'; cases ha'; rfl
  | let_ _ _ ih₁ ih₂ => intro v' h'; cases h'; rename_i h₁ h₂; cases ih₁ h₁; exact ih₂ h₂
  | iteT hc hx _ ih =>
    intro v' h'
    cases h' with
    | iteT _ _ h₁ => exact ih h₁
    | iteF hc' _ => rw [hc] at hc'; cases hc'; exact absurd rfl hx
  | iteF hc _ ih =>
    intro v' h'
    cases h' with
    | iteT hc' hx _ => rw [hc] at hc'; cases hc'; exact absurd rfl hx
    | iteF _ h₂ => exact ih h₂
  | mk h => intro v' h'; cases h'; rename_i h2; rw [h] at h2; cases h2; rfl
  | cas hj hx _ _ ih =>
    intro v' h'
    cases h' with
    | cas hj' hx' _ ha' => rw [hx] at hx'; cases hx'; exact ih ha'
  | call h _ ih =>
    intro v' h'
    cases h' with
    | call h2 hb => rw [h] at h2; cases h2; exact ih hb

/-! ## programs on bytes -/

/-- the byte list as a value (datatype `0`: `nil` = constructor `0`, `cons b rest` = constructor `1`) -/
def bytesV : List UInt8 → V
  | [] => .c 0 []
  | b :: bs => .c 1 [.w (b.toBitVec.setWidth 64), bytesV bs]

/-- the bytes of a byte-list value (the low byte of each word) -/
def bytesOut : V → Option (List UInt8)
  | .c 0 [] => some []
  | .c 1 [.w x, r] => (bytesOut r).map (UInt8.ofBitVec (x.setWidth 8) :: ·)
  | _ => none

/-- `main` maps the input to `v` -/
def Prog.Den (P : Prog) (input : List UInt8) (v : V) : Prop := Ev P [bytesV input] (P.body P.main) v

/-- **the meaning of a program on bytes**: the output bytes of `main` on the input bytes -/
noncomputable def Prog.run (P : Prog) (input : List UInt8) : Option (List UInt8) :=
  open Classical in if h : ∃ v, P.Den input v then bytesOut (Classical.choose h) else none

theorem Prog.run_eq {P : Prog} {input : List UInt8} {v : V} (h : P.Den input v) : P.run input = bytesOut v := by
  unfold Prog.run
  rw [dif_pos ⟨v, h⟩]
  rw [Ev.det (Classical.choose_spec (⟨v, h⟩ : ∃ v, P.Den input v)) h]

theorem Prog.run_some {P : Prog} {input out : List UInt8} (h : P.run input = some out) :
    ∃ v, P.Den input v ∧ bytesOut v = some out := by
  unfold Prog.run at h
  split at h
  · next hx => exact ⟨_, Classical.choose_spec hx, h⟩
  · exact nomatch h

noncomputable instance : Proven.Top.Program Prog := ⟨Prog.run⟩

/-! ## the well-foundedness slot -/

/-- evaluating `e` in `env` reaches a call of `g` on `ws` (only the branches taken) -/
inductive Reaches (P : Prog) (g : Fin P.S.fns.length) (ws : List V) : {Γ : List Ty} → {τ : Ty} → List V →
    Expr P.S Γ τ → Prop where
  | here {Γ τ env} {xs : Vars Γ (P.S.fn g).1} {h : (P.S.fn g).2 = τ} : xs.get env = some ws →
      Reaches P g ws env (.call g xs h)
  | let₁ {Γ σ τ env} {e₁ : Expr P.S Γ σ} {e₂ : Expr P.S (σ :: Γ) τ} : Reaches P g ws env e₁ →
      Reaches P g ws env (.let_ e₁ e₂)
  | let₂ {Γ σ τ env v₁} {e₁ : Expr P.S Γ σ} {e₂ : Expr P.S (σ :: Γ) τ} : Ev P env e₁ v₁ →
      Reaches P g ws (v₁ :: env) e₂ → Reaches P g ws env (.let_ e₁ e₂)
  | iteT {Γ τ env x} {c : Var Γ .b} {e₁ e₂ : Expr P.S Γ τ} : env[c.idx]? = some (.w x) → x ≠ 0 →
      Reaches P g ws env e₁ → Reaches P g ws env (.ite c e₁ e₂)
  | iteF {Γ τ env} {c : Var Γ .b} {e₁ e₂ : Expr P.S Γ τ} : env[c.idx]? = some (.w 0) →
      Reaches P g ws env e₂ → Reaches P g ws env (.ite c e₁ e₂)
  | cas {Γ τ env i j fs} {x : Var Γ (.d i)} {arms : (j : Fin (P.S.nc i)) → Expr P.S (P.S.fld i j ++ Γ) τ}
      (hj : j < P.S.nc i) : env[x.idx]? = some (.c j fs) → Reaches P g ws (fs ++ env) (arms ⟨j, hj⟩) →
      Reaches P g ws env (.cas x arms)

/-- **a program-level termination certificate** (the slot; structural recursion: `μ` = the size of an argument;
tuple measures and mutual recursion: any `μ` into `Nat`): every call decreases `μ`.  Not needed by the compiler
theorem (which takes the meaning as given), nor by the bridge (termination there is the Lean function's own). -/
structure WfCert (P : Prog) where
  μ : Fin P.S.fns.length → List V → Nat
  dec : ∀ f vs g ws, Reaches P g ws vs (P.body f) → μ g ws < μ f vs

end Proven.S3
