/- nano v2, worker 2 (small backend): the TYPED AST the backend compiles, and its Lean meaning.
PROVISIONAL until worker 1's frozen spec (NANO_V2_SPEC.md) lands; the backend adapts to it.  Notes:
Testing/notes/NANO_V2_BACKEND.md.

* Types: words, owned `Array UInt64` buffers, fixed nested products.  Everything is a 64-bit word at run time; a
  product is its components' slots side by side (no boxing).
* Variables: de Bruijn indices over WHOLE values (newest = 0).  The immutable input (bytes as words) is not a
  variable: `isize`/`iget` read it.
* `ite` only on comparisons (unsigned).  `loop` = the one recursion pattern (round 2 §1):
  `run (fuel) (s) := match fuel with | 0 => z s | n+1 => body s` where `body` ends in `rec s'` (= `run n s'`) or
  `ret r` in tail position.  Fuel is a WORD (`fuel.toNat`), so `fuel < 2^64` holds by construction.
* Buffers (round 3 §4): `mk cap` = `Array.mkEmpty cap` (= `#[]`, `cap` = the physical capacity), `size`, `get`
  (defaulted read), `set` (`setIfInBounds`), `push`.  Affine ownership is worker 1's elaborator check; the
  backend's meaning below is the FUNCTIONAL one, the in-place implementation is justified by ownership. -/
namespace Nano.V2B

inductive Ty where
  | w | buf | prod (a b : Ty)
  deriving DecidableEq, Repr

/-- run-time slots of a value -/
def Ty.size : Ty → Nat
  | .w => 1 | .buf => 1 | .prod a b => a.size + b.size

inductive Op where
  | add | sub | mul | and | or | xor | shl | shr
  deriving DecidableEq, Repr

inductive Cmp where
  | eq | ne | lt | ge
  deriving DecidableEq, Repr

mutual
inductive Ex where
  | lit (n : UInt64)
  | var (i : Nat)
  | bin (o : Op) (a b : Ex)
  | ite (c : Cmp) (a b : Ex) (t e : Ex)
  | let_ (v b : Ex)
  | pair (a b : Ex)
  | fst (e : Ex)
  | snd (e : Ex)
  /-- consuming decomposition `let (x, y) := e; b` (y = var 0, x = var 1) -/
  | split (e b : Ex)
  | mk (cap : Nat)
  | size (b : Ex)
  | get (b i : Ex)
  | set (b i x : Ex)
  | push (b x : Ex)
  | isize
  | iget (i : Ex)
  /-- `run fuel.toNat init`, state = var 0 inside `z` and `body` -/
  | loop (fuel init z : Ex) (body : Tl)
  deriving Repr
/-- the tail of a loop body -/
inductive Tl where
  | ret (e : Ex)
  | next (e : Ex)
  | ite (c : Cmp) (a b : Ex) (t e : Tl)
  | let_ (v : Ex) (b : Tl)
  /-- consuming decomposition inside a loop body -/
  | split (e : Ex) (b : Tl)
  deriving Repr
end

inductive Val where
  | wd (x : UInt64)
  | bf (l : List UInt64)
  | pr (a b : Val)
  deriving DecidableEq, Repr, Inhabited

def Val.word : Val → UInt64 | .wd x => x | _ => 0
def Val.list : Val → List UInt64 | .bf l => l | _ => []
def Val.fst : Val → Val | .pr a _ => a | _ => .wd 0
def Val.snd : Val → Val | .pr _ b => b | _ => .wd 0

def Op.eval : Op → UInt64 → UInt64 → UInt64
  | .add, x, y => x + y | .sub, x, y => x - y | .mul, x, y => x * y
  | .and, x, y => x &&& y | .or, x, y => x ||| y | .xor, x, y => x ^^^ y
  | .shl, x, y => x <<< y | .shr, x, y => x >>> y

def Cmp.eval : Cmp → UInt64 → UInt64 → Bool
  | .eq, x, y => x == y | .ne, x, y => x != y | .lt, x, y => decide (x < y) | .ge, x, y => decide (y ≤ x)

def lset (l : List UInt64) (i : UInt64) (x : UInt64) : List UInt64 :=
  if i.toNat < l.length then l.set i.toNat x else l

theorem Ex.sizeOf_pos (e : Ex) : 0 < sizeOf e := by cases e <;> simp <;> omega
theorem Tl.sizeOf_pos (t : Tl) : 0 < sizeOf t := by cases t <;> simp <;> omega

-- the meaning; `inp` = the input bytes as words.  `run`: the loop, `fuel` steps.
mutual
def den (inp : List UInt64) : Ex → List Val → Val
  | .lit n, _ => .wd n
  | .var i, env => env.getD i (.wd 0)
  | .bin o a b, env => .wd (o.eval (den inp a env).word (den inp b env).word)
  | .ite c a b t e, env =>
    if c.eval (den inp a env).word (den inp b env).word then den inp t env else den inp e env
  | .let_ v b, env => den inp b (den inp v env :: env)
  | .pair a b, env => .pr (den inp a env) (den inp b env)
  | .fst e, env => (den inp e env).fst
  | .snd e, env => (den inp e env).snd
  | .split e b, env => let v := den inp e env; den inp b (v.snd :: v.fst :: env)
  | .mk _, _ => .bf []
  | .size b, env => .wd (den inp b env).list.length.toUInt64
  | .get b i, env => .wd ((den inp b env).list.getD (den inp i env).word.toNat 0)
  | .set b i x, env => .bf (lset (den inp b env).list (den inp i env).word (den inp x env).word)
  | .push b x, env => .bf ((den inp b env).list ++ [(den inp x env).word])
  | .isize, _ => .wd inp.length.toUInt64
  | .iget i, env => .wd (inp.getD (den inp i env).word.toNat 0)
  | .loop f i z body, env => run inp z body env (den inp f env).word.toNat (den inp i env)
termination_by e => (sizeOf e, 0, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; have := Ex.sizeOf_pos z; have := Tl.sizeOf_pos body; have := Ex.sizeOf_pos f; omega)
    | (apply Prod.Lex.left; have := Ex.sizeOf_pos z; have := Tl.sizeOf_pos body; omega)
    | (apply Prod.Lex.right; apply Prod.Lex.left; omega)
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
def run (inp : List UInt64) (z : Ex) (body : Tl) (env : List Val) : Nat → Val → Val
  | 0, s => den inp z (s :: env)
  | n + 1, s => match denT inp body (s :: env) with
    | .inl r => r
    | .inr s' => run inp z body env n s'
termination_by n => (sizeOf z + sizeOf body, 1, n)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; have := Ex.sizeOf_pos z; have := Tl.sizeOf_pos body; have := Ex.sizeOf_pos f; omega)
    | (apply Prod.Lex.left; have := Ex.sizeOf_pos z; have := Tl.sizeOf_pos body; omega)
    | (apply Prod.Lex.right; apply Prod.Lex.left; omega)
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
-- `.inl r`: the loop returns `r`; `.inr s'`: next iteration on `s'`
def denT (inp : List UInt64) : Tl → List Val → Val ⊕ Val
  | .ret e, env => .inl (den inp e env)
  | .next e, env => .inr (den inp e env)
  | .ite c a b t e, env =>
    if c.eval (den inp a env).word (den inp b env).word then denT inp t env else denT inp e env
  | .let_ v b, env => denT inp b (den inp v env :: env)
  | .split e b, env => let v := den inp e env; denT inp b (v.snd :: v.fst :: env)
termination_by t => (sizeOf t, 0, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; have := Ex.sizeOf_pos z; have := Tl.sizeOf_pos body; have := Ex.sizeOf_pos f; omega)
    | (apply Prod.Lex.left; have := Ex.sizeOf_pos z; have := Tl.sizeOf_pos body; omega)
    | (apply Prod.Lex.right; apply Prod.Lex.left; omega)
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; apply Prod.Lex.right; omega)
end

/-- a program: `main` maps the input to `(status, output buffer)`; status 0 = ok -/
structure Prog where
  main : Ex

/-- the program's `Bytes → ok/error` function: `.ok bytes` (low bytes of the output words) or `.error status` -/
def Prog.eval (p : Prog) (input : List UInt8) : Except UInt64 (List UInt8) :=
  let v := den (input.map (·.toUInt64)) p.main []
  if v.fst.word = 0 then .ok (v.snd.list.map (·.toUInt8)) else .error v.fst.word

/-! ## typing (what the backend needs: slot counts).  Ownership is checked by worker 1's elaborator. -/
mutual
def tyOf : List Ty → Ex → Option Ty
  | _, .lit _ => some .w
  | env, .var i => env[i]?
  | env, .bin _ a b => if tyOf env a = some .w ∧ tyOf env b = some .w then some .w else none
  | env, .ite _ a b t e =>
    if tyOf env a = some .w ∧ tyOf env b = some .w ∧ tyOf env t = tyOf env e then tyOf env t else none
  | env, .let_ v b => match tyOf env v with
    | some τ => tyOf (τ :: env) b
    | none => none
  | env, .pair a b => match tyOf env a, tyOf env b with
    | some τ, some σ => some (.prod τ σ)
    | _, _ => none
  | env, .fst e => match tyOf env e with
    | some (.prod τ _) => some τ
    | _ => none
  | env, .snd e => match tyOf env e with
    | some (.prod _ σ) => some σ
    | _ => none
  | env, .split e b => match tyOf env e with
    | some (.prod τ σ) => tyOf (σ :: τ :: env) b
    | _ => none
  | _, .mk _ => some .buf
  | env, .size b => if tyOf env b = some .buf then some .w else none
  | env, .get b i => if tyOf env b = some .buf ∧ tyOf env i = some .w then some .w else none
  | env, .set b i x =>
    if tyOf env b = some .buf ∧ tyOf env i = some .w ∧ tyOf env x = some .w then some .buf else none
  | env, .push b x => if tyOf env b = some .buf ∧ tyOf env x = some .w then some .buf else none
  | _, .isize => some .w
  | env, .iget i => if tyOf env i = some .w then some .w else none
  | env, .loop f i z body =>
    if tyOf env f = some .w then
      match tyOf env i with
      | some σ => match tyOf (σ :: env) z with
        | some ρ => if tyT (σ :: env) σ ρ body then some ρ else none
        | none => none
      | none => none
    else none
-- the tail `body` returns `ρ` / continues on state type `σ`
def tyT : List Ty → Ty → Ty → Tl → Bool
  | env, _, ρ, .ret e => tyOf env e == some ρ
  | env, σ, _, .next e => tyOf env e == some σ
  | env, σ, ρ, .ite _ a b t e =>
    tyOf env a == some .w && tyOf env b == some .w && tyT env σ ρ t && tyT env σ ρ e
  | env, σ, ρ, .let_ v b => match tyOf env v with
    | some τ => tyT (τ :: env) σ ρ b
    | none => false
  | env, σ, ρ, .split e b => match tyOf env e with
    | some (.prod τ τ') => tyT (τ' :: τ :: env) σ ρ b
    | _ => false
end

end Nano.V2B
