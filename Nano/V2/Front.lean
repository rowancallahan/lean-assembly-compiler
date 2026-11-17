import Nano.Elab
import Nano.V2.Lang
/- nano v2 FRONT END (increment 3): source bytes → `Nano.V2B.Prog` (the ONE shared typed AST, Nano/V2/Lang.lean).
Increments 1–2 (words, `if` on `==`/`<`/`<=`, bit ops, shifts) plus:
* products: types `T × T` (right-assoc, parentheses), `(a, b)` (also `(a, b, c)` = `(a, (b, c))`), `e.1`/`e.2`
  (postfix on a name or a parenthesised expression), `let (a, b) := e; body` (consuming decomposition);
* the I/O prelude: `rd x i`, `len x` (the input `x : List UInt8`, read-only), `put o b`, `[]` (the output,
  `List UInt8`, affine).
Rules (strict: rejecting is always safe; the oracle checks acceptance):
* the INPUT is a def's FIRST parameter if it has type `List UInt8` and is used as input (`rd`/`len`/a callee's input
  position); every other `List UInt8` is an OUTPUT buffer. Positional: a def's first parameter of type `List UInt8`
  IS the input; other `List UInt8` parameters are outputs.
* every pair component is TYPED (contains a word-typed leaf: a parameter, a call, `rd`/`len`, a typed `let`
  variable): Lean gives an untyped numeral component the type `Nat` where no expected type exists.
* OWNERSHIP (conservative, increment 3): a variable whose type contains an output buffer occurs at most once (counting
  the larger `if` branch).
* calls are inlined (`let` chain); the main def is the LAST one: `def m (x : List UInt8) : List UInt8`.
* the declared types are checked with `tyOf` (bodies and call arguments). -/
namespace Nano.V2B
open Nano (isWordC isDigit spanId kwDef kwLet kwTy identOk adjOk)

inductive FTok where
  | kdef | klet | kif | kthen | kelse | kU64 | kList | kU8 | krd | klen | kput
  | id (s : List UInt8) | num (n : UInt64)
  | lp | rp | colon | assign | plus | minus | star | semi
  | eqeq | lt | le | band | bor | bxor | shl | shr
  | comma | times | p1 | p2 | nil
  | kNat | arrow | bar | darrow | klenP
  deriving DecidableEq

def wdTok (w : List UInt8) : Option FTok :=
  match w with
  | [] => none
  | c :: _ =>
    if isDigit c then (if w.all isDigit then some (.num (w.foldl (fun a d => a * 10 + (d - 48).toUInt64) 0)) else none)
    else if w == kwDef then some .kdef else if w == kwLet then some .klet
    else if w == kwTy then some .kU64
    else if w == [105, 102] then some .kif else if w == [116, 104, 101, 110] then some .kthen
    else if w == [101, 108, 115, 101] then some .kelse
    else if w == [76, 105, 115, 116] then some .kList else if w == [85, 73, 110, 116, 56] then some .kU8
    else if w == [114, 100] then some .krd else if w == [108, 101, 110] then some .klen
    else if w == [112, 117, 116] then some .kput
    else if w == [78, 97, 116] then some .kNat
    else if identOk w then some (.id w) else none

def flex : Nat → List UInt8 → Option (List FTok)
  | 0, xs => if xs.isEmpty then some [] else none
  | _ + 1, [] => some []
  | f + 1, c :: xs =>
    if c == 32 then flex f xs
    else if c == 10 then
      match xs with
      | [] => some []
      | 32 :: _ => flex f xs
      | 10 :: _ => flex f xs
      | 100 :: 101 :: 102 :: z => if (match z with | d :: _ => isWordC d | [] => false) then none else flex f xs
      | _ => none
    else if c == 40 then (flex f xs).map (.lp :: ·)
    else if c == 41 then (flex f xs).map (.rp :: ·)
    else if c == 43 then (flex f xs).map (.plus :: ·)
    else if c == 44 then (flex f xs).map (.comma :: ·)
    else if c == 45 then
      match xs with
      | 45 :: _ => none
      | _ => (flex f xs).map (.minus :: ·)
    else if c == 42 then (flex f xs).map (.star :: ·)
    else if c == 59 then (flex f xs).map (.semi :: ·)
    else if c == 58 then
      match xs with
      | 61 :: ys => (flex f ys).map (.assign :: ·)
      | _ => (flex f xs).map (.colon :: ·)
    else if c == 61 then
      match xs with
      | 61 :: 32 :: ys => (flex f ys).map (.eqeq :: ·)
      | 62 :: ys => (flex f ys).map (.darrow :: ·)
      | _ => none
    else if c == 60 then
      match xs with
      | 32 :: ys => (flex f ys).map (.lt :: ·)
      | 61 :: 32 :: ys => (flex f ys).map (.le :: ·)
      | 60 :: 60 :: 32 :: ys => (flex f ys).map (.shl :: ·)
      | _ => none
    else if c == 62 then
      match xs with
      | 62 :: 62 :: 32 :: ys => (flex f ys).map (.shr :: ·)
      | _ => none
    else if c == 38 then
      match xs with
      | 38 :: 38 :: 32 :: ys => (flex f ys).map (.band :: ·)
      | _ => none
    else if c == 124 then
      match xs with
      | 124 :: 124 :: 32 :: ys => (flex f ys).map (.bor :: ·)
      | 32 :: ys => (flex f ys).map (.bar :: ·)
      | _ => none
    else if c == 94 then
      match xs with
      | 94 :: 94 :: 32 :: ys => (flex f ys).map (.bxor :: ·)
      | _ => none
    else if c == 46 then
      -- `.1` / `.2` (not followed by a word character)
      match xs with
      | d :: ys =>
        if (d == 49 || d == 50) && (match ys with | e :: _ => !isWordC e | [] => true) then
          (flex f ys).map ((if d == 49 then .p1 else .p2) :: ·)
        else none
      | [] => none
    else if c == 0xE2 then
      match xs with
      | 0x86 :: 0x92 :: ys => (flex f ys).map (.arrow :: ·)
      | _ => none
    else if c == 0xC3 then
      match xs with
      | 0x97 :: ys => (flex f ys).map (.times :: ·)
      | _ => none
    else if c == 91 then
      match xs with
      | 93 :: ys => (flex f ys).map (.nil :: ·)
      | _ => none
    else if isWordC c then
      let r := spanId f (c :: xs)
      -- a numeral followed by `.` would be a decimal literal in Lean
      if isDigit c && (match r.2 with | 46 :: _ => true | _ => false) then none else
      -- `len'` (fuel only)
      if r.1 == [108, 101, 110] && (match r.2 with | 39 :: _ => true | _ => false) then
        (flex f (r.2.drop 1)).map (.klenP :: ·) else
      match wdTok r.1 with
      | some t => (flex f r.2).map (t :: ·)
      | none => none
    else none

/-! ## the surface AST (calls kept, for the Lean-subset guards) -/
inductive SCmp where
  | eq | lt | le
  deriving DecidableEq, Repr

inductive S where
  | num (n : UInt64) | var (i : Nat)
  | bin (o : Op) (a b : S)              -- `+ - * &&& ||| ^^^`
  | sh (l : Bool) (k : Nat) (a : S)
  | let_ (v b : S)
  | ite (k : SCmp) (a b t e : S)
  | call (g : Nat) (as : S)             -- `g` = index into the defs (newest first); `as` = `anil`/`acons`
  | anil | acons (e r : S)
  | pair (a b : S) | fst (e : S) | snd (e : S) | split (e b : S)
  | rd (i : S) | len | put (o e : S) | nil
  /-- a call of a fuel-loop def: fuel (`Nat`: `len'`, `+`, `*`, numerals), state arguments -/
  | lcall (g : Nat) (fuel as : S)
  deriving Repr, Inhabited

/- shift every variable `≥ c` by `k` -/
mutual
def Ex.lift (c k : Nat) : Ex → Ex
  | .lit n => .lit n
  | .var i => .var (if c ≤ i then i + k else i)
  | .bin o a b => .bin o (a.lift c k) (b.lift c k)
  | .ite q a b t e => .ite q (a.lift c k) (b.lift c k) (t.lift c k) (e.lift c k)
  | .let_ v b => .let_ (v.lift c k) (b.lift (c + 1) k)
  | .pair a b => .pair (a.lift c k) (b.lift c k)
  | .fst e => .fst (e.lift c k)
  | .snd e => .snd (e.lift c k)
  | .split e b => .split (e.lift c k) (b.lift (c + 2) k)
  | .mk n => .mk n
  | .size b => .size (b.lift c k)
  | .get b i => .get (b.lift c k) (i.lift c k)
  | .set b i x => .set (b.lift c k) (i.lift c k) (x.lift c k)
  | .push b x => .push (b.lift c k) (x.lift c k)
  | .isize => .isize
  | .iget i => .iget (i.lift c k)
  | .loop f i z t => .loop (f.lift c k) (i.lift c k) (z.lift (c + 1) k) (t.lift (c + 1) k)
def Tl.lift (c k : Nat) : Tl → Tl
  | .ret e => .ret (e.lift c k)
  | .next e => .next (e.lift c k)
  | .ite q a b t e => .ite q (a.lift c k) (b.lift c k) (t.lift c k) (e.lift c k)
  | .let_ v b => .let_ (v.lift c k) (b.lift (c + 1) k)
  | .split e b => .split (e.lift c k) (b.lift (c + 2) k)
end

/- the output capacity κ of `[]`: a parameter of the front end (`frontElabK`); lowering writes `mk 0`, replaced by
`mk κ` at the end (`Ex.cap`).  The machine traps above κ (status −2, outside the admitted domain). -/
mutual
def Ex.cap (κ : Nat) : Ex → Ex
  | .lit n => .lit n
  | .var i => .var i
  | .bin o a b => .bin o (a.cap κ) (b.cap κ)
  | .ite q a b t e => .ite q (a.cap κ) (b.cap κ) (t.cap κ) (e.cap κ)
  | .let_ v b => .let_ (v.cap κ) (b.cap κ)
  | .pair a b => .pair (a.cap κ) (b.cap κ)
  | .fst e => .fst (e.cap κ)
  | .snd e => .snd (e.cap κ)
  | .split e b => .split (e.cap κ) (b.cap κ)
  | .mk _ => .mk κ
  | .size b => .size (b.cap κ)
  | .get b i => .get (b.cap κ) (i.cap κ)
  | .set b i x => .set (b.cap κ) (i.cap κ) (x.cap κ)
  | .push b x => .push (b.cap κ) (x.cap κ)
  | .isize => .isize
  | .iget i => .iget (i.cap κ)
  | .loop f i z t => .loop (f.cap κ) (i.cap κ) (z.cap κ) (t.cap κ)
def Tl.cap (κ : Nat) : Tl → Tl
  | .ret e => .ret (e.cap κ)
  | .next e => .next (e.cap κ)
  | .ite q a b t e => .ite q (a.cap κ) (b.cap κ) (t.cap κ) (e.cap κ)
  | .let_ v b => .let_ (v.cap κ) (b.cap κ)
  | .split e b => .split (e.cap κ) (b.cap κ)
end

/-- `let a₁; let a₂↑1; …; body` -/
def inl (body : Ex) : Nat → List Ex → Ex
  | j, a :: as => .let_ (a.lift 0 j) (inl body (j + 1) as)
  | _, [] => body

/-- a def's lowered body: a function body, or a fuel loop (zero case, step; the state = the parameters as a
right-nested product, already unpacked inside) -/
inductive FB where
  | fn (b : Ex)
  | lp (z : Ex) (t : Tl)
  deriving Repr

/-- a def: (name, has the input, parameter types (outputs/words, first first), result type, body) -/
abbrev FDef := List UInt8 × Bool × List Ty × Ty × FB

/-- the state value of a loop call: `(a₁, (a₂, … aₖ))` -/
def tup : List Ex → Ex
  | [a] => a
  | a :: as => .pair a (tup as)
  | [] => .lit 0

/-- the state type -/
def tupT : List Ty → Ty
  | [a] => a
  | a :: as => .prod a (tupT as)
  | [] => .w

def S.args : S → List S
  | .acons e r => e :: r.args
  | _ => []

/-- lowering; `ds` newest first -/
def S.low (ds : List FDef) : S → Ex
  | .num n => .lit n
  | .var i => .var i
  | .bin o a b => .bin o (a.low ds) (b.low ds)
  | .sh l k a => .bin (if l then .shl else .shr) (a.low ds) (.lit k.toUInt64)
  | .let_ v b => .let_ (v.low ds) (b.low ds)
  | .ite .eq a b t e => .ite .eq (a.low ds) (b.low ds) (t.low ds) (e.low ds)
  | .ite .lt a b t e => .ite .lt (a.low ds) (b.low ds) (t.low ds) (e.low ds)
  | .ite .le a b t e => .ite .ge (b.low ds) (a.low ds) (t.low ds) (e.low ds)
  | .call g as => match ds[g]? with
    | some (_, _, _, _, .fn body) => inl body 0 (lowA ds as)
    | _ => .lit 0
  | .lcall g fu as => match ds[g]? with
    | some (_, _, _, _, .lp z t) => .loop (fu.low ds) (tup (lowA ds as)) z t
    | _ => .lit 0
  | .anil => .lit 0
  | .acons _ _ => .lit 0
  | .pair a b => .pair (a.low ds) (b.low ds)
  | .fst e => .fst (e.low ds)
  | .snd e => .snd (e.low ds)
  | .split e b => .split (e.low ds) (b.low ds)
  | .rd i => .iget (i.low ds)
  | .len => .isize
  | .put o e => .push (o.low ds) (e.low ds)
  | .nil => .mk 0
where lowA (ds : List FDef) : S → List Ex
  | .acons e r => e.low ds :: lowA ds r
  | _ => []

/-! ## guards (ported from Nano/V2Elab.lean to the surface AST) -/

/-- a word-typed leaf fixes Lean's type (numerals alone default to `Nat`) -/
def S.typed : List Bool → S → Bool
  | fl, .var i => fl.getD i false
  | fl, .bin _ a b => a.typed fl || b.typed fl
  | fl, .sh _ _ a => a.typed fl
  | fl, .let_ v b => b.typed (v.typed fl :: fl)
  | _, .call _ _ => true
  | _, .lcall _ _ _ => true
  | fl, .ite _ _ _ t e => t.typed fl || e.typed fl
  | fl, .pair a b => a.typed fl && b.typed fl
  | fl, .fst e => e.typed fl
  | fl, .snd e => e.typed fl
  | fl, .split e b => b.typed (e.typed fl :: e.typed fl :: fl)
  | _, .rd _ => true
  | _, .len => true
  | _, .put _ _ => true
  | _, .nil => true
  | _, _ => false

def S.hasSh : S → Bool
  | .bin _ a b | .let_ a b | .call _ (.acons a b) | .acons a b | .pair a b | .split a b | .put a b => a.hasSh || b.hasSh
  | .ite _ a b t e => a.hasSh || b.hasSh || t.hasSh || e.hasSh
  | .fst a | .snd a | .rd a | .lcall _ _ a => a.hasSh
  | .sh _ _ _ => true
  | _ => false

abbrev Sm := Bool × Bool × Bool × Bool
def comb (p q : Sm) : Sm := (p.1 || q.1, p.2.1 || q.2.1, p.2.2.1 && q.2.2.1, true)
def good (p : Sm) : Bool := p.2.2.1 && !(p.2.2.2 && p.1 && p.2.1)

/-- the SHIFT GUARD summary (Nano/V2Elab.lean `sm`), extended: projections/`rd`/`len` are typed leaves -/
def S.sm : List Bool → S → Sm
  | fl, .bin _ a b => comb (a.sm fl) (b.sm fl)
  | fl, .var i => (false, !(fl.getD i false), true, false)
  | fl, .call _ as => (as.hasSh, false, smA fl as, false)
  | fl, .lcall _ _ as => (as.hasSh, false, smA fl as, false)
  | fl, .let_ v b => (v.hasSh || b.hasSh, true, good (v.sm fl) && good (b.sm (v.typed fl :: fl)), false)
  | fl, .ite k a b t e =>
    ((S.ite k a b t e).hasSh, true, good (comb (a.sm fl) (b.sm fl)) && good (t.sm fl) && good (e.sm fl), false)
  | fl, .sh _ _ a => (true, false, a.typed fl && good (a.sm fl), false)
  | fl, .pair a b => (a.hasSh || b.hasSh, true, good (a.sm fl) && good (b.sm fl), false)
  | fl, .fst e => (e.hasSh, !(e.typed fl), good (e.sm fl), false)
  | fl, .snd e => (e.hasSh, !(e.typed fl), good (e.sm fl), false)
  | fl, .split e b =>
    (e.hasSh || b.hasSh, true, good (e.sm fl) && good (b.sm (e.typed fl :: e.typed fl :: fl)), false)
  | fl, .rd i => (i.hasSh, false, good (i.sm fl), false)
  | _, .len => (false, false, true, false)
  | fl, .put o e => (o.hasSh || e.hasSh, true, good (o.sm fl) && good (e.sm fl), false)
  | _, _ => (false, true, true, false)
where smA (fl : List Bool) : S → Bool
  | .acons e r => good (e.sm fl) && smA fl r
  | _ => true

/-! ## ownership: a buffer-holding variable occurs at most once -/
def Ty.hasBuf : Ty → Bool
  | .w => false | .buf => true | .prod a b => a.hasBuf || b.hasBuf

/- occurrences of variable `i` (the larger `if` branch) -/
mutual
def Ex.occ (i : Nat) : Ex → Nat
  | .var j => if i = j then 1 else 0
  | .bin _ a b | .pair a b | .get a b | .push a b => a.occ i + b.occ i
  | .ite _ a b t e => a.occ i + b.occ i + max (t.occ i) (e.occ i)
  | .let_ v b => v.occ i + b.occ (i + 1)
  | .split e b => e.occ i + b.occ (i + 2)
  | .fst e | .snd e | .size e | .iget e => e.occ i
  | .set a b c => a.occ i + b.occ i + c.occ i
  | .loop f s z t => f.occ i + s.occ i + 2 * (z.occ (i + 1) + t.occ (i + 1))
  | _ => 0
def Tl.occ (i : Nat) : Tl → Nat
  | .ret e | .next e => e.occ i
  | .ite _ a b t e => a.occ i + b.occ i + max (t.occ i) (e.occ i)
  | .let_ v b => v.occ i + b.occ (i + 1)
  | .split e b => e.occ i + b.occ (i + 2)
end

/- every buffer-holding binder (with types `env`, newest first) is used at most once -/
mutual
def Ex.aff : List Ty → Ex → Bool
  | env, .bin _ a b | env, .pair a b | env, .get a b | env, .push a b => a.aff env && b.aff env
  | env, .ite _ a b t e => a.aff env && b.aff env && t.aff env && e.aff env
  | env, .let_ v b => match tyOf env v with
    | some τ => v.aff env && b.aff (τ :: env) && (!τ.hasBuf || decide (b.occ 0 ≤ 1))
    | none => false
  | env, .split e b => match tyOf env e with
    | some (.prod τ σ) => e.aff env && b.aff (σ :: τ :: env) &&
        (!τ.hasBuf || decide (b.occ 1 ≤ 1)) && (!σ.hasBuf || decide (b.occ 0 ≤ 1))
    | _ => false
  | env, .fst e | env, .snd e | env, .size e | env, .iget e => e.aff env
  | env, .set a b c => a.aff env && b.aff env && c.aff env
  | env, .loop f i z t => match tyOf env i with
    | some σ => f.aff env && i.aff env && z.aff (σ :: env) && t.aff (σ :: env) &&
        (!σ.hasBuf || decide (z.occ 0 ≤ 1 ∧ t.occ 0 ≤ 1))
    | none => false
  | _, _ => true
def Tl.aff : List Ty → Tl → Bool
  | env, .ret e | env, .next e => e.aff env
  | env, .ite _ a b t e => a.aff env && b.aff env && t.aff env && e.aff env
  | env, .let_ v b => match tyOf env v with
    | some τ => v.aff env && b.aff (τ :: env) && (!τ.hasBuf || decide (b.occ 0 ≤ 1))
    | none => false
  | env, .split e b => match tyOf env e with
    | some (.prod τ σ) => e.aff env && b.aff (σ :: τ :: env) &&
        (!τ.hasBuf || decide (b.occ 1 ≤ 1)) && (!σ.hasBuf || decide (b.occ 0 ≤ 1))
    | _ => false
end

/-! ## the parser -/
/-- scope entry: `none` = the input; `some (τ, typed)` -/
abbrev FScope := List (List UInt8 × Option (Ty × Bool))

/-- the de Bruijn index of a non-input variable (the input takes no slot) -/
def fidx : List UInt8 → FScope → Nat → Option Nat
  | _, [], _ => none
  | s, (t, k) :: ts, i =>
    if s == t then (match k with | some _ => some i | none => none)
    else fidx s ts (if k.isSome then i + 1 else i)

def isInp : List UInt8 → FScope → Bool
  | _, [] => false
  | s, (t, k) :: ts => if s == t then k.isNone else isInp s ts

def tys (sc : FScope) : List Ty := sc.filterMap fun e => e.2.map (·.1)
def flags (sc : FScope) : List Bool := sc.filterMap fun e => e.2.map (·.2)

def fdef : List UInt8 → List FDef → Nat → Option (Nat × FDef)
  | _, [], _ => none
  | s, d :: ds, i => if s == d.1 then some (i, d) else fdef s ds (i + 1)

def cmpS : FTok → Option SCmp
  | .eqeq => some .eq | .lt => some .lt | .le => some .le | _ => none

/- fuel expressions (`Nat`): `len' x`, numerals `< 2^32`, `+`, `*`, parentheses; `pFA` = an atom -/
mutual
def pF : Nat → FScope → List FTok → Option (S × List FTok)
  | 0, _, _ => none
  | f + 1, sc, ts =>
    match pFM f sc ts with
    | some (a, .plus :: r) =>
      match pF f sc r with
      | some (b, r2) => some (.bin .add a b, r2)
      | none => none
    | x => x
def pFM : Nat → FScope → List FTok → Option (S × List FTok)
  | 0, _, _ => none
  | f + 1, sc, ts =>
    match pFA f sc ts with
    | some (a, .star :: r) =>
      match pFM f sc r with
      | some (b, r2) => some (.bin .mul a b, r2)
      | none => none
    | x => x
def pFA : Nat → FScope → List FTok → Option (S × List FTok)
  | 0, _, _ => none
  | _ + 1, _, .num n :: ts => if n < 2 ^ 32 then some (.num n, ts) else none
  | _ + 1, sc, .klenP :: .id x :: ts => if isInp x sc then some (.len, ts) else none
  | f + 1, sc, .lp :: ts =>
    match pF f sc ts with
    | some (e, .rp :: r) => some (e, r)
    | _ => none
  | _, _, _ => none
end

/- the parser state passes the defs `ds` (newest first) for calls and lowering -/
mutual
def pE : Nat → FScope → List FDef → List FTok → Option (S × List FTok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, .klet :: .lp :: .id a :: .comma :: .id b :: .rp :: .assign :: ts =>
    match pE f sc ds ts with
    | some (v, .semi :: r) =>
      match tyOf (tys sc) (v.low ds) with
      | some (.prod τ σ) =>
        let t := v.typed (flags sc)
        match pE f ((b, some (σ, t)) :: (a, some (τ, t)) :: sc) ds r with
        | some (e, r2) => some (.split v e, r2)
        | none => none
      | _ => none
    | _ => none
  | f + 1, sc, ds, .klet :: .id x :: .assign :: ts =>
    match pE f sc ds ts with
    | some (v, .semi :: r) =>
      match tyOf (tys sc) (v.low ds) with
      | some τ =>
        match pE f ((x, some (τ, v.typed (flags sc))) :: sc) ds r with
        | some (b, r2) => some (.let_ v b, r2)
        | none => none
      | none => none
    | _ => none
  | f + 1, sc, ds, .kif :: ts =>
    match pOr f sc ds ts with
    | some (a, op :: r) =>
      match cmpS op with
      | some k =>
        match pOr f sc ds r with
        | some (b, .kthen :: r2) =>
          if a.typed (flags sc) || b.typed (flags sc) then
            match pE f sc ds r2 with
            | some (t, .kelse :: r3) =>
              match pE f sc ds r3 with
              | some (e, r4) => some (.ite k a b t e, r4)
              | none => none
            | _ => none
          else none
        | _ => none
      | none => none
    | _ => none
  | f + 1, sc, ds, ts => pOr f sc ds ts
def pOr : Nat → FScope → List FDef → List FTok → Option (S × List FTok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, ts =>
    match pXor f sc ds ts with
    | some (e, r) => pOrT f sc ds e r
    | none => none
def pOrT : Nat → FScope → List FDef → S → List FTok → Option (S × List FTok)
  | 0, _, _, _, _ => none
  | f + 1, sc, ds, acc, .bor :: ts =>
    match pXor f sc ds ts with
    | some (e, r) => pOrT f sc ds (.bin .or acc e) r
    | none => none
  | _ + 1, _, _, acc, ts => some (acc, ts)
def pXor : Nat → FScope → List FDef → List FTok → Option (S × List FTok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, ts =>
    match pAnd f sc ds ts with
    | some (e, r) => pXorT f sc ds e r
    | none => none
def pXorT : Nat → FScope → List FDef → S → List FTok → Option (S × List FTok)
  | 0, _, _, _, _ => none
  | f + 1, sc, ds, acc, .bxor :: ts =>
    match pAnd f sc ds ts with
    | some (e, r) => pXorT f sc ds (.bin .xor acc e) r
    | none => none
  | _ + 1, _, _, acc, ts => some (acc, ts)
def pAnd : Nat → FScope → List FDef → List FTok → Option (S × List FTok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, ts =>
    match pSum f sc ds ts with
    | some (e, r) => pAndT f sc ds e r
    | none => none
def pAndT : Nat → FScope → List FDef → S → List FTok → Option (S × List FTok)
  | 0, _, _, _, _ => none
  | f + 1, sc, ds, acc, .band :: ts =>
    match pSum f sc ds ts with
    | some (e, r) => pAndT f sc ds (.bin .and acc e) r
    | none => none
  | _ + 1, _, _, acc, ts => some (acc, ts)
def pSum : Nat → FScope → List FDef → List FTok → Option (S × List FTok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, ts =>
    match pMul f sc ds ts with
    | some (e, r) => pAdd f sc ds e r
    | none => none
def pAdd : Nat → FScope → List FDef → S → List FTok → Option (S × List FTok)
  | 0, _, _, _, _ => none
  | f + 1, sc, ds, acc, .plus :: ts =>
    match pMul f sc ds ts with
    | some (e, r) => pAdd f sc ds (.bin .add acc e) r
    | none => none
  | f + 1, sc, ds, acc, .minus :: ts =>
    match pMul f sc ds ts with
    | some (e, r) => pAdd f sc ds (.bin .sub acc e) r
    | none => none
  | _ + 1, _, _, acc, ts => some (acc, ts)
def pMul : Nat → FScope → List FDef → List FTok → Option (S × List FTok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, ts =>
    match pSh f sc ds ts with
    | some (e, r) => pMulT f sc ds e r
    | none => none
def pMulT : Nat → FScope → List FDef → S → List FTok → Option (S × List FTok)
  | 0, _, _, _, _ => none
  | f + 1, sc, ds, acc, .star :: ts =>
    match pSh f sc ds ts with
    | some (e, r) => pMulT f sc ds (.bin .mul acc e) r
    | none => none
  | _ + 1, _, _, acc, ts => some (acc, ts)
def pSh : Nat → FScope → List FDef → List FTok → Option (S × List FTok)
  | 0, _, _, _ => none
  | _ + 1, _, _, .minus :: .num _ :: .shl :: _ => none
  | _ + 1, _, _, .minus :: .num _ :: .shr :: _ => none
  | f + 1, sc, ds, ts =>
    match pApp f sc ds ts with
    | some (e, r) => pShT f sc ds e r
    | none => none
def pShT : Nat → FScope → List FDef → S → List FTok → Option (S × List FTok)
  | 0, _, _, _, _ => none
  | f + 1, sc, ds, acc, .shl :: .num k :: ts =>
    if k < 64 then pShT f sc ds (.sh true k.toNat acc) ts else none
  | f + 1, sc, ds, acc, .shr :: .num k :: ts =>
    if k < 64 then pShT f sc ds (.sh false k.toNat acc) ts else none
  | _ + 1, _, _, _, .shl :: _ => none
  | _ + 1, _, _, _, .shr :: _ => none
  | _ + 1, _, _, acc, ts => some (acc, ts)
/-- application: a call, a prelude op, `-n`, or a postfix atom -/
def pApp : Nat → FScope → List FDef → List FTok → Option (S × List FTok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, .krd :: .id x :: ts =>
    if isInp x sc then
      match pAtom f sc ds ts with
      | some (i, r) => some (.rd i, r)
      | none => none
    else none
  | _ + 1, sc, _, .klen :: .id x :: ts => if isInp x sc then some (.len, ts) else none
  | f + 1, sc, ds, .kput :: ts =>
    match pAtom f sc ds ts with
    | some (o, r) =>
      match pAtom f sc ds r with
      | some (e, r2) => some (.put o e, r2)
      | none => none
    | none => none
  | f + 1, sc, ds, .id g :: ts =>
    match fidx g sc 0 with
    | some i => pPost f sc ds (.var i) ts
    | none =>
      match fdef g ds 0 with
      | some (j, (_, hi, ps, _, fb)) =>
        -- a loop: the fuel first
        let fu := match fb with
          | .fn _ => some (S.anil, ts)
          | .lp _ _ => pFA f sc ts
        match fu with
        | some (fe, ts1) =>
          -- the input argument (if the callee takes it) must be the input itself
          let ts' := if hi then (match ts1 with | .id x :: r => if isInp x sc then some r else none | _ => none)
            else some ts1
          match ts' with
          | some r =>
            match pArgs f sc ds ps r with
            | some (as, r2) => some (match fb with | .fn _ => .call j as | .lp _ _ => .lcall j fe as, r2)
            | none => none
          | none => none
        | none => none
      | none => none
  | _ + 1, _, _, .minus :: .num n :: ts => some (.num (0 - n), ts)
  | f + 1, sc, ds, ts => pAtom f sc ds ts
/-- arguments, each checked against the parameter type -/
def pArgs : Nat → FScope → List FDef → List Ty → List FTok → Option (S × List FTok)
  | 0, _, _, _, _ => none
  | _ + 1, _, _, [], ts => some (.anil, ts)
  | f + 1, sc, ds, τ :: ps, ts =>
    match pAtom f sc ds ts with
    | some (e, r) =>
      if tyOf (tys sc) (e.low ds) = some τ then
        match pArgs f sc ds ps r with
        | some (es, r2) => some (.acons e es, r2)
        | none => none
      else none
    | none => none
/-- an atom with postfix projections -/
def pAtom : Nat → FScope → List FDef → List FTok → Option (S × List FTok)
  | 0, _, _, _ => none
  | _ + 1, _, _, .num n :: ts => some (.num n, ts)
  | _ + 1, _, _, .nil :: ts => some (.nil, ts)
  | f + 1, sc, ds, .id g :: ts =>
    match fidx g sc 0 with
    | some i => pPost f sc ds (.var i) ts
    | none =>
      match fdef g ds 0 with
      | some (j, (_, false, [], _, .fn _)) => some (.call j .anil, ts)
      | _ => none
  | f + 1, sc, ds, .lp :: ts =>
    match pE f sc ds ts with
    | some (e, .rp :: r) => pPost f sc ds e r
    | some (e, .comma :: r) =>
      match pTup f sc ds r with
      | some (e2, r2) =>
        -- every component TYPED (an untyped numeral component would be `Nat` in Lean)
        if (S.pair e e2).typed (flags sc) then pPost f sc ds (.pair e e2) r2 else none
      | none => none
    | _ => none
  | _, _, _, _ => none
/-- the rest of a tuple after a comma, through the `)` -/
def pTup : Nat → FScope → List FDef → List FTok → Option (S × List FTok)
  | 0, _, _, _ => none
  | f + 1, sc, ds, ts =>
    match pE f sc ds ts with
    | some (e, .rp :: r) => some (e, r)
    | some (e, .comma :: r) =>
      match pTup f sc ds r with
      | some (e2, r2) => some (.pair e e2, r2)
      | none => none
    | _ => none
def pPost : Nat → FScope → List FDef → S → List FTok → Option (S × List FTok)
  | 0, _, _, _, _ => none
  | f + 1, sc, ds, e, .p1 :: ts => pPost f sc ds (.fst e) ts
  | f + 1, sc, ds, e, .p2 :: ts => pPost f sc ds (.snd e) ts
  | _ + 1, _, _, e, ts => some (e, ts)
end

/- types: `UInt64`, `List UInt8` (`none` here: the caller decides input/output), `T × T`, `(T)` -/
mutual
def pTy : Nat → List FTok → Option (Option Ty × List FTok)
  | 0, _ => none
  | f + 1, ts =>
    match pTyA f ts with
    | some (some a, .times :: r) =>
      match pTy f r with
      | some (some b, r2) => some (some (.prod a b), r2)
      | some (none, r2) => some (some (.prod a .buf), r2)
      | none => none
    | some (none, .times :: r) =>
      match pTy f r with
      | some (some b, r2) => some (some (.prod .buf b), r2)
      | some (none, r2) => some (some (.prod .buf .buf), r2)
      | none => none
    | x => x
def pTyA : Nat → List FTok → Option (Option Ty × List FTok)
  | 0, _ => none
  | _ + 1, .kU64 :: ts => some (some .w, ts)
  | _ + 1, .kList :: .kU8 :: ts => some (none, ts)
  | f + 1, .lp :: ts =>
    match pTy f ts with
    | some (some t, .rp :: r) => some (some t, r)
    | some (none, .rp :: r) => some (none, r)
    | _ => none
  | _, _ => none
end

/-- parameters `(x y : T)`: (scope, has input, parameter types first first) -/
def pPars : Nat → FScope → Bool → List Ty → List FTok → Option (FScope × Bool × List Ty × List FTok)
  | 0, _, _, _, _ => none
  | f + 1, sc, hi, ps, .lp :: .id x :: ts =>
    match pNs f [x] ts with
    | some (xs, r) =>
      match pTy f r with
      | some (t, .rp :: r2) =>
        -- the input: `List UInt8` as the very first parameter, alone in its group
        let first := sc.isEmpty
        match t with
        | none =>
          if first && xs.length == 1 then pPars f ((x, none) :: sc) true ps r2
          else pPars f (xs.foldl (fun s y => (y, some (.buf, true)) :: s) sc) hi (ps ++ xs.map fun _ => .buf) r2
        | some τ => pPars f (xs.foldl (fun s y => (y, some (τ, true)) :: s) sc) hi (ps ++ xs.map fun _ => τ) r2
      | _ => none
    | none => none
  | _ + 1, sc, hi, ps, ts => some (sc, hi, ps, ts)
where pNs : Nat → List (List UInt8) → List FTok → Option (List (List UInt8) × List FTok)
  | 0, _, _ => none
  | f + 1, xs, .id y :: ts => pNs f (xs ++ [y]) ts
  | _ + 1, xs, .colon :: ts => some (xs, ts)
  | _, _, _ => none

/-! ## fuel loops: `def f : Nat → T₁ → … → R | 0, x₁, … => e₀ | n + 1, x₁, … => e`, self calls `f n a₁ …` only
in tail position (lowered to `Ex.loop`, the state = the parameters as a right-nested product, unpacked by `split`s) -/

/-- self: (name, fuel variable, has the input, state parameter types) -/
abbrev Me := List UInt8 × List UInt8 × Bool × List Ty

def lowCmp (k : SCmp) (a b : Ex) : Cmp × Ex × Ex :=
  match k with
  | .eq => (.eq, a, b)
  | .lt => (.lt, a, b)
  | .le => (.ge, b, a)

/-- a leaf of a tail: an ordinary expression, returned -/
def pRet (f : Nat) (sc : FScope) (ds : List FDef) (ts : List FTok) : Option (Tl × List FTok) :=
  match pE f sc ds ts with
  | some (e, r) => if good (e.sm (flags sc)) then some (.ret (e.low ds), r) else none
  | none => none

/-- a loop body (tail position) -/
def pT : Nat → Me → FScope → List FDef → List FTok → Option (Tl × List FTok)
  | 0, _, _, _, _ => none
  | f + 1, me, sc, ds, .klet :: .lp :: .id a :: .comma :: .id b :: .rp :: .assign :: ts =>
    match pE f sc ds ts with
    | some (v, .semi :: r) =>
      match tyOf (tys sc) (v.low ds) with
      | some (.prod τ σ) =>
        let t := v.typed (flags sc)
        if good (v.sm (flags sc)) then
          match pT f me ((b, some (σ, t)) :: (a, some (τ, t)) :: sc) ds r with
          | some (e, r2) => some (.split (v.low ds) e, r2)
          | none => none
        else none
      | _ => none
    | _ => none
  | f + 1, me, sc, ds, .klet :: .id x :: .assign :: ts =>
    match pE f sc ds ts with
    | some (v, .semi :: r) =>
      match tyOf (tys sc) (v.low ds) with
      | some τ =>
        if good (v.sm (flags sc)) then
          match pT f me ((x, some (τ, v.typed (flags sc))) :: sc) ds r with
          | some (b, r2) => some (.let_ (v.low ds) b, r2)
          | none => none
        else none
      | none => none
    | _ => none
  | f + 1, me, sc, ds, .kif :: ts =>
    match pOr f sc ds ts with
    | some (a, op :: r) =>
      match cmpS op with
      | some k =>
        match pOr f sc ds r with
        | some (b, .kthen :: r2) =>
          if (a.typed (flags sc) || b.typed (flags sc)) && good (comb (a.sm (flags sc)) (b.sm (flags sc))) then
            match pT f me sc ds r2 with
            | some (t, .kelse :: r3) =>
              match pT f me sc ds r3 with
              | some (e, r4) =>
                let q := lowCmp k (a.low ds) (b.low ds)
                some (.ite q.1 q.2.1 q.2.2 t e, r4)
              | none => none
            | _ => none
          else none
        | _ => none
      | none => none
    | _ => none
  | f + 1, me, sc, ds, .id g :: .id n :: ts =>
    if g == me.1 then
      if n == me.2.1 then
        let ts' := if me.2.2.1 then (match ts with | .id x :: r => if isInp x sc then some r else none | _ => none)
          else some ts
        match ts' with
        | some r =>
          match pArgs f sc ds me.2.2.2 r with
          | some (as, r2) =>
            if S.sm.smA (flags sc) as then some (.next (tup (S.low.lowA ds as)), r2) else none
          | none => none
        | none => none
      else none
    else pRet f sc ds (.id g :: .id n :: ts)
  | f + 1, _, sc, ds, ts => pRet f sc ds ts

/-- `T → T → …` -/
def pArr : Nat → List FTok → Option (List (Option Ty) × List FTok)
  | 0, _ => none
  | f + 1, ts =>
    match pTy f ts with
    | some (t, .arrow :: r) => (pArr f r).map fun (l, r2) => (t :: l, r2)
    | some (t, r) => some ([t], r)
    | none => none

/-- the pattern names `, x₁, …, xₖ =>` -/
def pAN : Nat → List FTok → Option (List (List UInt8) × List FTok)
  | 0, _ => none
  | f + 1, .comma :: .id v :: ts => (pAN f ts).map fun (l, r) => (v :: l, r)
  | _ + 1, .darrow :: ts => some ([], ts)
  | _, _ => none

/-- the scope inside the loop after unpacking the state (`unE`/`unT`); `[]` names the intermediate pairs -/
def bScope : List (List UInt8 × Ty) → FScope → FScope
  | [(p, τ)], below => (p, some (τ, true)) :: below
  | (p, τ) :: ps, below => bScope ps ((p, some (τ, true)) :: ([], some (tupT (τ :: ps.map (·.2)), true)) :: below)
  | [], below => below

def unE : Nat → Ex → Ex
  | k + 2, b => .split (.var 0) (unE (k + 1) b)
  | _, b => b
def unT : Nat → Tl → Tl
  | k + 2, b => .split (.var 0) (unT (k + 1) b)
  | _, b => b

/-- the scope of an arm: the input (if any) at the bottom, then the unpacked state -/
def armScope (hi : Bool) (names : List (List UInt8)) (ps : List Ty) : FScope :=
  let inp : FScope := if hi then (match names with | x :: _ => [(x, none)] | [] => []) else []
  bScope ((if hi then names.drop 1 else names).zip ps) inp

/-- a fuel-loop definition after `def g : Nat →` -/
def pLoop (f : Nat) (ds : List FDef) (g : List UInt8) (ts : List FTok) : Option (FDef × List FTok) :=
  match pArr f ts with
  | some (all, .bar :: .num 0 :: r) =>
    let params := all.dropLast
    let ρ : Ty := match all.getLast? with | some (some t) => t | _ => .buf
    let hi := match params with | none :: _ => true | _ => false
    let ps : List Ty := (if hi then params.drop 1 else params).map (·.getD .buf)
    let k := ps.length
    let σ := tupT ps
    match pAN f r with
    | some (n0, r1) =>
      if n0.length = params.length ∧ 0 < k then
        let sc0 := armScope hi n0 ps
        match pE f sc0 ds r1 with
        | some (z, .bar :: .id n :: .plus :: .num 1 :: r2) =>
          match pAN f r2 with
          | some (n1, r3) =>
            if n1.length = params.length then
              let sc1 := armScope hi n1 ps
              match pT f (g, n, hi, ps) sc1 ds r3 with
              | some (t, r4) =>
                let zE := unE k (z.low ds)
                let tT := unT k t
                if good (z.sm (flags sc0)) && tyOf [σ] zE == some ρ && tyT [σ] σ ρ tT && zE.aff [σ] &&
                    tT.aff [σ] && (!σ.hasBuf || decide (zE.occ 0 ≤ 1 ∧ tT.occ 0 ≤ 1)) then
                  some ((g, hi, ps, ρ, .lp zE tT), r4)
                else none
              | none => none
            else none
          | none => none
        | _ => none
      else none
    | none => none
  | _ => none

/-- the definitions; returns the defs (newest first) -/
def pDs : Nat → List FDef → List FTok → Option (List FDef)
  | 0, _, _ => none
  | f + 1, ds, .kdef :: .id g :: .colon :: .kNat :: .arrow :: ts =>
    match fdef g ds 0, pLoop f ds g ts with
    | none, some (d, []) => some (d :: ds)
    | none, some (d, r) => pDs f (d :: ds) r
    | _, _ => none
  | f + 1, ds, .kdef :: .id g :: ts =>
    match fdef g ds 0 with
    | some _ => none
    | none =>
      match pPars f [] false [] ts with
      | some (sc, hi, ps, .colon :: r) =>
        match pTy f r with
        | some (rt, .assign :: r2) =>
          let ρ := rt.getD .buf
          match pE f sc ds r2 with
          | some (e, r3) =>
            let b := e.low ds
            if good (e.sm (flags sc)) && tyOf (tys sc) b == some ρ && b.aff (tys sc) &&
                (tys sc).zipIdx.all (fun (τ, i) => !τ.hasBuf || decide (b.occ i ≤ 1)) then
              let d : FDef := (g, hi, ps, ρ, .fn b)
              match r3 with
              | [] => some (d :: ds)
              | _ => pDs f (d :: ds) r3
            else none
          | none => none
        | _ => none
      | _ => none
  | _, _, _ => none

/-- the program of the main (last) def `def m (x : List UInt8) : List UInt8`: Lean's `[]` (error) ↦ status 1 -/
def mainProg (b : Ex) : Prog where
  main := .let_ b (.ite .eq (.size (.var 0)) (.lit 0) (.pair (.lit 1) (.var 0)) (.pair (.lit 0) (.var 0)))

/-- **the v2 front end**, output capacity `κ` -/
def frontElabK (κ : Nat) (xs : List UInt8) : Option Prog :=
  match (if adjOk xs then flex xs.length xs else none) with
  | some ts =>
    match pDs (16 * (ts.length + 2)) [] ts with
    | some ((_, true, [], .buf, .fn b) :: _) => some (mainProg (b.cap κ))
    | _ => none
  | none => none

def frontElab : List UInt8 → Option Prog := frontElabK 65536

end Nano.V2B
