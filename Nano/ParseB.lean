/- nano stage 2 (branch `nano-parse`): the parser of `nanoElab` (`pDefs` … `pAtom`, `Nano/Elab.lean`) as an
explicit-stack machine that emits the NON-INLINED micro-op stream `serU u` (`Nano/SerU.lean`, `u = nanoElabU`'s
result; `nanoElab_eq`, `inlB_serU`: inlining is the next stage).

Layer A (this file): the machine on decoded tokens.  State: the rest of the tokens, the output so far, the run-time
depth `d`, the scope (name, slot) newest first, the defs (name, arity, number), the continuation stack.  A call
emits its arguments, then `[14, j / 256] [15, j % 256] [9, k]`.  The fuel of the recursive descent is replicated
exactly (every control carries it).  `run` iterates `step` with gas. -/
import Nano.SerU

namespace Nano.PB
open Nano

/-- continuation frames: what to do when the current parse function returns -/
inductive Fr where
  | letV (f : Nat) (x : List UInt8)
  | letB
  | exprAdd (f : Nat)
  | addOp (f : Nat) (op : UInt8)
  | mulT (f : Nat)
  | mulOp (f : Nat)
  | call (j k : Nat)
  | args (f k : Nat)
  | paren

/-- the parse function being run (with its fuel), or a return -/
inductive Ctl where
  | defs (f : Nat) | params (f n : Nat) | names (f fp n : Nat) | dbody
  | expr (f : Nat) | add (f : Nat) | mul (f : Nat) | mulT (f : Nat) | app (f : Nat) | args (f k : Nat)
  | atom (f : Nat) | ret

structure St where
  ts : List Tok
  out : List UInt8
  d : Nat
  sc : List (List UInt8 × Nat)
  ds : List (List UInt8 × Nat × Nat)
  K : List Fr
  cg : List UInt8
  cf : Nat
  na : Nat

inductive Res where
  | go (c : Ctl) (s : St)
  | done (o : List UInt8)
  | fail

/-- slot of a name in the scope (newest first) -/
def lookS (g : List UInt8) : List (List UInt8 × Nat) → Option Nat
  | [] => none
  | (x, k) :: r => if g == x then some k else lookS g r

/-- arity and number of a def -/
def findD (g : List UInt8) : List (List UInt8 × Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | (x, k, b) :: r => if g == x then some (k, b) else findD g r

/-- a call of def `j` with `k` arguments (after the arguments) -/
def sCall (j k : Nat) : List UInt8 := mo 14 (j / 256).toUInt8 ++ mo 15 (j % 256).toUInt8 ++ mo 9 k.toUInt8

/-- a variable read -/
def sVar (d k : Nat) : List UInt8 := mo 7 (d - 1 - k).toUInt8 ++ mo 3 0

def retF (s : St) : Fr → List Fr → Res
  | .letV f x, K =>
    match s.ts with
    | Tok.semi :: r => .go (.expr f) { s with ts := r, sc := (x, s.d - 1) :: s.sc, K := .letB :: K }
    | _ => .fail
  | .letB, K => .go .ret { s with out := s.out ++ mo 9 1, d := s.d - 1, sc := s.sc.tail, K := K }
  | .exprAdd f, K => .go (.add f) { s with K := K }
  | .addOp f op, K => .go (.add f) { s with out := s.out ++ mo 8 op, d := s.d - 1, K := K }
  | .mulT f, K => .go (.mulT f) { s with K := K }
  | .mulOp f, K => .go (.mulT f) { s with out := s.out ++ mo 8 40, d := s.d - 1, K := K }
  | .call j k, K => .go .ret { s with out := s.out ++ sCall j k, d := s.d + 1 - k, K := K }
  | .args f k, K => .go (.args f k) { s with K := K }
  | .paren, K =>
    match s.ts with
    | Tok.rp :: r => .go .ret { s with ts := r, K := K }
    | _ => .fail

/-- the end of a def body: `[13, arity]`; done if no token is left -/
def endDef (s : St) : Res :=
  match s.ts with
  | [] => .done (s.out ++ mo 13 s.na.toUInt8)
  | _ => .go (.defs s.cf) { s with out := s.out ++ mo 13 s.na.toUInt8, ds := (s.cg, s.na, s.ds.length) :: s.ds }

/-- a name in a parse position: variable, else `call` (arity checked by `onDef`) -/
def step : Ctl → St → Res
  | .defs f, s =>
    match f, s.ts with
    | f + 1, Tok.kdef :: Tok.id g :: ts => .go (.params f 0) { s with ts := ts, cg := g, cf := f, sc := [] }
    | _, _ => .fail
  | .params f n, s =>
    match f, s.ts with
    | 0, _ => .fail
    | f + 1, Tok.lp :: ts => .go (.names f f n) { s with ts := ts }
    | _ + 1, _ => .go .dbody { s with na := n }
  | .names f fp n, s =>
    match f, s.ts with
    | 0, _ => .fail
    | f + 1, Tok.id x :: ts => .go (.names f fp (n + 1)) { s with ts := ts, sc := (x, n) :: s.sc }
    | _ + 1, Tok.colon :: Tok.kty _ :: Tok.rp :: ts => .go (.params fp n) { s with ts := ts }
    | _, _ => .fail
  | .dbody, s =>
    match s.ts with
    | Tok.colon :: Tok.kty _ :: Tok.assign :: r =>
      match findD s.cg s.ds with
      | some _ => .fail
      | none => .go (.expr s.cf) { s with ts := r, d := s.na, K := [] }
    | _ => .fail
  | .ret, s =>
    match s.K with
    | [] => endDef s
    | fr :: K => retF s fr K
  | .expr f, s =>
    match f, s.ts with
    | 0, _ => .fail
    | f + 1, Tok.klet :: Tok.id x :: Tok.assign :: ts => .go (.expr f) { s with ts := ts, K := .letV f x :: s.K }
    | f + 1, _ => .go (.mul f) { s with K := .exprAdd f :: s.K }
  | .add f, s =>
    match f, s.ts with
    | 0, _ => .fail
    | f + 1, Tok.plus :: ts => .go (.mul f) { s with ts := ts, K := .addOp f 24 :: s.K }
    | f + 1, Tok.minus :: ts => .go (.mul f) { s with ts := ts, K := .addOp f 32 :: s.K }
    | _ + 1, _ => .go .ret s
  | .mul f, s =>
    match f with
    | 0 => .fail
    | f + 1 => .go (.app f) { s with K := .mulT f :: s.K }
  | .mulT f, s =>
    match f, s.ts with
    | 0, _ => .fail
    | f + 1, Tok.star :: ts => .go (.app f) { s with ts := ts, K := .mulOp f :: s.K }
    | _ + 1, _ => .go .ret s
  | .app f, s =>
    match f, s.ts with
    | 0, _ => .fail
    | f + 1, Tok.id g :: ts =>
      match lookS g s.sc with
      | some k => .go .ret { s with ts := ts, out := s.out ++ sVar s.d k, d := s.d + 1 }
      | none =>
        match findD g s.ds with
        | some (k, j) => .go (.args f k) { s with ts := ts, K := .call j k :: s.K }
        | none => .fail
    | _ + 1, Tok.minus :: Tok.num n :: ts =>
      .go .ret { s with ts := ts, out := s.out ++ (sLi (0 - n) ++ mo 3 0), d := s.d + 1 }
    | f + 1, _ => .go (.atom f) s
  | .args f k, s =>
    match f, k with
    | 0, _ => .fail
    | _ + 1, 0 => .go .ret s
    | f + 1, k + 1 => .go (.atom f) { s with K := .args f k :: s.K }
  | .atom f, s =>
    match f, s.ts with
    | 0, _ => .fail
    | _ + 1, Tok.num n :: ts => .go .ret { s with ts := ts, out := s.out ++ (sLi n ++ mo 3 0), d := s.d + 1 }
    | _ + 1, Tok.id g :: ts =>
      match lookS g s.sc with
      | some k => .go .ret { s with ts := ts, out := s.out ++ sVar s.d k, d := s.d + 1 }
      | none =>
        match findD g s.ds with
        | some (0, j) => .go .ret { s with ts := ts, out := s.out ++ sCall j 0, d := s.d + 1 }
        | _ => .fail
    | f + 1, Tok.lp :: ts => .go (.expr f) { s with ts := ts, K := .paren :: s.K }
    | _, _ => .fail

def run : Nat → Ctl → St → Option (List UInt8)
  | 0, _, _ => none
  | g + 1, c, s =>
    match step c s with
    | .go c' s' => run g c' s'
    | .done o => some o
    | .fail => none

def st0 (ts : List Tok) : St := ⟨ts, [], 0, [], [], [], [], 0, 0⟩

/-- layer A: the parser machine on tokens, gas `g` -/
def parseA (g : Nat) (ts : List Tok) : Option (List UInt8) := run g (.defs (ts.length + 1)) (st0 ts)

end Nano.PB
