/- Nano/V2Self/Proof/ParSpec: the REFERENCE GRAMMAR of the parser stage (Par1), independent of Par1's code.
`refParse ts = some p` (= `ParsesProgram ts p`): the Lex2 token words `ts` (format of Lex2Spec) parse to the resolved first-order program `p`
(`List DefA`: defs with npw / nslots / kind / nres and a resolved `Nd` body).  `serialize p` is the IR v2.1 word stream (Testing/notes/NANO_V2_IR.md).
Written as a plain recursive descent over decoded tokens (fuel = a bound that is never reached), one clause per grammar rule:
* tokens: Lex2's tag set minus the rejected ones (Int64 4, `≤` 21, `≠` 22, `&&` 24, `||` 25); idents `14 (1,b)* 0`, numbers `5` + 8 LE bytes;
* types: UInt64 / Buf / Nat = one word, `A × B` right-nested; the FIRST `List UInt8` parameter (alone in its binder group) is the implicit INPUT (width 0),
  every other `List UInt8` (later parameters, tuple components, results) is a one-word byte buffer;
* defs: `def f (a b : T) (c : U) : R := e` (kind 0, constants included: Par1 and Gen never emit kind 2) and the fuel loop
  `def f : Nat → T1 → … → Tk → R | 0, x1,…,xk => Z | n + 1, y1,…,yk => S` (kind 1; fuel = slot 0, states after; body `LOOP Z S`); callee before caller;
* expressions: `|||`55 `&&&`60 `+ -`65 `*`70 `<<< >>>`75 (left assoc, shift rhs = numeral), `if A (==|<) B then T else E`, `let x := v; b`,
  `let (a, b) := v; b` (a at the slot, b after `width a`), tuple literals (right-nested PAIR), application by juxtaposition (atoms), prims, `[]` = BNEW;
* scoping / slots: a `let` takes the next free slot AFTER its value is parsed (never reused), `nslots` = params + all let words; the innermost binding wins
  (resolved by binding, not spelling);
* calls: arguments match the callee's parameter shapes; the input argument is dropped (width 0); self-calls only in TAIL position of a loop's step arm
  (inherited into `if` branches, the `let` body, parentheses; cleared for conditions, operands, call arguments, `let` values, tuple fields), exactly
  `f n e1..ek` with `n` the fuel binder as RESOLVED, becoming `CONTINUE e` (flat PAIR of the non-input states, bare when one; a loop whose only state is the input is rejected: CONTINUE needs a payload);
* the program is a non-empty def list ending in `m (x : List UInt8) : List UInt8`.
Anything else is rejected (`none`). -/
import Nano.V2Self.C.Lex2Spec
namespace ParSpec

/-! ## tokens -/
inductive Tok | k (t : Nat) | num (v : Nat) | id (n : List Nat)
  deriving DecidableEq, Repr

def okTag (t : Nat) : Bool :=
  (t = 1 || t = 2 || t = 3 || (6 ≤ t && t ≤ 13) || (15 ≤ t && t ≤ 20) || t = 23 || (26 ≤ t && t ≤ 47))

def idn : List Nat → Option (List Nat × List Nat)
  | 0 :: r => some ([], r)
  | 1 :: b :: r => (idn r).map fun (n, r') => (b :: n, r')
  | _ => none

def bytesVal (bs : List Nat) : Nat := bs.foldr (fun b a => b + 256 * a) 0

/-- accumulating (reversed) so that long token streams run in constant stack -/
def detokA : Nat → List Nat → List Tok → Option (List Tok)
  | _, [], acc => some acc.reverse
  | 0, _, _ => none
  | f + 1, t :: r, acc =>
    if t = 5 then
      (if 8 ≤ r.length then detokA f (r.drop 8) (Tok.num (bytesVal (r.take 8)) :: acc) else none)
    else if t = 14 then (idn r).bind fun (n, r') => detokA f r' (Tok.id n :: acc)
    else if okTag t then detokA f r (Tok.k t :: acc) else none

def detok (f : Nat) (l : List Nat) : Option (List Tok) := detokA f l []

def tokens (ts : List UInt64) : Option (List Tok) := detok (ts.length + 1) (ts.map UInt64.toNat)

/-! ## shapes, types, resolved nodes -/
/-- leaves: `uw` UInt64, `bf` Buf, `ls` List UInt8 (as a value), `nt` Nat (fuel only: numerals and `len'`) -/
inductive Sh | uw | bf | ls | nt | p (a b : Sh) deriving DecidableEq, Repr
def Sh.width : Sh → Nat | .p a b => a.width + b.width | _ => 1
def Sh.hasN : Sh → Bool | .nt => true | .p a b => a.hasN || b.hasN | _ => false

/-- binding / parameter kinds -/
inductive Ps | inp | fuel | sh (s : Sh) deriving DecidableEq, Repr
def Ps.width : Ps → Nat | .inp => 0 | .fuel => 1 | .sh s => s.width

/-- type of an expression: a shape, a numeral (UInt64 or Nat), the input, or `bot` (a CONTINUE: never returns) -/
inductive Ty | s (s : Sh) | lit | inp | bot deriving DecidableEq, Repr
def Ty.join : Ty → Ty → Option Ty
  | .bot, t => some t
  | t, .bot => some t
  | .lit, .s .uw => some (.s .uw)
  | .s .uw, .lit => some (.s .uw)
  | a, b => if a = b then some a else none
/-- a UInt64 operand -/
def isU : Ty → Bool | .s .uw => true | .lit => true | _ => false
/-- the shape a value of this type has when stored (let / tuple); Nat is never stored -/
def tyShape : Ty → Option Sh
  | .s s => if s.hasN then none else some s
  | .lit => some .uw
  | _ => none

inductive Nd
  | const (v : UInt64) | loc (slot w : Nat) | bin (op : Nat) (a b : Nd) | ite (cmp : Nat) (a b t e : Nd)
  | letE (slot w : Nat) (v b : Nd) | pair (cs : List Nd) | call (id : Nat) (args : List Nd) | prim (p : Nat) (args : List Nd)
  | loop (z s : Nd) | cont (e : Nd)
  deriving Repr

structure DefI where
  name : List Nat
  params : List Ps
  res : Sh
  resLst : Bool
  npw : Nat

structure Cx where
  defs : List DefI
  env : List (List Nat × Nat × Ps)
  self : Option (List Nat × List Ps)

abbrev Res := Option (Nd × Ty × List Tok × Nat)

def opInfo : Nat → Option (Nat × Nat)
  | 27 => some (5, 55) | 26 => some (4, 60) | 10 => some (1, 65) | 11 => some (2, 65) | 12 => some (3, 70)
  | 28 => some (6, 75) | 29 => some (7, 75) | _ => none

/-- prim signatures for tags 39..47: (prim id, parameter kinds incl. the input, result shape) -/
def primSig : Nat → Option (Nat × List Ps × Sh)
  | 39 => some (1, [.inp], .nt) | 40 => some (2, [.inp, .sh .uw], .uw) | 41 => some (3, [.inp], .uw)
  | 42 => some (4, [.sh .ls, .sh .uw], .ls) | 43 => some (5, [], .bf) | 44 => some (6, [.sh .bf], .uw)
  | 45 => some (7, [.sh .bf, .sh .uw], .uw) | 46 => some (8, [.sh .bf, .sh .uw, .sh .uw], .bf) | 47 => some (9, [.sh .bf, .sh .uw], .bf)
  | _ => none

def tyMatch : Ps → Ty → Bool
  | .inp, .inp => true
  | .sh s, .s t => s == t
  | .sh .uw, .lit => true
  | .fuel, .s .nt => true
  | .fuel, .lit => true
  | _, _ => false

/-- keep the non-input arguments, in order -/
def dropInp (ps : List Ps) (as : List Nd) : List Nd :=
  (List.zip ps as).filterMap fun (p, a) => match p with | .inp => none | _ => some a

def mkPairFlat : List Nd → Nd | [c] => c | cs => .pair cs

def findEnv (env : List (List Nat × Nat × Ps)) (n : List Nat) : Option (Nat × Ps) :=
  (env.find? fun e => e.1 == n).map fun e => e.2

def findDef (defs : List DefI) (n : List Nat) : Option (Nat × DefI) :=
  (defs.zipIdx.find? fun e => e.1.name == n).map fun e => (e.2, e.1)

mutual
/-- a full expression: `if`, `let`, or a binary expression; `tl` = tail position -/
def pExpr : Nat → Cx → Bool → List Tok → Nat → Res
  | 0, _, _, _, _ => none
  | f + 1, cx, tl, .k 2 :: .id x :: .k 9 :: r, nx =>
    (pExpr f cx false r nx).bind fun (v, tv, r1, nx1) =>
      match tyShape tv, r1 with
      | some s, .k 13 :: r2 =>
        (pExpr f { cx with env := (x, nx1, .sh s) :: cx.env } tl r2 (nx1 + s.width)).map fun (b, tb, r3, nx3) =>
          (.letE nx1 s.width v b, tb, r3, nx3)
      | _, _ => none
  | f + 1, cx, tl, .k 2 :: .k 6 :: .id x :: .k 15 :: .id y :: .k 7 :: .k 9 :: r, nx =>
    (pExpr f cx false r nx).bind fun (v, tv, r1, nx1) =>
      match tyShape tv, r1 with
      | some (.p l rr), .k 13 :: r2 =>
        (pExpr f { cx with env := (y, nx1 + l.width, .sh rr) :: (x, nx1, .sh l) :: cx.env } tl r2 (nx1 + l.width + rr.width)).map
          fun (b, tb, r3, nx3) => (.letE nx1 (l.width + rr.width) v b, tb, r3, nx3)
      | _, _ => none
  | f + 1, cx, tl, .k 32 :: r, nx =>
    (pBin f cx false 0 r nx).bind fun (a, ta, r1, nx1) =>
      match isU ta, r1 with
      | true, .k c :: r2 =>
        if c = 23 ∨ c = 20 then
          (pBin f cx false 0 r2 nx1).bind fun (b, tb, r3, nx2) =>
            match isU tb, r3 with
            | true, .k 33 :: r4 =>
              (pExpr f cx tl r4 nx2).bind fun (t, tt, r5, nx3) =>
                match r5 with
                | .k 34 :: r6 =>
                  (pExpr f cx tl r6 nx3).bind fun (e, te, r7, nx4) =>
                    (tt.join te).map fun ty => (.ite (if c = 23 then 1 else 2) a b t e, ty, r7, nx4)
                | _ => none
            | _, _ => none
        else none
      | _, _ => none
  | f + 1, cx, tl, ts, nx => pBin f cx tl 0 ts nx

/-- precedence climbing; the first operand inherits the tail flag only when no operator follows it -/
def pBin : Nat → Cx → Bool → Nat → List Tok → Nat → Res
  | 0, _, _, _, _, _ => none
  | f + 1, cx, tl, minp, ts, nx =>
    (pApp f cx tl ts nx).bind fun (a, ta, r, nx1) =>
      match tl, r with
      | true, .k t :: _ =>
        -- an operator follows: the first operand is NOT in tail position (so no self-call inside it, however nested)
        if (opInfo t).isSome then (pApp f cx false ts nx).bind fun (a', ta', r', nx') => pLoop f cx minp a' ta' r' nx'
        else pLoop f cx minp a ta r nx1
      | _, _ => pLoop f cx minp a ta r nx1

def pLoop : Nat → Cx → Nat → Nd → Ty → List Tok → Nat → Res
  | 0, _, _, _, _, _, _ => none
  | f + 1, cx, minp, a, ta, ts, nx =>
    match ts with
    | .k t :: r =>
      match opInfo t with
      | some (op, p) =>
        if p < minp then some (a, ta, ts, nx) else
        if isU ta then
          if t = 28 ∨ t = 29 then
            match r with
            | .num k :: r' => pLoop f cx minp (.bin op a (.const (UInt64.ofNat k))) (.s .uw) r' nx
            | _ => none
          else
            (pBin f cx false (p + 1) r nx).bind fun (b, tb, r', nx') =>
              if isU tb then pLoop f cx minp (.bin op a b) (.s .uw) r' nx' else none
        else none
      | none => some (a, ta, ts, nx)
    | _ => some (a, ta, ts, nx)

/-- an application head (prim / call / self-call) or an atom -/
def pApp : Nat → Cx → Bool → List Tok → Nat → Res
  | 0, _, _, _, _ => none
  | f + 1, cx, tl, .k t :: r, nx =>
    match primSig t with
    | some (pid, ps, rs) =>
      (pArgs f cx ps r nx).map fun (as, r1, nx1) => (.prim pid (dropInp ps (as.map (·.1))), .s rs, r1, nx1)
    | none => pAtom f cx tl (.k t :: r) nx
  | f + 1, cx, tl, .id n :: r, nx =>
    match findEnv cx.env n with
    | some _ => pAtom f cx tl (.id n :: r) nx
    | none =>
      match cx.self with
      | some (sn, sps) =>
        if sn == n then
          if tl then
            match r with
            | .id fn :: r1 =>
              match findEnv cx.env fn with
              | some (_, .fuel) =>
                (pArgs f cx sps r1 nx).bind fun (as, r2, nx2) =>
                  match dropInp sps (as.map (·.1)) with
                  | [] => none
                  | cs => some (.cont (mkPairFlat cs), .bot, r2, nx2)
              | _ => none
            | _ => none
          else none
        else pCallDef f cx n r nx
      | none => pCallDef f cx n r nx
  | f + 1, cx, tl, ts, nx => pAtom f cx tl ts nx

def pCallDef : Nat → Cx → List Nat → List Tok → Nat → Res
  | 0, _, _, _, _ => none
  | f + 1, cx, n, r, nx =>
    match findDef cx.defs n with
    | some (id, d) =>
      (pArgs f cx d.params r nx).map fun (as, r1, nx1) => (.call id (dropInp d.params (as.map (·.1))), .s d.res, r1, nx1)
    | none => none

/-- exactly one atom per parameter -/
def pArgs : Nat → Cx → List Ps → List Tok → Nat → Option (List (Nd × Ty) × List Tok × Nat)
  | 0, _, _, _, _ => none
  | _ + 1, _, [], ts, nx => some ([], ts, nx)
  | f + 1, cx, p :: ps, ts, nx =>
    (pAtom f cx false ts nx).bind fun (a, ta, r1, nx1) =>
      if tyMatch p ta then (pArgs f cx ps r1 nx1).map fun (as, r2, nx2) => ((a, ta) :: as, r2, nx2) else none

/-- atoms: numeral, variable, constant, `[]`, `bnew`, parenthesised expression / tuple -/
def pAtom : Nat → Cx → Bool → List Tok → Nat → Res
  | 0, _, _, _, _ => none
  | _ + 1, _, _, .num v :: r, nx => some (.const (UInt64.ofNat v), .lit, r, nx)
  | _ + 1, _, _, .k 30 :: .k 31 :: r, nx => some (.prim 5 [], .s .ls, r, nx)
  | _ + 1, _, _, .k 43 :: r, nx => some (.prim 5 [], .s .bf, r, nx)
  | _ + 1, cx, _, .id n :: r, nx =>
    match findEnv cx.env n with
    | some (slot, .sh s) => some (.loc slot s.width, .s s, r, nx)
    | some (slot, .inp) => some (.loc slot 0, .inp, r, nx)
    | some (_, .fuel) => none
    | none =>
      match findDef cx.defs n with
      | some (id, d) => if d.params.isEmpty then some (.call id [], .s d.res, r, nx) else none
      | none => none
  | f + 1, cx, tl, .k 6 :: r, nx =>
    (pExpr f cx tl r nx).bind fun (e, t, r1, nx1) =>
      match r1 with
      | .k 7 :: r2 => some (e, t, r2, nx1)
      | .k 15 :: _ =>
        (pExpr f cx false r nx).bind fun (e1, t1, r1', nx1') =>
          match tyShape t1 with
          | some s1 => (pTup f cx r1' nx1').map fun (tl', st, r3, nx3) => (.pair [e1, tl'], .s (.p s1 st), r3, nx3)
          | _ => none
      | _ => none
  | _ + 1, _, _, _, _ => none

/-- `, e2 , … , en )` → the right-nested remainder -/
def pTup : Nat → Cx → List Tok → Nat → Option (Nd × Sh × List Tok × Nat)
  | 0, _, _, _ => none
  | f + 1, cx, .k 15 :: r, nx =>
    (pExpr f cx false r nx).bind fun (e, t, r1, nx1) =>
      match tyShape t, r1 with
      | some s, .k 7 :: r2 => some (e, s, r2, nx1)
      | some s, .k 15 :: _ => (pTup f cx r1 nx1).map fun (rest, sr, r3, nx3) => (.pair [e, rest], .p s sr, r3, nx3)
      | _, _ => none
  | _ + 1, _, _, _ => none
end

/-! ## types -/
inductive TyR | sh (s : Sh) | lst
def trRes : TyR → Sh | .sh s => s | .lst => .ls

mutual
def pTyAtom : Nat → List Tok → Option (TyR × List Tok)
  | 0, _ => none
  | _ + 1, .k 3 :: r => some (.sh .uw, r)
  | _ + 1, .k 36 :: r => some (.sh .bf, r)
  | _ + 1, .k 35 :: r => some (.sh .nt, r)
  | _ + 1, .k 37 :: .k 38 :: r => some (.lst, r)
  | f + 1, .k 6 :: r => (pTy f r).bind fun (t, r1) => match r1 with | .k 7 :: r2 => some (t, r2) | _ => none
  | _ + 1, _ => none
def pTy : Nat → List Tok → Option (TyR × List Tok)
  | 0, _ => none
  | f + 1, ts => (pTyAtom f ts).bind fun (a, r) =>
    match r with
    | .k 16 :: r1 => (pTy f r1).bind fun (b, r2) =>
        some (.sh (.p (trRes a) (trRes b)), r2)
    | _ => some (a, r)
end

/-! ## defs -/
structure DefA where
  id : Nat
  npw : Nat
  nslots : Nat
  kind : Nat
  nres : Nat
  body : Nd

/-- binder groups `(a b : T)` -/
def pBinders : Nat → Bool → List Tok → Option (List (List (List Nat) × TyR) × List Tok)
  | 0, _, _ => none
  | f + 1, first, .k 6 :: r =>
    let rec ids : List Tok → Option (List (List Nat) × List Tok)
      | .id a :: r => (ids r).map fun (l, r') => (a :: l, r')
      | r => some ([], r)
    (ids r).bind fun (ns, r1) =>
      match ns, r1 with
      | _ :: _, .k 8 :: r2 =>
        (pTy f r2).bind fun (t, r3) =>
          match r3, t with
          | .k 7 :: r4, .sh _ => (pBinders f false r4).map fun (g, r5) => ((ns, t) :: g, r5)
          | .k 7 :: r4, .lst => (pBinders f false r4).map fun (g, r5) => ((ns, t) :: g, r5)
          | _, _ => none
      | _, _ => none
  | _ + 1, _, ts => some ([], ts)

/-- `T → T → … → R` arrow chain -/
def pArrows : Nat → List Tok → Option (List TyR × List Tok)
  | 0, _ => none
  | f + 1, ts => (pTy f ts).bind fun (t, r) =>
    match r with
    | .k 17 :: r1 => (pArrows f r1).map fun (l, r2) => (t :: l, r2)
    | _ => some ([t], r)

/-- parameter kind of a typed group: the first `List UInt8` alone in its group is the input, any other one a word -/
def pickPs (used : Bool) (single : Bool) : TyR → Ps × Bool
  | .sh s => (.sh s, used)
  | .lst => if !used && single then (.inp, true) else (.sh .ls, used)

/-- the parameters of a binder list: (name, slot, Ps) and the parameter kinds -/
def bindSlots (start : Nat) (used : Bool) : List (List (List Nat) × TyR) → (List (List Nat × Nat × Ps) × List Ps × Nat)
  | [] => ([], [], start)
  | (ns, t) :: g =>
    let (p, used') := pickPs used (ns.length == 1) t
    let rec go (s : Nat) : List (List Nat) → (List (List Nat × Nat × Ps) × List Ps × Nat)
      | [] => ([], [], s)
      | n :: l =>
        let (e, ps, s') := go (s + p.width) l
        ((n, s, p) :: e, p :: ps, s')
    let (e, ps, s') := go start ns
    let (e2, ps2, s2) := bindSlots s' used' g
    (e ++ e2, ps ++ ps2, s2)

/-- loop states: one type per state -/
def stateKinds : Bool → List TyR → List Ps
  | _, [] => []
  | used, t :: ts => let (p, u) := pickPs used true t; p :: stateKinds u ts

def armPat (n : Nat) : List Tok → Option (List (List Nat) × List Tok)
  | .k 19 :: r => some ([], r)
  | .k 15 :: .id a :: r => (armPat n r).map fun (l, r') => (a :: l, r')
  | _ => none

def mkEnv (start : Nat) : List Ps → List (List Nat) → Option (List (List Nat × Nat × Ps))
  | [], [] => some []
  | p :: ps, n :: ns => (mkEnv (start + p.width) ps ns).map fun e => (n, start, p) :: e
  | _, _ => none

def tyOk (res : Sh) (t : Ty) : Bool := match t with | .s s => s == res | .lit => res == .uw | _ => false

/-- one def; returns the def info, its output and the rest -/
def pDef (fuel : Nat) (defs : List DefI) : List Tok → Option (DefI × DefA × List Tok)
  | .k 1 :: .id name :: ts =>
    if (findDef defs name).isSome then none else
    match ts with
    | .k 8 :: .k 35 :: .k 17 :: r =>
      -- fuel loop
      (pArrows fuel r).bind fun (tys, r1) =>
        match tys.reverse with
        | resT :: revSt =>
          let sts := revSt.reverse
          let ps : List Ps := stateKinds false sts
          let res := trRes resT
          if res.hasN || ps.any (fun p => match p with | .sh s => s.hasN | _ => false) then none else
          let npw := 1 + (ps.map Ps.width).foldl (· + ·) 0
          match r1 with
          | .k 18 :: .num 0 :: r2 =>
            (armPat 0 r2).bind fun (zn, r3) =>
              if zn.eraseDups.length != zn.length then none else
              (mkEnv 1 ps zn).bind fun envZ =>
                let cx0 : Cx := { defs := defs, env := envZ.reverse, self := none }
                (pExpr fuel cx0 false r3 npw).bind fun (z, tz, r4, nx1) =>
                  if !tyOk res tz then none else
                  match r4 with
                  | .k 18 :: .id nb :: .k 10 :: .num 1 :: r5 =>
                    (armPat 0 r5).bind fun (sn, r6) =>
                      if (nb :: sn).eraseDups.length != sn.length + 1 then none else
                      (mkEnv 1 ps sn).bind fun envS =>
                        let cx1 : Cx := { defs := defs, env := (nb, 0, .fuel) :: envS.reverse, self := some (name, ps) }
                        (pExpr fuel cx1 true r6 nx1).bind fun (s, ts', r7, nx2) =>
                          match ts'.join (.s res) with
                          | some (.s _) =>
                            some ({ name, params := .fuel :: ps, res, resLst := false, npw },
                                  { id := defs.length, npw, nslots := nx2, kind := 1, nres := res.width, body := .loop z s }, r7)
                          | _ => none
                  | _ => none
          | _ => none
        | [] => none
    | _ =>
      -- plain def / constant
      (pBinders fuel true ts).bind fun (groups, r1) =>
        match r1 with
        | .k 8 :: r2 =>
          (pTy fuel r2).bind fun (resT, r3) =>
            match r3 with
            | .k 9 :: r4 =>
              let (env, ps, npw) := bindSlots 0 false groups
              if (trRes resT).hasN || ps.any (fun p => match p with | .sh s => s.hasN | _ => false) then none else
              let cx0 : Cx := { defs := defs, env := env.reverse, self := none }
              (pExpr fuel cx0 false r4 npw).bind fun (b, tb, r5, nx) =>
                let res := trRes resT
                if !tyOk res tb then none else
                some ({ name, params := ps, res, resLst := (match resT with | .lst => true | _ => false), npw },
                      { id := defs.length, npw, nslots := nx, kind := 0, nres := res.width, body := b }, r5)
            | _ => none
        | _ => none
  | _ => none

def pDefs (fuel : Nat) : Nat → List DefI → List Tok → Option (List DefI × List DefA)
  | 0, _, _ => none
  | _ + 1, defs, [] => some (defs, [])
  | f + 1, defs, ts =>
    (pDef fuel defs ts).bind fun (di, da, r) =>
      (pDefs fuel f (defs ++ [di]) r).map fun (ds, as) => (ds, da :: as)

def isMain (d : DefI) : Bool := d.name == [109] && d.params == [.inp] && d.resLst

def refParse (ts : List UInt64) : Option (List DefA) :=
  (tokens ts).bind fun toks =>
    let fuel := 8 * toks.length + 8
    (pDefs fuel (toks.length + 1) [] toks).bind fun (ds, as) =>
      match ds.getLast? with
      | some d => if isMain d then some as else none
      | none => none

def ParsesProgram (ts : List UInt64) (p : List DefA) : Prop := refParse ts = some p

/-! ## serialization: IR v2.1 -/
mutual
def Nd.ser : Nd → List UInt64
  | .const v => [1, v]
  | .loc s w => [2, s.toUInt64, w.toUInt64]
  | .bin op a b => 3 :: op.toUInt64 :: (a.ser ++ b.ser)
  | .ite c a b t e => 4 :: c.toUInt64 :: (a.ser ++ b.ser ++ t.ser ++ e.ser)
  | .letE s w v b => 5 :: s.toUInt64 :: w.toUInt64 :: (v.ser ++ b.ser)
  | .pair cs => 6 :: cs.length.toUInt64 :: serL cs
  | .call i as => 8 :: i.toUInt64 :: as.length.toUInt64 :: serL as
  | .prim p as => 9 :: p.toUInt64 :: serL as
  | .loop z s => 10 :: (z.ser ++ s.ser)
  | .cont e => 11 :: e.ser
def serL : List Nd → List UInt64
  | [] => []
  | n :: r => n.ser ++ serL r
end

def DefA.ser (d : DefA) : List UInt64 :=
  [20, d.id.toUInt64, d.npw.toUInt64, d.nslots.toUInt64, d.kind.toUInt64, d.nres.toUInt64] ++ d.body.ser ++ [21]

def serialize (p : List DefA) : List UInt64 := 2 :: p.flatMap DefA.ser

/-! ## examples: source text → Lex2 spec → refParse → serialize -/
def lexAcc : Nat → List UInt8 → List UInt64 → Option (List UInt64)
  | _, [], acc => some acc.reverse
  | 0, _, _ => none
  | f + 1, l, acc => (LexSpec.step l).bind fun (e, r) => lexAcc f r (e.reverse ++ acc)

def lexAll (f : Nat) (l : List UInt8) : Option (List UInt64) := lexAcc f l []

def parseStr (s : String) : Option (List UInt64) :=
  (lexAll (s.length + 1) s.toUTF8.toList).bind fun ts => (refParse ts).map serialize

/-! ### accepted programs (expected words hand-decoded against NANO_V2_IR.md) -/
-- 1. two defs: BIN, CONST, prims (RD keeps only its index; PUT/BNEW), a CALL with a prim argument; main = `DEF 0 0 nslots 0 1`
def ex1 : String := "def a (p q : UInt64) : UInt64 := p + q * 3
def m (x : List UInt8) : List UInt8 := put [] (a (rd x 0) 2)"
#guard parseStr ex1 = some [2,
  20, 0, 2, 2, 0, 1,  3, 1, 2, 0, 1,  3, 3, 2, 1, 1,  1, 3,  21,
  20, 1, 0, 0, 0, 1,  9, 4, 9, 5,  8, 0, 2,  9, 2, 1, 0,  1, 2,  21]
-- 2. let slots (c at 2, the pair (d, e) at 3..4: nslots 5), pair-let, `<`, tuple literals, a pair-valued call
def ex2 : String := "def f (a b : UInt64) : UInt64 × UInt64 := let c := a + b; let (d, e) := (c, a); if d < e then (d, e) else (e, d)
def m (x : List UInt8) : List UInt8 := let (u, v) := f 1 2; put (put [] u) v"
#guard parseStr ex2 = some [2,
  20, 0, 2, 5, 0, 2,  5, 2, 1,  3, 1, 2, 0, 1, 2, 1, 1,  5, 3, 2,  6, 2, 2, 2, 1, 2, 0, 1,
    4, 2,  2, 3, 1, 2, 4, 1,  6, 2, 2, 3, 1, 2, 4, 1,  6, 2, 2, 4, 1, 2, 3, 1,  21,
  20, 1, 0, 2, 0, 1,  5, 0, 2,  8, 0, 2, 1, 1, 1, 2,  9, 4, 9, 4, 9, 5, 2, 0, 1, 2, 1, 1,  21]
-- 3. a fuel loop: fuel = slot 0, state p = slot 1 (the input has width 0), `LOOP zero step`, the tail call is `CONTINUE (p + 1)`
def ex3 : String := "def g : Nat → List UInt8 → UInt64 → UInt64
  | 0, x, p => p
  | n + 1, x, p => if p < len x then g n x (p + 1) else p
def m (x : List UInt8) : List UInt8 := put [] (g (len' x) x 0)"
#guard parseStr ex3 = some [2,
  20, 0, 2, 2, 1, 1,  10,  2, 1, 1,  4, 2, 2, 1, 1, 9, 3,  11, 3, 1, 2, 1, 1, 1, 1,  2, 1, 1,  21,
  20, 1, 0, 0, 0, 1,  9, 4, 9, 5,  8, 0, 2, 9, 1, 1, 0,  21]
-- 4. a constant def, shadowing (innermost binding wins, resolved by binding), `let` inside parentheses, an if in a tail `let` body
def ex4 : String := "def k : UInt64 := 7
def m (x : List UInt8) : List UInt8 := let a := k; let a := (let a := a + 1; a * a); put [] a"
#guard (parseStr ex4).isSome

/-! ### rejected programs -/
-- the five Par1 gaps found by the differential fuzz (now fixed in Par1): input as data / as the body, rd on a non-input list,
-- `List <not UInt8>`, a loop whose only state is the input, duplicate pattern binders
#guard parseStr "def m (x : List UInt8) : List UInt8 := put x 1" = none
#guard parseStr "def m (x : List UInt8) : List UInt8 := x" = none
#guard parseStr "def m (x : List UInt8) : List UInt8 := let y := x; []" = none
#guard parseStr "def g (z : List UInt8) (a : List UInt8) : UInt64 := rd a 0\ndef m (x : List UInt8) : List UInt8 := []" = none
#guard parseStr "def g (z : List def) : UInt64 := 1\ndef m (x : List UInt8) : List UInt8 := []" = none
#guard parseStr "def f : Nat → List UInt8 → UInt64 × UInt64\n  | 0, z => (1, 2)\n  | n + 1, z => f n z\ndef m (x : List UInt8) : List UInt8 := []" = none
#guard parseStr "def f : Nat → UInt64 → UInt64 → UInt64\n  | 0, a, a => a\n  | n + 1, a, b => a\ndef m (x : List UInt8) : List UInt8 := []" = none
#guard parseStr "def f : Nat → UInt64 → UInt64\n  | 0, a => a\n  | n + 1, n => n\ndef m (x : List UInt8) : List UInt8 := []" = none
-- input / non-input List arguments swapped (call and CONTINUE); the matching programs are accepted
#guard (parseStr "def f (z : List UInt8) (a : List UInt8) : UInt64 := 1\ndef m (x : List UInt8) : List UInt8 := put [] (f x [])").isSome
#guard parseStr "def f (z : List UInt8) (a : List UInt8) : UInt64 := 1\ndef m (x : List UInt8) : List UInt8 := put [] (f [] x)" = none
#guard parseStr "def f (z : List UInt8) (a : List UInt8) : UInt64 := 1\ndef m (x : List UInt8) : List UInt8 := put [] (f x x)" = none
#guard (parseStr "def f : Nat → List UInt8 → List UInt8 → UInt64\n  | 0, z, a => 1\n  | n + 1, z, a => f n z []\ndef m (x : List UInt8) : List UInt8 := put [] (f 3 x [])").isSome
#guard parseStr "def f : Nat → List UInt8 → List UInt8 → UInt64\n  | 0, z, a => 1\n  | n + 1, z, a => f n [] z\ndef m (x : List UInt8) : List UInt8 := put [] (f 3 x [])" = none
#guard parseStr "def f : Nat → List UInt8 → List UInt8 → UInt64\n  | 0, z, a => 1\n  | n + 1, z, a => f n z z\ndef m (x : List UInt8) : List UInt8 := put [] (f 3 x [])" = none
def mainTail : String := "\ndef m (x : List UInt8) : List UInt8 := []"
-- non-tail self-call (`f n s + 1`), also parenthesised
#guard parseStr ("def g : Nat → UInt64 → UInt64\n  | 0, p => p\n  | n + 1, p => g n p + 1" ++ mainTail) = none
#guard parseStr ("def g : Nat → UInt64 → UInt64\n  | 0, p => p\n  | n + 1, p => (g n p) + 1" ++ mainTail) = none
-- a self-call nested in a parenthesised `if` that is the left operand of `+` is not in tail position either
#guard parseStr ("def g : Nat → UInt64 → UInt64\n  | 0, p => p\n  | n + 1, p => (if p < 3 then g n p else p) + 1" ++ mainTail) = none
-- tail self-call is fine (control)
#guard (parseStr ("def g : Nat → UInt64 → UInt64\n  | 0, p => p\n  | n + 1, p => if p < 3 then g n (p + 1) else p" ++ mainTail)).isSome
-- fuel as data; self-call in a let value; self-call with the wrong arity; fuel binder shadowed by a let
#guard parseStr ("def g : Nat → UInt64 → UInt64\n  | 0, p => p\n  | n + 1, p => p + n" ++ mainTail) = none
#guard parseStr ("def g : Nat → UInt64 → UInt64\n  | 0, p => p\n  | n + 1, p => let q := g n p; q" ++ mainTail) = none
#guard parseStr ("def g : Nat → UInt64 → UInt64\n  | 0, p => p\n  | n + 1, p => g n p p" ++ mainTail) = none
#guard parseStr ("def g : Nat → UInt64 → UInt64\n  | 0, p => p\n  | n + 1, p => let n := 5; g n p" ++ mainTail) = none
-- unbound name, use before definition, recursion in a plain def, shift by a variable, input used as data
#guard parseStr "def m (x : List UInt8) : List UInt8 := put [] y" = none
#guard parseStr "def a (p : UInt64) : UInt64 := b p\ndef b (p : UInt64) : UInt64 := p\ndef m (x : List UInt8) : List UInt8 := []" = none
#guard parseStr "def a (p : UInt64) : UInt64 := a p\ndef m (x : List UInt8) : List UInt8 := []" = none
#guard parseStr "def a (p q : UInt64) : UInt64 := p <<< q\ndef m (x : List UInt8) : List UInt8 := []" = none
#guard parseStr "def m (x : List UInt8) : List UInt8 := let y := x; bnew" = none
-- width mismatches: call arity / argument shape, tuple let on a word, if branches of different shape
#guard parseStr "def a (p q : UInt64) : UInt64 := p\ndef m (x : List UInt8) : List UInt8 := put [] (a 1)" = none
#guard parseStr "def a (p : UInt64 × UInt64) : UInt64 := let (u, v) := p; u\ndef m (x : List UInt8) : List UInt8 := put [] (a 1)" = none
#guard parseStr "def a (p : UInt64) : UInt64 := let (u, v) := p; u\ndef m (x : List UInt8) : List UInt8 := []" = none
#guard parseStr "def a (p : UInt64) : UInt64 × UInt64 := if p < 1 then (p, p) else p\ndef m (x : List UInt8) : List UInt8 := []" = none
-- tokens outside the restricted set, missing/misshapen main, duplicate def names, trailing junk
#guard parseStr "def a (p : UInt64) : UInt64 := if p ≤ 1 then p else 2\ndef m (x : List UInt8) : List UInt8 := []" = none
#guard parseStr "def a (p : UInt64) : UInt64 := p" = none
#guard parseStr "def m (x : List UInt8) : UInt64 := 1" = none
#guard parseStr "def a (p : UInt64) : UInt64 := p\ndef a (p : UInt64) : UInt64 := p\ndef m (x : List UInt8) : List UInt8 := []" = none
#guard parseStr "def m (x : List UInt8) : List UInt8 := [] )" = none

end ParSpec
