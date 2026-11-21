/- Nano/Expr/Eval: an evaluator for the Expr fragment `X` (EXPR.md §6 step 1). Values are the run-time values of
nano's types; constants are a closed table with their Lean meaning (the prelude, the ops, `ite`, `Prod`, `Nat`);
user defs are looked up by name. Fuel bounds the evaluation (each def call costs 1), so `evalX` is total. Step 2
(`eval_emit : evalX (emitXs p) = Sem κC p` where Sem has a result) is next; the #guards below are non-vacuity
witnesses. -/
import Nano.Expr.ExprSpec
namespace ExprSpec

inductive V | w (v : UInt64) | n (v : Nat) | b (v : List UInt64) | l (v : List UInt8) | p (a b : V)
  deriving Repr, DecidableEq, Inhabited

/-- head constant and arguments of an application spine -/
def spine : X → X × List X
  | .app f a => let (h, as) := spine f; (h, as ++ [a])
  | e => (e, [])

def binV (f : String) (a b : UInt64) : Option UInt64 :=
  match f with
  | "HAdd.hAdd" => a + b | "HSub.hSub" => a - b | "HMul.hMul" => a * b | "HAnd.hAnd" => a &&& b
  | "HOr.hOr" => a ||| b | "HShiftLeft.hShiftLeft" => a <<< b | "HShiftRight.hShiftRight" => a >>> b | _ => none

abbrev Prog := List (String × X)

def prim : String → List V → Option V
  | "rd", [.l x, .w i] => some (.w (x.getD i.toNat 0).toUInt64)
  | "len", [.l x] => some (.w x.length.toUInt64)
  | "len'", [.l x] => some (.n x.length)
  | "put", [.l o, .w v] => some (.l (o ++ [v.toUInt8]))
  | "bnew", [] => some (.b [])
  | "bsize", [.b b] => some (.w b.length.toUInt64)
  | "bget", [.b b, .w i] => some (.w (b.getD i.toNat 0))
  | "bset", [.b b, .w i, .w v] => some (.b (b.set i.toNat v))
  | "bpush", [.b b, .w v] => some (.b (b ++ [v]))
  | _, _ => none

/-- strip k leading λ -/
def strip : Nat → X → Option X
  | 0, e => some e
  | k + 1, .lam _ b => strip k b
  | _, _ => none

mutual
/-- evaluate `e` in `env` (de Bruijn: head = bvar 0) -/
def evalX (P : Prog) : Nat → List V → X → Option V
  | 0, _, _ => none
  | f + 1, env, e =>
    match e with
    | .bv i => env[i]?
    | .lt _ _ v b => (evalX P f env v).bind fun x => evalX P f (x :: env) b
    | e =>
      match spine e with
      | (.c "OfNat.ofNat" _, [.c "UInt64" [], .nat k, _]) => some (.w (UInt64.ofNat k))
      | (.c "OfNat.ofNat" _, [.c "Nat" [], .nat k, _]) => some (.n k)
      | (.c "ite" _, [_, c, _, t, el]) => do
        if ← evalB P f env c then evalX P f env t else evalX P f env el
      | (.c "Prod.mk" _, [_, _, a, b]) => do pure (.p (← evalX P f env a) (← evalX P f env b))
      | (.c "Prod.casesOn" _, [_, _, _, v, .lam _ (.lam _ body)]) => do
        let .p x y ← evalX P f env v | none
        evalX P f (y :: x :: env) body
      | (.c "Nat.casesOn" _, [_, d, z, .lam _ s]) => do
        match ← evalX P f env d with
        | .n 0 => evalX P f env z
        | .n (k + 1) => evalX P f (.n k :: env) s
        | _ => none
      | (.c "List.nil" _, [_]) => some (.l [])
      | (.c n _, as) =>
        match n.startsWith "H", as with
        | true, [_, _, _, _, a, b] => do
          let .w x ← evalX P f env a | none
          let .w y ← evalX P f env b | none
          pure (.w (← binV n x y))
        | _, _ => do
          let vs ← evalL P f env as
          prim n vs <|> ((P.lookup n).bind fun body => (strip vs.length body).bind fun b => evalX P f vs.reverse b)
      | _ => none
/-- conditions: `Eq Bool (BEq.beq ..) true` and `LT.lt ..` -/
def evalB (P : Prog) : Nat → List V → X → Option Bool
  | 0, _, _ => none
  | f + 1, env, c =>
    match spine c with
    | (.c "Eq" _, [_, q, _]) =>
      match spine q with
      | (.c "BEq.beq" _, [_, _, a, b]) => do
        let .w x ← evalX P f env a | none
        let .w y ← evalX P f env b | none
        pure (x == y)
      | _ => none
    | (.c "LT.lt" _, [_, _, a, b]) => do
      let .w x ← evalX P f env a | none
      let .w y ← evalX P f env b | none
      pure (decide (x < y))
    | _ => none
def evalL (P : Prog) : Nat → List V → List X → Option (List V)
  | 0, _, _ => none
  | _ + 1, _, [] => some []
  | f + 1, env, a :: as => do pure ((← evalX P f env a) :: (← evalL P f env as))
end

/-- run a program's `m` on an input: the output bytes -/
def runX (src : List UInt8) (inp : List UInt8) (fuel : Nat) : Option (List UInt8) := do
  let ds ← (emitXs src).toOption
  let P := ds.map fun (n, _, v) => (n, v)
  match evalX P fuel [.l inp] (.app (.c "m" []) (.bv 0)) with
  | some (.l o) => some o
  | _ => none

/-! non-vacuity: evalX of the emitted Expr computes the programs' outputs -/
def exSum : String := "def f : Nat → List UInt8 → UInt64 → UInt64 → UInt64
  | 0, x, i, a => a
  | n + 1, x, i, a => f n x (i + 1) (a + rd x i)
def m (x : List UInt8) : List UInt8 := put [] (f (len' x) x 0 0)"
def exPair : String := "def f (a b : UInt64) : UInt64 × UInt64 := let c := a + b; let (d, e) := (c, a); if d < e then (d, e) else (e, d)
def m (x : List UInt8) : List UInt8 := let (u, v) := f (rd x 0) 2; put (put [] u) v"
-- expected outputs: examples/sum.lean's `expect` line; exPair by hand (f 7 2 = (7, 9), f 1 2 = (1, 3))
#guard runX exSum.toUTF8.toList [97, 98, 99] 1000 = some [38]
#guard runX exPair.toUTF8.toList [7] 1000 = some [7, 9]
#guard runX exPair.toUTF8.toList [1] 1000 = some [1, 3]

end ExprSpec

