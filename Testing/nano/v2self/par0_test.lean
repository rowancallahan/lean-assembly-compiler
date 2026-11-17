import Nano.V2Self.C.Lex2
import Nano.V2Self.C.Par0
/- parser increments A-C: random trees (literals, params/let-bound names with shadowing, binary ops with Lean precedences, if, let), printed, lexed (`C.s10`),
parsed (`C.y13`), the pre-order AST decoded (slots) and evaluated against the tree's value (names, wraps mod 2^64).  run: lean --run Testing/nano/v2self/par0_test.lean -/
inductive T | cst (v : Nat) | var (n : String) | bin (op : Nat) (a b : T) | ite (k : Nat) (a b t e : T) | lt (n : String) (v b : T)
def T.eval (env : List (String × UInt64)) : T → UInt64
  | .cst v => v.toUInt64 | .var n => (env.lookup n).getD 0
  | .bin op a b => let x := a.eval env; let y := b.eval env
    match op with | 1 => x + y | 2 => x - y | 3 => x * y | 4 => x &&& y | 5 => x ||| y | 6 => x <<< y | _ => x >>> y
  | .ite k a b t e => let x := a.eval env; let y := b.eval env; if (if k == 1 then x == y else x < y) then t.eval env else e.eval env
  | .lt n v b => b.eval ((n, v.eval env) :: env)
def T.lets : T → Nat
  | .bin _ a b => a.lets + b.lets | .ite _ a b t e => a.lets + b.lets + t.lets + e.lets | .lt _ v b => 1 + v.lets + b.lets | _ => 0
def prec : Nat → Nat | 1 => 65 | 2 => 65 | 3 => 70 | 4 => 60 | 5 => 55 | _ => 75
def opS : Nat → String | 1 => " + " | 2 => " - " | 3 => " * " | 4 => " &&& " | 5 => " ||| " | 6 => " <<< " | _ => " >>> "
def pool := ["a", "b1", "c'", "d_e", "l1", "x"]
def T.pr : Nat → T → String
  | p, .lt n v b => let s := "let " ++ n ++ " := " ++ v.pr 0 ++ "; " ++ b.pr 0
      if p > 0 then "(" ++ s ++ ")" else s
  | p, .ite k a b t e => let s := "if " ++ a.pr 1 ++ (if k == 1 then " == " else " < ") ++ b.pr 1 ++ " then " ++ t.pr 0 ++ " else " ++ e.pr 0
      if p > 0 then "(" ++ s ++ ")" else s
  | _, .cst v => toString v | _, .var n => n
  | p, .bin op a b => let q := prec op
      let s := a.pr q ++ opS op ++ (b.pr (q + 1))
      if q < p then "(" ++ s ++ ")" else s
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64
def gen : Nat → List String → Nat → T × Nat
  | 0, sc, s => let s1 := lcg s; if (s1 >>> 33) % 3 == 0 then (.cst ((s1 >>> 20) % 1000), s1) else (.var (sc.getD ((s1 >>> 20) % sc.length) "a"), s1)
  | d+1, sc, s =>
    let s1 := lcg s
    if (s1 >>> 33) % 4 == 0 then gen 0 sc s1 else
    if (s1 >>> 45) % 5 == 0 then
      let (a, s2) := gen d sc s1; let (b, s3) := gen d sc s2; let (t, s4) := gen d sc s3; let (e, s5) := gen d sc s4
      (.ite ((s5 >>> 30) % 2 + 1) a b t e, lcg s5) else
    if (s1 >>> 50) % 5 == 0 then
      let n := pool.getD ((s1 >>> 22) % pool.length) "a"
      let (v, s2) := gen d sc s1; let (b, s3) := gen d (n :: sc) s2; (.lt n v b, s3) else
    let op := (s1 >>> 40) % 7 + 1
    if op ≥ 6 then let (a, s2) := gen d sc s1; (.bin op a (.cst ((s2 >>> 30) % 64)), lcg s2)
    else let (a, s2) := gen d sc s1; let (b, s3) := gen d sc s2; (.bin op a b, s3)
-- decode pre-order words; env = slot values
def setS (env : List UInt64) (i : Nat) (v : UInt64) : List UInt64 := env.set i v
def dec (ws : List UInt64) (env : List UInt64) : Nat → Option (UInt64 × List UInt64)
  | 0 => none
  | f+1 => match ws with
    | 1 :: v :: r => some (v, r)
    | 2 :: s :: 1 :: r => some (env.getD s.toNat 0, r)
    | 5 :: s :: 1 :: r => do
      let (v, r1) ← dec r env f
      dec r1 (setS env s.toNat v) f
    | 4 :: k :: r => do
      let (x, r1) ← dec r env f; let (y, r2) ← dec r1 env f; let (t, r3) ← dec r2 env f; let (e, r4) ← dec r3 env f
      some (if (if k == 1 then x == y else x < y) then t else e, r4)
    | 3 :: op :: r => do
      let (x, r1) ← dec r env f; let (y, r2) ← dec r1 env f
      some (match op with | 1 => x + y | 2 => x - y | 3 => x * y | 4 => x &&& y | 5 => x ||| y | 6 => x <<< y | _ => x >>> y, r2)
    | _ => none
def run (t : T) (hdr : String) : Bool :=
  let txt := s!"def f {hdr} : UInt64 := {t.pr 0}\n"
  let ws := C.y13 (C.s10 txt.toUTF8.toList)
  let ps : List UInt64 := [3, 1000003, 7, 0xFFFFFFFFFFFFFFF1]
  let env : List (String × UInt64) := (List.zip ["a", "b1", "c'", "d_e"] ps).reverse
  match ws with
  | 2 :: 20 :: 0 :: np :: ns :: 0 :: 1 :: r =>
    np == 4 && ns.toNat == 4 + t.lets && (match dec r (ps ++ List.replicate 60 0) 1000 with | some (v, [21]) => v == t.eval env | _ => false)
  | _ => false
def go : Nat → Nat → Nat × Nat → Nat × Nat
  | 0, _, r => r
  | k+1, s, (bad, tot) =>
    let (t, s') := gen (k % 7) ["a", "b1", "c'", "d_e"] s
    let hdr := if k % 2 == 0 then "(a b1 c' d_e : UInt64)" else "(a b1 : UInt64) (c' : UInt64) (d_e : UInt64)"
    go k (lcg s') (if run t hdr then bad else bad + 1, tot + 1)
def main : IO Unit := do
  IO.println s!"(mismatches, total) = {go 3000 11 (0, 0)}"
  let r := (List.range 400).foldl (fun n k => let (t, _) := gen (k % 7) ["a", "b1", "c'", "d_e"] (lcg (k * 7919)); n + t.lets) 0
  IO.println s!"lets in a sample of 400 trees: {r}"
  for t in ["def f (a : UInt64) : UInt64 := if a then 1 else 2\n", "def f (a : UInt64) : UInt64 := if a == 1 then 2\n", "def f (a : UInt64) : UInt64 := if a == 1 else 2\n",
      "def f (a : UInt64) : UInt64 := let z := 1 z\n", "def f (a : UInt64) : UInt64 := let z = 1; z\n", "def f (a : UInt64) : UInt64 := let z := 1; w\n", "def f (a : UInt64) : UInt64 := (let z := 1; z) + z\n",
      "def f (a : UInt64) : UInt64 := a +\n", "def f (a : UInt64) : UInt64 := (a + 1\n", "def f (a : UInt64) : UInt64 := z\n", "def f (a : UInt64) : UInt64 := a <<< b\n",
      "def f (a : UInt64) : UInt64 := a + 1 extra\n", "def f (a : Int64) : UInt64 := a\n"] do
    IO.println s!"reject {repr t}: {(C.y13 (C.s10 t.toUTF8.toList)).isEmpty}"
