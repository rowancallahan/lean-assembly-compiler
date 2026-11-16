/- FUZZ9 case generator: `lake env lean --run Testing/asm/fuzz9/gen9.lean ENTRY SEED N [big]` (run under `ulimit -s unlimited`).
Prints one line per case: `input-hex result-hex cells` where the result is Lean's (the repo's `T.enc` of the executed function) and
`cells` is the allocation count of the entry's own model (`pg.al`), from which the harness builds the stated work size. -/
import Riscv.Frontx.ExprExamples
import Riscv.Frontx.HofExamples
import Riscv.Frontx.TinyRepro

open Proven Proven.Frontx.ExprEx

def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def boolB (b : Bool) : List UInt8 := [if b then 1 else 0]
def M64 : Nat := 2 ^ 64

-- ---------------- random numbers (splitmix64) in a state monad
abbrev G := StateM UInt64
def nxt : G Nat := do
  let s ← get; let s := s + 0x9E3779B97F4A7C15; set s
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  return (z ^^^ (z >>> 31)).toNat
def below (n : Nat) : G Nat := do let x ← nxt; return x % n
def pick (xs : Array α) [Inhabited α] : G α := do let i ← below xs.size; return xs[i]!
def chance (p q : Nat) : G Bool := do return (← below q) < p

def edges : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 127, 128, 255, 256, 2^31, 2^32 - 1, 2^32, 2^63 - 1, 2^63, 2^63 + 1, M64 - 2, M64 - 1]
/-- a `Nat` below `2^64` (the input format keeps 8 bytes): edges, small, random -/
def genNat : G Nat := do
  let k ← below 10
  if k < 4 then pick edges else if k < 7 then below 12 else below M64

def strs : Array String := #["", "a", "x", "Nat", "succ", "é", "λ", "∀x", "Nat.add", "a\x00b", "12345678", "123456789", "abcdefghijklmnopqrstuvwxyz0123456789",
  "αβγδεζηθ", "\x00", "ÿ\x7f\x80", "𝔸𝔹"]
def genStr : G String := do
  if (← below 12) = 0 then
    let n ← below 70
    return String.ofList ((List.range n).map fun i => Char.ofNat (97 + i % 26))
  else pick strs
def genN : Nat → G ConLeche.Name
  | 0 => return .anonymous
  | d + 1 => do
    match ← below 4 with
    | 0 => return .str (← genN d) (← genStr)
    | 1 => return .num (← genN d) (← genNat)
    | 2 => return .anonymous
    | _ => return .str .anonymous (← genStr)
def genL : Nat → G ConLeche.Level
  | 0 => do if (← below 2) = 0 then return .zero else return .param (← genN 1)
  | d + 1 => do
    match ← below 6 with
    | 0 => return .zero | 1 => return .param (← genN 2) | 2 => return .succ (← genL d)
    | 3 => return .max (← genL d) (← genL d) | 4 => return .imax (← genL d) (← genL d)
    | _ => return .succ .zero
def genLs : G (List ConLeche.Level) := do
  let n ← pick #[0, 0, 1, 2, 3, 5]; let mut o := []
  for _ in [0:n] do o := (← genL (← below 4)) :: o
  return o

-- ---------------- expressions
/-- context: `bd` binder depth; `closed`: bound indices stay below `bd`; `fvb`: free variables only below this index (`none`: any), their types
generated with the bound lowered to their index; `nofv`: no free variable at all -/
structure Cx where
  bd : Nat := 0
  closed : Bool := false
  fvb : Option Nat := none
  nofv : Bool := false

def genBvar (c : Cx) : G Nat := do
  if c.closed then (if c.bd = 0 then return 0 else below c.bd)   -- closed with bd = 0 is not used for bvar (see leaf)
  else match ← below 6 with
    | 0 => return c.bd | 1 => return c.bd + 1 | 2 => genNat | 3 => return 2^64 - 1 | _ => below (c.bd + 2)

mutual
partial def leaf (c : Cx) : G ConLeche.Expr := do
  match ← below 6 with
  | 0 => if c.closed && c.bd = 0 then return .sort .zero else return .bvar (← genBvar c)
  | 1 => return .sort (← genL (← below 4))
  | 2 => return .const (← genN (← below 4)) (← genLs)
  | 3 => return .lit (.natVal (← genNat))
  | 4 => return .lit (.strVal (← genStr))
  | _ => if c.nofv then return .const .anonymous [] else fv c 1

partial def fv (c : Cx) (fuel : Nat) : G ConLeche.Expr := do
  if c.nofv then return .const .anonymous []
  match c.fvb with
  | some 0 => return .const (← genN 1) []
  | some b => let i ← (if (← below 3) = 0 then pure (b - 1) else below b); return .fvar i (← gen { c with fvb := some i } (fuel / 2))
  | none => return .fvar (← genNat) (← gen c (fuel / 2))

/-- split `fuel - 1` between two or three children: all to one (deep), even, or small to the others -/
partial def split (fuel : Nat) (k : Nat) : G (List Nat) := do
  let rest := fuel - 1
  let mode ← below 4
  let which ← below k
  let ev := rest / k
  return (List.range k).map fun i => match mode with
    | 0 => if i = which then rest - (k - 1) * (rest / 20) else rest / 20      -- one deep child
    | 1 => ev
    | 2 => if i = 0 then rest - (k - 1) * 2 else 2                           -- long left spine
    | _ => if i = k - 1 then rest - (k - 1) * 2 else 2                       -- long right spine

partial def gen (c : Cx) (fuel : Nat) : G ConLeche.Expr := do
  if fuel ≤ 1 then return ← leaf c
  match ← below 12 with
  | 0 => leaf c
  | 1 => fv c fuel
  | 2 | 3 | 4 => let [a, b] ← split fuel 2 | unreachable!; return .app (← gen c a) (← gen c b)
  | 5 => let [a, b] ← split fuel 2 | unreachable!; return .lam (← gen c a) (← gen { c with bd := c.bd + 1 } b)
  | 6 => let [a, b] ← split fuel 2 | unreachable!; return .forallE (← gen c a) (← gen { c with bd := c.bd + 1 } b)
  | 7 => let [a, v, b] ← split fuel 3 | unreachable!; return .letE (← gen c a) (← gen c v) (← gen { c with bd := c.bd + 1 } b)
  | 8 => let [e] ← split fuel 1 | unreachable!; return .proj (← genN (← below 4)) (← genNat) (← gen c e)
  | 9 => let [a, b] ← split fuel 2 | unreachable!; return .app (← gen c a) (.bvar (← genBvar c))
  | _ => let [a, b] ← split fuel 2 | unreachable!; return .app (← gen c a) (← gen c b)
end

/-- long structured expressions: binder chains, app spines (left / right), let chains, Pi chains, in an `fvar` or `const` head -/
def genChain (c : Cx) (n : Nat) : G ConLeche.Expr := do
  match ← below 7 with
  | 0 => -- app spine, head const / fvar / bvar, small arguments
    let mut e ← (match ← below 3 with | 0 => pure (ConLeche.Expr.const (← genN 2) (← genLs)) | 1 => (if c.nofv then leaf c else fv c 3) | _ => leaf c)
    for _ in [0:n] do e := .app e (← gen c (← below 4))
    return e
  | 1 => -- right-nested app
    let mut e ← leaf c
    for _ in [0:n] do e := .app (← gen c (← below 3)) e
    return e
  | 2 => -- binder chain (bodies refer to the binders)
    let ks ← (List.range n).mapM fun _ => below 3
    let rec build : List Nat → Cx → G ConLeche.Expr
      | [], c => gen c (← below 6)
      | k :: ks, c => do
        let ty ← gen c (← below 4); let c' := { c with bd := c.bd + 1 }
        match k with
        | 0 => return .lam ty (← build ks c')
        | 1 => return .forallE ty (← build ks c')
        | _ => return .letE ty (← gen c (← below 4)) (← build ks c')
    build ks c
  | 3 => -- Pi chain, result an application of a bound variable
    let mut e ← (do let h ← genBvar { c with bd := c.bd + n, closed := c.closed }; pure (ConLeche.Expr.app (.bvar h) (.bvar (← below (n + 1)))))
    for i in [0:n] do e := .forallE (← gen { c with bd := c.bd + n - 1 - i } (← below 4)) e
    return e
  | 4 => -- let chain
    let mut e ← gen { c with bd := c.bd + n } (← below 5)
    for i in [0:n] do e := .letE (← gen { c with bd := c.bd + n - 1 - i } 2) (← gen { c with bd := c.bd + n - 1 - i } 2) e
    return e
  | 5 => -- lam chain around a left spine
    let mut e ← leaf { c with bd := c.bd + n }
    for _ in [0:n] do e := .app e (.bvar (← below (c.bd + n + 1)))
    for i in [0:n] do e := .lam (← gen { c with bd := c.bd + n - 1 - i } (← below 3)) e
    return e
  | _ => -- proj chain
    let mut e ← leaf c
    for _ in [0:n] do e := .proj (← genN 2) (← genNat) e
    return e

def size : G Nat := do
  match ← below 6 with
  | 0 => below 4 | 1 => below 12 | 2 => below 40 | 3 => below 150 | 4 => below 600 | _ => below 2500
def genContext : G Cx := do
  match ← below 8 with
  | 0 => return { closed := true }                     -- closed expressions (no loose bound variable if generated from bd = 0)
  | 1 => return { nofv := true }
  | 2 => return { fvb := some (← pick #[0, 1, 2, 3, 8, 100]) }
  | 3 => return { bd := ← below 5 }
  | _ => return {}
def genExpr (big : Bool) : G ConLeche.Expr := do
  let c ← genContext
  let n ← if big then pick #[3000, 8000, 20000] else size
  match ← below 4 with
  | 0 => genChain c (min n 4000)
  | _ => do
    let e ← gen c n
    if (← below 3) = 0 then
      -- wrap in a binder chain / spine
      return ConLeche.Expr.lam e (.app e (.bvar 0))
    else return e

-- ---------------- entries
def spW (m nl cells : Nat) (x : List UInt8) : Nat := Proven.Frontx.Ind.spaceA m nl (fun _ => cells) x.length
def line (x y : List UInt8) (cells : Nat) : String := s!"{hx x} {hx y} {cells}"
def leN8 (n : Nat) : List UInt8 := (List.range 8).map fun i => UInt8.ofNat (n / 256 ^ i % 256)

def exprCase (name : String) (e : ConLeche.Expr) (d : Nat) (v : ConLeche.Expr) : String :=
  let x := TExpr.enc e; let emb := TExpr.emb e
  match name with
  | "hasfvar" => line x (boolB e.hasFvar) (ConLeche.Expr.hasFvar.ind.pg.al emb 0 .z)
  | "closed0" => line x (boolB (closed0 e)) (closed0.ind.pg.al emb 0 .z)
  | "inst1" => line (TExpr.enc2 (e, v)) (TExpr.enc (inst1 e v)) (inst1.ind.pg.al emb 0 (TExpr.emb v))
  | "sizef" => line x (leN8 e.sizeF) (ConLeche.Expr.sizeF.ind.pg.al emb 0 .z)
  | "scopedd" => line (x ++ leN8 d) (boolB (scopedD e d)) (scopedD.ind.pg.al emb (BitVec.ofNat 64 d) .z)
  | "isforalle" => line x (boolB e.isForallE) (ConLeche.Expr.isForallE.ind.pg.al emb 0 .z)
  | "getappfn" => line x (TExpr.enc e.getAppFn) (ConLeche.Expr.getAppFn.ind.pg.al emb 0 .z)
  | "piresult" => line x (TExpr.enc e.piResult) (ConLeche.Expr.piResult.ind.pg.al emb 0 .z)
  | "fvartyped" => line x (TExpr.enc e.fvarTypeD) (ConLeche.Expr.fvarTypeD.ind.pg.al emb 0 .z)
  | "numargs" => line x (leN8 e.numArgs) (ConLeche.Expr.numArgs.ind.pg.al emb 0 .z)
  | "islit" => line x (boolB e.isLit) (ConLeche.Expr.isLit.ind.pg.al emb 0 .z)
  | _ => panic! "entry"

/-- the depth query of `scopedD`: the bound the expression was built for, one below / above, edges, random -/
def genDepth (c : Cx) : G Nat := do
  let b := c.fvb.getD 0
  match ← below 6 with
  | 0 => return b | 1 => return b + 1 | 2 => return b - 1 | 3 => return 2^64 - 1 | 4 => below 10 | _ => genNat

def genBytes (kind : Nat) (n : Nat) : G (List UInt8) := do
  let mut o := []
  let pat ← below 4
  for i in [0:n] do
    let b : Nat ← match kind with
      | 0 => (match pat with | 0 => below 256 | 1 => below 8 | 2 => pick #[0, 3, 4, 5, 10, 32, 100, 101, 127, 128, 255] | _ => return 255 - (i % 5))
      | _ => below 256
    o := UInt8.ofNat b :: o
  return o.reverse
def genBytesLen (big : Bool) : G Nat := do
  if big then pick #[20000, 100000]
  else match ← below 5 with | 0 => below 3 | 1 => below 20 | 2 => below 100 | 3 => below 400 | _ => below 3000

def hofCase (name : String) (xs : List UInt8) : String :=
  let ba : ByteArray := ⟨xs.toArray⟩
  open Proven.Frontx.Hof in
  let r : List UInt8 := match name with
    | "hof_mapinc" => Res.enc (mapInc ba) | "hof_mapcomp" => Res.enc (mapComp ba) | "hof_mapxor" => Res.enc (mapXor ba)
    | "hof_filtergt3" => Res.enc (filterGt3 ba) | "hof_filternz" => Res.enc (filterNZ ba) | "hof_dupall" => Res.enc (dupAll ba)
    | "hof_stagemap" => Res.enc (stageMap ba) | "hof_pipe2" => Res.enc (pipe2 ba) | "hof_xstagefilter" => Res.enc (xstageFilter ba)
    | "hof_nonfindgt3" => Res.enc (nonFindGt3 ba) | "hof_findgt3" => Res.enc (findGt3 ba) | "hof_foldrsum" => Res.enc (foldrSum ba)
    | "hof_sumfoldl" => Res.enc (sumFoldl ba) | "hof_xorarr" => Res.enc (xorArr ba) | "hof_anynl" => Res.enc (anyNL ba)
    | "hof_allascii" => Res.enc (allAscii ba) | "hof_findhigh" => Res.enc (findHigh ba) | "hof_countsp" => Res.enc (countSp ba)
    | "hof_arrfindgt3" => arrFindGt3.enc (arrFindGt3 ba) | "hof_countabove100" => Res.enc (countAbove100 ba)
    | _ => panic! "hof entry"
  line xs r 0

def main (args : List String) : IO Unit := do
  let [name, seed, n] := args.take 3 | throw (IO.userError "usage: ENTRY SEED N [big]")
  let big := args.length > 3
  let st := (seed.toNat!.toUInt64 + 1) * 0x2545F4914F6CDD1D + (name.hash)
  let gens : G (List String) := do
    let mut out := []
    for i in [0:n.toNat!] do
      if name.startsWith "hof_" then
        let L ← (if i < 4 then pure i else genBytesLen big)
        out := hofCase name (← genBytes 0 L) :: out
      else
        let c ← genContext
        let e ← (match ← below 5 with | 0 => genChain c (← pick #[1, 2, 5, 30, 200, 1500]) | _ => gen c (← (if big then pick #[3000, 8000, 20000] else size)))
        let v ← (match ← below 3 with | 0 => pure (ConLeche.Expr.bvar (← genNat)) | 1 => gen {} (← below 8) | _ => gen { bd := 2 } (← size))
        let d ← genDepth c
        out := exprCase name e d v :: out
    return out.reverse
  for l in (gens.run' st) do IO.println l
