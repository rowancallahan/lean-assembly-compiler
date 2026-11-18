import Nano.V2Self.C.Lex2
import Nano.V2Self.C.Par0
import Nano.V2Self.C.Gen
/- Chain test: random scalar defs (generator copied from par0_test.lean) → text → C.s10 (lex) → C.y13 (Par0) → append a
hand-written main (args from input bytes, 8 result bytes out) → C.g41 → RV64 code.  Expected outputs = native evaluation
of the tree.  Writes Testing/asm/ir-words/cgc_K.{words,cases}; run each with NOSAIL=1 cg_test.py cgc_K.
run: lean --run Testing/nano/v2self/cg_chain.lean N -/
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
def ks : List UInt64 := [3, 1000003, 0x8000000000000007, 0xFFFFFFFFFFFFFFF1]
-- main: LET 0 1 (CALL 0 4 (RD j + k_j)…) in 8 nested PUTs of slot0 >>> 8i
def arg (j : Nat) : List UInt64 := [3, 1, 9, 2, 1, j.toUInt64, 1, ks.getD j 0]
def puts : Nat → List UInt64
  | 0 => [9, 5]
  | i+1 => [9, 4] ++ puts i ++ [3, 7, 2, 0, 1, 1, (8 * i).toUInt64]
def mainW : List UInt64 := [20, 1, 0, 1, 0, 1, 5, 0, 1, 8, 0, 4] ++ arg 0 ++ arg 1 ++ arg 2 ++ arg 3 ++ puts 8 ++ [21]
def hex (l : List UInt8) : String := if l.isEmpty then "-" else String.join (l.map fun b =>
  let s := (Nat.toDigits 16 b.toNat).asString; if s.length == 1 then "0" ++ s else s)
def u8 (v : UInt64) : List UInt8 := (List.range 8).map fun i => (v >>> (8 * i).toUInt64).toUInt8
def inputs : List (List UInt8) := [[0, 0, 0, 0], [1, 2, 3, 4], [255, 0, 255, 7], [9, 9, 200, 1], [17, 250, 3, 128]]
def main (args : List String) : IO Unit := do
  let n := (args.headD "40").toNat!
  let mut s := 977
  for k in [0:n] do
    let (t, s') := gen (k % 7 + 1) ["a", "b1", "c'", "d_e"] s
    s := lcg s'
    let txt := s!"def f (a b1 c' d_e : UInt64) : UInt64 := {t.pr 0}\n"
    let ws := C.y13 (C.s10 txt.toUTF8.toList)
    if ws.isEmpty then throw (IO.userError s!"parser rejected {txt}")
    let code := C.g41 (ws ++ mainW)
    if code.isEmpty then throw (IO.userError s!"g41 rejected {txt}")
    let wd := (List.range (code.length / 4)).map fun q =>
      (code.getD (4*q) 0).toNat + 256 * (code.getD (4*q+1) 0).toNat + 65536 * (code.getD (4*q+2) 0).toNat + 16777216 * (code.getD (4*q+3) 0).toNat
    let hx := wd.map fun w => let h := (Nat.toDigits 16 w).asString; String.ofList (List.replicate (8 - h.length) '0') ++ h
    IO.FS.writeFile s!"Testing/asm/ir-words/cgc_{k}.words" (s!"cgc {k}\n" ++ " ".intercalate hx ++ "\n")
    let cs := inputs.map fun x =>
      let ps := (List.range 4).map fun j => (x.getD j 0).toUInt64 + ks.getD j 0
      let env := (List.zip ["a", "b1", "c'", "d_e"] ps).reverse
      hex x ++ " 0 " ++ hex (u8 (t.eval env))
    IO.FS.writeFile s!"Testing/asm/ir-words/cgc_{k}.cases" ("\n".intercalate cs ++ "\n")
  IO.println s!"wrote {n} programs"
