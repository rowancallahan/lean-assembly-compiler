/- nano v2 (increment 1: `if` + comparisons) code generator tests: random well-scoped `Nano.V2.E` programs with `if`
nodes of every comparison kind, and sources (UInt64 and Int64) through `Nano.V2.nanoElab`; their words
(`Nano.V2.nanoGen` = `asm ∘ Nano.V2.genR`) and per case the input (arguments as 8-byte LE words), `Prog.eval`'s
result (8 LE bytes) and `memoryNeeded = 8 * depth`.  Only programs in the proved domain (`ScE`, `depth ≤ 256`) are
emitted.  Writes `Testing/asm/ir-words/nanov2_<i>.{words,cases}`; run with `Testing/asm/nano_v2_test.sh`. -/
import Nano.V2Elab
import Nano.V2Gen
import Nano.V2Rec
open Nano.V2

def leN (n v : Nat) : List UInt8 := (List.range n).map fun i => (v / 256 ^ i % 256).toUInt8
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j + 12345) % 2^64

/-- interesting words: around 0, 2^63 and 2^64 (the signed / unsigned boundaries) -/
def word (s : Nat) : UInt64 := match s % 9 with
  | 0 => UInt64.ofNat (rnd s 1) | 1 => 0xFFFFFFFFFFFFFFFF | 2 => 0 | 3 => 0x8000000000000000
  | 4 => 0x7FFFFFFFFFFFFFFF | 5 => 1 | 6 => 0x8000000000000001
  | _ => UInt64.ofNat (rnd s 2 % 1000)

def mkArgs : List E → E
  | [] => .anil
  | e :: es => .acons e (mkArgs es)

def cmpK (n : Nat) : Cmp := match n % 5 with | 0 => .eq | 1 => .ltu | 2 => .leu | 3 => .lts | _ => .les

/-- a random expression over `nv ≥ 1` variables, depth `d`, many `if` nodes -/
def tE : Nat → Nat → Nat → E
  | 0, nv, s => if rnd s 3 % 3 != 0 then .var (rnd s 4 % nv) else .num (word s)
  | d + 1, nv, s => match rnd s d % 14 with
    | 0 => .num (word s)
    | 1 => .var (rnd s 5 % nv)
    | 2 => .add (tE d nv (2 * s + 1)) (tE d nv (2 * s + 2))
    | 3 => .sub (tE d nv (2 * s + 1)) (tE d nv (2 * s + 2))
    | 4 => .mul (tE d nv (2 * s + 1)) (tE d nv (2 * s + 2))
    | 5 => .let_ (tE d nv (2 * s + 1)) (tE d (nv + 1) (2 * s + 2))
    | 6 =>
      let k := rnd s 6 % 3 + 1
      .call (tE d k (3 * s + 5)) (mkArgs ((List.range k).map fun j => tE d nv (3 * s + 7 + 11 * j)))
    | 11 => .bit (match rnd s 8 % 3 with | 0 => .and | 1 => .or | _ => .xor) (tE d nv (2 * s + 1)) (tE d nv (2 * s + 2))
    | 12 => .sh (rnd s 9 % 2 == 0) (rnd s 10 % 70) (tE d nv (2 * s + 1))
    | _ => .ite (cmpK (rnd s 7)) (tE d nv (4 * s + 1)) (tE d nv (4 * s + 2)) (tE d nv (4 * s + 3)) (tE d nv (4 * s + 4))

def progs : List Prog :=
  [(2, .ite .ltu (.var 1) (.var 0) (.num 1) (.num 2)), (2, .ite .lts (.var 1) (.var 0) (.num 1) (.num 2)),
   (2, .ite .leu (.var 1) (.var 0) (.num 1) (.num 2)), (2, .ite .les (.var 1) (.var 0) (.num 1) (.num 2)),
   (2, .ite .eq (.var 1) (.var 0) (.num 1) (.num 2)),
   (2, .bit .and (.var 1) (.var 0)), (2, .bit .or (.var 1) (.var 0)), (2, .bit .xor (.var 1) (.var 0)),
   (1, .sh true 7 (.var 0)), (1, .sh false 63 (.var 0)), (1, .sh true 64 (.var 0)), (1, .sh false 100 (.var 0))] ++
  (List.range 40).map fun i => (i % 3 + 1, tE (i % 5 + 2) (i % 3 + 1) (i * 7 + 1))

def srcs : List String := [
  "def f (x y : UInt64) : UInt64 := if x < y then x else y",
  "def f (x y : Int64) : Int64 := if x < y then x else y",
  "def f (x y : UInt64) : UInt64 := if x <= y then y - x else x - y",
  "def f (x y : Int64) : Int64 := if x <= y then y - x else x - y",
  "def f (x : Int64) : Int64 := if x < 0 then 0 - x else x",
  "def f (x : UInt64) : UInt64 := if x == 0 then 1 else if x == 1 then 1 else x * 2",
  "def m (a b : UInt64) : UInt64 := if a < b then b else a\ndef f (x y z : UInt64) : UInt64 := m (m x y) z",
  "def s (x : Int64) : Int64 := if x < 0 then -1 else if x == 0 then 0 else 1\ndef f (x y : Int64) : Int64 := s x * 3 + s y",
  "def f (x y : UInt64) : UInt64 := let d := x - y; if d < 9223372036854775808 then d else 0 - d",
  "def c (x l h : Int64) : Int64 := if x < l then l else if h < x then h else x\ndef f (x : Int64) : Int64 := c x (-100) 100",
  "def d (c : UInt64) : UInt64 := if 48 <= c then (if c <= 57 then 1 else 0) else 0\ndef f (x : UInt64) : UInt64 := d x + d (x + 1) * 2",
  "def f (x y : UInt64) : UInt64 := x &&& y ||| x ^^^ y",
  "def b (o c : UInt64) : UInt64 := (o &&& 7) <<< 4 ||| (c >>> 1)\ndef f (x y : UInt64) : UInt64 := b x y ^^^ (x <<< 63)",
  "def f (x : UInt64) : UInt64 := if x &&& 1 == x - x then x >>> 1 else x <<< 1 ||| x"]

def inputs (p : Prog) (i : Nat) : List (List UInt64) :=
  (List.range 8).map fun j => (List.range p.1).map fun a => word (rnd i (j * 5 + a))

def emitP (name : String) (p : Prog) (i : Nat) : IO Unit := do
  if !(Nano.V2R.ScE p.2 p.1 && decide (depth p ≤ 256)) then
    IO.println s!"{name}: outside the proved domain, skipped"; return
  let ws := (nanoGen p).toArray
  let mut lines := [s!"{name} 0"]
  for k in [0:ws.size / 4] do
    let w := ws[4*k]!.toNat + 256 * ws[4*k+1]!.toNat + 65536 * ws[4*k+2]!.toNat + 16777216 * ws[4*k+3]!.toNat
    lines := lines ++ [hex8 (BitVec.ofNat 32 w)]
  IO.FS.writeFile s!"Testing/asm/ir-words/{name}.words" (String.intercalate "\n" lines ++ "\n")
  let mut s := ""
  for args in inputs p i do
    let x := (args.map fun a => leN 8 a.toNat).flatten
    match p.eval args with
    | some y => s := s ++ s!"{hx x} {hx (leN 8 y.toNat)} {8 * depth p}\n"
    | none => IO.println s!"{name}: eval failed"
  IO.FS.writeFile s!"Testing/asm/ir-words/{name}.cases" s
  IO.println s!"{name}: arity {p.1}, {ws.size / 4} words, depth {depth p}"

def runAll : IO Unit := do
  for (p, i) in progs.zipIdx do emitP s!"nanov2_{i}" p i
  for (src, i) in srcs.zipIdx do
    match nanoElab src.toUTF8.toList with
    | some p => emitP s!"nanov2_src{i}" p (100 + i)
    | none => IO.println s!"nanov2_src{i}: nanoElab failed"

#eval runAll
