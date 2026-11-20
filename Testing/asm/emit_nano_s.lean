/- nano code generator tests (`Nano/GenIr.lean`, proved in `Nano/ProofTop.lean`): random nano programs (and a few
sources through `nanoElab`), their words (`nanoGen` = `Ir.compile ∘ lower`) and per case the input (arguments as
8-byte LE words), `Prog.eval`'s result (8 LE bytes) and `memoryNeeded` (from the IR interpreter).  Writes
`Testing/asm/ir-words/nano_<i>.{words,cases}`.  Run:
`lake env lean Testing/asm/emit_nano.lean`, then `for i in ...; python3 Testing/asm/ir_test.py check 8 nano_$i`
(QEMU + Sail at `memoryNeeded` and `memoryNeeded - 1`), or `Testing/asm/nano_test.sh`. -/
import Legacy.Nano.Gen
open Nano

def leN (n v : Nat) : List UInt8 := (List.range n).map fun i => (v / 256 ^ i % 256).toUInt8

def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j + 12345) % 2^64

/-- interesting words -/
def word (s : Nat) : UInt64 := match s % 6 with
  | 0 => UInt64.ofNat (rnd s 1) | 1 => 0xFFFFFFFFFFFFFFFF | 2 => 0 | 3 => 0x8000000000000000
  | _ => UInt64.ofNat (rnd s 2 % 1000)

def mkArgs : List Ex → Ex
  | [] => .anil
  | e :: es => .acons e (mkArgs es)

/-- a random expression over `nv` variables (some indices out of range on purpose), depth `d` -/
def tE : Nat → Nat → Nat → Ex
  | 0, nv, s => if rnd s 3 % 3 != 0 then .var (rnd s 4 % (nv + 1)) else .num (word s)
  | d + 1, nv, s => match rnd s d % 9 with
    | 0 => .num (word s)
    | 1 => .var (rnd s 5 % (nv + 1))
    | 2 => .add (tE d nv (2 * s + 1)) (tE d nv (2 * s + 2))
    | 3 => .sub (tE d nv (2 * s + 1)) (tE d nv (2 * s + 2))
    | 4 => .mul (tE d nv (2 * s + 1)) (tE d nv (2 * s + 2))
    | 5 | 6 => .let_ (tE d nv (2 * s + 1)) (tE d (nv + 1) (2 * s + 2))
    | _ =>
      -- a call of a fresh callee of arity `k` (its body over its own parameters)
      let k := rnd s 6 % 3
      .call (tE d k (3 * s + 5)) (mkArgs ((List.range k).map fun j => tE d nv (3 * s + 7 + 11 * j)))

/-- a full tree of operators / lets / calls of depth `d` (large frames: hundreds of slots) -/
def tBig : Nat → Nat → Nat → Ex
  | 0, nv, s => if nv > 0 then .var (rnd s 4 % (nv + 1)) else .num (word s)
  | d + 1, nv, s => match rnd s d % 5 with
    | 0 => .add (tBig d nv (2 * s + 1)) (tBig d nv (2 * s + 2))
    | 1 => .sub (tBig d nv (2 * s + 1)) (tBig d nv (2 * s + 2))
    | 2 => .mul (tBig d nv (2 * s + 1)) (tBig d nv (2 * s + 2))
    | 3 => .let_ (tBig d nv (2 * s + 1)) (tBig d (nv + 1) (2 * s + 2))
    | _ => .call (tBig d 2 (2 * s + 1)) (mkArgs [tBig d nv (2 * s + 2), .num (word s)])

def progs : List Prog :=
  [(1, .add (.var 0) .anil), (0, .call (.var 0) (.num 3)), (2, .acons (.num 1) (.num 2)), (1, .mul (.call (.add (.var 0) (.var 3)) (.acons (.var 0) .anil)) (.var 9))] ++
  (List.range 6).map (fun i => (i % 4, tBig (i + 5) (i % 4) (i * 13 + 3))) ++
  (List.range 30).map fun i => (i % 4, tE (i % 6 + 1) (i % 4) (i * 7 + 1))

def srcs : List String := [
  "def f (x y : UInt64) : UInt64 := x * y + 3",
  "def g (x : UInt64) : UInt64 := x - 1\ndef h (a b : UInt64) : UInt64 := let c := g a; c * (b + g b)",
  "def k : UInt64 := 18446744073709551615 + 2 * 3"]

def inputs (p : Prog) (i : Nat) : List (List UInt64) :=
  (List.range 8).map fun j => (List.range p.1).map fun a => word (rnd i (j * 5 + a))

def emitP (name : String) (p : Prog) (i : Nat) : IO Unit := do
  let ws := (asm (genR p)).toArray
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
  for (p, i) in progs.zipIdx do emitP s!"nanos_{i}" p i
  for (src, i) in srcs.zipIdx do
    match nanoElab src.toUTF8.toList with
    | some p => emitP s!"nanos_src{i}" p (100 + i)
    | none => IO.println s!"nanos_src{i}: nanoElab failed"

#eval runAll
