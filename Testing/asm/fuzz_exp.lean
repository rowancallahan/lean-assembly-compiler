/- Random differential testing generator. usage: SEED=1 NCASES=100 K=100 [BACKEND=fast] [SMALL=1] [MODE=stats] lake env lean Testing/asm/fuzz_exp.lean > out.txt
   BACKEND=fast: test the unproved fast backends (Testing/asm/fast/*; build with Testing/asm/fast/build.sh); SMALL=1: mostly small constants;
   MODE=stats: print code-size table instead of test cases. (the Sail model already defines a root `main`, so this uses #eval + env vars)
   Emits the format read by asm/triple.py (plus an `exp` line per case). Reproducible from SEED. -/
import Arm.CompilerArm
import Compiler.Front.Reify
import CodeFast
import CompilerArmFast
open Proven

abbrev G := ReaderT Bool (StateM UInt64)   -- reader: SMALL mode (constants mostly small)
def next : G UInt64 := modifyGet fun (s : UInt64) =>   -- splitmix64
  let s : UInt64 := s + 0x9E3779B97F4A7C15
  let z : UInt64 := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z : UInt64 := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)
def below (n : Nat) : G Nat := return (← next).toNat % n

def edge : Array Nat := #[0, 1, 2, 3, 2^63, 2^63 - 1, 2^64 - 1, 2^64 - 2, 2^32, 2^32 - 1, 0xFF, 0xFFF, 0x800, 0x7FF, 2^63 + 1, 63, 64, 65, 127, 128, 31, 32, 2^64 - 1]
def word : G Nat := do
  if (← below 3) == 0 then return edge[← below edge.size]! else
  -- uniform 64-bit
  return (← next).toNat
/-- constants: in SMALL mode mostly 12-bit signed values, else `word` -/
def wordC : G Nat := do
  if !(← read) then return ← word
  match ← below 4 with
  | 0 | 1 => let v ← below 2048; return if (← below 4) == 0 then 2^64 - v else v
  | 2 => return edge[← below edge.size]!
  | _ => return (← next).toNat
def Op.all : Array Op := #[.add, .sub, .and, .or, .xor, .shl, .lshr, .ashr, .ult, .slt, .eq]
instance : Inhabited Op := ⟨.add⟩
/-- all constructors of `Exp` the generator knows about; extend here when `Exp` grows -/
def genExp : Nat → G Exp
  | 0 => do if (← below 4) == 0 then return .const (BitVec.ofNat 64 (← wordC)) else return .var (Fin.ofNat 4 (← below 4))
  | f + 1 => do
    match ← below 12 with
    | 0 => genExp 0
    | 1 | 2 => do  -- ite; condition biased to 0 / nonzero constants and comparisons
      let c ← match ← below 4 with
        | 0 => pure (Exp.const 0)
        | 1 => pure (Exp.const (BitVec.ofNat 64 (1 + (← below 3))))
        | 2 => do pure (Exp.bin Op.all[8 + (← below 3)]! (← genExp (f / 2)) (← genExp (f / 2)))
        | _ => genExp f
      return .ite c (← genExp f) (← genExp f)
    | 3 => do  -- shift with edge shift amount
      let amt := #[0, 1, 63, 64, 65, 127, 2^64 - 1, 32][← below 8]!
      return .bin Op.all[5 + (← below 3)]! (← genExp f) (.const (BitVec.ofNat 64 amt))
    | _ => return .bin Op.all[← below Op.all.size]! (← genExp f) (← genExp f)
instance : Inhabited Exp := ⟨.const 0⟩
partial def genOk : G Exp := do
  let e ← genExp (← below 8)
  if e.depth < 11 then return e else genOk
def hex (w : Nat) : String := String.ofList (Nat.toDigits 16 w)

def fuzz : IO Unit := do
  let env := fun v => do return (← IO.getEnv v).get!
  let seed ← env "SEED"; let n ← env "NCASES"; let k ← env "K"
  let fast := (← IO.getEnv "BACKEND") == some "fast"   -- default: the proved std backend
  let small := (← IO.getEnv "SMALL") == some "1"   -- SMALL=1: mostly small constants
  let stats := (← IO.getEnv "MODE") == some "stats"    -- MODE=stats: print code-size table instead of test cases
  let mut s : UInt64 := seed.toNat!.toUInt64
  let mut es : Array Exp := #[]
  for i in [0:n.toNat!] do
    let (e, s') := (genOk.run small).run s
    s := s'
    assert! e.depth < 11
    if stats then es := es.push e; continue
    IO.println s!"case f{seed}_{i}"
    IO.println s!"exp {(repr e).pretty 100000 |>.replace "\n" " "}"
    let (rv, arm) := if fast then (Proven.Fast.compile e, Proven.Arm.Fast.compile e) else (compile e, Arm.compile e)
    IO.println s!"rv {" ".intercalate (rv.map (hex ·.toNat))}"
    IO.println s!"arm {" ".intercalate (arm.map (hex ·.toNat))}"
    for _ in [0:k.toNat!] do
      let (a, s') := (do let a ← word; let b ← word; let c ← word; let d ← word; pure [a, b, c, d] : G (List Nat)).run false |>.run s
      s := s'
      let env : Fin 4 → BitVec 64 := fun i => BitVec.ofNat 64 (a[i.val]!)
      IO.println s!"t {" ".intercalate (a.map hex)} {hex (e.denote env).toNat}"

#eval fuzz
