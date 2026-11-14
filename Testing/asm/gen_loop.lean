/- Generator (b): random terminating `Stmt` programs (counted loops / countdown loops, so termination is by construction),
   expected final a0..a3 from a fuel-bounded Lean evaluator of the `Exec` semantics.
   usage: SEED=1 NPROG=50 K=16 lake env lean Testing/asm/gen_loop.lean > cases.txt -/
import Riscv.Direct.Loop
open Proven

abbrev G := StateM UInt64
def next : G UInt64 := modifyGet fun (s : UInt64) =>
  let s : UInt64 := s + 0x9E3779B97F4A7C15
  let z : UInt64 := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z : UInt64 := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)
def below (n : Nat) : G Nat := return (← next).toNat % n
def pick {α} [Inhabited α] (a : Array α) : G α := do return a[← below a.size]!
def word : G Nat := do
  if (← below 3) == 0 then pick #[0, 1, 2, 3, 63, 64, 65, 2^63, 2^63 - 1, 2^64 - 1, 2^32] else return (← next).toNat
instance : Inhabited Op := ⟨.add⟩
instance : Inhabited Exp := ⟨.const 0⟩
instance : Inhabited (Fin 4) := ⟨0⟩
def fin4 (n : Nat) : Fin 4 := Fin.ofNat 4 n
def ops : Array Op := #[.add, .sub, .and, .or, .xor, .shl, .lshr, .ashr, .ult, .slt, .eq]

def genE : Nat → G Exp
  | 0 => do if (← below 4) == 0 then return .const (BitVec.ofNat 64 (← word)) else return .var (fin4 (← below 4))
  | f + 1 => do
    match ← below 9 with
    | 0 => genE 0
    | 1 => return .ite (← genE (f / 2)) (← genE f) (← genE f)
    | 2 => return .bin (← pick #[Op.shl, .lshr, .ashr]) (← genE f) (.const (BitVec.ofNat 64 (← pick #[0, 1, 63, 64, 65, 127])))
    | _ => return .bin (← pick ops) (← genE f) (← genE f)

def asg (v : Fin 4) (e : Exp) : Stmt := .assign v e
def seqs : List Stmt → Stmt
  | [] => .assign 0 (.var 0)
  | [s] => s
  | s :: r => .seq s (seqs r)
def inc (c : Fin 4) : Stmt := asg c (.bin .add (.var c) (.const 1))

/-- `forb`: variables the generated code must not assign (loop counters and bounds of enclosing loops) -/
def genS : Nat → List (Fin 4) → G Stmt
  | d, forb => do
    let allowed := (List.range 4).map fin4 |>.filter (!forb.contains ·)
    let n := 1 + (← below (if d ≥ 2 then 5 else 3))
    let mut out : List Stmt := []
    for _ in [0:n] do
      let r ← below 6
      if allowed.length ≥ 3 && d > 0 && r == 4 then      -- counted loop: c := 0; while c < N do body; c := c + 1
        let c := allowed[← below allowed.length]!
        let b := (allowed.filter (· != c))[← below (allowed.length - 1)]!
        let bound ← match ← below 2 with
          | 0 => pure (Exp.const (BitVec.ofNat 64 (← below 13)))
          | _ => pure (Exp.bin .add (.bin .and (.var b) (.const 7)) (.const 1))
        let body ← genS (d - 1) (c :: b :: forb)
        out := out ++ [asg c (.const 0), .loop (.bin .ult (.var c) bound) (.seq body (inc c))]
      else if allowed.length ≥ 2 && d > 0 && r == 5 then   -- countdown: x := x & 15; while x ≠ 0 do body; x := x - 1
        let x := allowed[← below allowed.length]!
        let body ← genS (d - 1) (x :: forb)
        out := out ++ [asg x (.bin .and (.var x) (.const 15)), .loop (.var x) (.seq body (asg x (.bin .sub (.var x) (.const 1))))]
      else if allowed.isEmpty then out := out ++ [asg 0 (.var 0)]   -- harmless no-op
      else out := out ++ [asg allowed[← below allowed.length]! (← genE (← below 4))]
    return seqs out

def Proven.Stmt.okB : Stmt → Bool
  | .assign _ e => e.depth < 11
  | .seq a b => a.okB && b.okB
  | .loop c b => c.depth < 11 && b.okB && (gen c 0).length + (compileS b).length + 2 < 1024

/-- interpreter of the `Exec` semantics with a step budget (each statement execution costs 1) -/
partial def exec : Stmt → (Fin 4 → BitVec 64) → Nat → Option ((Fin 4 → BitVec 64) × Nat)
  | _, _, 0 => none
  | .assign v e, σ, f + 1 => some (Env.set σ v (e.denote σ), f)
  | .seq a b, σ, f => do let (σ1, f1) ← exec a σ f; exec b σ1 f1
  | .loop c b, σ, f + 1 => if c.denote σ = 0 then some (σ, f) else do let (σ1, f1) ← exec b σ f; exec (.loop c b) σ1 f1
def bucket (n : Nat) : String :=
  if n ≤ 50 then "<=50" else if n ≤ 100 then "<=100" else if n ≤ 200 then "<=200" else if n ≤ 400 then "<=400" else ">400"
def bump (a : Array (String × Nat)) (k : String) : Array (String × Nat) :=
  match a.findIdx? (·.1 == k) with
  | some i => a.modify i fun (k, n) => (k, n + 1)
  | none => a.push (k, 1)
def showStat (a : Array (String × Nat)) : String := ", ".intercalate (a.toList.map fun (k, n) => s!"{k}:{n}")
def hex32 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s

def genMain : IO Unit := do
  let env := fun v => do return (← IO.getEnv v).get!
  let seed ← env "SEED"; let np ← env "NPROG"; let k ← env "K"
  let mut s : UInt64 := seed.toNat!.toUInt64
  let mut hist : Array (String × Nat) := #[]; let mut steps : Array (String × Nat) := #[]
  let mut made := 0; let mut tried := 0
  while made < np.toNat! do
    tried := tried + 1
    let (p, s') := (genS 3 []).run s
    s := s'
    if !p.okB then continue
    let mut ins : List String := []
    let mut good := true; let mut st := 0
    for _ in [0:k.toNat!] do
      let (a, s') := (do let a ← word; let b ← word; let c ← word; let d ← word; pure [a, b, c, d] : G (List Nat)).run s
      s := s'
      let σ : Fin 4 → BitVec 64 := fun i => BitVec.ofNat 64 a[i.val]!
      match exec p σ 8000 with
      | none => good := false
      | some (r, f) =>
        st := max st (8000 - f)
        ins := ins ++ [s!"in v={",".intercalate (a.map toString)},1,2,3,4 ev={",".intercalate ((List.range 4).map fun i => toString (r (fin4 i)).toNat)},?,?,?,?"]
    if !good then continue
    hist := bump hist (bucket (compileF p).length); steps := bump steps (if st ≤ 100 then "<=100" else if st ≤ 1000 then "<=1000" else "<=8000")
    IO.println s!"prog loop_{seed}_{made}"
    IO.println "kind var8"
    IO.println s!"words {" ".intercalate ((compileF p).map hex32)}"
    IO.println "bv"
    IO.println "rw"
    for l in ins do IO.println l
    made := made + 1
  IO.println s!"# STAT loop: accepted {made} of {tried} generated; code words {showStat hist}; max statements executed {showStat steps}"
#eval genMain
