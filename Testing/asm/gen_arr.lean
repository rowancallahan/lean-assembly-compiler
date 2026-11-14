/- Generator (c): random `AStmt` programs over 3 blocks (0 = read-only input, 1 = scratch, 2 = output) with in-bounds loads and
   stores by construction (index `ite (e <u L) e 0`, `L` the block length) and terminating loops by construction; expected state
   from a Lean interpreter of the `AExec` semantics.   usage: SEED=1 NPROG=50 K=8 lake env lean Testing/asm/gen_arr.lean > cases.txt -/
import Riscv.Direct.Arr
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
  if (← below 3) == 0 then pick #[0, 1, 2, 3, 63, 64, 65, 255, 256, 2^63, 2^64 - 1] else return (← next).toNat
instance : Inhabited Op := ⟨.add⟩
instance : Inhabited AExp := ⟨.const 0⟩
instance : Inhabited (Fin 8) := ⟨0⟩
def fin8 (n : Nat) : Fin 8 := Fin.ofNat 8 n
def ops : Array Op := #[.add, .sub, .and, .or, .xor, .shl, .lshr, .ashr, .ult, .slt, .eq]
def bvs : List (Fin 8) := [0, 1, 2]       -- base variables of blocks 0, 1, 2 (never assigned)
def scalars : List (Fin 8) := [3, 4, 5, 6, 7]

def genEv (vs : List (Fin 8)) : Nat → G AExp
  | 0 => do if (← below 4) == 0 then return .const (BitVec.ofNat 64 (← word)) else return .var (vs[← below vs.length]!)
  | f + 1 => do
    match ← below 9 with
    | 0 => genEv vs 0
    | 1 => return .ite (← genEv vs (f / 2)) (← genEv vs f) (← genEv vs f)
    | _ => return .bin (← pick ops) (← genEv vs f) (← genEv vs f)
def genE : Nat → G AExp := genEv scalars
/-- an in-bounds index into a block of length `L ≥ 1` -/
def idx (L : Nat) : G AExp := do
  let e ← genE (← below 3)
  let c := AExp.const (BitVec.ofNat 64 L)
  return .ite (.bin .ult e c) e (.const 0)

def asg (v : Fin 8) (e : AExp) : AStmt := .assign v e
def seqs : List AStmt → AStmt
  | [] => .assign 3 (.var 3)
  | [s] => s
  | s :: r => .seq s (seqs r)
def genS (lens : List Nat) : Nat → List (Fin 8) → G AStmt
  | d, forb => do
    let allowed := scalars.filter (!forb.contains ·)
    let n := 1 + (← below 4)
    let mut out : List AStmt := []
    for _ in [0:n] do
      let r ← below 9
      if allowed.length ≥ 3 && d > 0 && r == 6 then
        let c := allowed[← below allowed.length]!
        let N ← below 10
        let body ← genS lens (d - 1) (c :: forb)
        out := out ++ [asg c (.const 0), .loop (.bin .ult (.var c) (.const (BitVec.ofNat 64 N))) (.seq body (asg c (.bin .add (.var c) (.const 1))))]
      else if allowed.length ≥ 2 && d > 0 && r == 7 then
        let x := allowed[← below allowed.length]!
        let body ← genS lens (d - 1) (x :: forb)
        out := out ++ [asg x (.bin .and (.var x) (.const 7)), .loop (.var x) (.seq body (asg x (.bin .sub (.var x) (.const 1))))]
      else if allowed.isEmpty then out := out ++ [asg 3 (.var 3)]
      else if r < 3 then
        let b ← below 3
        out := out ++ [.load allowed[← below allowed.length]! b (← idx lens[b]!)]
      else if r < 5 then
        let b := 1 + (← below 2)
        out := out ++ [.store b (← idx lens[b]!) (← genE (← below 3))]
      else out := out ++ [asg allowed[← below allowed.length]! (← genE (← below 4))]
    return seqs out

def lt (a b : AExp) : AExp := .bin .ult a b
def idxG (L : Nat) (e : AExp) : AExp := .ite (lt e (.const (BitVec.ofNat 64 L))) e (.const 0)
def forLoop (c : Fin 8) (n : Nat) (body : AStmt) : AStmt :=
  seqs [.assign c (.const 0), .loop (lt (.var c) (.const (BitVec.ofNat 64 n))) (.seq body (.assign c (.bin .add (.var c) (.const 1))))]
/-- one phase over blocks of lengths `lens` (3 = i, 4 = j, 5 = acc, 6/7 = temporaries) -/
def phase (lens : List Nat) : G AStmt := do
  let i : AExp := .var 3; let j : AExp := .var 4
  match ← below 5 with
  | 0 => do   -- copy / map: scratch[i] := f(in[i])
    let n := 1 + (← below 24)
    return forLoop 3 n (seqs [.load 6 0 (idxG lens[0]! i), .store 1 (idxG lens[1]! i) (← genEv [6, 3, 5] (← below 3))])
  | 1 => do   -- in-place transform: out[i] := f(out[i], scratch[i])
    let n := 1 + (← below 24)
    return forLoop 3 n (seqs [.load 6 2 (idxG lens[2]! i), .load 7 1 (idxG lens[1]! i), .store 2 (idxG lens[2]! i) (← genEv [6, 7, 3] (← below 3))])
  | 2 => do   -- reduction over a block, result stored
    let n := 1 + (← below 24); let b ← below 3
    return seqs [.assign 5 (.const (BitVec.ofNat 64 (← below 5))),
      forLoop 3 n (seqs [.load 6 b (idxG lens[b]! i), .assign 5 (← genEv [5, 6, 3] (← below 3))]),
      .store 2 (idxG lens[2]! (.const 0)) (.var 5)]
  | 3 => do   -- nested loops over a 2-D index i*m + j, reading one block and updating another
    let m := 1 + (← below 6); let n := 1 + (← below 8)
    let ix := idxG lens[0]! (.bin .add (.bin .shl i (.const (BitVec.ofNat 64 (← below 3)))) j)
    return forLoop 3 n (forLoop 4 m (seqs [.load 6 0 ix, .load 7 2 (idxG lens[2]! j), .store 2 (idxG lens[2]! j) (← genEv [6, 7, 3, 4] (← below 3))]))
  | _ => do genS lens 1 []
def genPhased (lens : List Nat) : G AStmt := do
  let n := 2 + (← below 3)
  let mut ps : List AStmt := []
  for _ in [0:n] do ps := ps ++ [← phase lens]
  return seqs ps

def Proven.AStmt.okB : AStmt → Bool
  | .assign _ e => e.depth < 7
  | .load _ _ i => i.depth < 6
  | .store _ i e => i.depth < 6 && e.depth < 6
  | .seq a b => a.okB && b.okB
  | .loop c b => c.depth < 7 && b.okB && (gen8 c 0).length + (compileA bvs b).length + 2 < 1024

structure IS where
  env : Fin 8 → BitVec 64
  heap : Array (Array UInt8)
/-- interpreter with a step budget (every statement execution costs 1); `none` = budget exhausted; out-of-bounds
    access is a generator bug (panics) -/
partial def exec : AStmt → IS → Nat → Option (IS × Nat)
  | _, _, 0 => none
  | .assign v e, σ, f + 1 => some ({ σ with env := AEnv.set σ.env v (e.denote σ.env) }, f)
  | .load v b i, σ, f + 1 =>
    let k := (i.denote σ.env).toNat
    if k < σ.heap[b]!.size then some ({ σ with env := AEnv.set σ.env v (BitVec.ofNat 64 (σ.heap[b]!)[k]!.toNat) }, f)
    else panic! "generator bug: load out of bounds"
  | .store b i e, σ, f + 1 =>
    let k := (i.denote σ.env).toNat
    if k < σ.heap[b]!.size then some ({ σ with heap := σ.heap.set! b (σ.heap[b]!.set! k (e.denote σ.env).toNat.toUInt8) }, f)
    else panic! "generator bug: store out of bounds"
  | .seq a b, σ, f => do let (σ1, f1) ← exec a σ f; exec b σ1 f1
  | .loop c b, σ, f + 1 => if c.denote σ.env = 0 then some (σ, f) else do let (σ1, f1) ← exec b σ f; exec (.loop c b) σ1 f1

def hexb (bs : List UInt8) : String := if bs.isEmpty then "-" else
  String.join (bs.map fun b => let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s)
def hex32 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def blocks (h : Array (Array UInt8)) : String := ":".intercalate (h.toList.map fun b => hexb b.toList)

def bucket (n : Nat) : String :=
  if n ≤ 100 then "<=100" else if n ≤ 200 then "<=200" else if n ≤ 400 then "<=400" else if n ≤ 800 then "<=800" else ">800"
def bump (a : Array (String × Nat)) (k : String) : Array (String × Nat) :=
  match a.findIdx? (·.1 == k) with
  | some i => a.modify i fun (k, n) => (k, n + 1)
  | none => a.push (k, 1)
def showStat (a : Array (String × Nat)) : String := ", ".intercalate (a.toList.map fun (k, n) => s!"{k}:{n}")

def genMain : IO Unit := do
  let env := fun v => do return (← IO.getEnv v).get!
  let seed ← env "SEED"; let np ← env "NPROG"; let k ← env "K"
  let budget := 8000
  let mut s : UInt64 := seed.toNat!.toUInt64
  let mut made := 0; let mut tried := 0; let mut over := 0; let mut notwf := 0; let mut phased := 0
  let mut hist : Array (String × Nat) := #[]; let mut steps : Array (String × Nat) := #[]
  while made < np.toNat! do
    tried := tried + 1
    let (lens, s1) := (do pure [1 + (← below 40), 1 + (← below 40), 1 + (← below 40)] : G (List Nat)).run s
    let (ph, s1) := (below 5).run s1
    let (p, s2) := (if ph < 3 then genPhased lens else genS lens 2 []).run s1
    s := s2
    if !p.okB then notwf := notwf + 1; continue
    let mut ins : List String := []
    let mut good := true; let mut st := 0
    for _ in [0:k.toNat!] do
      let (vs, s') := ((List.range 8).mapM fun _ => word : G (List Nat)).run s
      let (hs, s'') := (lens.mapM fun L => (List.range L).mapM fun _ => (do pure (← below 256).toUInt8 : G UInt8)).run s'
      s := s''
      let σ : IS := ⟨fun i => BitVec.ofNat 64 vs[i.val]!, (hs.map fun l => l.toArray).toArray⟩
      match exec p σ budget with
      | none => good := false
      | some (r, f) =>
        st := max st (budget - f)
        ins := ins ++ [s!"in v={",".intercalate (vs.map toString)} b={":".intercalate (hs.map hexb)} ev={",".intercalate ((List.range 8).map fun i => toString (r.env (fin8 i)).toNat)} eb={blocks r.heap}"]
    if !good then over := over + 1; continue
    let code := compileAF bvs p
    hist := bump hist (bucket code.length); steps := bump steps (if st ≤ 100 then "<=100" else if st ≤ 1000 then "<=1000" else "<=8000")
    if ph < 3 then phased := phased + 1
    IO.println s!"prog arr_{seed}_{made}"
    IO.println "kind var8"
    IO.println s!"words {" ".intercalate (code.map hex32)}"
    IO.println "bv 0 1 2"
    IO.println "rw 0 1 1"
    for l in ins do IO.println l
    made := made + 1
  IO.println s!"# STAT arr: accepted {made} of {tried} generated ({phased} multi-phase); code words {showStat hist}; max statements executed {showStat steps}; dropped: over step budget {over}, not wf (depth/branch range) {notwf}"
#eval genMain
