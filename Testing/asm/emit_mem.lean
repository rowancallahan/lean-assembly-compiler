/- Run-time memory tests of the inductive path (`Riscv/Frontx/IndMem.lean`): for every `frontx_ind` entry the code
with the run-time checks (`memCode`, the same program `indProgM` as the entry's `.code`), and per case the input,
Lean's result, and `memoryNeeded` (8 bytes times the peak of the run's events, computed by an interpreter of the
source run `TExec`, `Compiler/MemRun.lean`).  Run: `lake env lean --tstack=4000000 Testing/asm/emit_mem.lean`, then
`python3 Testing/asm/mem_test.py check 50 <name>` (QEMU + Sail: the run at `memoryNeeded` succeeds, at
`memoryNeeded - 1` it returns `a0 = -1` and writes nothing outside the output and work blocks). -/
import Riscv.Frontx.IndMem
import Riscv.Frontx.IndExamples
import Riscv.Frontx.Ind2Examples
import Riscv.Frontx.IndCmpExamples
open Proven.Frontx
open Proven (leN)
def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64

namespace MemInterp
open Proven.Top.Alloc
open Proven.Mach (BStmt BExp CStmt Prog)
/-- the interpreter's state: variables, byte blocks, the heap (word block 0) as arrays -/
structure St where
  env : Array (BitVec 64)
  heap : Array (Array (BitVec 8))
  W : Array (BitVec 64)
def St.get (σ : St) (i : Nat) : BitVec 64 := σ.env.getD i 0
def St.set (σ : St) (i : Nat) (v : BitVec 64) : St :=
  { σ with env := if i < σ.env.size then σ.env.set! i v else (σ.env ++ Array.replicate (i + 1 - σ.env.size) 0).set! i v }
def den (σ : St) : BExp → BitVec 64
  | .var i => σ.get i
  | .const c => c
  | .bin op a b => op.eval (den σ a) (den σ b)
  | .ite c a b => if den σ c = 0 then den σ b else den σ a
/-- grow the heap to `n` words with zeros; the event -/
def grow (σ : St) (n : Nat) (E : List MemEvent) : St × List MemEvent :=
  if σ.W.size < n then
    let σ' := { σ with W := σ.W ++ Array.replicate (n - σ.W.size) 0 }
    (σ'.set 7 (BitVec.ofNat 64 n), .alloc (n - σ.W.size) :: E)
  else (σ, E)
/-- an interpreter of `TExecB` / `TExec` (events newest first) -/
partial def evalB : BStmt → St → List MemEvent → Option (St × List MemEvent)
  | .assign v e, σ, E => some (σ.set v (den σ e), E)
  | .load v b i, σ, E => do
    let blk ← σ.heap[b]?
    let x ← blk[(den σ i).toNat]?
    some (σ.set v (x.setWidth 64), E)
  | .store b i e, σ, E => do
    let blk ← σ.heap[b]?
    let j := (den σ i).toNat
    if j < blk.size then some ({ σ with heap := σ.heap.set! b (blk.set! j ((den σ e).setWidth 8)) }, E) else none
  | .seq p q, σ, E => do let (σ₁, E₁) ← evalB p σ E; evalB q σ₁ E₁
  | .loop c b, σ, E => if den σ c = 0 then some (σ, E) else do
    let (σ₁, E₁) ← evalB b σ E; evalB (.loop c b) σ₁ E₁
  | .load64 v 0 i, σ, E =>
    let j := (den σ i).toNat; let (σ', E') := grow σ (j + 1) E
    some (σ'.set v (σ'.W.getD j 0), E')
  | .store64 0 i e, σ, E =>
    let j := (den σ i).toNat; let x := den σ e; let (σ', E') := grow σ (j + 1) E
    some ({ σ' with W := σ'.W.set! j x }, E')
  | _, _, _ => none
partial def evalC (P : Prog) : CStmt → St → List MemEvent → Option (St × List MemEvent)
  | .base p, σ, E => evalB p σ E
  | .seq p q, σ, E => do let (σ₁, E₁) ← evalC P p σ E; evalC P q σ₁ E₁
  | .ite c p q, σ, E => if den σ c ≠ 0 then evalC P p σ E else evalC P q σ E
  | .loop c b, σ, E => if den σ c = 0 then some (σ, E) else do
    let (σ₁, E₁) ← evalC P b σ E; evalC P (.loop c b) σ₁ E₁
  | .call res f args, σ, E => do
    let F ← P[f]?
    let vals := args.map (den σ)
    let env : Array (BitVec 64) := (σ.env.extract 0 8 ++ Array.replicate (8 - min 8 σ.env.size) 0) ++
      ((List.range F.nlocals).map fun j => vals.getD j 0).toArray
    let (σ₁, E₁) ← evalC P F.body { σ with env := env } (.alloc (F.nlocals + 1) :: E)
    let r := den σ₁ F.ret
    let back : St := { σ₁ with env := (σ₁.env.extract 0 8) ++ σ.env.extract 8 σ.env.size }
    some (back.set res r, .free (F.nlocals + 1) :: E₁)
/-- the peak, oldest event first (the same as `peak`) -/
def peakF (E : List MemEvent) : Nat :=
  (E.reverse.foldl (fun (c, m) e => match e with
    | .alloc n => (c + n, max m (c + n)) | .free n => (c - n, max m (c - n))) (0, 0)).2
/-- the canonical start (`IndMem.canon`): globals zero but the input length, a zero output block, empty heap -/
def canon (x : List UInt8) (m : Nat) : St :=
  ⟨(Array.replicate 8 0).set! 1 (BitVec.ofNat 64 x.length), #[(x.map (·.toBitVec)).toArray, Array.replicate m 0], #[]⟩
def runC (P : Prog) (x y : List UInt8) : Option (St × List MemEvent) := evalC P (.call 1 0 []) (canon x y.length) []
/-- `memoryNeeded`: the stub's two cells, then the run from the canonical start -/
def need (P : Prog) (x y : List UInt8) : Nat :=
  match runC P x y with
  | some (_, E) => 8 * peakF (E ++ [.alloc 2])
  | none => 0
/-- the output block after the run (to check the interpreter against Lean) -/
def outB (P : Prog) (x y : List UInt8) : Option (List UInt8) :=
  match runC P x y with
  | some (σ, _) => (σ.heap[1]?).map fun a => a.toList.map UInt8.ofBitVec
  | none => none
end MemInterp

open Lean Elab Term Meta in
/-- the program of an entry's `.code` (`callsCode1W P res 0`) -/
elab "prog%" n:ident : term => do
  let c ← realizeGlobalConstNoOverloadWithInfo n
  let some (.defnInfo d) := (← getEnv).find? c | throwError "not a definition"
  match d.value.getAppFnArgs with
  | (``Proven.Mach.Riscv.callsCode1W, #[P, _, _]) => return P
  | _ => throwError "not callsCode1W"

def emitM (name : String) (P : Proven.Mach.Prog) (retLen : Bool) (cases : List (List UInt8 × List UInt8)) : IO Unit := do
  let code := Proven.Mach.Riscv.memCode P 1 0
  IO.FS.writeFile s!"Testing/asm/mem-words/{name}.words"
    (String.intercalate "\n" (s!"mem {if retLen then 1 else 0}" :: code.map hex8) ++ "\n")
  let mut s := ""
  let mut bad := 0
  for (x, y) in cases do
    if MemInterp.outB P x y != some y then bad := bad + 1
    s := s ++ s!"{hx x} {hx y} {MemInterp.need P x y}\n"
  IO.FS.writeFile s!"Testing/asm/mem-words/{name}.cases" s
  IO.println s!"{name}: {code.length} words, {cases.length} cases, interpreter output != Lean: {bad}"
section
open Proven.Frontx.IndEx
/-- payloads: small, and some at and above `2^64` (the format keeps them mod `2^64`) -/
def payload (i : Nat) : Nat := match i % 7 with
  | 0 => rnd i 1 % 2 ^ 64 | 1 => 2 ^ 64 - 1 | 2 => 2 ^ 64 + 5 | _ => rnd i 2 % 1000
def genT : Nat → Nat → BinTree Nat
  | 0, _ => .leaf
  | d + 1, s => if rnd s d % 4 = 0 then .leaf else .branch (genT d (2 * s + 1)) (payload s) (genT d (2 * s + 2))
def trees : List (BinTree Nat) := [.leaf, .branch .leaf 7 .leaf] ++ (List.range 48).map fun i => genT (i % 6 + 1) (i + 3)
def genP : Nat → Pos | 0 => .one | n + 1 => .succ (genP n)
def poss : List Pos := (List.range 50).map fun i => genP (rnd i 5 % 60)
def lists : List (List Nat) := [[], [3], [2 ^ 64 - 1, 1]] ++ (List.range 47).map fun i =>
  (List.range (rnd i 9 % 25)).map fun j => payload (i * 31 + j)
def genL : Nat → Nat → ConLeche.Level
  | 0, s => if s % 2 = 0 then .zero else .param .anonymous
  | d + 1, s => match rnd s d % 8 with
    | 0 => .zero | 1 => .param .anonymous | 2 | 3 => .succ (genL d (s + 1))
    | 4 | 5 => .max (genL d (2 * s)) (genL d (2 * s + 1)) | _ => .imax (genL d (2 * s)) (genL d (2 * s + 1))
def levels : List ConLeche.Level := (List.range 50).map fun i => genL (i % 9) (i + 1)
def natB (n : Nat) : List UInt8 := leN 8 n
def boolB (b : Bool) : List UInt8 := [if b then 1 else 0]
#eval do
  emitM "bt_count" (prog% BinTree.count.code) false (trees.map fun t => (BTN.enc t, natB t.count))
  emitM "bt_mirror" (prog% BinTree.mirror.code) true (trees.map fun t => (BTN.enc t, BTN.enc t.mirror))
  emitM "bt_graftleft" (prog% BinTree.graftLeft.code) true
    ((List.range 50).map fun i => let p := (trees.getD i .leaf, trees.getD ((i * 7 + 3) % 50) .leaf); (BTN.enc2 p, BTN.enc (p.1.graftLeft p.2)))
  emitM "pos_tonat" (prog% Pos.toNat.code) false (poss.map fun p => (PosT.enc p, natB p.toNat))
  emitM "pos_plus" (prog% Pos.plus.code) true
    ((List.range 50).map fun i => let p := (poss.getD i .one, poss.getD ((i * 7 + 3) % 50) .one); (PosT.enc2 p, PosT.enc (p.1.plus p.2)))
  emitM "nontail_sum_ln" (prog% NonTail.sum.code) false (lists.map fun l => (LN.enc l, natB (NonTail.sum l)))
  emitM "tail_sum_ln" (prog% Tail.sum.code) false (lists.map fun l => (LN.enc l, natB (Tail.sum l)))
  emitM "tail_reverse_ln" (prog% Tail.reverse.code) true (lists.map fun l => (LN.enc l, LN.enc (Tail.reverse l)))
  emitM "list_append_ln" (prog% List.append.code) true
    ((List.range 50).map fun i => let p := (lists.getD i [], lists.getD ((i * 7 + 3) % 50) []); (LN.enc2 p, LN.enc (List.append p.1 p.2)))
  emitM "level_hasparam" (prog% ConLeche.levelHasParam.code) false
    (levels.map fun l => (LevelT.enc l, boolB (ConLeche.levelHasParam l)))
  emitM "level_isneverzero" (prog% ConLeche.Level.isNeverZero.code) false
    (levels.map fun l => (LevelT.enc l, boolB (ConLeche.Level.isNeverZero l)))
end
-- conditionals and comparisons (`IndCmpExamples.lean`, NOTES section 19): inputs in the subtype (every `Nat` field
-- below `2^64`); keys small (the key `5` is often present) and some near `2^64` (unsigned comparisons)
section
open Proven.Frontx.IndCmp
def key (i : Nat) : Nat := match i % 9 with
  | 0 => 2 ^ 64 - 1 - rnd i 4 % 3 | 1 => rnd i 1 % 2 ^ 63 + 2 ^ 63 | _ => rnd i 2 % 12
/-- binary search trees built by the book's own `insert` -/
def bsts : List (Tree Unit) := [.leaf, Tree.leaf.insert 5 ()] ++ (List.range 48).map fun i =>
  (List.range (rnd i 8 % 40)).foldl (fun t j => t.insert (key (i * 53 + j)) ()) .leaf
def keyLists : List (List Nat) := [[], [5], [2 ^ 64 - 1, 5, 5]] ++ (List.range 47).map fun i =>
  (List.range (rnd i 9 % 30)).map fun j => key (i * 31 + j)
#eval do
  emitM "tree_contains5" (prog% contains5.code) false (bsts.map fun t => (TU.enc t, boolB (contains5 t)))
  emitM "tree_insert5" (prog% insert5.code) true (bsts.map fun t => (TU.enc t, TU.enc (insert5 t)))
  emitM "list_elem5" (prog% elem5.code) false (keyLists.map fun l => (LN.enc l, boolB (elem5 l)))
  emitM "list_erase5" (prog% erase5.code) true (keyLists.map fun l => (LN.enc l, LN.enc (erase5 l)))
-- enumerations: every value (every pair), repeated to 50 cases
def days : List Weekday := [.monday, .tuesday, .wednesday, .thursday, .friday, .saturday, .sunday]
def ords : List Ordering := [.lt, .eq, .gt]
def cyc {α : Type} (xs : List α) : List α := (List.range 50).flatMap fun i => (xs.drop (i % xs.length)).take 1
#eval do
  emitM "weekday_isweekend_a" (prog% A.Weekday.isWeekend.code) false
    ((cyc days).map fun d => (WD.enc d, boolB (A.Weekday.isWeekend d)))
  emitM "weekday_isweekend_b" (prog% B.Weekday.isWeekend.code) false
    ((cyc days).map fun d => (WD.enc d, boolB (B.Weekday.isWeekend d)))
  emitM "ordering_swap" (prog% Ordering.swap.code) true ((cyc ords).map fun o => (OrdT.enc o, OrdT.enc o.swap))
  emitM "ordering_then" (prog% Ordering.then.code) true
    ((cyc (ords.flatMap fun a => ords.map fun b => (a, b))).map fun p => (OrdT.enc2 p, OrdT.enc (p.1.then p.2)))
  emitM "ordering_isle" (prog% Ordering.isLE.code) false ((cyc ords).map fun o => (OrdT.enc o, boolB o.isLE))
  emitM "ordering_iseq" (prog% Ordering.isEq.code) false ((cyc ords).map fun o => (OrdT.enc o, boolB o.isEq))
end
-- inductives, part 2 (`Ind2Examples.lean`, NOTES section 21): first line `indw <L>`, the work block per case: the
-- theorem's space with this input's cells (`Ind.spaceA m nl (fun _ => cells)`; the theorem's `cellsSup` is at
-- least that), or `Ind.spaceA 1 16 (fun n => M * n)` for one function
section
open Proven.Frontx.IndEx Proven.Frontx.IndCmp
def emitW (name : String) (P : Proven.Mach.Prog) (retLen : Bool) (cases : List (List UInt8 × List UInt8 × Nat)) :
    IO Unit := emitM name P retLen (cases.map fun (x, y, _) => (x, y))
def spW (m nl cells : Nat) (x : List UInt8) : Nat := Proven.Frontx.Ind.spaceA m nl (fun _ => cells) x.length
def possS : List Pos := (List.range 50).map fun i => genP (rnd i 5 % 40)
def posPairs : List (Pos × Pos) := (List.range 50).map fun i => (possS.getD i .one, possS.getD ((i * 7 + 3) % 50) .one)
/-- trees with payloads below `2^64` (the subtype of `eqBinTree`); every third pair equal, every third one payload apart -/
def genS : Nat → Nat → BinTree Nat
  | 0, _ => .leaf
  | d + 1, s => if rnd s d % 4 = 0 then .leaf else .branch (genS d (2 * s + 1)) (key s) (genS d (2 * s + 2))
/-- the payload of the rightmost node, plus one -/
def bump : BinTree Nat → BinTree Nat
  | .leaf => .leaf
  | .branch l x .leaf => .branch l ((x + 1) % 2 ^ 64) .leaf
  | .branch l x r => .branch l x (bump r)
def treePairs : List (BinTree Nat × BinTree Nat) := (List.range 50).map fun i =>
  let t := genS (i % 6 + 1) (i + 3)
  match i % 3 with | 0 => (t, t) | 1 => (t, genS (i % 5 + 1) (i + 11)) | _ => (t, bump t)
def keyTrees : List (Tree Unit × Nat) := (List.range 50).map fun i => (bsts.getD i .leaf, if i % 3 = 0 then 5 else key (i * 17 + 1))
def lvPairs : List (ConLeche.Level × ConLeche.Level) := (List.range 50).map fun i => (levels.getD i .zero, levels.getD ((i * 7 + 3) % 50) .zero)
def ordB (o : Ordering) : List UInt8 := OrdT.enc o
def smallT : BinTree Nat → Bool
  | .leaf => true | .branch l x r => decide (x < 2 ^ 64) && smallT l && smallT r
#eval do
  emitW "pos_mul" (prog% Pos.mul.code) true (posPairs.map fun p =>
    (PosT.enc2 p, PosT.enc (p.1.mul p.2), spW 2 16 (Pos.mul.ind.pg.al (PosT.emb p.1) 0 (PosT.emb p.2)) (PosT.enc2 p)))
  emitW "nontail_reverse_ln" (prog% NonTail.reverse.code) true (lists.map fun l =>
    (Proven.Frontx.IndEx.LN.enc l, Proven.Frontx.IndEx.LN.enc (NonTail.reverse l), spW 2 17 (NonTail.reverse.ind.pg.al (Proven.Frontx.IndEx.LN.emb l) 0 .z) (Proven.Frontx.IndEx.LN.enc l)))
  emitM "eq_bintree" (prog% eqBinTree.code) false
    (treePairs.map fun p => (BTN.enc2 p, boolB (eqBinTree p.1 p.2)))
  emitM "pos_comp" (prog% Pos.comp.code) true (posPairs.map fun p => (PosT.enc2 p, ordB (p.1.comp p.2)))
  emitW "tree_containsk" (prog% containsK.code) false (keyTrees.map fun (p : Tree Unit × Nat) =>
    let x := TU.enc p.1 ++ leN 8 p.2; (x, boolB (containsK p.1 p.2), Proven.Frontx.Ind.spaceA 1 16 (fun n => containsK.ind.pg.M * n) x.length))
  emitW "tree_findk" (prog% findK.code) true (keyTrees.map fun (p : Tree Unit × Nat) =>
    let x := TU.enc p.1 ++ leN 8 p.2; (x, OU.enc (findK p.1 p.2), Proven.Frontx.Ind.spaceA 1 16 (fun n => findK.ind.pg.M * n) x.length))
  emitM "level_combining" (prog% ConLeche.Level.combining.code) true
    (lvPairs.map fun (p : ConLeche.Level × ConLeche.Level) => (LevelT.enc2 p, LevelT.enc (ConLeche.Level.combining p.1 p.2)))
  emitW "level_simplify" (prog% ConLeche.Level.simplify.code) true (levels.map fun l =>
    (LevelT.enc l, LevelT.enc l.simplify, spW 2 20 (ConLeche.Level.simplify.ind.pg.al (LevelT.emb l) 0 .z) (LevelT.enc l)))
end
