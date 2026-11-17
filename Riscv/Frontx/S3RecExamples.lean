/- **Recursion through S3** (`Testing/notes/S3_REC.md`): recursive functions compiled from their equation lemmas
(`f.eq_def`), certified by Lean's own induction principles (`f.induct`; `f.mutual_induct`, ONE induction for a whole
mutual component).  Each entry: `main = encodeOut ∘ f ∘ decodeIn` (byte formats below and in `S3IO.lean`), the S3
program, certificates, `computes`, `correct` (exactly the Sail axioms).  Tests: `Testing/asm/emit_s3rec.lean`,
`python3 Testing/asm/ir_test.py check 50 s3_<name>`.

| entry | function under test | recursion |
|---|---|---|
| `S3Incs` | `Mach.IR.SR.incs` (self-hoster, verbatim) | structural (`List.brecOn`), `Nat`, result `Code Nat` |
| `S3Inits` | `Mach.IR.SR.inits` (verbatim) | structural (`List.brecOn`), extra `Nat` parameter |
| `S3Sets` | `Mach.IR.Hoist.sets` (verbatim) | structural (`List.brecOn`), `Nat` accumulator `m + 1` (`Nat.add`) |
| `S3InitL` | `Mach.initL` (verbatim, static `sp : Nat → Bool`) | structural (`List.brecOn`), `Nat.beq`/`Nat.blt` |
| `S3StoreRegs` | `Ir.storeRegs` (verbatim) | structural on two lists, `Reg = Fin 15`, result `List EOp` (`Int` field) |
| `S3FetchG` | `fetchG` (verbatim) | structural, accumulator `AStmt` (`Fin 8` fields) |
| `S3Merge` | `merge` | well-founded (`termination_by xs.length + ys.length`), not structural |
| `S3EvOd` | `evSum` / `odCnt` | mutual, different result types, non-tail calls |
| `S3Lex` | `lex` | lexicographic `(xs.length, k.toNat)`, the inner counter resets |
| `S3IotaNumArgs` | con-leche `Cached.iotaNumArgs` (`CoreC.lean`, verbatim) | structural over con-leche's `Expr` |
| `S3MkAppRange` | con-leche `Cached.mkAppRange` (`CoreC.lean`, verbatim) | well-founded (`termination_by j - i`), `args[i]` with its proof (`List.get`, dependent `Fin xs.length`) |
| `S3GetAppArgsArr` | con-leche `Cached.getAppArgsArr` + `getAppArgsArrGo` + `iotaNumArgs` (verbatim) | structural; `Array.set!`, `Array.replicate` from their equations |
| `S3StExc` | `stepS : List UInt64 → StateT UInt64 (Except UInt8) UInt64` | structural; state and exception across a non-tail call |
-/
import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Compiler.Opt.Hoist
import Compiler.Opt.BFn
import Compiler.Ir.Emit
import Compiler.Front.Pipe
import Riscv.Frontx.ExprExamples

namespace Proven.S3.Rec
open Proven.S3 Proven.S3.Ex Proven.Mach.IR

/-! ## byte formats and harness -/


s3_enc Proven.Op
s3_enc Proven.Mach.MOp
s3_enc Proven.Mach.Cond
s3_enc Proven.Mach.IR.Arg
s3_enc Proven.Mach.IR.Tst
s3_enc Proven.Mach.IR.Ins
s3_enc Proven.Mach.IR.Code

/-- harness: a `Nat` as a word -/
def natW : Nat → UInt64
  | 0 => 0
  | n + 1 => natW n + 1
/-- harness: a word as a `Nat` (well-founded) -/
def wNat (x : UInt64) : Nat := if h : x = 0 then 0 else wNat (x - 1) + 1
termination_by x.toNat
decreasing_by
  have hk : x.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega

def opB : Proven.Op → UInt8
  | .add => 0 | .sub => 1 | .and => 2 | .or => 3 | .xor => 4 | .shl => 5 | .lshr => 6 | .ashr => 7
  | .ult => 8 | .slt => 9 | .eq => 10
def mopB : Proven.Mach.MOp → UInt8
  | .mul => 0 | .divu => 1 | .remu => 2 | .div => 3 | .rem => 4
def condB : Proven.Mach.Cond → UInt8
  | .eq => 0 | .ne => 1 | .ltu => 2 | .geu => 3 | .lt => 4 | .ge => 5
def argB : Arg Nat → List UInt8
  | .r x => 0 :: enc8 (natW x)
  | .i c => 1 :: enc8 (UInt64.ofBitVec c)
def tstB (t : Tst Nat) : List UInt8 := condB t.c :: (argB t.a ++ argB t.b)
def insB : Ins Nat → List UInt8
  | .set d a => 0 :: (enc8 (natW d) ++ argB a)
  | .bin o d a b => 1 :: opB o :: (enc8 (natW d) ++ argB a ++ argB b)
  | .mop o d a b => 2 :: mopB o :: (enc8 (natW d) ++ argB a ++ argB b)
  | .lbu d a off => 3 :: (enc8 (natW d) ++ argB a ++ enc8 (UInt64.ofBitVec off))
  | .sb v a off => 4 :: (argB v ++ argB a ++ enc8 (UInt64.ofBitVec off))
  | .ldS d j => 5 :: (enc8 (natW d) ++ enc8 (natW j))
  | .stS j v => 6 :: (enc8 (natW j) ++ enc8 (natW v))
  | .ld d a off => 7 :: (enc8 (natW d) ++ enc8 (natW a) ++ enc8 (UInt64.ofBitVec off))
  | .sd v a off => 8 :: (enc8 (natW v) ++ enc8 (natW a) ++ enc8 (UInt64.ofBitVec off))
def codeB : Code Nat → List UInt8
  | .skip => [0]
  | .ins i => 1 :: insB i
  | .seq a b => 2 :: (codeB a ++ codeB b)
  | .when t b => 3 :: (tstB t ++ codeB b)
  | .loop p t b => 4 :: (codeB p ++ tstB t ++ codeB b)
  | .loop2 p t q u b => 5 :: (codeB p ++ tstB t ++ codeB q ++ tstB u ++ codeB b)

/-- pairs of byte-sized `Nat`s -/
def pairsN : List UInt8 → List (Nat × Nat)
  | a :: b :: r => (wNat a.toUInt64, wNat b.toUInt64) :: pairsN r
  | _ => []

def incsMain (bs : List UInt8) : List UInt8 := codeB (SR.incs (pairsN bs))
s3_compile S3Incs := incsMain
def initsMain (bs : List UInt8) : List UInt8 :=
  match bs with
  | i :: r => codeB (SR.inits (wNat i.toUInt64) (pairsN r))
  | [] => []
s3_compile S3Inits := initsMain

def setsMain (bs : List UInt8) : List UInt8 :=
  match decW bs with
  | m :: r => codeB (Hoist.sets (wNat (m &&& 255)) (r.map UInt64.toBitVec))
  | [] => []
s3_compile S3Sets := setsMain

def natsN : List UInt8 → List Nat
  | a :: r => wNat a.toUInt64 :: natsN r
  | [] => []
def initLMain (bs : List UInt8) : List UInt8 := codeB (Proven.Mach.initL (fun j => j == 3 || j < 2) (natsN bs))
s3_compile S3InitL := initLMain

/-! ### `Fin` (proof fields not stored), `Int`, `AStmt` -/

s3_enc Int
s3_enc Proven.Mach.WOp
s3_enc Proven.Ir.EOp
s3_enc Proven.AExp
s3_enc Proven.AStmt

def regB (r : Proven.Mach.Reg) : UInt64 := natW r.val
def eopB : Proven.Ir.EOp → List UInt8
  | .w (.stS j v) => 1 :: (enc8 (natW j) ++ enc8 (regB v))
  | _ => [0]
def eopsB : List Proven.Ir.EOp → List UInt8
  | [] => []
  | o :: r => eopB o ++ eopsB r
def regsN : List UInt8 → List Proven.Mach.Reg
  | a :: r => (if h : wNat a.toUInt64 < 15 then ⟨wNat a.toUInt64, h⟩ else ⟨14, by decide⟩) :: regsN r
  | [] => []
def storeRegsMain (bs : List UInt8) : List UInt8 :=
  match decW bs with
  | n :: _ => eopsB (Proven.Ir.storeRegs (natsN (bs.take (wNat (n &&& 15)))) (regsN bs))
  | [] => []
s3_compile S3StoreRegs := storeRegsMain
def fin8 (b : UInt8) : Fin 8 := if h : wNat (b.toUInt64 &&& 7) < 8 then ⟨wNat (b.toUInt64 &&& 7), h⟩ else 0
def aexpB : Proven.AExp → List UInt8
  | .var i => [0, (natW i.val).toUInt8]
  | .const c => 1 :: enc8 (UInt64.ofBitVec c)
  | .bin o a b => 2 :: opB o :: (aexpB a ++ aexpB b)
  | .ite c a b => 3 :: (aexpB c ++ aexpB a ++ aexpB b)
def astmtB : Proven.AStmt → List UInt8
  | .assign v e => 0 :: (natW v.val).toUInt8 :: aexpB e
  | .load v b i => 1 :: (natW v.val).toUInt8 :: (enc8 (natW b) ++ aexpB i)
  | .store b i e => 2 :: (enc8 (natW b) ++ aexpB i ++ aexpB e)
  | .seq p q => 3 :: (astmtB p ++ astmtB q)
  | .loop c b => 4 :: (aexpB c ++ astmtB b)
/-- expressions: `0 i` a variable, `1 c` a constant byte, `2 a b` a sum of the next two -/
def aexpsN : List UInt8 → List Proven.AExp
  | k :: c :: r =>
    (if k == 0 then .var (fin8 c) else if k == 1 then .const c.toUInt64.toBitVec
     else .bin .add (.var (fin8 c)) (.const 5)) :: aexpsN r
  | _ => []
def fetchGMain (bs : List UInt8) : List UInt8 :=
  astmtB (Proven.fetchG (.assign 3 (.const 7)) (aexpsN bs))
s3_compile S3FetchG := fetchGMain

/-! ## (b) well-founded, not structural -/


/-- (b) well-founded, not structural: merge by total length -/
def merge : List UInt64 → List UInt64 → List UInt64
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => if x ≤ y then x :: merge xs (y :: ys) else y :: merge (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- the words of the input, split at the first zero word, merged -/
def splitZ : List UInt64 → List UInt64 × List UInt64
  | [] => ([], [])
  | x :: r => if x = 0 then ([], r) else match splitZ r with | (a, b) => (x :: a, b)
def mergeMain (bs : List UInt8) : List UInt8 :=
  match splitZ (decW bs) with
  | (a, b) => encW (merge a b)
s3_compile S3Merge := mergeMain

/-! ## (c) mutual and (d) lexicographic -/


mutual
/-- (c) mutual, different result types, non-tail calls -/
def evSum : List UInt64 → List UInt64
  | [] => []
  | x :: r => (x + odCnt r) :: evSum r
def odCnt : List UInt64 → UInt64
  | [] => 0
  | x :: r => match evSum r with
    | [] => x
    | y :: _ => x * 2 + y
end

/-- (d) lexicographic measure; the inner counter resets from the next word -/
def lex : List UInt64 → UInt64 → UInt64 → UInt64
  | [], _, acc => acc
  | x :: r, k, acc =>
    if h : k = 0 then lex r (x &&& 7) (acc + x) else lex (x :: r) (k - 1) (acc * 3 + k)
termination_by xs k => (xs.length, k.toNat)
decreasing_by
  · exact Prod.Lex.left _ _ (by simp)
  · apply Prod.Lex.right
    have hk : k.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
def evMain (bs : List UInt8) : List UInt8 := encW (evSum (decW bs))
s3_compile S3EvOd := evMain
def lexMain (bs : List UInt8) : List UInt8 :=
  match decW bs with
  | k :: r => enc8 (lex r k 1)
  | [] => []
s3_compile S3Lex := lexMain

/-! ## state + exceptions across recursive calls (`StateT UInt64 (Except UInt8)`, CONLECHE_KNOT.md step 5) -/

s3_enc Except

/-- a running sum in the state, an exception at a zero word, a non-tail recursive call between them -/
def stepS : List UInt64 → StateT UInt64 (Except UInt8) UInt64
  | [] => return 0
  | x :: r => do
    if x == 0 then throw 7
    let s ← get
    set (s + x)
    let t ← stepS r
    return t * 2 + s

def stMain (bs : List UInt8) : List UInt8 :=
  match (stepS (decW bs)).run 1 with
  | .ok (a, s) => enc8 a ++ enc8 s
  | .error e => [e]
s3_compile S3StExc := stMain


/-! ## con-leche `CoreC`: its smallest recursive component, verbatim -/

-- con-leche `ConLeche/Cached/CoreC.lean` (`Testing/conleche-depth/out/F2.lean.txt` on `origin/conleche-depth`,
-- lines 17868-17873; con-leche @6810492c1), verbatim; over con-leche's `Expr` (`ExprExamples.lean`: `Name` with `String`, `Level`,
-- `Literal`)
end Proven.S3.Rec
namespace ConLeche.Cached
open ConLeche
/-- The length of an application spine, without building its argument
list. -/
def iotaNumArgs : Expr → Nat → Nat
  | .app f _, n => iotaNumArgs f (n + 1)
  | _, n => n

-- (F2.lean.txt lines 17875-17885)
/-- Fill `acc` from position `i` down with the arguments of the spine `e`,
innermost first (`getAppArgsArr`). -/
def getAppArgsArrGo : Expr → Nat → Array Expr → Array Expr
  | .app f a, i + 1, acc => getAppArgsArrGo f i (acc.set! i a)
  | _, _, acc => acc

/-- **The arguments of an application spine, as an array** (outermost
last), written into an array of the spine's length from the back: no
list is built. -/
@[inline] def getAppArgsArr (e : Expr) : Array Expr :=
  getAppArgsArrGo e (iotaNumArgs e 0) (Array.replicate (iotaNumArgs e 0) e)

-- (F2.lean.txt lines 17889-17893)
/-- **`f` applied to the arguments `args[i:j]`**, the range read in
place. -/
def mkAppRange (f : Expr) (args : Array Expr) (i j : Nat) : Expr :=
  if h : i < j ∧ i < args.size then mkAppRange (.app f args[i]) args (i + 1) j else f
termination_by j - i
end ConLeche.Cached
namespace Proven.S3.Rec
open Proven.S3 Proven.S3.Ex Proven.Mach.IR

s3_enc ConLeche.Name
s3_enc ConLeche.Level
s3_enc ConLeche.Literal
s3_enc ConLeche.Expr

/-- a spine: byte `b` is the argument `.bvar b`, the head `.sort .zero` -/
def spine : List UInt8 → ConLeche.Expr
  | [] => .sort .zero
  | b :: r => .app (spine r) (.bvar (wNat b.toUInt64))
def numArgsMain (bs : List UInt8) : List UInt8 := enc8 (natW (ConLeche.Cached.iotaNumArgs (spine bs) 0))
s3_compile S3IotaNumArgs := numArgsMain

/-- expressions in postorder: `2` an application of the two before it, `k b` (`k ≠ 2`) the expression `.bvar b`
(a stack machine) -/
def exprsGo : List UInt8 → List ConLeche.Expr → List ConLeche.Expr
  | [], st => st
  | b :: r, st =>
    if b == 2 then match st with
      | a :: f :: st' => exprsGo r (.app f a :: st')
      | [a] => exprsGo r [a]
      | [] => exprsGo r []
    else match r with
      | x :: r' => exprsGo r' (.bvar (wNat x.toUInt64) :: st)
      | [] => st
def exprB : ConLeche.Expr → List UInt8
  | .app f a => 2 :: (exprB f ++ exprB a)
  | .bvar i => [1, (natW i).toUInt8]
  | _ => [0]
def rangeMain (bs : List UInt8) : List UInt8 :=
  match bs with
  | i :: j :: r => exprB (ConLeche.Cached.mkAppRange (.sort .zero) (exprsGo r []).toArray (wNat i.toUInt64) (wNat j.toUInt64))
  | _ => []
s3_compile S3MkAppRange := rangeMain

def argsMain (bs : List UInt8) : List UInt8 :=
  (ConLeche.Cached.getAppArgsArr (spine bs)).toList.flatMap exprB
s3_compile S3GetAppArgsArr := argsMain

end Proven.S3.Rec
