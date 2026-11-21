/- S3 recursion examples, part B (from branch s3-rec via ir-strong; split off `S3RecExamples` for the 5-min module
budget): `Fin` / `Int` / `AStmt` encodings (`S3StoreRegs`, `S3FetchG`), state + exceptions across recursive calls
(`S3StExc`), con-leche `Cached.iotaNumArgs` verbatim (`S3IotaNumArgs`).  Format of each entry as in
`Riscv/Frontx/S3RecExamples.lean`. -/
import Legacy.Riscv.Frontx.S3RecExamplesA
import Legacy.Compiler.Ir.Emit
import Nano.Base.Compiler.Front.Pipe
import Legacy.Riscv.Frontx.ExprExamples

namespace Proven.S3.Rec
open Proven.S3 Proven.S3.Ex Proven.Mach.IR

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

end Proven.S3.Rec
