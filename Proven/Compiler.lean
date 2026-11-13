/- A tiny verified compiler: expressions over `BitVec 64` to RV64I code, run on the Sail model. -/
import Proven.Step
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Proven

/-! ## Source language -/

inductive Op where | add | sub | and | or | xor
  deriving DecidableEq, Repr

def Op.eval : Op → BitVec 64 → BitVec 64 → BitVec 64
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b

/-- Expressions over four 64-bit inputs (passed in `a0..a3`). -/
inductive Exp where
  | var (i : Fin 4)
  | const (c : BitVec 64)
  | bin (op : Op) (a b : Exp)
  deriving Repr

def Exp.denote (env : Fin 4 → BitVec 64) : Exp → BitVec 64
  | .var i => env i
  | .const c => c
  | .bin op a b => op.eval (a.denote env) (b.denote env)

/-- registers needed beyond the result register -/
def Exp.depth : Exp → Nat
  | .var _ | .const _ => 0
  | .bin _ a b => max a.depth (b.depth + 1)

/-! ## Target: RV64I words over a fixed register stack `t0 t1 t2 t3 t4` -/

def D : Nat := 5
/-- the register stack -/
def T : Fin 5 → Fin 32
  | 0 => 5 | 1 => 6 | 2 => 7 | 3 => 28 | 4 => 29
/-- argument registers `a0..a3` -/
def A : Fin 4 → Fin 32
  | 0 => 10 | 1 => 11 | 2 => 12 | 3 => 13

def encR (f7 f3 : Nat) (rd rs1 rs2 : Fin 32) : BitVec 32 :=
  BitVec.ofNat 32 (f7 <<< 25 ||| rs2.val <<< 20 ||| rs1.val <<< 15 ||| f3 <<< 12 ||| rd.val <<< 7 ||| 0x33)
def encI (f3 imm : Nat) (rd rs1 : Fin 32) : BitVec 32 :=
  BitVec.ofNat 32 (imm <<< 20 ||| rs1.val <<< 15 ||| f3 <<< 12 ||| rd.val <<< 7 ||| 0x13)

def Op.enc : Op → Fin 32 → Fin 32 → Fin 32 → BitVec 32
  | .add => encR 0 0 | .sub => encR 0x20 0 | .and => encR 0 7 | .or => encR 0 6 | .xor => encR 0 4

def iOp (op : Op) (k : Fin 4) : BitVec 32 := op.enc (T k.castSucc) (T k.castSucc) (T k.succ)
def iVar (i : Fin 4) (k : Fin 5) : BitVec 32 := encR 0 0 (T k) 0 (A i)   -- add tk, x0, ai
def iZero (k : Fin 5) : BitVec 32 := encI 0 0 (T k) 0                  -- addi tk, x0, 0
def iShl (k : Fin 5) : BitVec 32 := encI 1 1 (T k) (T k)               -- slli tk, tk, 1
def iInc (k : Fin 5) : BitVec 32 := encI 0 1 (T k) (T k)               -- addi tk, tk, 1
def iRes : BitVec 32 := encR 0 0 10 0 5                                 -- add a0, x0, t0
def iRet : BitVec 32 := 0x00008067#32                                   -- jalr x0, 0(ra)

/-- build the constant `n` in `t_k`, most significant bit first -/
def genConst (k : Fin 5) (n : Nat) : List (BitVec 32) :=
  if n = 0 then [iZero k] else genConst k (n / 2) ++ [iShl k] ++ (if n % 2 = 1 then [iInc k] else [])

/-- code leaving the value of `e` in `t_k`, clobbering only `t_k..t_4` -/
def gen : Exp → Fin 5 → List (BitVec 32)
  | .var i, k => [iVar i k]
  | .const c, k => genConst k c.toNat
  | .bin op a b, k =>
    if h : k.val + 1 < 5 then gen a k ++ gen b ⟨k.val + 1, h⟩ ++ [iOp op ⟨k.val, by omega⟩] else []

/-- the compiled function: result in `a0`, then `ret` -/
def compile (e : Exp) : List (BitVec 32) := gen e 0 ++ [iRes, iRet]

end Proven
