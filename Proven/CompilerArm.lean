/- AArch64 backend for the same `Exp` language. NOT yet proved against the ARM Sail model. -/
import Proven.Compiler
namespace Proven.Arm
open Proven

/-- temporaries `x9..x13`; arguments and result in `x0..x3` / `x0` -/
def T (k : Nat) : Nat := 9 + min k 4
def rrr (base rd rn rm : Nat) : BitVec 32 := BitVec.ofNat 32 (base ||| rm <<< 16 ||| rn <<< 5 ||| rd)

def Op.base : Op → Nat
  | .add => 0x8B000000 | .sub => 0xCB000000 | .and => 0x8A000000 | .or => 0xAA000000 | .xor => 0xCA000000

def iOp (op : Op) (k : Nat) := rrr (Op.base op) (T k) (T k) (T (k + 1))   -- op xk, xk, xk+1
def iVar (i k : Nat) := rrr 0xAA000000 (T k) 31 i                        -- mov xk, xi
def iZero (k : Nat) : BitVec 32 := BitVec.ofNat 32 (0xD2800000 ||| T k)  -- movz xk, #0
def iShl (k : Nat) := rrr 0x8B000000 (T k) (T k) (T k)                    -- add xk, xk, xk
def iInc (k : Nat) : BitVec 32 := BitVec.ofNat 32 (0x91000400 ||| T k <<< 5 ||| T k) -- add xk, xk, #1
def iRes := rrr 0xAA000000 0 31 (T 0)                                     -- mov x0, x9
def iRet : BitVec 32 := 0xD65F03C0#32

def genConst (k n : Nat) : List (BitVec 32) :=
  if n = 0 then [iZero k] else genConst k (n / 2) ++ [iShl k] ++ (if n % 2 = 1 then [iInc k] else [])

def gen : Exp → Nat → List (BitVec 32)
  | .var i, k => [iVar i k]
  | .const c, k => genConst k c.toNat
  | .bin op a b, k => gen a k ++ gen b (k + 1) ++ [iOp op k]

def compile (e : Exp) : List (BitVec 32) := gen e 0 ++ [iRes, iRet]
end Proven.Arm
