/- AArch64 backend for the same `Exp` language. NOT proved against the ARM Sail model; tested only. -/
import Proven.Code
namespace Proven.Arm
open Proven

/-- temporaries `x9..x15, x4..x7`; arguments and result in `x0..x3` / `x0` -/
def T : Nat → Nat
  | 0 => 9 | 1 => 10 | 2 => 11 | 3 => 12 | 4 => 13 | 5 => 14 | 6 => 15 | 7 => 4 | 8 => 5 | 9 => 6 | _ => 7
def rrr (base rd rn rm : Nat) : BitVec 32 := BitVec.ofNat 32 (base ||| rm <<< 16 ||| rn <<< 5 ||| rd)

/-- `cset xk, c` = `csinc xk, xzr, xzr, !c`, given the inverted condition code -/
def cset (inv k : Nat) := rrr (0x9A800400 ||| inv <<< 12) (T k) 31 31
def cmp (k : Nat) := rrr 0xEB000000 31 (T k) (T (k + 1))                   -- cmp xk, xk+1

def opCode (op : Op) (k : Nat) : List (BitVec 32) :=
  let r base := [rrr base (T k) (T k) (T (k + 1))]                        -- op xk, xk, xk+1
  match op with
  | .add => r 0x8B000000 | .sub => r 0xCB000000 | .and => r 0x8A000000 | .or => r 0xAA000000
  | .xor => r 0xCA000000 | .shl => r 0x9AC02000 | .lshr => r 0x9AC02400 | .ashr => r 0x9AC02800
  | .ult => [cmp k, cset 2 k]   -- cset lo
  | .slt => [cmp k, cset 10 k]  -- cset lt
  | .eq => [cmp k, cset 1 k]    -- cset eq

def iVar (i k : Nat) := rrr 0xAA000000 (T k) 31 i                        -- mov xk, xi
def iZero (k : Nat) : BitVec 32 := BitVec.ofNat 32 (0xD2800000 ||| T k)  -- movz xk, #0
def iShl (k : Nat) := rrr 0x8B000000 (T k) (T k) (T k)                    -- add xk, xk, xk
def iInc (k : Nat) : BitVec 32 := BitVec.ofNat 32 (0x91000400 ||| T k <<< 5 ||| T k) -- add xk, xk, #1
def iRes := rrr 0xAA000000 0 31 (T 0)                                     -- mov x0, x9
def iRet : BitVec 32 := 0xD65F03C0#32

/-- `cmp xk, #0; csel xk, xk+1, xk+2, ne` -/
def selCode (k : Nat) : List (BitVec 32) :=
  [BitVec.ofNat 32 (0xF100001F ||| T k <<< 5), rrr 0x9A801000 (T k) (T (k + 1)) (T (k + 2))]

def genConst (k n : Nat) : List (BitVec 32) :=
  if n = 0 then [iZero k] else genConst k (n / 2) ++ [iShl k] ++ (if n % 2 = 1 then [iInc k] else [])

def gen : Exp → Nat → List (BitVec 32)
  | .var i, k => [iVar i k]
  | .const c, k => genConst k c.toNat
  | .bin op a b, k => gen a k ++ gen b (k + 1) ++ opCode op k
  | .ite c a b, k => gen c k ++ gen a (k + 1) ++ gen b (k + 2) ++ selCode k

def compile (e : Exp) : List (BitVec 32) := gen e 0 ++ [iRes, iRet]
end Proven.Arm
