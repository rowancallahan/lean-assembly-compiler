/- Faster AArch64 backend (NOT proved, tested only): constants by movz/movn/movk, variables and xzr used directly as
   operands, immediate add/sub/shift/cmp forms, cmp+csel fused for comparison conditions, result straight to x0,
   constant folding (`Exp.fold` from `Proven.CodeFast`). Word tags: 0 const, 1 move, 2 op, 3 select, 4 return. -/
import Arm.CompilerArm
import CodeFast
namespace Proven.Arm.Fast
open Proven Proven.Fast

def mov (base : Nat) (hw imm d : Nat) : BitVec 32 := BitVec.ofNat 32 (base ||| hw <<< 21 ||| imm <<< 5 ||| d)
def chunk (v i : Nat) : Nat := (v >>> (16 * i)) % 65536

/-- load the 64-bit value `v` into `d`: movz/movn + movk for the remaining halfwords -/
def liArm (d v : Nat) : List (BitVec 32) :=
  let idx := [0, 1, 2, 3]
  let zeros := (idx.filter fun i => chunk v i == 0).length
  let ones := (idx.filter fun i => chunk v i == 0xFFFF).length
  if ones > zeros then
    let rest := idx.filter fun i => chunk v i != 0xFFFF
    match rest with
    | [] => [mov 0x92800000 0 0 d]
    | i0 :: tl => mov 0x92800000 i0 (0xFFFF - chunk v i0) d :: tl.map fun i => mov 0xF2800000 i (chunk v i) d
  else
    let rest := idx.filter fun i => chunk v i != 0
    match rest with
    | [] => [mov 0xD2800000 0 0 d]
    | i0 :: tl => mov 0xD2800000 i0 (chunk v i0) d :: tl.map fun i => mov 0xF2800000 i (chunk v i) d

def addI (d rn imm : Nat) : BitVec 32 := BitVec.ofNat 32 (0x91000000 ||| imm <<< 10 ||| rn <<< 5 ||| d)
def subI (d rn imm : Nat) : BitVec 32 := BitVec.ofNat 32 (0xD1000000 ||| imm <<< 10 ||| rn <<< 5 ||| d)
def cmpI (rn imm : Nat) : BitVec 32 := BitVec.ofNat 32 (0xF1000000 ||| imm <<< 10 ||| rn <<< 5 ||| 31)
def cmpR (rn rm : Nat) : BitVec 32 := rrr 0xEB000000 31 rn rm
def csetD (inv d : Nat) : BitVec 32 := rrr (0x9A800400 ||| inv <<< 12) d 31 31
def cselD (cond d rn rm : Nat) : BitVec 32 := rrr (0x9A800000 ||| cond <<< 12) d rn rm
def shI (base s d rn : Nat) (isShl : Bool) : BitVec 32 :=
  if isShl then BitVec.ofNat 32 (0xD3400000 ||| ((64 - s) % 64) <<< 16 ||| (63 - s) <<< 10 ||| rn <<< 5 ||| d)
  else BitVec.ofNat 32 (base ||| s <<< 16 ||| 0xFC00 ||| rn <<< 5 ||| d)

/-- condition code (for "true") of a comparison operator -/
def condOf : Op → Nat | .ult => 3 | .slt => 11 | _ => 0
def isCmp : Op → Bool | .ult | .slt | .eq => true | _ => false

def immWords (op : Op) (ra d : Nat) (c : BitVec 64) : Option (List (BitVec 32)) :=
  let n := c.toNat
  let s := n % 64
  match op with
  | .add => if n < 4096 then some [addI d ra n] else if 2^64 - 4096 < n then some [subI d ra (2^64 - n)] else none
  | .sub => if n < 4096 then some [subI d ra n] else if 2^64 - 4096 < n then some [addI d ra (2^64 - n)] else none
  | .shl => some [shI 0 s d ra true]
  | .lshr => some [shI 0xD340FC00 s d ra false]
  | .ashr => some [shI 0x9340FC00 s d ra false]
  | .ult | .slt | .eq => if n < 4096 then some [cmpI ra n, csetD (match op with | .ult => 2 | .slt => 10 | _ => 1) d] else none
  | _ => none

def opWords (op : Op) (d ra rb : Nat) : List (BitVec 32) :=
  let r base := [rrr base d ra rb]
  match op with
  | .add => r 0x8B000000 | .sub => r 0xCB000000 | .and => r 0x8A000000 | .or => r 0xAA000000
  | .xor => r 0xCA000000 | .shl => r 0x9AC02000 | .lshr => r 0x9AC02400 | .ashr => r 0x9AC02800
  | .ult => [cmpR ra rb, csetD 2 d] | .slt => [cmpR ra rb, csetD 10 d] | .eq => [cmpR ra rb, csetD 1 d]

def opnd (e : Exp) (k : Nat) (c : List W) : List W × Nat :=
  match e with
  | .var i => ([], i.val)
  | .const c0 => if c0 = 0 then ([], 31) else (c, T k)
  | _ => (c, T k)

/-- simple second operand of a comparison: variable, 0, or a constant below 4096 -/
def simple : Exp → Bool
  | .var _ => true
  | .const c => c.toNat < 4096
  | _ => false

def genTo : Exp → Nat → Nat → List W
  | .var i, _, d => if d = i.val then [] else [(1, rrr 0xAA000000 d 31 i.val)]
  | .const c, _, d => (liArm d c.toNat).map fun w => (0, w)
  | .bin op a b, k, d =>
    let (ca, ra) := opnd a k (genTo a k (T k))
    let (cb, rb) := opnd b (k + 1) (genTo b (k + 1) (T (k + 1)))
    let imm := match b with | .const c => if ra = 31 then none else immWords op ra d c | _ => none
    match imm with
    | some ws => ca ++ ws.map fun w => (2, w)
    | none => ca ++ cb ++ (opWords op d ra rb).map fun w => (2, w)
  | .ite c a b, k, d =>
    let (ca, ra) := opnd a (k + 1) (genTo a (k + 1) (T (k + 1)))
    let (cb, rb) := opnd b (k + 2) (genTo b (k + 2) (T (k + 2)))
    let fused : Option (List W × W × Nat) :=
      match c with
      | .bin cop x y =>
        if isCmp cop && simple y then
          let (cx, rx) := opnd x k (genTo x k (T k))
          let cmpw := match y with
            | .const c0 => if c0 = 0 then cmpR rx 31 else cmpI rx c0.toNat
            | .var j => cmpR rx j.val
            | _ => cmpR rx 31
          some (cx, (3, cmpw), condOf cop)
        else none
      | _ => none
    match fused with
    | some (cc, cw, cond) => cc ++ ca ++ cb ++ [cw, (3, cselD cond d ra rb)]
    | none =>
      let (cc, rc) := opnd c k (genTo c k (T k))
      cc ++ ca ++ cb ++ [(3, cmpI rc 0), (3, cselD 1 d ra rb)]

def compileT (e : Exp) : List W := genTo e.fold 0 0 ++ [(4, Arm.iRet)]
def compile (e : Exp) : List (BitVec 32) := (compileT e).map (·.2)
end Proven.Arm.Fast
