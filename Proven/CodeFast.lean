/- Faster RV64I backend for `Exp` (copy of the idea of `Proven/Code.lean`; NOT proved, tested only).
   Differences: constants by `lui`/`addi`/`slli` (li), variables and `x0` used directly as operands,
   immediate forms for small/shift constants, results written straight to a0, no `snez` for boolean conditions,
   constant folding. Words are tagged with a category for measurement: 0 const, 1 move, 2 op, 3 select, 4 return. -/
import Proven.Code
namespace Proven.Fast
open Proven

abbrev W := Nat × BitVec 32

def encI' (f3 : Nat) (imm : Int) (rd rs1 : Fin 32) : BitVec 32 :=
  BitVec.ofNat 32 ((imm % 4096).toNat <<< 20 ||| rs1.val <<< 15 ||| f3 <<< 12 ||| rd.val <<< 7 ||| 0x13)
def encLui (rd : Fin 32) (imm20 : Int) : BitVec 32 :=
  BitVec.ofNat 32 ((imm20 % 1048576).toNat <<< 12 ||| rd.val <<< 7 ||| 0x37)
def sext12 (v : Int) : Int := if v % 4096 ≥ 2048 then v % 4096 - 4096 else v % 4096
def ctz : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n ≠ 0 ∧ n % 2 = 0 then 1 + ctz f (n / 2) else 0

/-- load the signed value `v` into `d`: `addi`, `lui`+`addi`, or `li (v >> sh); slli sh; addi lo` -/
def li : Nat → Fin 32 → Int → List (BitVec 32)
  | 0, d, v => [encI' 0 v d 0]
  | f + 1, d, v =>
    if -2048 ≤ v ∧ v < 2048 then [encI' 0 v d 0] else
    let lo := sext12 v
    let rest := v - lo
    if -2147483648 ≤ v ∧ v < 2147483648 - 2048 then
      encLui d (rest / 4096) :: (if lo = 0 then [] else [encI' 0 lo d d])
    else
      let sh := ctz 64 rest.natAbs
      li f d (rest / (2 : Int) ^ sh) ++ [encI' 1 (sh : Int) d d] ++ (if lo = 0 then [] else [encI' 0 lo d d])

def smallC (c : BitVec 64) : Bool := decide (-2048 ≤ c.toInt ∧ c.toInt < 2048)

/-- single-immediate forms; `none` if the constant does not fit -/
def immWords (op : Op) (ra d : Fin 32) (c : BitVec 64) : Option (List (BitVec 32)) :=
  let s := c.toInt
  let sh : Int := (c.toNat % 64 : Nat)
  match op with
  | .add => if smallC c then some [encI' 0 s d ra] else none
  | .sub => if -2048 ≤ -s ∧ -s < 2048 then some [encI' 0 (-s) d ra] else none
  | .and => if smallC c then some [encI' 7 s d ra] else none
  | .or => if smallC c then some [encI' 6 s d ra] else none
  | .xor => if smallC c then some [encI' 4 s d ra] else none
  | .shl => some [encI' 1 sh d ra]
  | .lshr => some [encI' 5 sh d ra]
  | .ashr => some [encI' 5 (0x400 + sh) d ra]
  | .ult => if smallC c then some [encI' 3 s d ra] else none
  | .slt => if smallC c then some [encI' 2 s d ra] else none
  | .eq => if c = 0 then some [encI' 3 1 d ra] else if smallC c then some [encI' 4 s d ra, encI' 3 1 d d] else none

def opWords (op : Op) (d ra rb : Fin 32) : List (BitVec 32) :=
  if op = .eq then [encR 0 4 d ra rb, encI' 3 1 d d] else [encR op.f7 op.f3 d ra rb]

/-- operand register of `e` (generated at stack depth `k`, code `c`): variables and 0 need no code -/
def opnd (e : Exp) (k : Nat) (c : List W) : List W × Fin 32 :=
  match e with
  | .var i => ([], A i.val)
  | .const c0 => if c0 = 0 then ([], 0) else (c, T k)
  | _ => (c, T k)

def isBool : Exp → Bool | .bin .ult _ _ | .bin .slt _ _ | .bin .eq _ _ => true | _ => false

/-- code leaving the value of `e` in register `d`, clobbering only `t_k ..` (and `d`, last) -/
def genTo : Exp → Nat → Fin 32 → List W
  | .var i, _, d => if d = A i.val then [] else [(1, encR 0 0 d 0 (A i.val))]
  | .const c, _, d => (li 8 d c.toInt).map fun w => (0, w)
  | .bin op a b, k, d =>
    let (ca, ra) := opnd a k (genTo a k (T k))
    let (cb, rb) := opnd b (k + 1) (genTo b (k + 1) (T (k + 1)))
    let imm := match b with | .const c => immWords op ra d c | _ => none
    match imm with
    | some ws => ca ++ ws.map fun w => (2, w)
    | none => ca ++ cb ++ (opWords op d ra rb).map fun w => (2, w)
  | .ite c a b, k, d =>
    let (cc, rc) := opnd c k (genTo c k (T k))
    let (ca, ra) := opnd a (k + 1) (genTo a (k + 1) (T (k + 1)))
    let (cb, rb) := opnd b (k + 2) (genTo b (k + 2) (T (k + 2)))
    let mask := if isBool c then [encR 0x20 0 (T k) 0 rc] else [encR 0 3 (T k) 0 rc, encR 0x20 0 (T k) 0 (T k)]
    cc ++ ca ++ cb ++ mask.map (fun w => (3, w)) ++
      [(3, encR 0 4 (T (k + 1)) ra rb), (3, encR 0 7 (T k) (T k) (T (k + 1))), (3, encR 0 4 d (T k) rb)]

/-- constant folding; constants on the right of commutative operators; never increases `depth` -/
def _root_.Proven.Op.comm : Op → Bool | .add | .and | .or | .xor | .eq => true | _ => false
def _root_.Proven.Exp.fold : Exp → Exp
  | .var i => .var i
  | .const c => .const c
  | .bin op a b =>
    match a.fold, b.fold with
    | .const x, .const y => .const (op.eval x y)
    | .const x, b' => if op.comm then .bin op b' (.const x) else .bin op (.const x) b'
    | a', b' => .bin op a' b'
  | .ite c a b =>
    match c.fold with
    | .const x => if x = 0 then b.fold else a.fold
    | c' => .ite c' a.fold b.fold

def compileT (e : Exp) : List W := genTo e.fold 0 (A 0) ++ [(4, iRet)]
def compile (e : Exp) : List (BitVec 32) := (compileT e).map (·.2)
end Proven.Fast
