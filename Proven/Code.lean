/- A tiny compiler: the source language `Exp` and its RV64I code generator.
The proof is in `Proven/Compiler.lean`, the per-word step lemmas in `Proven/Words.lean`. -/

namespace Proven

/-! ## Source language -/

inductive Op where | add | sub | and | or | xor | shl | lshr | ashr | ult | slt | eq
  deriving DecidableEq, Repr

/-- Shift amounts are taken mod 64 (as RV64 `sll/srl/sra` and AArch64 `lslv/lsrv/asrv` do);
comparisons give `1` or `0`; `ult` is unsigned, `slt` signed. -/
def Op.eval : Op → BitVec 64 → BitVec 64 → BitVec 64
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => a <<< (b.toNat % 64)
  | .lshr, a, b => a >>> (b.toNat % 64)
  | .ashr, a, b => a.sshiftRight (b.toNat % 64)
  | .ult, a, b => if a < b then 1 else 0
  | .slt, a, b => if a.slt b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0

/-- Expressions over four 64-bit inputs (passed in `a0..a3`). -/
inductive Exp where
  | var (i : Fin 4)
  | const (c : BitVec 64)
  | bin (op : Op) (a b : Exp)
  /-- `ite c a b` is `a` if `c ≠ 0`, else `b` (both are evaluated) -/
  | ite (c a b : Exp)
  deriving Repr

def Exp.denote (env : Fin 4 → BitVec 64) : Exp → BitVec 64
  | .var i => env i
  | .const c => c
  | .bin op a b => op.eval (a.denote env) (b.denote env)
  | .ite c a b => if c.denote env = 0 then b.denote env else a.denote env

/-- registers needed beyond the result register -/
def Exp.depth : Exp → Nat
  | .var _ | .const _ => 0
  | .bin _ a b => max a.depth (b.depth + 1)
  | .ite c a b => max c.depth (max (a.depth + 1) (b.depth + 2))

/-! ## Target: RV64I words over a fixed register stack `t0 .. t6, a4 .. a7` -/

/-- number of temporaries -/
def N : Nat := 11

/-- the register stack: `t0 t1 t2 t3 t4 t5 t6 a4 a5 a6 a7` -/
def T : Nat → Fin 32
  | 0 => 5 | 1 => 6 | 2 => 7 | 3 => 28 | 4 => 29 | 5 => 30 | 6 => 31 | 7 => 14 | 8 => 15 | 9 => 16
  | _ => 17
/-- argument registers `a0..a3` -/
def A : Nat → Fin 32
  | 0 => 10 | 1 => 11 | 2 => 12 | _ => 13

def encR (f7 f3 : Nat) (rd rs1 rs2 : Fin 32) : BitVec 32 :=
  BitVec.ofNat 32 (f7 <<< 25 ||| rs2.val <<< 20 ||| rs1.val <<< 15 ||| f3 <<< 12 ||| rd.val <<< 7 ||| 0x33)
def encI (f3 imm : Nat) (rd rs1 : Fin 32) : BitVec 32 :=
  BitVec.ofNat 32 (imm <<< 20 ||| rs1.val <<< 15 ||| f3 <<< 12 ||| rd.val <<< 7 ||| 0x13)

def Op.f7 : Op → Nat | .sub | .ashr => 0x20 | _ => 0
def Op.f3 : Op → Nat
  | .add | .sub => 0 | .shl => 1 | .slt => 2 | .ult => 3 | .xor | .eq => 4 | .lshr | .ashr => 5
  | .or => 6 | .and => 7

/-- what the single R-type word `iOp op` computes (`eq` is `xor` followed by `iSeqz`) -/
def Op.raw (op : Op) : BitVec 64 → BitVec 64 → BitVec 64 := if op = .eq then Op.eval .xor else op.eval

def iOp (op : Op) (k : Nat) : BitVec 32 := encR op.f7 op.f3 (T k) (T k) (T (k + 1)) -- op tk, tk, tk+1
def iVar (i k : Nat) : BitVec 32 := encR 0 0 (T k) 0 (A i)    -- add tk, x0, ai
def iZero (k : Nat) : BitVec 32 := encI 0 0 (T k) 0           -- addi tk, x0, 0
def iShl (k : Nat) : BitVec 32 := encI 1 1 (T k) (T k)        -- slli tk, tk, 1
def iInc (k : Nat) : BitVec 32 := encI 0 1 (T k) (T k)        -- addi tk, tk, 1
def iSeqz (k : Nat) : BitVec 32 := encI 3 1 (T k) (T k)       -- sltiu tk, tk, 1
def iSnez (k : Nat) : BitVec 32 := encR 0 3 (T k) 0 (T k)     -- sltu tk, x0, tk
def iNeg (k : Nat) : BitVec 32 := encR 0x20 0 (T k) 0 (T k)   -- sub tk, x0, tk
def iXor2 (k : Nat) : BitVec 32 := encR 0 4 (T k) (T k) (T (k + 2)) -- xor tk, tk, tk+2
def iRes : BitVec 32 := encR 0 0 10 0 5                        -- add a0, x0, t0
def iRet : BitVec 32 := 0x00008067#32                          -- jalr x0, 0(ra)

/-- build the constant `n` in `t_k`, most significant bit first -/
def genConst (k n : Nat) : List (BitVec 32) :=
  if n = 0 then [iZero k] else genConst k (n / 2) ++ [iShl k] ++ (if n % 2 = 1 then [iInc k] else [])

/-- `t_k := op t_k t_k+1` -/
def opCode (op : Op) (k : Nat) : List (BitVec 32) := if op = .eq then [iOp op k, iSeqz k] else [iOp op k]

/-- `t_k := t_k ≠ 0 ? t_k+1 : t_k+2`, as `t_k+2 ^ ((t_k+1 ^ t_k+2) & -(t_k ≠ 0))` -/
def selCode (k : Nat) : List (BitVec 32) := [iSnez k, iNeg k, iOp .xor (k + 1), iOp .and k, iXor2 k]

/-- code leaving the value of `e` in `t_k`, clobbering only `t_k ..` -/
def gen : Exp → Nat → List (BitVec 32)
  | .var i, k => [iVar i k]
  | .const c, k => genConst k c.toNat
  | .bin op a b, k => gen a k ++ gen b (k + 1) ++ opCode op k
  | .ite c a b, k => gen c k ++ gen a (k + 1) ++ gen b (k + 2) ++ selCode k

/-- the compiled function: result in `a0`, then `ret` -/
def compile (e : Exp) : List (BitVec 32) := gen e 0 ++ [iRes, iRet]

end Proven
