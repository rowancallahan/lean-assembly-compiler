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
| `S3Merge` | `merge` | well-founded (`termination_by xs.length + ys.length`), not structural |
| `S3EvOd` | `evSum` / `odCnt` | mutual, different result types, non-tail calls |
| `S3Lex` | `lex` | lexicographic `(xs.length, k.toNat)`, the inner counter resets |
-/
import Riscv.Frontx.S3IO
import Riscv.Back.S3Top
import Compiler.Opt.Hoist
import Compiler.Opt.BFn

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
end Proven.S3.Rec
