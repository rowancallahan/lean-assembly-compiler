/- **Recursion through S3**, part 1 (structural recursion: `S3Incs`, `S3Inits`, `S3Sets`, `S3InitL`); the table and
parts (b)–(d) in Riscv/Frontx/S3RecExamples.lean (split in two files to keep each build ≤ 5 min). -/
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

end Proven.S3.Rec
