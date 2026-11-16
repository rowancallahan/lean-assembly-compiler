/- Test cases of the monomorphised IR accessors (`frontx_mono`, `Riscv/Frontx/MonoExamples.lean`, NOTES section 35)
against executed Lean: `lake env lean --tstack=4000000 Testing/asm/emit_mono.lean`, then
`python3 Testing/asm/frontx_test.py check 60 mono_<name>`.  Work block per case: the theorem's space
`Ind.spaceA 1 16 (fun n => M * n)` at this input's length. -/
import Riscv.Frontx.MonoExamples

open Proven Proven.Frontx.MonoEx

def hex8 (w : BitVec 32) : String := let s := String.ofList (Nat.toDigits 16 w.toNat); "".pushn '0' (8 - s.length) ++ s
def hex2 (b : UInt8) : String := let s := String.ofList (Nat.toDigits 16 b.toNat); if s.length < 2 then "0" ++ s else s
def hx (xs : List UInt8) : String := if xs.isEmpty then "-" else String.join (xs.map hex2)
def rnd (i j : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + j * 0xD1B54A32D192ED03 + i * i * j) % 2^64

def emitIndW (name : String) (code : List (BitVec 32)) (retLen : Bool) (cases : List (List UInt8 × List UInt8 × Nat)) :
    IO Unit := do
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.words"
    (String.intercalate "\n" (s!"indw {if retLen then 1 else 0}" :: code.map hex8) ++ "\n")
  IO.FS.writeFile s!"Testing/asm/frontx-words/{name}.cases"
    (String.join (cases.map fun (x, y, w) => s!"{hx x} {hx y} {w}\n"))
def sp (M : Nat) (x : List UInt8) : Nat := Proven.Frontx.Ind.spaceA 1 16 (fun n => M * n) x.length

/-- register numbers: small, near `2^63`, random below `2^63` -/
def nat (s : Nat) : Nat := match rnd s 1 % 4 with | 0 => s % 5 | 1 => 2 ^ 63 - 1 - s % 3 | _ => rnd s 2 % 2 ^ 63
def ops : List Op := [.add, .sub, .and, .or, .xor, .shl, .lshr, .ashr, .ult, .slt, .eq]
def mops : List Proven.Mach.MOp := [.mul, .divu, .remu, .div, .rem]
def conds : List Proven.Mach.Cond := [.eq, .ne, .ltu, .geu, .lt, .ge]
def bv (s : Nat) : BitVec 64 := BitVec.ofNat 64 (rnd s 3)

def mArg (s : Nat) : Proven.Mach.IR.Arg Nat := if rnd s 4 % 2 = 0 then .r (nat s) else .i (bv s)
def mTst (s : Nat) : Proven.Mach.IR.Tst Nat := ⟨conds.getD (s % 6) .eq, mArg (s + 1), mArg (s + 7)⟩
def mIns (s : Nat) : Proven.Mach.IR.Ins Nat := match s % 9 with
  | 0 => .set (nat s) (mArg (s + 1)) | 1 => .bin (ops.getD (s % 11) .add) (nat s) (mArg (s + 1)) (mArg (s + 2))
  | 2 => .mop (mops.getD (s % 5) .mul) (nat s) (mArg (s + 1)) (mArg (s + 2)) | 3 => .lbu (nat s) (mArg (s + 3)) (bv s)
  | 4 => .sb (mArg (s + 1)) (mArg (s + 2)) (bv s) | 5 => .ldS (nat s) (nat (s + 1)) | 6 => .stS (nat s) (nat (s + 2))
  | 7 => .ld (nat s) (nat (s + 1)) (bv s) | _ => .sd (nat s) (nat (s + 3)) (bv s)

def iArg (s : Nat) : Proven.Ir.Arg Nat := if rnd s 4 % 2 = 0 then .r (nat s) else .i (bv s)
def iTst (s : Nat) : Proven.Ir.Tst Nat := ⟨conds.getD (s % 6) .eq, iArg (s + 1), iArg (s + 7)⟩
def iRhs (s : Nat) : Proven.Ir.Rhs Nat := match s % 4 with
  | 0 => .arg (iArg s) | 1 => .op (ops.getD (s % 11) .add) (iArg s) (iArg (s + 1))
  | 2 => .mop (mops.getD (s % 5) .mul) (iArg s) (iArg (s + 1)) | _ => .padd (nat s) (iArg (s + 2))
def iArgs (s : Nat) : List (Proven.Ir.Arg Nat) := (List.range (s % 4)).map fun j => iArg (s + j)
def iInst (s : Nat) : Proven.Ir.Inst Nat := match s % 8 with
  | 0 => .let_ (nat s) (iRhs (s + 1)) | 1 => .ldb (nat s) (nat (s + 1)) (iArg (s + 2))
  | 2 => .stb (iArg s) (nat (s + 1)) (iArg (s + 2)) | 3 => .ld (nat s) (nat (s + 1)) (s % 7)
  | 4 => .st (iArg s) (nat (s + 1)) (s % 5) | 5 => .alloc (nat s) (iArg (s + 3)) | 6 => .free (nat s)
  | _ => .call ((List.range (s % 3)).map nat) (s % 4) (iArgs s)
def iTerm (s : Nat) : Proven.Ir.Term Nat := match s % 4 with
  | 0 => .jmp (s % 9) (iArgs s) | 1 => .br (iTst s) (s % 5) (iArgs s) (s % 7) (iArgs (s + 1))
  | 2 => .switch (nat s) ((List.range (s % 4)).map (· + s)) (s % 3) | _ => .ret (iArgs (s + 2))
def iBlock (s : Nat) : Proven.Ir.Block Nat :=
  ⟨(List.range (s % 5)).map (fun j => nat (s + j)), (List.range (s % 6)).map (fun j => iInst (s + j)), iTerm s⟩

def N : List Nat := List.range 60

#eval do
  emitIndW "mono_mtst_a" Proven.Mach.IR.Tst.a.at_Nat.code true (N.map fun i => let t := mTst i
    (TTst.enc t, TTst.N2.enc (Proven.Mach.IR.Tst.a t), sp Proven.Mach.IR.Tst.a.at_Nat.ind.pg.M (TTst.enc t)))
  emitIndW "mono_mtst_b" Proven.Mach.IR.Tst.b.at_Nat.code true (N.map fun i => let t := mTst i
    (TTst.enc t, TTst.N2.enc (Proven.Mach.IR.Tst.b t), sp Proven.Mach.IR.Tst.b.at_Nat.ind.pg.M (TTst.enc t)))
  emitIndW "mono_mtst_c" Proven.Mach.IR.Tst.c.at_Nat.code true (N.map fun i => let t := mTst i
    (TTst.enc t, TTst.N1.enc (Proven.Mach.IR.Tst.c t), sp Proven.Mach.IR.Tst.c.at_Nat.ind.pg.M (TTst.enc t)))
  emitIndW "mono_itst_a" Proven.Ir.Tst.a.at_Nat.code true (N.map fun i => let t := iTst i
    (TIrTst.enc t, TIrTst.N2.enc (Proven.Ir.Tst.a t), sp Proven.Ir.Tst.a.at_Nat.ind.pg.M (TIrTst.enc t)))
  emitIndW "mono_itst_b" Proven.Ir.Tst.b.at_Nat.code true (N.map fun i => let t := iTst i
    (TIrTst.enc t, TIrTst.N2.enc (Proven.Ir.Tst.b t), sp Proven.Ir.Tst.b.at_Nat.ind.pg.M (TIrTst.enc t)))
  emitIndW "mono_itst_c" Proven.Ir.Tst.c.at_Nat.code true (N.map fun i => let t := iTst i
    (TIrTst.enc t, TIrTst.N1.enc (Proven.Ir.Tst.c t), sp Proven.Ir.Tst.c.at_Nat.ind.pg.M (TIrTst.enc t)))
  emitIndW "mono_ins_dst" Proven.Mach.IR.Ins.dst.at_Nat.code true (N.map fun i => let t := mIns i
    (TIns.enc t, TOptN.enc (Proven.Mach.IR.Ins.dst t), sp Proven.Mach.IR.Ins.dst.at_Nat.ind.pg.M (TIns.enc t)))
  emitIndW "mono_arg_regs" Proven.Mach.IR.Arg.regs.at_Nat.code true (N.map fun i => let t := mArg i
    (TArg.enc t, TListN.enc (Proven.Mach.IR.Arg.regs t), sp Proven.Mach.IR.Arg.regs.at_Nat.ind.pg.M (TArg.enc t)))
  emitIndW "mono_block_term" Proven.Ir.Block.term.at_Nat.code true (N.map fun i => let t := iBlock i
    (TIrBlock.enc t, TIrBlock.N3.enc (Proven.Ir.Block.term t), sp Proven.Ir.Block.term.at_Nat.ind.pg.M (TIrBlock.enc t)))
  emitIndW "mono_block_params" Proven.Ir.Block.params.at_Nat.code true (N.map fun i => let t := iBlock i
    (TIrBlock.enc t, TIrBlock.N1.enc (Proven.Ir.Block.params t), sp Proven.Ir.Block.params.at_Nat.ind.pg.M (TIrBlock.enc t)))
  emitIndW "mono_block_body" Proven.Ir.Block.body.at_Nat.code true (N.map fun i => let t := iBlock i
    (TIrBlock.enc t, TIrBlock.N2.enc (Proven.Ir.Block.body t), sp Proven.Ir.Block.body.at_Nat.ind.pg.M (TIrBlock.enc t)))
