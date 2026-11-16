import Nano.Elab
/- nano code generator: stack machine on RISC-V.  Every value lives on the machine stack (sp); the environment is the
   top slots; temporaries are above it (`d` of them).  Calls are inlined.  Entry convention: a0 = input words,
   a1 = output word; arity < 128 and expression depth + scope < 256 (12-bit offsets). -/
namespace Nano

def w32 (x : UInt64) : List UInt8 := [x.toUInt8, (x >>> 8).toUInt8, (x >>> 16).toUInt8, (x >>> 24).toUInt8]

-- registers: sp = 2, t0 = 5, t1 = 6, a0 = 10, a1 = 11
def iTy (imm rs f rd op : UInt64) : List UInt8 := w32 (((imm &&& 4095) <<< 20) ||| (rs <<< 15) ||| (f <<< 12) ||| (rd <<< 7) ||| op)
def sTy (imm rs2 rs1 : UInt64) : List UInt8 :=
  w32 ((((imm >>> 5) &&& 127) <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) ||| ((3 : UInt64) <<< 12) ||| ((imm &&& 31) <<< 7) ||| 0x23)
def rTy (f7 f3 rd rs1 rs2 : UInt64) : List UInt8 :=
  w32 ((f7 <<< 25) ||| (rs2 <<< 20) ||| (rs1 <<< 15) ||| (f3 <<< 12) ||| (rd <<< 7) ||| 0x33)

def ldW (rd off rs : UInt64) : List UInt8 := iTy off rs 3 rd 3          -- ld rd, off(rs)
def addiW (rd rs imm : UInt64) : List UInt8 := iTy imm rs 0 rd 0x13     -- addi rd, rs, imm
def push : List UInt8 := addiW 2 2 (0 - 8) ++ sTy 0 5 2                  -- sp -= 8; sd t0, 0(sp)

/-- t0 := n by shifting in its 8 bytes, most significant first -/
def li : UInt64 → List UInt8 := fun n =>
  addiW 5 0 0 ++
  (iTy 8 5 1 5 0x13 ++ iTy ((n >>> 56) &&& 255) 5 6 5 0x13) ++
  (iTy 8 5 1 5 0x13 ++ iTy ((n >>> 48) &&& 255) 5 6 5 0x13) ++
  (iTy 8 5 1 5 0x13 ++ iTy ((n >>> 40) &&& 255) 5 6 5 0x13) ++
  (iTy 8 5 1 5 0x13 ++ iTy ((n >>> 32) &&& 255) 5 6 5 0x13) ++
  (iTy 8 5 1 5 0x13 ++ iTy ((n >>> 24) &&& 255) 5 6 5 0x13) ++
  (iTy 8 5 1 5 0x13 ++ iTy ((n >>> 16) &&& 255) 5 6 5 0x13) ++
  (iTy 8 5 1 5 0x13 ++ iTy ((n >>> 8) &&& 255) 5 6 5 0x13) ++
  (iTy 8 5 1 5 0x13 ++ iTy (n &&& 255) 5 6 5 0x13)

/-- binary op on the two top slots: pops b, a; pushes a ∘ b.  f7/f3 select add / sub / mul -/
def binop (f7 : UInt64) : List UInt8 :=
  ldW 6 0 2 ++ ldW 5 8 2 ++ addiW 2 2 8 ++ rTy f7 0 5 5 6 ++ sTy 0 5 2

/-- stack slots of k fresh variables starting at depth b, newest first -/
def mkSc : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, b => (b + k) :: mkSc k b

def cnt : Ex → Nat
  | .acons _ r => cnt r + 1
  | _ => 0

-- `sc`: absolute stack slot of each variable (newest first), `d`: number of slots on the stack (frame base 0)
mutual
def genE : List Nat → Nat → Ex → List UInt8
  | _, _, .num n => li n ++ push
  | sc, d, .var i => ldW 5 ((d - 1 - sc.getD i 0) * 8).toUInt64 2 ++ push
  | sc, d, .add a b => genE sc d a ++ genE sc (d + 1) b ++ binop 0
  | sc, d, .sub a b => genE sc d a ++ genE sc (d + 1) b ++ binop 32
  | sc, d, .mul a b => genE sc d a ++ genE sc (d + 1) b ++ binop 1
  | sc, d, .let_ v b => genE sc d v ++ genE (d :: sc) (d + 1) b ++ ldW 5 0 2 ++ addiW 2 2 8 ++ sTy 0 5 2
  | sc, d, .call b as =>
    genA sc d as ++ genE (mkSc (cnt as) d) (d + cnt as) b ++ ldW 5 0 2 ++ addiW 2 2 ((cnt as) * 8).toUInt64 ++ sTy 0 5 2
  | _, _, _ => []
def genA : List Nat → Nat → Ex → List UInt8
  | sc, d, .acons e r => genE sc d e ++ genA sc (d + 1) r
  | _, _, _ => []
end

/-- load the k arguments from a0 onto the stack, in order -/
def pro : Nat → UInt64 → List UInt8
  | 0, _ => []
  | k + 1, i => ldW 5 (i * 8) 10 ++ push ++ pro k (i + 1)

def nanoGen (p : Prog) : List UInt8 :=
  pro p.1 0 ++ genE (mkSc p.1 0) p.1 p.2 ++ ldW 5 0 2 ++ sTy 0 5 11 ++ addiW 2 2 ((p.1 + 1) * 8).toUInt64 ++ w32 0x00008067

def nanoCompile (xs : List UInt8) : Option (List UInt8) := (nanoElab xs).map nanoGen

end Nano
