import Nano.Elab
import Nano.Asm
/- nano code generator: AST -> pseudo-instruction records (see Nano/Asm.lean) -> RISC-V words.  Stack machine: every
   value lives on the machine stack (sp); calls are inlined.  Entry convention: a0 = input words, a1 = output word.
   Limits (12-bit offsets): arity < 127, stack slots used by the expression < 256. -/
namespace Nano

def r (a b c d : UInt8) : List UInt8 := [a, b, c, d]
-- registers: sp = 2, t0 = 5, t1 = 6, a0 = 10, a1 = 11.  Offsets are in slots (8 bytes).
def ld (rd rs slot : Nat) : List UInt8 := r 0 rd.toUInt8 rs.toUInt8 slot.toUInt8
def sd (rs2 rs1 slot : Nat) : List UInt8 := r 1 rs2.toUInt8 rs1.toUInt8 slot.toUInt8
def addSp (k : Nat) : List UInt8 := r 2 2 2 k.toUInt8           -- sp += 8k
def push : List UInt8 := r 2 2 2 255 ++ sd 5 2 0                -- sp -= 8; sd t0, 0(sp)

/-- t0 := n by shifting in its 8 bytes, most significant first -/
def li (n : UInt64) : List UInt8 :=
  r 2 5 0 0 ++
  r 4 5 5 8 ++ r 3 5 5 ((n >>> 56).toUInt8) ++ r 4 5 5 8 ++ r 3 5 5 ((n >>> 48).toUInt8) ++
  r 4 5 5 8 ++ r 3 5 5 ((n >>> 40).toUInt8) ++ r 4 5 5 8 ++ r 3 5 5 ((n >>> 32).toUInt8) ++
  r 4 5 5 8 ++ r 3 5 5 ((n >>> 24).toUInt8) ++ r 4 5 5 8 ++ r 3 5 5 ((n >>> 16).toUInt8) ++
  r 4 5 5 8 ++ r 3 5 5 ((n >>> 8).toUInt8) ++ r 4 5 5 8 ++ r 3 5 5 (n.toUInt8)

/-- pops b, a; pushes a ∘ b (`k`: 5 add, 6 sub, 7 mul) -/
def binop (k : UInt8) : List UInt8 := ld 6 2 0 ++ ld 5 2 1 ++ addSp 1 ++ r k 5 5 6 ++ sd 5 2 0

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
  | sc, d, .var i => ld 5 2 (d - 1 - sc.getD i 0) ++ push
  | sc, d, .add a b => genE sc d a ++ genE sc (d + 1) b ++ binop 5
  | sc, d, .sub a b => genE sc d a ++ genE sc (d + 1) b ++ binop 6
  | sc, d, .mul a b => genE sc d a ++ genE sc (d + 1) b ++ binop 7
  | sc, d, .let_ v b => genE sc d v ++ genE (d :: sc) (d + 1) b ++ ld 5 2 0 ++ addSp 1 ++ sd 5 2 0
  | sc, d, .call b as =>
    genA sc d as ++ genE (mkSc (cnt as) d) (d + cnt as) b ++ ld 5 2 0 ++ addSp (cnt as) ++ sd 5 2 0
  | _, _, _ => []
def genA : List Nat → Nat → Ex → List UInt8
  | sc, d, .acons e r => genE sc d e ++ genA sc (d + 1) r
  | _, _, _ => []
end

/-- load the k arguments from a0 onto the stack, in order -/
def pro : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, i => ld 5 10 i ++ push ++ pro k (i + 1)

/-- the records of a program -/
def genR (p : Prog) : List UInt8 :=
  pro p.1 0 ++ genE (mkSc p.1 0) p.1 p.2 ++ ld 5 2 0 ++ sd 5 11 0 ++ addSp (p.1 + 1) ++ r 8 0 0 0

/-- the stack generator (self-hostable; tested, not proved). The proved `nanoGen` is in `Nano/GenIr.lean`
(Testing/notes/NANO_PROOF.md). -/
def nanoGenS (p : Prog) : List UInt8 := asm (genR p)

def nanoCompileS (xs : List UInt8) : Option (List UInt8) := (nanoElab xs).map nanoGenS

end Nano
