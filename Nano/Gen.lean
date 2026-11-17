import Nano.Elab
import Nano.Asm
/- nano stack-machine code generator: AST -> pseudo-instruction records (see Nano/Asm.lean) -> RISC-V words.
   Calling convention = `StartCorrect` (Spec/Top.lean): a0 = input address, a2 = work base, sp = work top, a3 = output
   address.  Prologue: t6 := sp rounded down to a multiple of 8 (`srli`/`slli`: `ld`/`sd` on the Sail model need
   8-aligned addresses, `StartCorrect` aligns only the work START); t3 := a0.  Input: `arity` 8-byte LE words, read BYTEWISE (not aligned); output: one 8-byte LE word written BYTEWISE.
   Value stack = work block, descending from the work top in t6 (x31); every push checks `t6 >= a2` after the
   decrement and else sets a0 := -1 (oomFlag) and returns.  Calls are inlined.  Registers touched: t0 t1 t3 t6, a0 only
   on overflow.  Limits (8-bit slot offsets): arity < 127, stack slots used by the expression < 256.
   `memoryNeeded` = 8 * `depth` bytes. -/
namespace Nano

def r (a b c d : UInt8) : List UInt8 := [a, b, c, d]
-- registers: sp = 2, t0 = 5, t1 = 6, a0 = 10, a2 = 12, a3 = 13, t3 = 28, t6 = 31 (stack pointer).  Slots are 8 bytes.
def ld (rd rs slot : Nat) : List UInt8 := r 3 rd.toUInt8 rs.toUInt8 slot.toUInt8
def sd (rs2 rs1 slot : Nat) : List UInt8 := r 11 rs2.toUInt8 rs1.toUInt8 slot.toUInt8
def addSp (k : Nat) : List UInt8 := r 8 31 31 k.toUInt8           -- t6 += 8k
/-- t6 -= 8; if t6 < a2 then (a0 := -1; ret); sd t0, 0(t6) -/
def push : List UInt8 := r 0 31 31 248 ++ r 7 0 31 12 ++ r 0 10 0 255 ++ r 48 0 1 0 ++ sd 5 31 0

/-- t0 := n by shifting in its 8 bytes, most significant first -/
def li (n : UInt64) : List UInt8 :=
  r 0 5 0 0 ++
  r 1 5 5 8 ++ r 6 5 5 ((n >>> 56).toUInt8) ++ r 1 5 5 8 ++ r 6 5 5 ((n >>> 48).toUInt8) ++
  r 1 5 5 8 ++ r 6 5 5 ((n >>> 40).toUInt8) ++ r 1 5 5 8 ++ r 6 5 5 ((n >>> 32).toUInt8) ++
  r 1 5 5 8 ++ r 6 5 5 ((n >>> 24).toUInt8) ++ r 1 5 5 8 ++ r 6 5 5 ((n >>> 16).toUInt8) ++
  r 1 5 5 8 ++ r 6 5 5 ((n >>> 8).toUInt8) ++ r 1 5 5 8 ++ r 6 5 5 (n.toUInt8)

/-- pops b, a; pushes a ∘ b (`k`: 24 add, 32 sub, 40 mul) -/
def binop (k : UInt8) : List UInt8 := ld 6 31 0 ++ ld 5 31 1 ++ addSp 1 ++ r k 5 5 6 ++ sd 5 31 0

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
  | sc, d, .var i => (match sc[i]? with | some s => ld 5 31 (d - 1 - s) ++ push | none => li 0 ++ push)
  | sc, d, .add a b => genE sc d a ++ genE sc (d + 1) b ++ binop 24
  | sc, d, .sub a b => genE sc d a ++ genE sc (d + 1) b ++ binop 32
  | sc, d, .mul a b => genE sc d a ++ genE sc (d + 1) b ++ binop 40
  | sc, d, .let_ v b => genE sc d v ++ genE (d :: sc) (d + 1) b ++ ld 5 31 0 ++ addSp 1 ++ sd 5 31 0
  | sc, d, .call b as =>
    genA sc d as ++ genE (mkSc (cnt as) d) (d + cnt as) b ++ ld 5 31 0 ++ addSp (cnt as) ++ sd 5 31 0
  | _, _, _ => li 0 ++ push   -- `anil`/`acons` as expressions mean 0 (`den`)
def genA : List Nat → Nat → Ex → List UInt8
  | sc, d, .acons e r => genE sc d e ++ genA sc (d + 1) r
  | _, _, _ => []
end

/-- argument words: t0 := the 8 bytes at t3 (LE, bytewise), pushed; t3 += 8 -/
def rd8 : List UInt8 :=
  r 4 5 28 7 ++ (List.range 7).foldr (fun j acc => r 1 5 5 8 ++ r 4 6 28 (6 - j).toUInt8 ++ r 14 5 5 6 ++ acc) []

/-- load the k arguments from t3 onto the stack, in order -/
def pro : Nat → List UInt8
  | 0 => []
  | k + 1 => rd8 ++ push ++ r 8 28 28 1 ++ pro k

/-- result t0 -> 8 bytes at a3, bytewise -/
def wr8 : List UInt8 := (List.range 8).foldr (fun k acc => r 5 6 5 (8 * k).toUInt8 ++ r 16 6 13 k.toUInt8 ++ acc) []

/-- the records of a program -/
def genR (p : Prog) : List UInt8 :=
  r 5 31 2 3 ++ r 1 31 31 3 ++ r 0 28 10 0 ++ pro p.1 ++ genE (mkSc p.1 0) p.1 p.2 ++ ld 5 31 0 ++ wr8 ++ r 48 0 1 0

-- most stack slots in use (what `genR`'s pushes need); `memoryNeeded` = 8 * `depth p`
mutual
def depE : Nat → Ex → Nat
  | d, .num _ => d + 1
  | d, .var _ => d + 1
  | d, .add a b => max (depE d a) (depE (d + 1) b)
  | d, .sub a b => max (depE d a) (depE (d + 1) b)
  | d, .mul a b => max (depE d a) (depE (d + 1) b)
  | d, .let_ v b => max (depE d v) (depE (d + 1) b)
  | d, .call b as => max (depA d as) (depE (d + cnt as) b)
  | d, _ => d + 1
def depA : Nat → Ex → Nat
  | d, .acons e r => max (depE d e) (depA (d + 1) r)
  | _, _ => 0
end
def depth (p : Prog) : Nat := max p.1 (depE p.1 p.2)

def nanoGen (p : Prog) : List UInt8 := asm (genR p)

/-- rejects (`none`) a program whose stack needs 256 or more slots (8-bit slot offsets of the records) -/
def nanoCompile (xs : List UInt8) : Option (List UInt8) :=
  (nanoElab xs).bind fun p => if depth p < 256 then some (nanoGen p) else none

end Nano
