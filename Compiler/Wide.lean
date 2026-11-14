/- The WIDE operation set: an extension of the machine interface (`Compiler/Iface.lean`, untouched) for
the optimising back end (`Compiler/Opt/`).  Every operation takes ARBITRARY abstract registers; there are
immediate forms, base+offset byte loads/stores, compare-and-branch on two registers (forward and backward)
and jumps in both directions.  A target is a `Wide`: the generic `Core` laws plus one law per `WOp`.

Pure Lean (core only), like `Iface.lean`. -/
import Compiler.Frame

namespace Proven.Mach

/-- branch conditions on two 64-bit values -/
inductive Cond where | eq | ne | ltu | geu | lt | ge
  deriving DecidableEq, Repr

def Cond.eval : Cond → BitVec 64 → BitVec 64 → Bool
  | .eq, a, b => decide (a = b)
  | .ne, a, b => !decide (a = b)
  | .ltu, a, b => decide (a < b)
  | .geu, a, b => !decide (a < b)
  | .lt, a, b => a.slt b
  | .ge, a, b => !a.slt b

def Cond.neg : Cond → Cond
  | .eq => .ne | .ne => .eq | .ltu => .geu | .geu => .ltu | .lt => .ge | .ge => .lt

theorem Cond.eval_neg (c : Cond) (a b : BitVec 64) : c.neg.eval a b = !c.eval a b := by
  cases c <;> simp only [Cond.neg, Cond.eval, Bool.not_not]

/-- wide abstract operations (one may expand to several target words) -/
inductive WOp where
  /-- `d := a` -/
  | mov (d a : Reg)
  /-- `d := c` -/
  | li (d : Reg) (c : BitVec 64)
  /-- `d := op.eval a b`, any registers -/
  | bin (op : Op) (d a b : Reg)
  /-- `d := op.eval a c` (law only for `immOK op c`) -/
  | bini (op : Op) (d a : Reg) (c : BitVec 64)
  /-- `d := zero-extended byte mem[a + off]` (law only for `offOK off`) -/
  | lbu (d a : Reg) (off : BitVec 64)
  /-- `mem[a + off] := low byte of v` -/
  | sb (v a : Reg) (off : BitVec 64)
  /-- if `c.eval a b` (`b = none`: zero) jump `n` words forward / back from the start of this op -/
  | br (c : Cond) (a : Reg) (b : Option Reg) (back : Bool) (n : Nat)
  /-- jump `n` words forward / back from the start of this op -/
  | jmp (back : Bool) (n : Nat)
  /-- jump to the return address -/
  | ret
  /-- `d := slot j` (the 8 bytes at `fr + 8 (j + 1)`), any register -/
  | ldS (d : Reg) (j : Nat)
  /-- `slot j := v`, any register -/
  | stS (j : Nat) (v : Reg)
  deriving Repr

/-- the target of a jump over `n` words from `pc` -/
def tgt (pc : BitVec 64) (back : Bool) (n : Nat) : BitVec 64 :=
  if back then pc - BitVec.ofNat 64 (4 * n) else next pc n

/-- an optional register operand (`none`: zero) -/
def Base.getO (B : Base) (s : B.S) : Option Reg → BitVec 64
  | some b => B.get s b
  | none => 0

/-- **The wide interface.**  `Core` (generic laws) plus encodings, decidable operand-range checks and one
law per `WOp`; shape of each law as in `Machine`. -/
structure Wide extends Core where
  wenc : WOp → List (BitVec 32)
  /-- which immediates `bini op` supports -/
  immOK : Op → BitVec 64 → Bool
  /-- which load/store offsets are supported -/
  offOK : BitVec 64 → Bool
  /-- which branch / jump distances (direction, words) are supported -/
  brOK : Bool → Nat → Bool
  jOK : Bool → Nat → Bool
  lenBr : Nat
  lenJ : Nat
  len_br : ∀ c a b k n, (wenc (.br c a b k n)).length = lenBr
  len_j : ∀ k n, (wenc (.jmp k n)).length = lenJ
  w_mov : ∀ {d a : Reg} {s : S} {pc : BitVec 64}, toBase.At s pc (wenc (.mov d a)) →
    runsTo s fun s' => toBase.Done s s' (next pc (wenc (.mov d a)).length) ∧
      toBase.Set1 s s' d (get s a) ∧ mem s' = mem s
  w_li : ∀ {d : Reg} {c : BitVec 64} {s : S} {pc : BitVec 64}, toBase.At s pc (wenc (.li d c)) →
    runsTo s fun s' => toBase.Done s s' (next pc (wenc (.li d c)).length) ∧
      toBase.Set1 s s' d c ∧ mem s' = mem s
  w_bin : ∀ {op : Op} {d a b : Reg} {s : S} {pc : BitVec 64}, toBase.At s pc (wenc (.bin op d a b)) →
    runsTo s fun s' => toBase.Done s s' (next pc (wenc (.bin op d a b)).length) ∧
      toBase.Set1 s s' d (op.eval (get s a) (get s b)) ∧ mem s' = mem s
  w_bini : ∀ {op : Op} {d a : Reg} {c : BitVec 64} {s : S} {pc : BitVec 64}, immOK op c = true →
    toBase.At s pc (wenc (.bini op d a c)) →
    runsTo s fun s' => toBase.Done s s' (next pc (wenc (.bini op d a c)).length) ∧
      toBase.Set1 s s' d (op.eval (get s a) c) ∧ mem s' = mem s
  w_lbu : ∀ {d a : Reg} {off : BitVec 64} {s : S} {pc : BitVec 64} {v : BitVec 8}, offOK off = true →
    toBase.At s pc (wenc (.lbu d a off)) → toBase.inRAM (get s a + off).toNat 1 →
    mem s (get s a + off).toNat = some v →
    runsTo s fun s' => toBase.Done s s' (next pc (wenc (.lbu d a off)).length) ∧
      toBase.Set1 s s' d (v.setWidth 64) ∧ mem s' = mem s
  w_sb : ∀ {v a : Reg} {off : BitVec 64} {s : S} {pc : BitVec 64}, offOK off = true →
    toBase.At s pc (wenc (.sb v a off)) → toBase.inRAM (get s a + off).toNat 1 →
    runsTo s fun s' => toBase.Done s s' (next pc (wenc (.sb v a off)).length) ∧
      toBase.Same s s' ∧ mem s' = (mem s).upd (get s a + off).toNat ((get s v).setWidth 8)
  w_br : ∀ {c : Cond} {a : Reg} {b : Option Reg} {k : Bool} {n : Nat} {s : S} {pc : BitVec 64},
    brOK k n = true → toBase.At s pc (wenc (.br c a b k n)) →
    runsTo s fun s' => toBase.Done s s'
        (if c.eval (get s a) (toBase.getO s b) = true then tgt pc k n
         else next pc lenBr) ∧
      toBase.Same s s' ∧ mem s' = mem s
  w_jmp : ∀ {k : Bool} {n : Nat} {s : S} {pc : BitVec 64}, jOK k n = true → toBase.At s pc (wenc (.jmp k n)) →
    runsTo s fun s' => toBase.Done s s' (tgt pc k n) ∧ toBase.Same s s' ∧ mem s' = mem s
  w_ret : ∀ {s : S} {pc : BitVec 64}, retOK (ra s) → toBase.At s pc (wenc .ret) →
    runsTo s fun s' => toBase.Done s s' (ra s) ∧ toBase.Same s s' ∧ mem s' = mem s
  /-- the frame register (as `MachineF.fr`); not an abstract register, unchanged by every wide operation -/
  fr : S → BitVec 64
  maxSlots : Nat
  keep_fr : ∀ {s s' : S}, keep s s' → fr s' = fr s
  w_ldS : ∀ {d : Reg} {j : Nat} {s : S} {pc : BitVec 64} {v : BitVec 64}, j < maxSlots →
    toBase.At s pc (wenc (.ldS d j)) → toBase.inRAM ((fr s).toNat + 8 * (j + 1)) 8 →
    ((fr s).toNat + 8 * (j + 1)) % 8 = 0 → bytes (mem s) ((fr s).toNat + 8 * (j + 1)) 8 = (le8 v).map some →
    runsTo s fun s' => toBase.Done s s' (next pc (wenc (.ldS d j)).length) ∧ toBase.Set1 s s' d v ∧ mem s' = mem s
  w_stS : ∀ {j : Nat} {v : Reg} {s : S} {pc : BitVec 64}, j < maxSlots →
    toBase.At s pc (wenc (.stS j v)) → toBase.inRAM ((fr s).toNat + 8 * (j + 1)) 8 →
    ((fr s).toNat + 8 * (j + 1)) % 8 = 0 →
    runsTo s fun s' => toBase.Done s s' (next pc (wenc (.stS j v)).length) ∧ toBase.Same s s' ∧
      mem s' = (mem s).wr ((fr s).toNat + 8 * (j + 1)) (le8 (get s v))

namespace Wide
variable (M : Wide)

/-- the target words of a wide program -/
def wcode : List WOp → List (BitVec 32)
  | [] => []
  | o :: os => M.wenc o ++ wcode os

theorem wcode_append : ∀ (a b : List WOp), M.wcode (a ++ b) = M.wcode a ++ M.wcode b
  | [], _ => rfl
  | o :: os, b => by
    show M.wenc o ++ M.wcode (os ++ b) = (M.wenc o ++ M.wcode os) ++ M.wcode b
    rw [wcode_append os b, List.append_assoc]

theorem wcode_one (o : WOp) : M.wcode [o] = M.wenc o := List.append_nil _

end Wide
end Proven.Mach
