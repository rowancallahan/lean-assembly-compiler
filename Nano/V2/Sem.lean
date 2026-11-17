import Nano.V2.Gen
/- nano v2 small backend, proof layer 1: the semantics of STRUCTURED STACK CODE (`SC`, Nano/V2/Gen.lean) on an
abstract machine: registers, a WORD memory for the work block (stack + heap; only 8-aligned accesses inside
`[lo, hi)`), the input bytes (read-only), the output bytes.  An access outside its block is stuck (`none`), so a
proof that the code runs also proves every access valid (what the Sail refinement needs).
Layer 2 (Nano/V2/Expr.lean): the uniform expression contract for `cE`/`cT` on this machine.
Layer 3 (to do): `SC.flat` + `I.enc` on Sail. -/
namespace Nano.V2

/-- the fixed blocks of a run -/
structure Cfg where
  lo : Nat
  hi : Nat
  inp : List UInt8
  ib : Nat
  ob : Nat
  ol : Nat

structure St where
  x : Nat → UInt64
  w : Nat → UInt64
  o : Nat → UInt8

def St.get (s : St) (r : Nat) : UInt64 := if r = 0 then 0 else s.x r
def St.set (s : St) (r : Nat) (v : UInt64) : St :=
  if r = 0 then s else { s with x := fun j => if j = r then v else s.x j }

def ROp.eval : ROp → UInt64 → UInt64 → UInt64
  | .add, a, b => a + b | .sub, a, b => a - b | .mul, a, b => a * b | .and, a, b => a &&& b
  | .or, a, b => a ||| b | .xor, a, b => a ^^^ b | .sll, a, b => a <<< (b % 64) | .srl, a, b => a >>> (b % 64)
  | .sltu, a, b => if a < b then 1 else 0
def IOp.eval : IOp → UInt64 → Int → UInt64
  | .addi, a, i => a + UInt64.ofInt i | .ori, a, i => a ||| UInt64.ofInt i | .andi, a, i => a &&& UInt64.ofInt i
  | .xori, a, i => a ^^^ UInt64.ofInt i | .slli, a, i => a <<< (UInt64.ofNat (i.toNat % 64))
  | .srli, a, i => a >>> (UInt64.ofNat (i.toNat % 64))
def BOp.eval : BOp → UInt64 → UInt64 → Bool
  | .beq, a, b => a == b | .bne, a, b => a != b | .bltu, a, b => decide (a < b) | .bgeu, a, b => decide (b ≤ a)

/-- a valid word address -/
def Cfg.wok (c : Cfg) (a : Nat) : Prop := c.lo ≤ a ∧ a + 8 ≤ c.hi ∧ a % 8 = 0
instance (c : Cfg) (a : Nat) : Decidable (c.wok a) := by unfold Cfg.wok; infer_instance

def ea (s : St) (r : Nat) (off : Int) : Nat := (s.get r + UInt64.ofInt off).toNat

/-- one straight-line instruction (control transfers are not straight: `none`) -/
def I.run (c : Cfg) (s : St) : I → Option St
  | .r f rd a b => some (s.set rd (f.eval (s.get a) (s.get b)))
  | .i f rd a imm => some (s.set rd (f.eval (s.get a) imm))
  | .ld rd a off => if c.wok (ea s a off) then some (s.set rd (s.w (ea s a off))) else none
  | .sd b a off => if c.wok (ea s a off) then
      some { s with w := fun j => if j = ea s a off then s.get b else s.w j } else none
  | .lbu rd a off => if c.ib ≤ ea s a off ∧ ea s a off < c.ib + c.inp.length then
      some (s.set rd (c.inp.getD (ea s a off - c.ib) 0).toUInt64) else none
  | .sb b a off => if c.ob ≤ ea s a off ∧ ea s a off < c.ob + c.ol then
      some { s with o := fun j => if j = ea s a off then (s.get b).toUInt8 else s.o j } else none
  | _ => none

def runL (c : Cfg) : List I → St → Option St
  | [], s => some s
  | i :: l, s => (i.run c s).bind (runL c l)

/-- how structured code ends: falls through, or jumps -/
inductive Res where
  | ok (s : St)
  | jmp (t : Tg) (s : St)

/-- big-step semantics of structured code -/
inductive SC.Ex (c : Cfg) : SC → St → Res → Prop
  | ins {l s s'} : runL c l s = some s' → SC.Ex c (.ins l) s (.ok s')
  | seq {a b s s1 r} : SC.Ex c a s (.ok s1) → SC.Ex c b s1 r → SC.Ex c (.seq a b) s r
  | seqJ {a b s t s1} : SC.Ex c a s (.jmp t s1) → SC.Ex c (.seq a b) s (.jmp t s1)
  | iteT {k r1 r2 t e s r} : k.eval (s.get r1) (s.get r2) = true → SC.Ex c t s r → SC.Ex c (.ite k r1 r2 t e) s r
  | iteF {k r1 r2 t e s r} : k.eval (s.get r1) (s.get r2) = false → SC.Ex c e s r →
      SC.Ex c (.ite k r1 r2 t e) s r
  | jmp {t s} : SC.Ex c (.jmp t) s (.jmp t s)
  /-- fuel 0: `z`, which falls through or jumps to EXIT (= falls through) -/
  | loopZ {test dec z body s s1 s2} : runL c test s = some s1 → s1.get 5 = 0 → SC.Ex c z s1 (.ok s2) →
      SC.Ex c (.loop test dec z body) s (.ok s2)
  | loopZX {test dec z body s s1 s2} : runL c test s = some s1 → s1.get 5 = 0 → SC.Ex c z s1 (.jmp .exit s2) →
      SC.Ex c (.loop test dec z body) s (.ok s2)
  /-- an abort (out of memory / capacity) inside `z` or `body` leaves the loop -/
  | loopZA {test dec z body s s1 t s2} : runL c test s = some s1 → s1.get 5 = 0 → SC.Ex c z s1 (.jmp t s2) →
      t = .oom ∨ t = .cap → SC.Ex c (.loop test dec z body) s (.jmp t s2)
  | loopX {test dec z body s s1 s2 s3} : runL c test s = some s1 → s1.get 5 ≠ 0 → runL c dec s1 = some s2 →
      SC.Ex c body s2 (.jmp .exit s3) → SC.Ex c (.loop test dec z body) s (.ok s3)
  | loopA {test dec z body s s1 s2 t s3} : runL c test s = some s1 → s1.get 5 ≠ 0 → runL c dec s1 = some s2 →
      SC.Ex c body s2 (.jmp t s3) → t = .oom ∨ t = .cap → SC.Ex c (.loop test dec z body) s (.jmp t s3)
  | loopH {test dec z body s s1 s2 s3 r} : runL c test s = some s1 → s1.get 5 ≠ 0 → runL c dec s1 = some s2 →
      SC.Ex c body s2 (.jmp .head s3) → SC.Ex c (.loop test dec z body) s3 r →
      SC.Ex c (.loop test dec z body) s r

theorem runL_append (c : Cfg) (l₁ l₂ : List I) (s : St) :
    runL c (l₁ ++ l₂) s = (runL c l₁ s).bind (runL c l₂) := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons i l ih =>
    simp only [List.cons_append, runL]
    cases i.run c s with
    | none => rfl
    | some s' => exact ih s'

end Nano.V2
