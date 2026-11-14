/- The optimiser's IR: structured register code.  Polymorphic in the register type `ρ` (virtual registers
`Nat` before allocation, abstract machine registers `Reg` after).  Operands are registers or constants;
control is structured (`seq`, `when`, `loop`), so the semantics is big-step and has no program counter.

State: registers `ρ → BitVec 64` and a byte memory `Mem`; loads/stores must hit addresses satisfying `ram`
(a parameter: the target's RAM range) and, for loads, a mapped byte. -/
import Compiler.Wide

namespace Proven.Mach.IR

/-- operand -/
inductive Arg (ρ : Type) where
  | r (x : ρ)
  | i (c : BitVec 64)
  deriving Repr

/-- a test: `c.eval a b` -/
structure Tst (ρ : Type) where
  c : Cond
  a : Arg ρ
  b : Arg ρ
  deriving Repr

inductive Ins (ρ : Type) where
  /-- `d := a` -/
  | set (d : ρ) (a : Arg ρ)
  /-- `d := op.eval a b` -/
  | bin (op : Op) (d : ρ) (a b : Arg ρ)
  /-- `d := zero-extended byte mem[a + off]` -/
  | lbu (d : ρ) (a : Arg ρ) (off : BitVec 64)
  /-- `mem[a + off] := low byte of v` -/
  | sb (v : Arg ρ) (a : Arg ρ) (off : BitVec 64)
  /-- `d := slot j` (8 bytes at `fp + 8 (j + 1)`) -/
  | ldS (d : ρ) (j : Nat)
  /-- `slot j := v` -/
  | stS (j : Nat) (v : ρ)
  deriving Repr

inductive Code (ρ : Type) where
  | skip
  | ins (i : Ins ρ)
  | seq (a b : Code ρ)
  /-- `if t then body` -/
  | when (t : Tst ρ) (body : Code ρ)
  /-- `while (pre; t) do body` -/
  | loop (pre : Code ρ) (t : Tst ρ) (body : Code ρ)
  /-- `while (pre₁; t₁) && (pre₂; t₂) do body` (short-circuit) -/
  | loop2 (pre₁ : Code ρ) (t₁ : Tst ρ) (pre₂ : Code ρ) (t₂ : Tst ρ) (body : Code ρ)
  deriving Repr

variable {ρ : Type}

abbrev Regs (ρ : Type) := ρ → BitVec 64

def Arg.eval (σ : Regs ρ) : Arg ρ → BitVec 64
  | .r x => σ x
  | .i c => c

def Tst.eval (σ : Regs ρ) (t : Tst ρ) : Bool := t.c.eval (t.a.eval σ) (t.b.eval σ)

def Tst.neg (t : Tst ρ) : Tst ρ := ⟨t.c.neg, t.a, t.b⟩

theorem Tst.eval_neg (σ : Regs ρ) (t : Tst ρ) : t.neg.eval σ = !t.eval σ := Cond.eval_neg _ _ _

def upd [DecidableEq ρ] (σ : Regs ρ) (d : ρ) (v : BitVec 64) : Regs ρ := fun x => if x = d then v else σ x

structure St (ρ : Type) where
  reg : Regs ρ
  mem : Mem

section
variable [DecidableEq ρ] (ram : Nat → Prop) (fp : Nat)

inductive Step : Ins ρ → St ρ → St ρ → Prop
  | set {d a s} : Step (.set d a) s ⟨upd s.reg d (a.eval s.reg), s.mem⟩
  | bin {op d a b s} : Step (.bin op d a b) s ⟨upd s.reg d (op.eval (a.eval s.reg) (b.eval s.reg)), s.mem⟩
  | lbu {d a off s v} : ram (a.eval s.reg + off).toNat → s.mem (a.eval s.reg + off).toNat = some v →
      Step (.lbu d a off) s ⟨upd s.reg d (v.setWidth 64), s.mem⟩
  | sb {v a off s} : ram (a.eval s.reg + off).toNat →
      Step (.sb v a off) s ⟨s.reg, s.mem.upd (a.eval s.reg + off).toNat ((v.eval s.reg).setWidth 8)⟩
  | ldS {d j s v} : fp % 8 = 0 → (∀ i, i < 8 → ram (fp + 8 * (j + 1) + i)) → bytes s.mem (fp + 8 * (j + 1)) 8 = (le8 v).map some →
      Step (.ldS d j) s ⟨upd s.reg d v, s.mem⟩
  | stS {j v s} : fp % 8 = 0 → (∀ i, i < 8 → ram (fp + 8 * (j + 1) + i)) →
      Step (.stS j v) s ⟨s.reg, s.mem.wr (fp + 8 * (j + 1)) (le8 (s.reg v))⟩

inductive Exec : Code ρ → St ρ → St ρ → Prop
  | skip {s} : Exec .skip s s
  | ins {i s s'} : Step ram fp i s s' → Exec (.ins i) s s'
  | seq {a b s s₁ s₂} : Exec a s s₁ → Exec b s₁ s₂ → Exec (.seq a b) s s₂
  | whenT {t body s s'} : t.eval s.reg = true → Exec body s s' → Exec (.when t body) s s'
  | whenF {t body s} : t.eval s.reg = false → Exec (.when t body) s s
  | loopF {pre t body s s₁} : Exec pre s s₁ → t.eval s₁.reg = false → Exec (.loop pre t body) s s₁
  | loopT {pre t body s s₁ s₂ s₃} : Exec pre s s₁ → t.eval s₁.reg = true → Exec body s₁ s₂ →
      Exec (.loop pre t body) s₂ s₃ → Exec (.loop pre t body) s s₃
  | loop2A {p₁ t₁ p₂ t₂ body s s₁} : Exec p₁ s s₁ → t₁.eval s₁.reg = false → Exec (.loop2 p₁ t₁ p₂ t₂ body) s s₁
  | loop2B {p₁ t₁ p₂ t₂ body s s₁ s₂} : Exec p₁ s s₁ → t₁.eval s₁.reg = true → Exec p₂ s₁ s₂ →
      t₂.eval s₂.reg = false → Exec (.loop2 p₁ t₁ p₂ t₂ body) s s₂
  | loop2T {p₁ t₁ p₂ t₂ body s s₁ s₂ s₃ s₄} : Exec p₁ s s₁ → t₁.eval s₁.reg = true → Exec p₂ s₁ s₂ →
      t₂.eval s₂.reg = true → Exec body s₂ s₃ → Exec (.loop2 p₁ t₁ p₂ t₂ body) s₃ s₄ →
      Exec (.loop2 p₁ t₁ p₂ t₂ body) s s₄

/-- memory changes only at `ram` addresses -/
theorem Exec.mem_out {c : Code ρ} {s s' : St ρ} (h : Exec ram fp c s s') : ∀ a, ¬ram a → s'.mem a = s.mem a := by
  induction h with
  | skip => exact fun _ _ => rfl
  | ins hst =>
    intro a ha
    cases hst with
    | set => rfl
    | bin => rfl
    | lbu _ _ => rfl
    | sb hr => exact ite_neg fun e => ha (e ▸ hr)
    | ldS _ _ _ => rfl
    | @stS j _ _ _ hr =>
      refine Mem.wr_out ?_
      rw [length_le8]
      by_cases h : fp + 8 * (j + 1) ≤ a ∧ a < fp + 8 * (j + 1) + 8
      · exact absurd (by have := hr (a - (fp + 8 * (j + 1))) (by omega); rwa [Nat.add_sub_cancel' h.1] at this) ha
      · omega
  | seq _ _ iha ihb => exact fun a ha => (ihb a ha).trans (iha a ha)
  | whenT _ _ ih => exact ih
  | whenF _ => exact fun _ _ => rfl
  | loopF _ _ ih => exact ih
  | loopT _ _ _ _ ihp ihb ihl => exact fun a ha => (ihl a ha).trans ((ihb a ha).trans (ihp a ha))
  | loop2A _ _ ih => exact ih
  | loop2B _ _ _ _ ih₁ ih₂ => exact fun a ha => (ih₂ a ha).trans (ih₁ a ha)
  | loop2T _ _ _ _ _ _ ih₁ ih₂ ihb ihl =>
    exact fun a ha => (ihl a ha).trans ((ihb a ha).trans ((ih₂ a ha).trans (ih₁ a ha)))

end

/-- `seq` of a list -/
def Code.seqs : List (Code ρ) → Code ρ
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqs cs)

end Proven.Mach.IR
