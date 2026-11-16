/- One shared IR (`Testing/notes/IR_DESIGN.md` §2.1): basic blocks with parameters (no phi, no SSA requirement),
64-bit values, explicit `alloc` / `ld` / `st` / `call`.  One datatype parametrised by the location type `ρ`:
RTL (`ρ = VReg`, made by front ends), LTL / Lin (`ρ` a location; here slot numbers, after allocation).

Pure Lean (core only). -/
import Compiler.Wide

namespace Proven.Ir
open Proven.Mach
set_option autoImplicit false

abbrev Lbl := Nat
abbrev FId := Nat
abbrev VReg := Nat

/-- a value: a 64-bit word or a pointer (block, offset in 8-byte cells).  Block `0` is the input (bytes),
block `1` the output (bytes), block `k + 2` the `k`-th allocated cell block. -/
inductive Val where
  | w (x : BitVec 64)
  | p (blk : Nat) (off : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- an operand: a location or an immediate -/
inductive Arg (ρ : Type) where
  | r (x : ρ)
  | i (c : BitVec 64)
  deriving Repr

/-- the right-hand side of a `let_` -/
inductive Rhs (ρ : Type) where
  | arg (a : Arg ρ)
  | op (o : Op) (a b : Arg ρ)
  | mop (m : Proven.Mach.MOp) (a b : Arg ρ)
  /-- pointer + cells (cell blocks only; one past the end allowed) -/
  | padd (p : ρ) (i : Arg ρ)
  deriving Repr

/-- a branch test -/
structure Tst (ρ : Type) where
  c : Cond
  a : Arg ρ
  b : Arg ρ
  deriving Repr

inductive Inst (ρ : Type) where
  | let_ (d : ρ) (e : Rhs ρ)
  /-- `d := byte i` of a byte block (input or output) -/
  | ldb (d : ρ) (p : ρ) (i : Arg ρ)
  /-- `byte i of the output := low byte of v` (the output grows on write) -/
  | stb (v : Arg ρ) (p : ρ) (i : Arg ρ)
  /-- `d := cell k` of a cell block (`p` points into it) -/
  | ld (d : ρ) (p : ρ) (k : Nat)
  /-- `cell k := v` -/
  | st (v : Arg ρ) (p : ρ) (k : Nat)
  /-- a fresh block of `cells` uninitialised cells -/
  | alloc (d : ρ) (cells : Arg ρ)
  | free (p : ρ)
  | call (ds : List ρ) (f : FId) (args : List (Arg ρ))
  deriving Repr

inductive Term (ρ : Type) where
  | jmp (l : Lbl) (as : List (Arg ρ))
  | br (t : Tst ρ) (l₁ : Lbl) (a₁ : List (Arg ρ)) (l₂ : Lbl) (a₂ : List (Arg ρ))
  /-- tag dispatch: `x = .w k` goes to `ls[k]`, else `dflt` -/
  | switch (x : ρ) (ls : List Lbl) (dflt : Lbl)
  | ret (vs : List (Arg ρ))
  deriving Repr

structure Block (ρ : Type) where
  params : List ρ
  body : List (Inst ρ)
  term : Term ρ
  deriving Repr

structure Func (ρ : Type) where
  params : List ρ
  entry : Lbl
  blocks : List (Lbl × Block ρ)
  /-- frame slots (0 at RTL; set by allocation) -/
  slots : Nat := 0
  deriving Repr

structure Prog (ρ : Type) where
  funcs : List (Func ρ)
  main : FId
  deriving Repr

/-! ## Renaming (the shape of allocation) -/

def Arg.map {ρ σ : Type} (f : ρ → σ) : Arg ρ → Arg σ
  | .r x => .r (f x)
  | .i c => .i c

def Rhs.map {ρ σ : Type} (f : ρ → σ) : Rhs ρ → Rhs σ
  | .arg a => .arg (a.map f)
  | .op o a b => .op o (a.map f) (b.map f)
  | .mop m a b => .mop m (a.map f) (b.map f)
  | .padd p i => .padd (f p) (i.map f)

def Tst.map {ρ σ : Type} (f : ρ → σ) (t : Tst ρ) : Tst σ := ⟨t.c, t.a.map f, t.b.map f⟩

def Inst.map {ρ σ : Type} (f : ρ → σ) : Inst ρ → Inst σ
  | .let_ d e => .let_ (f d) (e.map f)
  | .ldb d p i => .ldb (f d) (f p) (i.map f)
  | .stb v p i => .stb (v.map f) (f p) (i.map f)
  | .ld d p k => .ld (f d) (f p) k
  | .st v p k => .st (v.map f) (f p) k
  | .alloc d n => .alloc (f d) (n.map f)
  | .free p => .free (f p)
  | .call ds g as => .call (ds.map f) g (as.map (Arg.map f))

def Term.map {ρ σ : Type} (f : ρ → σ) : Term ρ → Term σ
  | .jmp l as => .jmp l (as.map (Arg.map f))
  | .br t l₁ a₁ l₂ a₂ => .br (t.map f) l₁ (a₁.map (Arg.map f)) l₂ (a₂.map (Arg.map f))
  | .switch x ls d => .switch (f x) ls d
  | .ret vs => .ret (vs.map (Arg.map f))

def Block.map {ρ σ : Type} (f : ρ → σ) (b : Block ρ) : Block σ :=
  ⟨b.params.map f, b.body.map (Inst.map f), b.term.map f⟩

end Proven.Ir
