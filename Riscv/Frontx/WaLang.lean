/- Word arrays, tables, growing output (NOTES section 20): the source language `WA`.

A small typed language whose meaning (`den`) is written with the very Lean operations library code uses
(`UInt32` `^^^`, `a[i]!`, `Array.set!`, `ByteArray.push`, ...), so that a Lean definition, reflected into
this syntax, is equal to the meaning of its syntax by unfolding (`simp only [den lemmas]`), with no
restatement.  Values: scalars (`Ty`) and arrays (`AK`: `ByteArray` or `Array t`).  A program `Pg` is a
sequence of stages: scalar `let`s, fresh arrays (`replicate`, constant tables, copies, views of the
input) and loops; a loop is a decision tree `T` over its state `Δ` (plus read-only access to the enclosing
values) whose leaves continue (`call`: the new state) or stop (`ret`).  Loops have a relational meaning
(`Runs`); `runs_of` turns the equation of a Lean function (`g s = b.den s g`) plus a measure into `Runs`.

The compiler and its proof: `WaComp.lean`; reflection and commands: `WaCmd.lean`. -/
import Riscv.Frontx.Exc

namespace Proven.WA
open Proven Proven.Frontx

/-! ## Types and values -/

inductive Ty | u8 | u16 | u32 | u64 | nat | bool
  deriving DecidableEq, Repr

abbrev Ty.T : Ty → Type
  | .u8 => UInt8 | .u16 => UInt16 | .u32 => UInt32 | .u64 => UInt64 | .nat => Nat | .bool => Bool

instance Ty.inh : (t : Ty) → Inhabited t.T
  | .u8 => inferInstanceAs (Inhabited UInt8) | .u16 => inferInstanceAs (Inhabited UInt16)
  | .u32 => inferInstanceAs (Inhabited UInt32) | .u64 => inferInstanceAs (Inhabited UInt64)
  | .nat => inferInstanceAs (Inhabited Nat) | .bool => inferInstanceAs (Inhabited Bool)

instance Ty.deq : (t : Ty) → DecidableEq t.T
  | .u8 => inferInstanceAs (DecidableEq UInt8) | .u16 => inferInstanceAs (DecidableEq UInt16)
  | .u32 => inferInstanceAs (DecidableEq UInt32) | .u64 => inferInstanceAs (DecidableEq UInt64)
  | .nat => inferInstanceAs (DecidableEq Nat) | .bool => inferInstanceAs (DecidableEq Bool)

/-- the machine word of a value -/
def Ty.rep : (t : Ty) → t.T → BitVec 64
  | .u8, x => r8 x | .u16, x => r16 x | .u32, x => r32 x | .u64, x => r64 x | .nat, x => rN x | .bool, x => rB x

/-- bytes of a value in a result (little-endian) -/
def Ty.width : Ty → Nat | .u8 => 1 | .u16 => 2 | .u32 => 4 | .u64 => 8 | .nat => 8 | .bool => 1

/-- `ByteArray` or `Array t` -/
inductive AK | ba | arr (t : Ty)
  deriving DecidableEq, Repr

abbrev AK.T : AK → Type | .ba => ByteArray | .arr t => Array t.T
def AK.el : AK → Ty | .ba => .u8 | .arr t => t

def AK.size : (k : AK) → k.T → Nat
  | .ba, a => a.size | .arr .u8, a => a.size | .arr .u16, a => a.size | .arr .u32, a => a.size
  | .arr .u64, a => a.size | .arr .nat, a => a.size | .arr .bool, a => a.size

/-- `a[i]!` -/
def AK.get : (k : AK) → k.T → Nat → k.el.T
  | .ba, a, i => a[i]! | .arr .u8, a, i => a[i]! | .arr .u16, a, i => a[i]! | .arr .u32, a, i => a[i]!
  | .arr .u64, a, i => a[i]! | .arr .nat, a, i => a[i]! | .arr .bool, a, i => a[i]!

/-- `a.set! i x` -/
def AK.set : (k : AK) → k.T → Nat → k.el.T → k.T
  | .ba, a, i, x => a.set! i x | .arr .u8, a, i, x => a.set! i x | .arr .u16, a, i, x => a.set! i x
  | .arr .u32, a, i, x => a.set! i x | .arr .u64, a, i, x => a.set! i x | .arr .nat, a, i, x => a.set! i x
  | .arr .bool, a, i, x => a.set! i x

/-- `a.push x` -/
def AK.push : (k : AK) → k.T → k.el.T → k.T
  | .ba, a, x => a.push x | .arr .u8, a, x => a.push x | .arr .u16, a, x => a.push x
  | .arr .u32, a, x => a.push x | .arr .u64, a, x => a.push x | .arr .nat, a, x => a.push x
  | .arr .bool, a, x => a.push x

/-- the elements as a list -/
def AK.toList : (k : AK) → k.T → List k.el.T
  | .ba, a => a.data.toList | .arr .u8, a => a.toList | .arr .u16, a => a.toList | .arr .u32, a => a.toList
  | .arr .u64, a => a.toList | .arr .nat, a => a.toList | .arr .bool, a => a.toList

/-- a slot of an environment: a scalar or an array -/
inductive Sl | sc (t : Ty) | ar (k : AK)
  deriving DecidableEq, Repr

abbrev Sl.T : Sl → Type | .sc t => t.T | .ar k => k.T

/-- values of an environment: nested pairs -/
abbrev Vals : List Sl → Type
  | [] => Unit
  | s :: Γ => s.T × Vals Γ

/-- a variable: a position in the environment, typed -/
inductive Mem : List Sl → Sl → Type
  | hd {s Γ} : Mem (s :: Γ) s
  | tl {s s' Γ} : Mem Γ s → Mem (s' :: Γ) s

def Mem.get : {Γ : List Sl} → {s : Sl} → Mem Γ s → Vals Γ → s.T
  | _, _, .hd, v => v.1
  | _, _, .tl m, v => m.get v.2

def Mem.idx : {Γ : List Sl} → {s : Sl} → Mem Γ s → Nat
  | _, _, .hd => 0
  | _, _, .tl m => m.idx + 1

/-- appending environments (a loop body sees its state, then the enclosing values) -/
def Vals.app : {Δ Γ : List Sl} → Vals Δ → Vals Γ → Vals (Δ ++ Γ)
  | [], _, _, c => c
  | _ :: _, _, s, c => (s.1, Vals.app s.2 c)

/-! ## Operations -/

inductive Op2 | add | sub | mul | div | mod | and | or | xor | shl | shr | band | bor
  deriving DecidableEq, Repr

def Op2.den : (o : Op2) → (t : Ty) → t.T → t.T → t.T
  | .add, .u8, a, b => @HAdd.hAdd UInt8 UInt8 UInt8 _ a b | .add, .u16, a, b => @HAdd.hAdd UInt16 UInt16 UInt16 _ a b | .add, .u32, a, b => @HAdd.hAdd UInt32 UInt32 UInt32 _ a b 
  | .add, .u64, a, b => @HAdd.hAdd UInt64 UInt64 UInt64 _ a b | .add, .nat, a, b => @HAdd.hAdd Nat Nat Nat _ a b 
  | .sub, .u8, a, b => @HSub.hSub UInt8 UInt8 UInt8 _ a b | .sub, .u16, a, b => @HSub.hSub UInt16 UInt16 UInt16 _ a b | .sub, .u32, a, b => @HSub.hSub UInt32 UInt32 UInt32 _ a b 
  | .sub, .u64, a, b => @HSub.hSub UInt64 UInt64 UInt64 _ a b | .sub, .nat, a, b => @HSub.hSub Nat Nat Nat _ a b 
  | .mul, .nat, a, b => @HMul.hMul Nat Nat Nat _ a b 
  | .div, .nat, a, b => @HDiv.hDiv Nat Nat Nat _ a b 
  | .mod, .nat, a, b => @HMod.hMod Nat Nat Nat _ a b 
  | .and, .u8, a, b => @HAnd.hAnd UInt8 UInt8 UInt8 _ a b | .and, .u16, a, b => @HAnd.hAnd UInt16 UInt16 UInt16 _ a b | .and, .u32, a, b => @HAnd.hAnd UInt32 UInt32 UInt32 _ a b 
  | .and, .u64, a, b => @HAnd.hAnd UInt64 UInt64 UInt64 _ a b | .and, .nat, a, b => @HAnd.hAnd Nat Nat Nat _ a b 
  | .or, .u8, a, b => a ||| b | .or, .u16, a, b => a ||| b | .or, .u32, a, b => a ||| b
  | .or, .u64, a, b => a ||| b | .or, .nat, a, b => a ||| b
  | .xor, .u8, a, b => @HXor.hXor UInt8 UInt8 UInt8 _ a b | .xor, .u16, a, b => @HXor.hXor UInt16 UInt16 UInt16 _ a b | .xor, .u32, a, b => @HXor.hXor UInt32 UInt32 UInt32 _ a b 
  | .xor, .u64, a, b => @HXor.hXor UInt64 UInt64 UInt64 _ a b | .xor, .nat, a, b => @HXor.hXor Nat Nat Nat _ a b 
  | .shl, .u8, a, b => @HShiftLeft.hShiftLeft UInt8 UInt8 UInt8 _ a b | .shl, .u16, a, b => @HShiftLeft.hShiftLeft UInt16 UInt16 UInt16 _ a b | .shl, .u32, a, b => @HShiftLeft.hShiftLeft UInt32 UInt32 UInt32 _ a b 
  | .shl, .u64, a, b => @HShiftLeft.hShiftLeft UInt64 UInt64 UInt64 _ a b 
  | .shr, .u8, a, b => @HShiftRight.hShiftRight UInt8 UInt8 UInt8 _ a b | .shr, .u16, a, b => @HShiftRight.hShiftRight UInt16 UInt16 UInt16 _ a b | .shr, .u32, a, b => @HShiftRight.hShiftRight UInt32 UInt32 UInt32 _ a b 
  | .shr, .u64, a, b => @HShiftRight.hShiftRight UInt64 UInt64 UInt64 _ a b | .shr, .nat, a, b => @HShiftRight.hShiftRight Nat Nat Nat _ a b 
  | .band, .bool, a, b => a && b 
  | .bor, .bool, a, b => a || b
  | _, _, _, _ => default

inductive Cmp | eq | ne | lt | le
  deriving DecidableEq, Repr

def Cmp.den : (o : Cmp) → (t : Ty) → t.T → t.T → Bool
  | .eq, .u8, a, b => @BEq.beq UInt8 _ a b | .eq, .u16, a, b => @BEq.beq UInt16 _ a b | .eq, .u32, a, b => @BEq.beq UInt32 _ a b 
  | .eq, .u64, a, b => @BEq.beq UInt64 _ a b | .eq, .nat, a, b => @BEq.beq Nat _ a b | .eq, .bool, a, b => @BEq.beq Bool _ a b 
  | .ne, .u8, a, b => @bne UInt8 _ a b | .ne, .u16, a, b => @bne UInt16 _ a b | .ne, .u32, a, b => @bne UInt32 _ a b 
  | .ne, .u64, a, b => @bne UInt64 _ a b | .ne, .nat, a, b => @bne Nat _ a b | .ne, .bool, a, b => @bne Bool _ a b 
  | .lt, .u8, a, b => decide (@LT.lt UInt8 _ a b) | .lt, .u16, a, b => decide (@LT.lt UInt16 _ a b) | .lt, .u32, a, b => decide (@LT.lt UInt32 _ a b) 
  | .lt, .u64, a, b => decide (@LT.lt UInt64 _ a b) | .lt, .nat, a, b => decide (@LT.lt Nat _ a b) 
  | .le, .u8, a, b => decide (@LE.le UInt8 _ a b) | .le, .u16, a, b => decide (@LE.le UInt16 _ a b) | .le, .u32, a, b => decide (@LE.le UInt32 _ a b) 
  | .le, .u64, a, b => decide (@LE.le UInt64 _ a b) | .le, .nat, a, b => decide (@LE.le Nat _ a b) 
  | _, _, _, _ => false

/-- casts: `toNat`, `ofNat`, widening and narrowing between the unsigned types, `!` on `Bool` -/
def cast : (s t : Ty) → s.T → t.T
  | .u8, .nat, x => x.toNat | .u16, .nat, x => x.toNat | .u32, .nat, x => x.toNat | .u64, .nat, x => x.toNat
  | .nat, .u8, x => UInt8.ofNat x | .nat, .u16, x => UInt16.ofNat x | .nat, .u32, x => UInt32.ofNat x
  | .nat, .u64, x => UInt64.ofNat x
  | .u8, .u16, x => x.toUInt16 | .u8, .u32, x => x.toUInt32 | .u8, .u64, x => x.toUInt64
  | .u16, .u8, x => x.toUInt8 | .u16, .u32, x => x.toUInt32 | .u16, .u64, x => x.toUInt64
  | .u32, .u8, x => x.toUInt8 | .u32, .u16, x => x.toUInt16 | .u32, .u64, x => x.toUInt64
  | .u64, .u8, x => x.toUInt8 | .u64, .u16, x => x.toUInt16 | .u64, .u32, x => x.toUInt32
  | .bool, .bool, x => !x
  | _, _, _ => default

/-! ## Syntax -/

/-- scalar expressions; `get m i chk` is `a[i]!` (`chk = false`: the source read `a[i]'h` with a proof, the
compiler emits a plain load and the bound is an obligation); `getB` reads a `ByteArray`, `getA` an `Array` -/
inductive E (Γ : List Sl) : Ty → Type
  | var {t} (m : Mem Γ (.sc t)) : E Γ t
  | lit (t : Ty) (c : t.T) : E Γ t
  | bin {t} (o : Op2) (a b : E Γ t) : E Γ t
  | cmp {t} (o : Cmp) (a b : E Γ t) : E Γ .bool
  | cast {s} (t : Ty) (a : E Γ s) : E Γ t
  | ite {t} (c : E Γ .bool) (a b : E Γ t) : E Γ t
  | getB (m : Mem Γ (.ar .ba)) (i : E Γ .nat) (chk : Bool) : E Γ .u8
  | getA {t} (m : Mem Γ (.ar (.arr t))) (i : E Γ .nat) (chk : Bool) : E Γ t
  | size {k} (m : Mem Γ (.ar k)) : E Γ .nat

/-- in-place updates of the array in a state slot (`base`) -/
inductive A (Γ : List Sl) (k : AK) : Type
  | var (m : Mem Γ (.ar k)) : A Γ k
  | set (a : A Γ k) (i : E Γ .nat) (x : E Γ k.el) : A Γ k
  | push (a : A Γ k) (x : E Γ k.el) : A Γ k
  | ite (c : E Γ .bool) (a b : A Γ k) : A Γ k

/-- fresh arrays (and read-only views) -/
inductive F (Γ : List Sl) : AK → Type
  /-- `Array.replicate n x` -/
  | rep {t} (n : E Γ .nat) (x : E Γ t) : F Γ (.arr t)
  /-- a constant table (a top-level `Array` definition) -/
  | const {t} (c : Array t.T) : F Γ (.arr t)
  /-- `ByteArray.empty` -/
  | empty : F Γ .ba
  /-- `xs.extract lo hi` -/
  | extract (m : Mem Γ (.ar .ba)) (lo hi : E Γ .nat) : F Γ .ba
  /-- `xs.data` (read-only view) -/
  | data (m : Mem Γ (.ar .ba)) : F Γ (.arr .u8)
  /-- an existing array (read-only) -/
  | alias {k} (m : Mem Γ (.ar k)) : F Γ k

/-- the new value of a state slot at a `call` -/
abbrev Arg (Γ : List Sl) : Sl → Type
  | .sc t => E Γ t
  | .ar k => A Γ k

/-- the initial value of a slot (`let`, loop start) -/
abbrev Ini (Γ : List Sl) : Sl → Type
  | .sc t => E Γ t
  | .ar k => F Γ k

inductive Args (Γ : List Sl) : List Sl → Type
  | nil : Args Γ []
  | cons {s Δ} (a : Arg Γ s) (as : Args Γ Δ) : Args Γ (s :: Δ)

inductive Inis (Γ : List Sl) : List Sl → Type
  | nil : Inis Γ []
  | cons {s Δ} (a : Ini Γ s) (as : Inis Γ Δ) : Inis Γ (s :: Δ)

/-- a loop body over scope `Γ` (state `Δ` first), result `R` -/
inductive T : List Sl → List Sl → Sl → Type
  | ret {Γ Δ R} (r : Arg Γ R) : T Γ Δ R
  | call {Γ Δ R} (as : Args Γ Δ) : T Γ Δ R
  | ite {Γ Δ R} (c : E Γ .bool) (a b : T Γ Δ R) : T Γ Δ R
  | let_ {Γ Δ R t} (e : E Γ t) (k : T (.sc t :: Γ) Δ R) : T Γ Δ R

/-- a program: stages -/
inductive Pg : List Sl → Sl → Type
  | ret {Γ R} (r : Arg Γ R) : Pg Γ R
  | let_ {Γ R s} (x : Ini Γ s) (k : Pg (s :: Γ) R) : Pg Γ R
  | loop {Γ R s} (Δ : List Sl) (b : T (Δ ++ Γ) Δ s) (init : Inis Γ Δ) (k : Pg (s :: Γ) R) : Pg Γ R

/-! ## Meaning -/

def E.den {Γ : List Sl} : {t : Ty} → E Γ t → Vals Γ → t.T
  | _, .var m, v => m.get v
  | _, .lit _ c, _ => c
  | _, .bin o a b, v => o.den _ (a.den v) (b.den v)
  | _, .cmp o a b, v => o.den _ (a.den v) (b.den v)
  | _, .cast t a, v => WA.cast _ t (a.den v)
  | _, .ite c a b, v => if c.den v = true then a.den v else b.den v
  | _, .getB m i _, v => AK.get .ba (m.get v) (i.den v)
  | _, .getA m i _, v => AK.get (.arr _) (m.get v) (i.den v)
  | _, .size m, v => AK.size _ (m.get v)

def A.den {Γ : List Sl} {k : AK} : A Γ k → Vals Γ → k.T
  | .var m, v => m.get v
  | .set a i x, v => AK.set k (a.den v) (i.den v) (x.den v)
  | .push a x, v => AK.push k (a.den v) (x.den v)
  | .ite c a b, v => if c.den v = true then a.den v else b.den v

def F.den {Γ : List Sl} : {k : AK} → F Γ k → Vals Γ → k.T
  | _, @F.rep _ t n x, v => match t, x.den v with
    | .u8, y => Array.replicate (n.den v) y | .u16, y => Array.replicate (n.den v) y
    | .u32, y => Array.replicate (n.den v) y | .u64, y => Array.replicate (n.den v) y
    | .nat, y => Array.replicate (n.den v) y | .bool, y => Array.replicate (n.den v) y
  | _, .const c, _ => c
  | _, .empty, _ => ByteArray.empty
  | _, .extract m lo hi, v => (m.get v).extract (lo.den v) (hi.den v)
  | _, .data m, v => (m.get v).data
  | _, .alias m, v => m.get v

def Arg.den {Γ : List Sl} : (s : Sl) → Arg Γ s → Vals Γ → s.T
  | .sc _, e, v => E.den e v
  | .ar _, a, v => A.den a v

def Ini.den {Γ : List Sl} : (s : Sl) → Ini Γ s → Vals Γ → s.T
  | .sc _, e, v => E.den e v
  | .ar _, a, v => F.den a v

def Args.den {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → Vals Γ → Vals Δ
  | _, .nil, _ => ()
  | _, .cons (s := s) a as, v => (Arg.den s a v, as.den v)

def Inis.den {Γ : List Sl} : {Δ : List Sl} → Inis Γ Δ → Vals Γ → Vals Δ
  | _, .nil, _ => ()
  | _, .cons (s := s) a as, v => (Ini.den s a v, as.den v)

/-- the meaning of a body with the continuation `g` at `call` leaves (the shape of a Lean equation) -/
def T.den : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → Vals Γ → (Vals Δ → R.T) → R.T
  | _, _, R, .ret r, v, _ => Arg.den R r v
  | _, _, _, .call as, v, g => g (as.den v)
  | _, _, _, .ite c a b, v, g => if c.den v = true then a.den v g else b.den v g
  | _, _, _, .let_ e k, v, g => k.den (e.den v, v) g

/-- the leaf a body reaches: a new state or the result -/
def T.out : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → Vals Γ → Vals Δ ⊕ R.T
  | _, _, R, .ret r, v => .inr (Arg.den R r v)
  | _, _, _, .call as, v => .inl (as.den v)
  | _, _, _, .ite c a b, v => if c.den v = true then a.out v else b.out v
  | _, _, _, .let_ e k, v => k.out (e.den v, v)

theorem T.den_out {Γ Δ : List Sl} {R : Sl} (b : T Γ Δ R) (v : Vals Γ) (g : Vals Δ → R.T) :
    b.den v g = match b.out v with | .inl s => g s | .inr r => r := by
  induction b with
  | ret r => rfl
  | call as => rfl
  | ite c a b iha ihb => simp only [T.den, T.out]; split <;> simp_all
  | let_ e k ih => simp only [T.den, T.out]; exact ih _ _

/-- iterating a loop body from state `s` (enclosing values `c`) ends with `r` -/
inductive Runs {Δ Γ : List Sl} {R : Sl} (b : T (Δ ++ Γ) Δ R) (c : Vals Γ) : Vals Δ → R.T → Prop
  | ret {s r} : b.out (Vals.app s c) = .inr r → Runs b c s r
  | call {s s' r} : b.out (Vals.app s c) = .inl s' → Runs b c s' r → Runs b c s r

/-- **A Lean function satisfying the body's equation runs to its value** (by a measure and an invariant) -/
theorem runs_of {Δ Γ : List Sl} {R : Sl} (b : T (Δ ++ Γ) Δ R) (c : Vals Γ) (g : Vals Δ → R.T)
    (P : Vals Δ → Prop) (μ : Vals Δ → Nat) (heq : ∀ s, P s → g s = b.den (Vals.app s c) g)
    (hstep : ∀ s s', P s → b.out (Vals.app s c) = .inl s' → P s' ∧ μ s' < μ s) :
    ∀ s, P s → Runs b c s (g s) := by
  suffices H : ∀ n s, μ s < n → P s → Runs b c s (g s) from fun s => H _ s (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro s h; omega
  | succ n ih =>
    intro s hn hP
    have he := heq s hP
    rw [T.den_out] at he
    revert he
    cases ho : b.out (Vals.app s c) with
    | inl s' =>
      intro he
      obtain ⟨hP', hμ⟩ := hstep s s' hP ho
      rw [he]; exact .call ho (ih s' (by omega) hP')
    | inr r => intro he; rw [he]; exact .ret ho

/-- the meaning of a program (relational: loops through `Runs`) -/
def Pg.Den : {Γ : List Sl} → {R : Sl} → Pg Γ R → Vals Γ → R.T → Prop
  | _, R, .ret r, v, y => y = Arg.den R r v
  | _, _, .let_ (s := s) x k, v, y => k.Den (Ini.den s x v, v) y
  | _, _, .loop _ b init k, v, y => ∃ r, Runs b v (init.den v) r ∧ k.Den (r, v) y

end Proven.WA
