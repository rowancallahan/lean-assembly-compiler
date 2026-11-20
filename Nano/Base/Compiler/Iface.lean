/- The machine interface: what the middle layer (`Proven/Mach/{Logic,Mem,Exp,Stmt,Arr}.lean`) assumes of
a target.  No Sail model here: a target is a `Machine`, i.e. a state type with a `runsTo` relation, 15
abstract 64-bit registers, a byte memory, a PC, an encoding of every abstract operation `AOp` into 32-bit
instruction words, and one LAW per abstract operation (what running its words does).

Pure Lean (core only, no `Std`); compiles unchanged under Lean 4.29.0 and 4.34.1. -/
import Spec.Code

namespace Proven.Mach

/-- abstract registers.  The middle layer's conventions: `r0 .. r10` expression temporaries (the `Exp`
compiler uses all 11, the array compiler `r0 .. r6`); `r11 .. r14` the variables `v0 .. v3`; the array
compiler's variables `v4 .. v7` are `r7 .. r10`. -/
abbrev Reg := Fin 15

/-- abstract operations (one may expand to several target words) -/
inductive AOp where
  /-- `d := a` -/
  | mov (d a : Reg)
  /-- `d := c` -/
  | li (d : Reg) (c : BitVec 64)
  /-- `d := op.eval a b` -/
  | bin (op : Op) (d a b : Reg)
  /-- `d := if c = 0 then b else a`; may clobber `a` -/
  | sel (d c a b : Reg)
  /-- `d := zero-extended byte mem[a]` -/
  | lbu (d a : Reg)
  /-- `mem[a] := low byte of v` -/
  | sb (v a : Reg)
  /-- if `c = 0` jump `n` words forward (from the start of this op), else fall through -/
  | bz (c : Reg) (n : Nat)
  /-- jump `n` words back (from the start of this op) -/
  | jmp (n : Nat)
  /-- jump to the return address -/
  | ret

/-- `if` with a known condition (stable names across Lean versions) -/
theorem ite_pos {α : Type} {p : Prop} [h : Decidable p] {a b : α} (hp : p) : (if p then a else b) = a := by
  cases h with
  | isTrue _ => rfl
  | isFalse hn => exact absurd hp hn

theorem ite_neg {α : Type} {p : Prop} [h : Decidable p] {a b : α} (hp : ¬p) : (if p then a else b) = b := by
  cases h with
  | isTrue h' => exact absurd h' hp
  | isFalse _ => rfl

theorem dite_pos' {α : Type} {p : Prop} [h : Decidable p] {a : p → α} {b : ¬p → α} (hp : p) :
    dite p a b = a hp := by
  cases h with
  | isTrue _ => rfl
  | isFalse hn => exact absurd hp hn

theorem dite_neg' {α : Type} {p : Prop} [h : Decidable p] {a : p → α} {b : ¬p → α} (hp : ¬p) :
    dite p a b = b hp := by
  cases h with
  | isTrue h' => exact absurd h' hp
  | isFalse _ => rfl

/-- byte memory -/
abbrev Mem := Nat → Option (BitVec 8)

def Mem.upd (m : Mem) (a : Nat) (v : BitVec 8) : Mem := fun x => if x = a then some v else m x

/-- the data of a target -/
structure Base where
  S : Type
  /-- `runsTo s P`: from `s` the machine runs (finitely many steps, no fault) to a state satisfying `P` -/
  runsTo : S → (S → Prop) → Prop
  /-- the fixed control state (RISC-V: `Cfg`) -/
  ok : S → Prop
  /-- the frame: everything outside the abstract registers, PC and memory is unchanged -/
  keep : S → S → Prop
  pcIs : S → BitVec 64 → Prop
  get : S → Reg → BitVec 64
  mem : S → Mem
  /-- the return address (RISC-V `ra`) -/
  ra : S → BitVec 64
  retOK : BitVec 64 → Prop
  instrAt : S → BitVec 64 → BitVec 32 → Prop
  /-- the byte at this address may be stored to (`sb`).  Supplied by the caller of a store; a target with
  plain RAM takes "in RAM", a target with page permissions takes "mapped writable". -/
  writable : S → Nat → Prop
  /-- RAM `[ramLo, ramHi)`: code and data live here -/
  ramLo : Nat
  ramHi : Nat
  /-- which forward branch / backward jump distances (in words) the target supports -/
  bzOK : Nat → Prop
  jmpOK : Nat → Prop
  enc : AOp → List (BitVec 32)
  /-- word length of `bz` and of `jmp` (independent of the operands) -/
  lenBz : Nat
  lenJmp : Nat

/-- the address `n` words after `pc` -/
def next (pc : BitVec 64) (n : Nat) : BitVec 64 := pc + BitVec.ofNat 64 (4 * n)

namespace Base
variable (B : Base)

/-- the words `ws` sit at `pc, pc+4, ...` -/
def codeAt (s : B.S) (pc : BitVec 64) (ws : List (BitVec 32)) : Prop :=
  ∀ i (hi : i < ws.length), B.instrAt s (pc + BitVec.ofNat 64 (4 * i)) ws[i]

/-- `[pc, pc + 4n)` is word aligned and in RAM -/
def codeOK (pc : BitVec 64) (n : Nat) : Prop :=
  pc.toNat % 4 = 0 ∧ B.ramLo ≤ pc.toNat ∧ pc.toNat + 4 * n ≤ B.ramHi

def inRAM (a n : Nat) : Prop := B.ramLo ≤ a ∧ a + n ≤ B.ramHi

/-- about to run the words `ws` -/
structure At (s : B.S) (pc : BitVec 64) (ws : List (BitVec 32)) : Prop where
  ok : B.ok s
  hpc : B.pcIs s pc
  code : B.codeAt s pc ws
  codeOK : B.codeOK pc ws.length

/-- what every operation guarantees about the end state -/
structure Done (s s' : B.S) (pc' : BitVec 64) : Prop where
  ok : B.ok s'
  keep : B.keep s s'
  hpc : B.pcIs s' pc'

/-- register `d` set to `v`, every other register unchanged -/
def Set1 (s s' : B.S) (d : Reg) (v : BitVec 64) : Prop := ∀ r, B.get s' r = if r = d then v else B.get s r

/-- all registers unchanged -/
def Same (s s' : B.S) : Prop := ∀ r, B.get s' r = B.get s r

end Base

/-- the `mov` operand shapes the middle layer emits -/
def MovOK (d a : Reg) : Prop :=
  (d.val < 11 ∧ 11 ≤ a.val) ∨ (d.val < 7 ∧ 7 ≤ a.val ∧ a.val < 11) ∨ (a.val = 0 ∧ 7 ≤ d.val)

/-- generic laws (no operation) -/
structure Core extends Base where
  runsTo_of : ∀ {s : S} {P : S → Prop}, P s → runsTo s P
  runsTo_trans : ∀ {s : S} {P Q : S → Prop}, runsTo s P → (∀ s', P s' → runsTo s' Q) → runsTo s Q
  keep_refl : ∀ s, keep s s
  keep_trans : ∀ {s₁ s₂ s₃ : S}, keep s₁ s₂ → keep s₂ s₃ → keep s₁ s₃
  keep_ra : ∀ {s s' : S}, keep s s' → ra s' = ra s
  /-- an instruction word depends only on its 4 bytes -/
  instrAt_frame : ∀ {s s' : S} {pc : BitVec 64} {w : BitVec 32},
    (∀ j, j < 4 → mem s' (pc.toNat + j) = mem s (pc.toNat + j)) → instrAt s pc w → instrAt s' pc w
  ramHi_lt : ramHi < 2 ^ 64
  len_bz : ∀ c n, (enc (.bz c n)).length = lenBz
  len_jmp : ∀ n, (enc (.jmp n)).length = lenJmp

/-- **The interface**: one law per abstract operation.  Each law starts from `At s pc (enc o)` (control
state ok, PC at `pc`, the words of `o` at `pc`, in RAM) and ends in `Done` (control state ok, frame kept,
the PC given) plus the operation's effect on registers and memory. -/
structure Machine extends Core where
  law_mov : ∀ {d a : Reg} {s : S} {pc : BitVec 64}, MovOK d a → toBase.At s pc (enc (.mov d a)) →
    runsTo s fun s' => toBase.Done s s' (next pc (enc (.mov d a)).length) ∧
      toBase.Set1 s s' d (get s a) ∧ mem s' = mem s
  law_li : ∀ {d : Reg} {c : BitVec 64} {s : S} {pc : BitVec 64}, d.val < 11 → toBase.At s pc (enc (.li d c)) →
    runsTo s fun s' => toBase.Done s s' (next pc (enc (.li d c)).length) ∧
      toBase.Set1 s s' d c ∧ mem s' = mem s
  law_bin : ∀ {op : Op} {d a b : Reg} {s : S} {pc : BitVec 64}, d.val < 10 → a = d → b.val = d.val + 1 →
    toBase.At s pc (enc (.bin op d a b)) →
    runsTo s fun s' => toBase.Done s s' (next pc (enc (.bin op d a b)).length) ∧
      toBase.Set1 s s' d (op.eval (get s a) (get s b)) ∧ mem s' = mem s
  law_sel : ∀ {d c a b : Reg} {s : S} {pc : BitVec 64}, d.val < 9 → c = d → a.val = d.val + 1 →
    b.val = d.val + 2 → toBase.At s pc (enc (.sel d c a b)) →
    runsTo s fun s' => toBase.Done s s' (next pc (enc (.sel d c a b)).length) ∧
      get s' d = (if get s c = 0 then get s b else get s a) ∧
      (∀ r, r ≠ d → r ≠ a → get s' r = get s r) ∧ mem s' = mem s
  law_lbu : ∀ {d a : Reg} {s : S} {pc : BitVec 64} {v : BitVec 8}, d.val = 0 → a.val = 0 →
    toBase.At s pc (enc (.lbu d a)) → toBase.inRAM (get s a).toNat 1 → mem s (get s a).toNat = some v →
    runsTo s fun s' => toBase.Done s s' (next pc (enc (.lbu d a)).length) ∧
      toBase.Set1 s s' d (v.setWidth 64) ∧ mem s' = mem s
  law_sb : ∀ {v a : Reg} {s : S} {pc : BitVec 64}, v.val = 1 → a.val = 0 →
    toBase.At s pc (enc (.sb v a)) → writable s (get s a).toNat →
    runsTo s fun s' => toBase.Done s s' (next pc (enc (.sb v a)).length) ∧
      toBase.Same s s' ∧ mem s' = (mem s).upd (get s a).toNat ((get s v).setWidth 8)
  law_bz : ∀ {c : Reg} {n : Nat} {s : S} {pc : BitVec 64}, c.val = 0 → bzOK n → toBase.At s pc (enc (.bz c n)) →
    runsTo s fun s' => toBase.Done s s'
        (if get s c = 0 then next pc n else next pc (enc (.bz c n)).length) ∧
      toBase.Same s s' ∧ mem s' = mem s
  law_jmp : ∀ {n : Nat} {s : S} {pc : BitVec 64}, jmpOK n → toBase.At s pc (enc (.jmp n)) →
    runsTo s fun s' => toBase.Done s s' (pc - BitVec.ofNat 64 (4 * n)) ∧ toBase.Same s s' ∧ mem s' = mem s
  law_ret : ∀ {s : S} {pc : BitVec 64}, retOK (ra s) → toBase.At s pc (enc .ret) →
    runsTo s fun s' => toBase.Done s s' (ra s) ∧ toBase.Same s s' ∧ mem s' = mem s

end Proven.Mach
