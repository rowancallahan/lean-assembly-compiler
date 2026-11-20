/- The target interface of the IR back end (`Testing/notes/IR_DESIGN.md` §2.5): the wide operations with a frame
(`WideF`: any registers, slots, 8-byte loads/stores, compare-and-branch both ways, jumps both ways, `enter`/`leave`)
plus the top of the work block (`top`, read by `getTop`), so the code can check that a frame fits before opening
it.  A new target is these laws only; emission and its correctness (`Compiler/Ir/Emit*.lean`) are proved once.

Pure Lean (core only). -/
import Nano.Base.Compiler.Opt.BFn

namespace Proven.Ir
open Proven.Mach
set_option autoImplicit false

structure Target extends WideF where
  /-- the aligned top of the work block (RISC-V: `sp` rounded down to 8 bytes) -/
  top : S → Nat
  /-- `d := top - 8` -/
  encT : Reg → List (BitVec 32)
  t_top : ∀ {d : Reg} {s : S} {pc : BitVec 64}, d.val < 7 → 16 ≤ top s → toBase.At s pc (encT d) →
    runsTo s fun s' => toBase.Done s s' (next pc (encT d).length) ∧
      toBase.Set1 s s' d (BitVec.ofNat 64 (top s - 8)) ∧ mem s' = mem s
  top_keepF : ∀ {s s' : S}, keepF s s' → top s' = top s
  frameAt_top : ∀ (s : S) (n : Nat), frameAt s n = top s - 8 * (n + 1)
  enterOK_of : ∀ {s : S} {n : Nat}, n ≤ maxSlots → 8 * (n + 1) ≤ top s → top s % 8 = 0 →
    toBase.inRAM (top s - 8 * (n + 1)) (8 * (n + 1)) → enterOK s n
  -- calls (as `MachineC`, `Compiler/Call.lean`) and the out-of-memory exit (as `MachineM.exit`)
  /-- `keepF` without the link register -/
  keepC : S → S → Prop
  keepC_of_keepF : ∀ {s s' : S}, keepF s s' → keepC s s'
  keepC_trans : ∀ {s₁ s₂ s₃ : S}, keepC s₁ s₂ → keepC s₂ s₃ → keepC s₁ s₃
  top_keepC : ∀ {s s' : S}, keepC s s' → top s' = top s
  /-- a word-aligned address is a valid return address -/
  retOK_al : ∀ v : BitVec 64, v.toNat % 4 = 0 → retOK v
  /-- `call d`: jump `d` words (signed, from the start of this op), the link register := the next op -/
  encCall : Int → List (BitVec 32)
  callOK : Int → Bool
  lenCall : Nat
  len_call : ∀ d, (encCall d).length = lenCall
  c_call : ∀ {d : Int} {s : S} {pc : BitVec 64}, callOK d = true → toBase.At s pc (encCall d) →
    runsTo s fun s' => ok s' ∧ keepC s s' ∧ pcIs s' (pc + BitVec.ofInt 64 (4 * d)) ∧
      ra s' = next pc lenCall ∧ fr s' = fr s ∧ toBase.Same s s' ∧ mem s' = mem s
  /-- `enterC n`: a frame of `n` slots below the current one, its cell 0 := the link register -/
  encEC : Nat → List (BitVec 32)
  c_enterC : ∀ {n : Nat} {s : S} {pc : BitVec 64}, n ≤ maxSlots → toBase.At s pc (encEC n) →
    8 * (n + 1) ≤ (fr s).toNat → toBase.inRAM ((fr s).toNat - 8 * (n + 1)) 8 → (fr s).toNat % 8 = 0 →
    (∀ i, i < 8 → writable s ((fr s).toNat - 8 * (n + 1) + i)) →
    runsTo s fun s' => ok s' ∧ keepC s s' ∧ pcIs s' (next pc (encEC n).length) ∧
      fr s' = BitVec.ofNat 64 ((fr s).toNat - 8 * (n + 1)) ∧ toBase.Same s s' ∧
      mem s' = (mem s).wr ((fr s).toNat - 8 * (n + 1)) (le8 (ra s))
  /-- `leaveC n`: the link register := cell 0, the frame register up by the frame -/
  encLC : Nat → List (BitVec 32)
  c_leaveC : ∀ {n : Nat} {s : S} {pc : BitVec 64} {w : BitVec 64}, n ≤ maxSlots →
    toBase.At s pc (encLC n) → toBase.inRAM (fr s).toNat (8 * (n + 1)) → (fr s).toNat % 8 = 0 →
    bytes (mem s) (fr s).toNat 8 = (le8 w).map some →
    runsTo s fun s' => ok s' ∧ keepC s s' ∧ pcIs s' (next pc (encLC n).length) ∧ ra s' = w ∧
      fr s' = BitVec.ofNat 64 ((fr s).toNat + 8 * (n + 1)) ∧ toBase.Same s s' ∧ mem s' = mem s
  /-- out of memory: return to the address in the cell `top - 16`, the status register (`r11`) `:= -1` -/
  encX : List (BitVec 32)
  c_exit : ∀ {s : S} {pc w : BitVec 64}, toBase.At s pc encX → 16 ≤ top s →
    toBase.inRAM (top s - 16) 8 → (top s - 16) % 8 = 0 → bytes (mem s) (top s - 16) 8 = (le8 w).map some →
    retOK w → runsTo s fun s' => ok s' ∧ pcIs s' w ∧ get s' ⟨11, by decide⟩ = BitVec.allOnes 64 ∧ mem s' = mem s

/-- the operations emitted -/
inductive EOp where
  | w (o : WOp)
  | enter (n : Nat)
  | leave
  | top (d : Reg)
  | call (d : Int)
  | enterC (n : Nat)
  | leaveC (n : Nat)
  | exit
  deriving Repr

namespace Target
variable (T : Target)

def encO : EOp → List (BitVec 32)
  | .w o => T.wenc o
  | .enter n => T.encE n
  | .leave => T.encL
  | .top d => T.encT d
  | .call d => T.encCall d
  | .enterC n => T.encEC n
  | .leaveC n => T.encLC n
  | .exit => T.encX

/-- the words of a list of operations -/
def words : List EOp → List (BitVec 32)
  | [] => []
  | o :: os => T.encO o ++ words os

theorem words_append : ∀ (a b : List EOp), T.words (a ++ b) = T.words a ++ T.words b
  | [], _ => rfl
  | o :: os, b => by
    show T.encO o ++ T.words (os ++ b) = (T.encO o ++ T.words os) ++ T.words b
    rw [words_append os b, List.append_assoc]

theorem words_cons (o : EOp) (os : List EOp) : T.words (o :: os) = T.encO o ++ T.words os := rfl

theorem words_nil : T.words [] = [] := rfl

end Target
end Proven.Ir
