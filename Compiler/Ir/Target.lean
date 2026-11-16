/- The target interface of the IR back end (`Testing/notes/IR_DESIGN.md` §2.5): the wide operations with a frame
(`WideF`: any registers, slots, 8-byte loads/stores, compare-and-branch both ways, jumps both ways, `enter`/`leave`)
plus the top of the work block (`top`, read by `getTop`), so the code can check that a frame fits before opening
it.  A new target is these laws only; emission and its correctness (`Compiler/Ir/Emit*.lean`) are proved once.

Pure Lean (core only). -/
import Compiler.Opt.BFn

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

/-- the operations emitted -/
inductive EOp where
  | w (o : WOp)
  | enter (n : Nat)
  | leave
  | top (d : Reg)
  deriving Repr

namespace Target
variable (T : Target)

def encO : EOp → List (BitVec 32)
  | .w o => T.wenc o
  | .enter n => T.encE n
  | .leave => T.encL
  | .top d => T.encT d

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
