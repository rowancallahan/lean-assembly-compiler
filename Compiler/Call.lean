/- The interface, extended for function calls (`MachineC`): a stack of frames addressed by the frame
register, jump-and-link, and return through the link register.

`MachineF` (`Frame.lean`) is unchanged; `MachineC extends MachineF` adds four operations `COp` (encoding
`encC`), a weaker frame relation `keepC` (everything but the abstract registers, the PC, the memory, the
frame register AND the link register `ra` is unchanged: it holds across calls) and ONE law per operation.

The stack: the frame register `fr` points at the current frame; cell 0 (`fr`) holds the saved return
address, slot `j` is the 8 bytes at `fr + 8 (j + 1)` (as in `Frame.lean`: `ldS` / `stS`).  A callee with
`n` slots has its frame directly below: `[fr - 8 (n + 1), fr)`.

Pure Lean (core only). -/
import Compiler.Frame

namespace Proven.Mach

inductive COp where
  /-- jump `d` words (signed, from the start of this op) and set the link register to the next op -/
  | call (d : Int)
  /-- open a frame of `n` slots below the current one: `fr := fr - 8 (n + 1)`, cell 0 := `ra` -/
  | enterC (n : Nat)
  /-- close it: `ra := cell 0`, `fr := fr + 8 (n + 1)` -/
  | leaveC (n : Nat)
  /-- outgoing argument: the 8 bytes at `fr - 8 m` := `v` (slot `n - m` of a callee with `n` slots) -/
  | stA (m : Nat) (v : Reg)

/-- an abstract operation of the call interface -/
inductive YOp where
  | x (o : XOp)
  | c (o : COp)

structure MachineC extends MachineF where
  encC : COp → List (BitVec 32)
  /-- `keepF` without the link register -/
  keepC : S → S → Prop
  /-- call distances (in words) the target supports -/
  callOK : Int → Prop
  /-- word length of `call` (independent of the distance) -/
  lenCall : Nat
  len_call : ∀ d, (encC (.call d)).length = lenCall
  keepC_of_keepF : ∀ {s s' : S}, keepF s s' → keepC s s'
  keepC_trans : ∀ {s₁ s₂ s₃ : S}, keepC s₁ s₂ → keepC s₂ s₃ → keepC s₁ s₃
  keepF_of_keepC : ∀ {s s' : S}, keepC s s' → ra s' = ra s → keepF s s'
  /-- a word-aligned address is a valid return address -/
  retOK_al : ∀ v : BitVec 64, v.toNat % 4 = 0 → retOK v
  law_call : ∀ {d : Int} {s : S} {pc : BitVec 64}, callOK d → toBase.At s pc (encC (.call d)) →
    runsTo s fun s' => ok s' ∧ keepC s s' ∧ pcIs s' (pc + BitVec.ofInt 64 (4 * d)) ∧
      ra s' = next pc lenCall ∧ fr s' = fr s ∧ toBase.Same s s' ∧ mem s' = mem s
  law_enterC : ∀ {n : Nat} {s : S} {pc : BitVec 64}, n ≤ maxSlots → toBase.At s pc (encC (.enterC n)) →
    8 * (n + 1) ≤ (fr s).toNat → toBase.inRAM ((fr s).toNat - 8 * (n + 1)) 8 → (fr s).toNat % 8 = 0 →
    runsTo s fun s' => ok s' ∧ keepC s s' ∧ pcIs s' (next pc (encC (.enterC n)).length) ∧
      fr s' = BitVec.ofNat 64 ((fr s).toNat - 8 * (n + 1)) ∧ toBase.Same s s' ∧
      mem s' = (mem s).wr ((fr s).toNat - 8 * (n + 1)) (le8 (ra s))
  law_leaveC : ∀ {n : Nat} {s : S} {pc : BitVec 64} {w : BitVec 64}, n ≤ maxSlots →
    toBase.At s pc (encC (.leaveC n)) → toBase.inRAM (fr s).toNat (8 * (n + 1)) → (fr s).toNat % 8 = 0 →
    bytes (mem s) (fr s).toNat 8 = (le8 w).map some →
    runsTo s fun s' => ok s' ∧ keepC s s' ∧ pcIs s' (next pc (encC (.leaveC n)).length) ∧ ra s' = w ∧
      fr s' = BitVec.ofNat 64 ((fr s).toNat + 8 * (n + 1)) ∧ toBase.Same s s' ∧ mem s' = mem s
  law_stA : ∀ {m : Nat} {v : Reg} {s : S} {pc : BitVec 64}, v.val = 0 → 1 ≤ m → m ≤ maxSlots →
    toBase.At s pc (encC (.stA m v)) → 8 * m ≤ (fr s).toNat → toBase.inRAM ((fr s).toNat - 8 * m) 8 →
    (fr s).toNat % 8 = 0 →
    runsTo s fun s' => toBase.Done s s' (next pc (encC (.stA m v)).length) ∧ toBase.Same s s' ∧
      mem s' = (mem s).wr ((fr s).toNat - 8 * m) (le8 (get s v))

namespace MachineC
variable (M : MachineC)

def encY : YOp → List (BitVec 32)
  | .x o => M.encF o
  | .c o => M.encC o

/-- the target words of a program with calls -/
def codeC : List YOp → List (BitVec 32)
  | [] => []
  | o :: os => M.encY o ++ codeC os

theorem codeC_append : ∀ (a b : List YOp), M.codeC (a ++ b) = M.codeC a ++ M.codeC b
  | [], _ => rfl
  | o :: os, b => by
    show M.encY o ++ M.codeC (os ++ b) = (M.encY o ++ M.codeC os) ++ M.codeC b
    rw [codeC_append os b, List.append_assoc]

theorem codeC_one (o : YOp) : M.codeC [o] = M.encY o := List.append_nil _

theorem codeC_cons (o : YOp) (os : List YOp) : M.codeC (o :: os) = M.encY o ++ M.codeC os := rfl

/-- call-free abstract code embeds with the same words -/
theorem codeC_map (os : List XOp) : M.codeC (os.map .x) = M.codeF os := by
  induction os with
  | nil => rfl
  | cons o os ih => show M.encF o ++ M.codeC (os.map .x) = M.encF o ++ M.codeF os; rw [ih]

/-- the target of a call from word `a` to word `o` of the same code block -/
theorem next_call (cb : BitVec 64) (a o : Nat) :
    next cb a + BitVec.ofInt 64 (4 * ((o : Int) - (a : Int))) = next cb o := by
  unfold next
  have e : BitVec.ofNat 64 (4 * o) = BitVec.ofNat 64 (4 * a) + BitVec.ofInt 64 (4 * ((o : Int) - (a : Int))) := by
    rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
    congr 1; omega
  rw [e, BitVec.add_assoc]

end MachineC
end Proven.Mach
