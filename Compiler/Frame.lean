/- The interface, extended for spill slots and 8-byte memory (`MachineF`): a stack frame with `N` 8-byte
slots over a target-held frame register, slot loads/stores, and 8-byte loads/stores on blocks.

`Machine` (`Iface.lean`) is unchanged; `MachineF extends Machine` adds the new operations `FOp` (with their
own encoding `encX`), the frame register `fr`, a weaker frame relation `keepF` (everything but the abstract
registers, the PC, the memory AND the frame register is unchanged: it holds while a frame is open), and one
law per new operation.  The abstract programs are lists of `XOp` (an old `AOp` or a new `FOp`).

Pure Lean (core only); compiles unchanged under Lean 4.29.0 and 4.34.1. -/
import Compiler.Mem
import Compiler.Exp

namespace Proven.Mach

/-- the new abstract operations -/
inductive FOp where
  /-- open a frame of `n` 8-byte slots (slots zeroed; the old frame register saved in cell 0) -/
  | enter (n : Nat)
  /-- close the frame: restore the frame register from cell 0 -/
  | leave
  /-- `d := slot j` (the 8 bytes at `fr + 8 (j + 1)`) -/
  | ldS (d : Reg) (j : Nat)
  /-- `slot j := v` -/
  | stS (j : Nat) (v : Reg)
  /-- `d := the 8 bytes at a` (little-endian; `a` 8-aligned) -/
  | ld (d a : Reg)
  /-- `the 8 bytes at a := v` -/
  | sd (v a : Reg)

/-- an abstract operation of the extended interface -/
inductive XOp where
  | a (o : AOp)
  | f (o : FOp)

/-- the little-endian bytes of a 64-bit word (the same definition as `Proven.le8`) -/
def le8 (x : BitVec 64) : List (BitVec 8) := (List.range 8).map fun i => x.extractLsb' (8 * i) 8

/-- write the bytes `l` at `a, a + 1, ...` -/
def Mem.wr : Mem → Nat → List (BitVec 8) → Mem
  | m, _, [] => m
  | m, a, v :: l => Mem.wr (m.upd a v) (a + 1) l

/-- **The extended interface.** -/
structure MachineF extends Machine where
  encX : FOp → List (BitVec 32)
  /-- the frame register (RISC-V `gp`); not an abstract register -/
  fr : S → BitVec 64
  /-- `keep` without the frame register -/
  keepF : S → S → Prop
  /-- the base of a frame of `n` slots opened in state `s` (RISC-V: `alignDown(sp, 8) - 8 (n + 1)`) -/
  frameAt : S → Nat → Nat
  /-- the target's conditions for `enter n` in `s` (RISC-V: frame in RAM, at most 16 slots) -/
  enterOK : S → Nat → Prop
  /-- slot indices the target can address -/
  maxSlots : Nat
  keepF_of_keep : ∀ {s s' : S}, keep s s' → keepF s s'
  keepF_trans : ∀ {s₁ s₂ s₃ : S}, keepF s₁ s₂ → keepF s₂ s₃ → keepF s₁ s₃
  keep_fr : ∀ {s s' : S}, keep s s' → fr s' = fr s
  keep_of_keepF : ∀ {s s' : S}, keepF s s' → fr s' = fr s → keep s s'
  keepF_ra : ∀ {s s' : S}, keepF s s' → ra s' = ra s
  /-- what the middle may assume of an opened frame -/
  enterOK_frame : ∀ {s : S} {n : Nat}, enterOK s n →
    n ≤ maxSlots ∧ toBase.inRAM (frameAt s n) (8 * (n + 1)) ∧ frameAt s n % 8 = 0
  law_enter : ∀ {n : Nat} {s : S} {pc : BitVec 64}, enterOK s n → toBase.At s pc (encX (.enter n)) →
    disjoint ⟨pc.toNat, 4 * (encX (.enter n)).length⟩ ⟨frameAt s n, 8 * (n + 1)⟩ →
    runsTo s fun s' => ok s' ∧ keepF s s' ∧ pcIs s' (next pc (encX (.enter n)).length) ∧
      fr s' = BitVec.ofNat 64 (frameAt s n) ∧ (∀ r : Reg, 7 ≤ r.val → get s' r = get s r) ∧
      Out [⟨frameAt s n, 8 * (n + 1)⟩] (mem s) (mem s') ∧
      bytes (mem s') (frameAt s n) 8 = (le8 (fr s)).map some ∧
      ∀ j, j < n → bytes (mem s') (frameAt s n + 8 * (j + 1)) 8 = (le8 0).map some
  law_leave : ∀ {s : S} {pc : BitVec 64} {w : BitVec 64}, toBase.At s pc (encX .leave) →
    toBase.inRAM (fr s).toNat 8 → (fr s).toNat % 8 = 0 → bytes (mem s) (fr s).toNat 8 = (le8 w).map some →
    runsTo s fun s' => ok s' ∧ keepF s s' ∧ pcIs s' (next pc (encX .leave).length) ∧ fr s' = w ∧
      toBase.Same s s' ∧ mem s' = mem s
  law_ldS : ∀ {d : Reg} {j : Nat} {s : S} {pc : BitVec 64} {v : BitVec 64}, d.val < 7 → j < maxSlots →
    toBase.At s pc (encX (.ldS d j)) → toBase.inRAM ((fr s).toNat + 8 * (j + 1)) 8 →
    ((fr s).toNat + 8 * (j + 1)) % 8 = 0 → bytes (mem s) ((fr s).toNat + 8 * (j + 1)) 8 = (le8 v).map some →
    runsTo s fun s' => toBase.Done s s' (next pc (encX (.ldS d j)).length) ∧ toBase.Set1 s s' d v ∧ mem s' = mem s
  law_stS : ∀ {j : Nat} {v : Reg} {s : S} {pc : BitVec 64}, v.val = 0 → j < maxSlots →
    toBase.At s pc (encX (.stS j v)) → toBase.inRAM ((fr s).toNat + 8 * (j + 1)) 8 →
    ((fr s).toNat + 8 * (j + 1)) % 8 = 0 →
    runsTo s fun s' => toBase.Done s s' (next pc (encX (.stS j v)).length) ∧ toBase.Same s s' ∧
      mem s' = (mem s).wr ((fr s).toNat + 8 * (j + 1)) (le8 (get s v))
  law_ld : ∀ {d a : Reg} {s : S} {pc : BitVec 64} {v : BitVec 64}, d.val = 0 → a.val = 0 →
    toBase.At s pc (encX (.ld d a)) → toBase.inRAM (get s a).toNat 8 → (get s a).toNat % 8 = 0 →
    bytes (mem s) (get s a).toNat 8 = (le8 v).map some →
    runsTo s fun s' => toBase.Done s s' (next pc (encX (.ld d a)).length) ∧ toBase.Set1 s s' d v ∧ mem s' = mem s
  law_sd : ∀ {v a : Reg} {s : S} {pc : BitVec 64}, v.val = 1 → a.val = 0 →
    toBase.At s pc (encX (.sd v a)) → toBase.inRAM (get s a).toNat 8 → (get s a).toNat % 8 = 0 →
    runsTo s fun s' => toBase.Done s s' (next pc (encX (.sd v a)).length) ∧ toBase.Same s s' ∧
      mem s' = (mem s).wr (get s a).toNat (le8 (get s v))

/-! ## Memory writes -/

theorem Mem.wr_out : ∀ {m : Mem} {a : Nat} {l : List (BitVec 8)} {x : Nat}, (x < a ∨ a + l.length ≤ x) →
    Mem.wr m a l x = m x
  | _, _, [], _, _ => rfl
  | m, a, v :: l, x, h => by
    simp only [List.length_cons] at h
    show Mem.wr (m.upd a v) (a + 1) l x = m x
    rw [Mem.wr_out (l := l) (by omega)]
    unfold Mem.upd; rw [ite_neg (by omega)]

theorem Mem.wr_in : ∀ {m : Mem} {a : Nat} {l : List (BitVec 8)} {i : Nat} (hi : i < l.length),
    Mem.wr m a l (a + i) = some l[i]
  | _, _, [], _, hi => absurd hi (Nat.not_lt_zero _)
  | m, a, v :: l, 0, _ => by
    show Mem.wr (m.upd a v) (a + 1) l (a + 0) = some v
    rw [Mem.wr_out (m := m.upd a v) (a := a + 1) (l := l) (x := a + 0) (.inl (by omega))]
    unfold Mem.upd; rw [ite_pos (by omega)]
  | m, a, v :: l, i + 1, hi => by
    have hi' : i < l.length := by simp only [List.length_cons] at hi; omega
    show Mem.wr (m.upd a v) (a + 1) l (a + (i + 1)) = some l[i]
    rw [show a + (i + 1) = a + 1 + i by omega]
    exact Mem.wr_in hi'

theorem bytes_getElem : ∀ {m : Mem} {a n i : Nat} (h : i < (bytes m a n).length), (bytes m a n)[i] = m (a + i)
  | _, _, 0, _, h => absurd h (by rw [length_bytes]; exact Nat.not_lt_zero _)
  | _, _, _ + 1, 0, _ => rfl
  | m, a, n + 1, i + 1, h => by
    have h' : i < (bytes m (a + 1) n).length := by rw [length_bytes]; rw [length_bytes] at h; omega
    show (bytes m (a + 1) n)[i]'h' = _
    rw [bytes_getElem, show a + 1 + i = a + (i + 1) by omega]

theorem bytes_wr_self {m : Mem} {a : Nat} {l : List (BitVec 8)} : bytes (Mem.wr m a l) a l.length = l.map some := by
  apply List.ext_getElem (by rw [length_bytes, List.length_map])
  intro i h1 h2
  rw [List.getElem_map, bytes_getElem]
  rw [length_bytes] at h1
  exact Mem.wr_in h1

theorem bytes_wr_out {m : Mem} {a n x : Nat} {l : List (BitVec 8)} (h : a + n ≤ x ∨ x + l.length ≤ a) :
    bytes (Mem.wr m x l) a n = bytes m a n :=
  bytes_congr fun j hj => Mem.wr_out (by omega)

theorem length_le8 (x : BitVec 64) : (le8 x).length = 8 := by
  unfold le8; rw [List.length_map, List.length_range]

namespace MachineF
variable (M : MachineF)

/-- the words of an extended operation -/
def encF : XOp → List (BitVec 32)
  | .a o => M.enc o
  | .f o => M.encX o

/-- the target words of an extended abstract program -/
def codeF : List XOp → List (BitVec 32)
  | [] => []
  | o :: os => M.encF o ++ codeF os

theorem codeF_append : ∀ (a b : List XOp), M.codeF (a ++ b) = M.codeF a ++ M.codeF b
  | [], _ => rfl
  | o :: os, b => by
    show M.encF o ++ M.codeF (os ++ b) = (M.encF o ++ M.codeF os) ++ M.codeF b
    rw [codeF_append os b, List.append_assoc]

theorem codeF_one (o : XOp) : M.codeF [o] = M.encF o := List.append_nil _

/-- old abstract code embeds with the same words -/
theorem codeF_map (os : List AOp) : M.codeF (os.map .a) = M.code os := by
  induction os with
  | nil => rfl
  | cons o os ih => show M.enc o ++ M.codeF (os.map .a) = M.enc o ++ M.code os; rw [ih]

/-- the frame-aware `Done`: `keepF` instead of `keep` -/
structure DoneF (s s' : M.S) (pc' : BitVec 64) : Prop where
  ok : M.ok s'
  keepF : M.keepF s s'
  hpc : M.pcIs s' pc'

theorem DoneF.of {s s' : M.S} {pc'} (d : M.Done s s' pc') : M.DoneF s s' pc' := ⟨d.ok, M.keepF_of_keep d.keep, d.hpc⟩

theorem DoneF.trans {s₁ s₂ s₃ : M.S} {p₂ p₃} (d₁ : M.DoneF s₁ s₂ p₂) (d₂ : M.DoneF s₂ s₃ p₃) : M.DoneF s₁ s₃ p₃ :=
  ⟨d₂.ok, M.keepF_trans d₁.keepF d₂.keepF, d₂.hpc⟩

/-- the frame register is back: `DoneF` is a `Done` -/
theorem DoneF.done {s s' : M.S} {pc'} (d : M.DoneF s s' pc') (h : M.fr s' = M.fr s) : M.Done s s' pc' :=
  ⟨d.ok, M.keep_of_keepF d.keepF h, d.hpc⟩

end MachineF
end Proven.Mach
