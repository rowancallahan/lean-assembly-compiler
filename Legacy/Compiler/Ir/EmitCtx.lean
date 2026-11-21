/- The context of emission correctness: the start state and its blocks (`Ctx`), where code sits (`InW`), the
value of an IR value in a machine register (`repr`), and the relation `MR` between an IR memory with registers
and a machine state (frame slots, cells, output bytes, the heap pointer, nothing changed outside the output and
work blocks).  Then one lemma per kind of target operation that advances the code position. -/
import Legacy.Compiler.Ir.Emit
import Legacy.Compiler.Ir.SemFacts

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

/-- the words `ws` sit at word `q` of `W` -/
def InW (W : List (BitVec 32)) (q : Nat) (ws : List (BitVec 32)) : Prop :=
  ∃ pre post, W = pre ++ ws ++ post ∧ pre.length = q

theorem InW.left {W : List (BitVec 32)} {q : Nat} {a b : List (BitVec 32)} (h : InW W q (a ++ b)) : InW W q a :=
  let ⟨pre, post, e, hl⟩ := h
  ⟨pre, b ++ post, by rw [e]; simp only [List.append_assoc], hl⟩

theorem InW.right {W : List (BitVec 32)} {q : Nat} {a b : List (BitVec 32)} (h : InW W q (a ++ b)) :
    InW W (q + a.length) b :=
  let ⟨pre, post, e, hl⟩ := h
  ⟨pre ++ a, post, by rw [e]; simp only [List.append_assoc], by rw [List.length_append, hl]⟩

/-- the start of a run: code, input, output, work block -/
structure Ctx (T : Target) where
  W : List (BitVec 32)
  pc0 : BitVec 64
  s0 : T.S
  input : List UInt8
  inA : Nat
  outA : Nat
  outL : Nat
  wb : Nat
  wl : Nat
  /-- the current frame: its slots, its base, the word in its cell 0 -/
  nS : Nat
  F0 : Nat
  sv : BitVec 64
  /-- the memory above the current frame (the callers' frames and the stub), as it must stay -/
  hm : Nat → Option (BitVec 8)
  code0 : T.codeAt s0 pc0 W
  codeOK : T.codeOK pc0 W.length
  lo : 0 < T.ramLo
  inR : T.inRAM inA input.length
  outR : T.inRAM outA outL
  wR : T.inRAM wb wl
  wal : wb % 8 = 0
  dCO : disjoint ⟨pc0.toNat, 4 * W.length⟩ ⟨outA, outL⟩
  dCW : disjoint ⟨pc0.toNat, 4 * W.length⟩ ⟨wb, wl⟩
  dIO : disjoint ⟨inA, input.length⟩ ⟨outA, outL⟩
  dIW : disjoint ⟨inA, input.length⟩ ⟨wb, wl⟩
  dOW : disjoint ⟨outA, outL⟩ ⟨wb, wl⟩
  inb : ∀ i (h : i < input.length), T.mem s0 (inA + i) = some input[i].toBitVec
  wr : ∀ (s : T.S) (a : Nat), (outA ≤ a ∧ a < outA + outL) ∨ (wb ≤ a ∧ a < wb + wl) → T.writable s a
  retOK : T.retOK (T.ra s0)
  /-- the top of the work block, 8-aligned -/
  htop : T.top s0 = wb + wl / 8 * 8

namespace Ctx
variable {T : Target} (C : Ctx T)

/-- the aligned top of the work block -/
def T0 : Nat := C.wb + C.wl / 8 * 8

/-- the same run with another current frame -/
def fa (n fb : Nat) (v : BitVec 64) (M : Nat → Option (BitVec 8)) : Ctx T := { C with nS := n, F0 := fb, sv := v, hm := M }

/-- nothing changed outside the output and work blocks -/
def Unch (s : T.S) : Prop :=
  ∀ a, (a < C.outA ∨ C.outA + C.outL ≤ a) → (a < C.wb ∨ C.wb + C.wl ≤ a) → T.mem s a = T.mem C.s0 a

/-- at word `q` of the code -/
def AtQ (s : T.S) (q : Nat) : Prop := T.ok s ∧ T.pcIs s (next C.pc0 q) ∧ C.Unch s

/-- the machine value of an IR value (for the block table `bl`) -/
def repr (bl : List (Nat × Nat × Bool)) : Val → BitVec 64
  | .w x => x
  | .p 0 o => BitVec.ofNat 64 (C.inA + 8 * o)
  | .p 1 o => BitVec.ofNat 64 (C.outA + 8 * o)
  | .p (k + 2) o => match bl[k]? with
    | some (a, _, _) => BitVec.ofNat 64 (C.wb + 8 * (a + o))
    | none => 0

theorem ramHi_lt : T.ramHi < 2 ^ 64 := T.ramHi_lt

theorem in_lt : C.inA + C.input.length ≤ T.ramHi := C.inR.2
theorem out_lt : C.outA + C.outL ≤ T.ramHi := C.outR.2
theorem w_lt : C.wb + C.wl ≤ T.ramHi := C.wR.2

theorem codeAt_of {s : T.S} (h : C.Unch s) : T.codeAt s C.pc0 C.W := by
  intro i hi
  refine T.instrAt_frame (fun j hj => ?_) (C.code0 i hi)
  have e := T.toCore.pc_toNat C.codeOK (a := i) (by omega)
  simp only [next] at e
  rw [e]
  have h1 := C.dCO; have h2 := C.dCW
  unfold disjoint at h1 h2; dsimp only at h1 h2
  exact h _ (by omega) (by omega)

theorem at_of {s : T.S} {q : Nat} {ws : List (BitVec 32)} (hA : C.AtQ s q) (hin : InW C.W q ws) :
    T.At s (next C.pc0 q) ws := by
  obtain ⟨pre, post, e, hl⟩ := hin
  have hc := C.codeAt_of hA.2.2
  rw [e, List.append_assoc] at hc
  have h1 := (T.toCore.codeAt_append).1 hc
  have h2 := (T.toCore.codeAt_append).1 h1.2
  have ho := C.codeOK
  rw [e, List.append_assoc, List.length_append, List.length_append] at ho
  have o1 := (T.toCore.codeOK_append ho).2
  have o2 := (T.toCore.codeOK_append o1).1
  rw [hl] at h2 o2
  exact ⟨hA.1, hA.2.1, h2.1, o2⟩

/-- one target operation: from word `q` to the next, with the law's effect `Q` -/
theorem op {s : T.S} {q : Nat} {o : EOp} {rest : List (BitVec 32)} {Q : T.S → Prop}
    (hA : C.AtQ s q) (hin : InW C.W q (T.encO o ++ rest))
    (law : T.At s (next C.pc0 q) (T.encO o) →
      T.runsTo s fun s' => T.Done s s' (next (next C.pc0 q) (T.encO o).length) ∧ T.mem s' = T.mem s ∧ Q s') :
    T.runsTo s fun s' => C.AtQ s' (q + (T.encO o).length) ∧ T.keep s s' ∧ T.mem s' = T.mem s ∧ Q s' := by
  refine T.toCore.runsTo_mono (law (C.at_of hA hin.left)) fun s' ⟨d, hm, hq⟩ => ?_
  refine ⟨⟨d.ok, ?_, fun a h1 h2 => by rw [hm]; exact hA.2.2 a h1 h2⟩, d.keep, hm, hq⟩
  have := d.hpc
  rwa [next_add] at this

/-- one target operation that may store (the caller shows nothing changed outside output and work) -/
theorem opW {s : T.S} {q : Nat} {o : EOp} {rest : List (BitVec 32)} {Q : T.S → Prop}
    (hA : C.AtQ s q) (hin : InW C.W q (T.encO o ++ rest))
    (law : T.At s (next C.pc0 q) (T.encO o) →
      T.runsTo s fun s' => T.Done s s' (next (next C.pc0 q) (T.encO o).length) ∧ Q s')
    (hU : ∀ s', Q s' → C.Unch s') :
    T.runsTo s fun s' => C.AtQ s' (q + (T.encO o).length) ∧ T.keep s s' ∧ Q s' := by
  refine T.toCore.runsTo_mono (law (C.at_of hA hin.left)) fun s' ⟨d, hq⟩ => ?_
  refine ⟨⟨d.ok, ?_, hU s' hq⟩, d.keep, hq⟩
  have := d.hpc
  rwa [next_add] at this

end Ctx

theorem InW.cons {W : List (BitVec 32)} {q : Nat} {T : Target} {o : EOp} {os : List EOp} {rest : List (BitVec 32)}
    (h : InW W q (T.words (o :: os) ++ rest)) : InW W q (T.encO o ++ (T.words os ++ rest)) := by
  rwa [T.words_cons, List.append_assoc] at h

theorem InW.next {W : List (BitVec 32)} {q : Nat} {T : Target} {o : EOp} {os : List EOp} {rest : List (BitVec 32)}
    (h : InW W q (T.words (o :: os) ++ rest)) : InW W (q + (T.encO o).length) (T.words os ++ rest) :=
  h.cons.right

end Proven.Ir
