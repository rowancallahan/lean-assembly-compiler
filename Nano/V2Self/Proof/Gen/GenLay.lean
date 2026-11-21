/- Groundwork for the template layer over a target encoder (cleanup step 9, layer 2; not yet used by the chain).
"The cells Gen appends are the target encoding of the J templates", with the target's encoder and layout as
parameters, so that it also covers non-uniform (variable-length) targets.  J offsets stay in J-instruction units; a
target encodes a jump from its NATIVE displacement, computed from a layout `pos : J index → cell index` (prefix sums
of `size`).  RISC-V: size 1, pos = id, enc = [encG ·].  `Exact T` ties the encoders of GenE.lean (class `Em`) to the
templates (so far: CONST and the jump word); `rv_exact` is the RISC-V instance. -/
import Nano.V2Self.Proof.Machine.NdCG
namespace GenEmit
open GenRef CallProbe

/-- a target encoder -/
structure Tgt where
  /-- cells of one J instruction; for a jump it must not depend on the offset -/
  size : J → Nat
  /-- the cells, given the native displacement of the instruction's jump target (0 if it has none) -/
  enc : Int → J → List UInt64

structure Tgt.OK (T : Tgt) : Prop where
  enc_len : ∀ d j, (T.enc d j).length = T.size j

/-- the J-unit offset of a control transfer -/
def joff : J → Option Int
  | .jal _ o | .bgeu _ _ o | .beq _ _ o | .bltu _ _ o | .bne _ _ o => some o
  | _ => none

/-- the native displacement of instruction j placed at J index q -/
def disp (pos : Nat → Nat) (q : Nat) (j : J) : Int :=
  match joff j with
  | some o => (pos ((q : Int) + o).toNat : Int) - (pos q : Int)
  | none => 0

/-- the cells of the J list l placed at J index q -/
def encL (T : Tgt) (pos : Nat → Nat) : Nat → List J → List UInt64
  | _, [] => []
  | q, j :: l => T.enc (disp pos q j) j ++ encL T pos (q + 1) l

/-- pos is the layout of the program C -/
def GLay (T : Tgt) (pos : Nat → Nat) (C : List J) : Prop :=
  pos 0 = 0 ∧ ∀ j (h : j < C.length), pos (j + 1) = pos j + T.size C[j]

/-- the fact that replaces `h + c.length` arithmetic: a template's end cell is its end J index's cell -/
theorem lay_at {T : Tgt} {pos : Nat → Nat} {C : List J} (hT : T.OK) (hG : GLay T pos C) :
    ∀ (l : List J) (q : Nat), At C q l → pos (q + l.length) = pos q + (encL T pos q l).length
  | [], q, _ => by simp [encL]
  | j :: l, q, h => by
    have h0 : C[q]? = some j := by simpa using h 0 (by simp)
    obtain ⟨hq, e⟩ := List.getElem?_eq_some_iff.mp h0
    have ih := lay_at hT hG l (q + 1) (fun i hi => by
      have := h (i + 1) (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    have e1 := hG.2 q hq
    rw [e] at e1
    simp only [encL, List.length_cons, List.length_append, hT.enc_len]
    rw [show q + (l.length + 1) = q + 1 + l.length by omega, ih, e1]; omega

/-- the per-target tie between the encoders `Em` and the templates -/
structure Exact [Em] (T : Tgt) : Prop where
  const : ∀ (C : List J) (pos : Nat → Nat) (q : Nat) (v : UInt64) (o : Buf), GLay T pos C →
    q + (constT 1 q v).length ≤ C.length → 1 ≤ C.length → o.length = pos q → o.length + 21 < 2 ^ 32 →
    Em.g21 (Em.g23 o 5 v) = o ++ encL T pos q (constT 1 q v)
  jmp : ∀ (C : List J) (pos : Nat → Nat) (q n d : Nat), GLay T pos C → q ≤ C.length → n ≤ C.length →
    pos q < 2 ^ 32 → pos n < 2 ^ 32 →
    [Em.g13 d.toUInt64 (pos q).toUInt64 (pos n).toUInt64] =
      T.enc ((pos n : Int) - (pos q : Int)) (.jal d ((n : Int) - (q : Int)))

/-- the generic CONST matching step: the reference relation's opaque `em` list is the template's encoding -/
theorem em_const [Em] {T : Tgt} (hX : Exact T) {C pos q} (v : UInt64) (hG : GLay T pos C)
    (hq : q + (constT 1 q v).length ≤ C.length) (hC : 1 ≤ C.length) (hh : pos q + 21 < 2 ^ 32) :
    em (fun o => Em.g21 (Em.g23 o 5 v)) (pos q) = encL T pos q (constT 1 q v) := by
  unfold em
  show List.drop (pos q) (Em.g21 (Em.g23 (List.replicate (pos q) 0) 5 v)) = _
  rw [hX.const C pos q v _ hG hq hC (by simp) (by simpa using hh)]
  simp

/-! ## the RISC-V instance -/

def rvT : Tgt := ⟨fun _ => 1, fun _ j => [encG j]⟩

theorem rvT_ok : rvT.OK := ⟨fun _ _ => rfl⟩

theorem encL_rv (pos : Nat → Nat) : ∀ (l : List J) (q : Nat), encL rvT pos q l = l.map encG
  | [], _ => rfl
  | j :: l, q => by
    show [encG j] ++ encL rvT pos (q + 1) l = _
    rw [encL_rv pos l (q + 1)]; rfl

theorem pos_rv {pos : Nat → Nat} {C : List J} (hG : GLay rvT pos C) : ∀ j, j ≤ C.length → pos j = j
  | 0, _ => hG.1
  | j + 1, h => by rw [hG.2 j (by omega), pos_rv hG j (by omega)]; rfl

theorem rv_exact : @Exact GenRef.rvEm rvT where
  const := fun C pos q v o hG hq _ ho hb => by
    rw [pos_rv hG q (by omega)] at ho
    rw [encL_rv]; subst ho
    exact CallProbe.const_exact o v (by omega)
  jmp := fun _ pos q n d hG hq hn hq2 hn2 => by
    rw [pos_rv hG q hq] at hq2 ⊢; rw [pos_rv hG n hn] at hn2 ⊢
    show [_root_.C.g13 _ _ _] = [encG _]
    rw [Templates.g13_enc d q n hq2 hn2]
end GenEmit
