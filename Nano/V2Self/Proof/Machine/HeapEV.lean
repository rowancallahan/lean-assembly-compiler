/- The heap side of the fragment contracts, shared definitions.  `Hp` = heap image (top + known cells);
`HRel hb s H` ties it to the machine: t5 = top, hb ≤ top ≤ t6, 8-aligned, and every known cell [hb, top) equals memory
(`HRel_stack`, `hread`).  `InvOKH`, the closing-fragment shapes `Fin1`/`Fin2`/`Fin3`, and the heap prim semantics
`bsizeF`, `bgetF`, `bpushF`, `bsetF`, `bnewS` (`bufInfo`).  Run theorems: EVSFin.lean, EVSLeaf.lean. -/
import Nano.V2Self.Proof.Machine.Templates
import Nano.V2Self.Proof.Machine.Heap
namespace Templates
open CallProbe

structure Hp where
  top : Nat
  m : Nat → Option UInt64

/-- memory agrees with the heap image on its known cells; t5 is the heap top -/
def HI (hb : Nat) (H : Hp) (s : St) : Prop :=
  (s.x 30).toNat = H.top ∧ ∀ a v, hb ≤ a → a < H.top → H.m a = some v → s.m a = v

def HRel (hb : Nat) (s : St) (H : Hp) : Prop :=
  16 ≤ hb ∧ hb ≤ H.top ∧ H.top ≤ (s.x 31).toNat ∧ H.top % 8 = 0 ∧ HI hb H s

/-- `Inv` reads only s0, x28, x29, the code base and memory outside [hb, frame top) (the code base never changes
along a run: `Star.b`; the machine bridge's global invariant bounds it for return addresses) -/
def InvOKH (hb p : Nat) (Inv : St → Prop) : Prop :=
  ∀ s s' : St, Inv s → s'.x 8 = s.x 8 → s'.x 28 = s.x 28 → s'.x 29 = s.x 29 → s'.b = s.b → s'.ly = s.ly →
    (∀ a, ¬ (hb ≤ a ∧ a < (s.x 8).toNat + 8 * p + 16) → s'.m a = s.m a) → Inv s'

/-- the closing fragment of a two-operand step (pops two words, pushes the result over the new top) -/
def Fin2 (C : List J) (q lu : Nat) (Inv : St → Prop) (hb : Nat)
    (F : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) : Prop :=
  ∀ (s2 : St) (H2 : Hp) (v : UInt64) (H3 : Hp), Inv s2 → s2.x 0 = 0 → HRel hb s2 H2 → (s2.x 31).toNat + 16 < 2 ^ 63 →
    F (s2.m ((s2.x 31).toNat + 8)) (s2.m (s2.x 31).toNat) (s2.x 31).toNat H2 = some (v, H3) →
    ∃ s3 : St, Star C (q, s2) (q + lu, s3) ∧ (s3.x 31).toNat = (s2.x 31).toNat + 8 ∧ s3.m ((s2.x 31).toNat + 8) = v ∧
      HRel hb s3 H3 ∧ (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → r ≠ 31 → s3.x r = s2.x r) ∧
      ∀ a, a ≠ (s2.x 31).toNat + 8 → ¬ (hb ≤ a ∧ a < H3.top) → s3.m a = s2.m a

/-- the closing fragment of a one-operand step (rewrites the top word in place) -/
def Fin1 (C : List J) (q lu : Nat) (Inv : St → Prop) (hb : Nat)
    (F : UInt64 → Nat → Hp → Option (UInt64 × Hp)) : Prop :=
  ∀ (s1 : St) (H1 : Hp) (v : UInt64) (H2 : Hp), Inv s1 → s1.x 0 = 0 → HRel hb s1 H1 →
    F (s1.m (s1.x 31).toNat) (s1.x 31).toNat H1 = some (v, H2) →
    ∃ s3 : St, Star C (q, s1) (q + lu, s3) ∧ s3.x 31 = s1.x 31 ∧ s3.m (s1.x 31).toNat = v ∧
      HRel hb s3 H2 ∧ (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → s3.x r = s1.x r) ∧
      ∀ a, a ≠ (s1.x 31).toNat → ¬ (hb ≤ a ∧ a < H2.top) → s3.m a = s1.m a

/-- the closing fragment of a three-operand step (buf below, index, value on top; result over the buffer's cell) -/
def Fin3 (C : List J) (q lu : Nat) (Inv : St → Prop) (hb : Nat)
    (F : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp)) : Prop :=
  ∀ (s3 : St) (H3 : Hp) (v : UInt64) (H4 : Hp), Inv s3 → s3.x 0 = 0 → HRel hb s3 H3 → (s3.x 31).toNat + 24 < 2 ^ 62 →
    F (s3.m ((s3.x 31).toNat + 16)) (s3.m ((s3.x 31).toNat + 8)) (s3.m (s3.x 31).toNat) (s3.x 31).toNat H3 = some (v, H4) →
    ∃ s4 : St, Star C (q, s3) (q + lu, s4) ∧ (s4.x 31).toNat = (s3.x 31).toNat + 16 ∧
      s4.m ((s3.x 31).toNat + 16) = v ∧ HRel hb s4 H4 ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → r ≠ 31 → s4.x r = s3.x r) ∧
      ∀ a, a ≠ (s3.x 31).toNat + 16 → ¬ (hb ≤ a ∧ a < H4.top) → s4.m a = s3.m a

/-! ## the heap prims as closing fragments -/

/-- a known heap cell -/
def hread (hb : Nat) (H : Hp) (a : Nat) : Option UInt64 := if hb ≤ a ∧ a < H.top then H.m a else none

theorem hread_mem {hb : Nat} {s : St} {H : Hp} {a : Nat} {v : UInt64} (hR : HRel hb s H) (h : hread hb H a = some v) :
    s.m a = v := by
  unfold hread at h; split at h
  · rename_i hc; exact hR.2.2.2.2.2 a v hc.1 hc.2 h
  · simp at h

theorem hread_lt {hb : Nat} {H : Hp} {a : Nat} {v : UInt64} (h : hread hb H a = some v) : hb ≤ a ∧ a < H.top := by
  unfold hread at h; split at h
  · assumption
  · simp at h

/-- only stack-side changes (not in the heap, t5 kept, t6 above the heap) keep the heap relation -/
theorem HRel_stack {hb : Nat} {s s' : St} {H : Hp} (hR : HRel hb s H) (e30 : s'.x 30 = s.x 30)
    (h31 : H.top ≤ (s'.x 31).toNat) (hm : ∀ a, hb ≤ a → a < H.top → s'.m a = s.m a) : HRel hb s' H := by
  obtain ⟨b16, b1, t1, al, hx, hc⟩ := hR
  refine ⟨b16, b1, h31, al, ?_, ?_⟩
  · rw [e30]; exact hx
  · intro a v h1 h2 hv; rw [hm a h1 h2]; exact hc a v h1 h2 hv

/-- BSIZE: the buffer's length word -/
def bsizeF (hb : Nat) : UInt64 → Nat → Hp → Option (UInt64 × Hp) :=
  fun b _ H => (hread hb H b.toNat).map fun len => (len, H)

/-- BGET: word `idx` of buffer `buf` (0 when out of range) -/
def bgetF (hb : Nat) : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp) :=
  fun buf idx _ H => (hread hb H buf.toNat).bind fun len =>
    if idx.toNat < len.toNat then
      (if buf.toNat + 16 + 8 * idx.toNat < 2 ^ 62 then (hread hb H (buf.toNat + 16 + 8 * idx.toNat)).map fun w => (w, H) else none)
    else some (0, H)

/-- a well-formed buffer in the heap image: (len, cap) -/
def bufInfo (hb : Nat) (H : Hp) (b : UInt64) : Option (UInt64 × UInt64) :=
  if hb ≤ b.toNat ∧ b.toNat % 8 = 0 then
    (hread hb H b.toNat).bind fun len => (hread hb H (b.toNat + 8)).bind fun cap =>
      if len.toNat ≤ cap.toNat ∧ b.toNat + 16 + 8 * cap.toNat ≤ H.top then some (len, cap) else none
  else none

theorem bufInfo_spec {hb : Nat} {H : Hp} {b len cap : UInt64} (h : bufInfo hb H b = some (len, cap)) :
    hb ≤ b.toNat ∧ hread hb H b.toNat = some len ∧ hread hb H (b.toNat + 8) = some cap ∧ len.toNat ≤ cap.toNat ∧
      b.toNat + 16 + 8 * cap.toNat ≤ H.top := by
  unfold bufInfo at h
  split at h
  · rename_i hc
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, c, hcc, h⟩ := h
    split at h
    · rename_i hh; simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨hc.1, hl, hcc, hh.1, hh.2⟩
    · simp at h
  · simp at h

/-- BPUSH / PUT: append `v` to the buffer `buf` (cap exit = failure here); the buffer address stays -/
def bpushF (hb : Nat) : UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp) :=
  fun buf v _ H => (bufInfo hb H buf).bind fun lc =>
    if lc.1.toNat < lc.2.toNat ∧ buf.toNat + 16 + 8 * lc.1.toNat < 2 ^ 62 then
      some (buf, ⟨H.top, fun a => if a = buf.toNat then some (lc.1 + 1)
        else if a = buf.toNat + 16 + 8 * lc.1.toNat then some v else H.m a⟩)
    else none

/-- BSET: write `v` at index `idx` when in range (out of range is a no-op); result is the buffer -/
def bsetF (hb : Nat) : UInt64 → UInt64 → UInt64 → Nat → Hp → Option (UInt64 × Hp) :=
  fun buf idx v _ H => (bufInfo hb H buf).bind fun lc =>
    if idx.toNat < lc.1.toNat then
      (if buf.toNat + 16 + 8 * idx.toNat < 2 ^ 62 then
        some (buf, ⟨H.top, fun a => if a = buf.toNat + 16 + 8 * idx.toNat then some v else H.m a⟩) else none)
    else some (buf, H)

/-- BNEW κ: allocate a zeroed header (len 0, cap κ) at the heap top; the new heap image knows only the header -/
def bnewS (κ : Nat) : (Nat → UInt64) → Nat → Hp → Option (UInt64 × Hp) :=
  fun _ sp H => if H.top + 8 * (κ + 2) + 8 ≤ sp ∧ sp < 2 ^ 62 ∧ κ < 2 ^ 40 then
    some (UInt64.ofNat H.top, ⟨H.top + 8 * (κ + 2), fun a =>
      if a = H.top then some 0 else if a = H.top + 8 then some (UInt64.ofNat κ) else if a < H.top then H.m a else none⟩)
  else none

end Templates
