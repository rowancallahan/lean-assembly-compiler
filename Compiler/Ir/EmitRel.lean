/- The relation between an IR state (memory and registers of the one frame) and a machine state, and how it
survives register-only operations and the three kinds of stores (frame slot, cell, output byte). -/
import Compiler.Ir.EmitCtx

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

theorem ofNat_toNat' {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- values that may sit in registers and cells: words, the byte blocks' bases, pointers into existing blocks -/
def Valid (bl : List (Nat × Nat × Bool)) : Val → Prop
  | .w _ => True
  | .p 0 o => o = 0
  | .p 1 o => o = 0
  | .p (k + 2) o => ∃ a sz, bl[k]? = some (a, sz, true) ∧ o ≤ sz

theorem Valid.ext {bl : List (Nat × Nat × Bool)} (X : List (Nat × Nat × Bool)) :
    ∀ {v : Val}, Valid bl v → Valid (bl ++ X) v
  | .w _, _ => trivial
  | .p 0 _, h => h
  | .p 1 _, h => h
  | .p (k + 2) _, ⟨a, sz, e, ho⟩ => ⟨a, sz, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 e).1, e], ho⟩

namespace Ctx
variable {T : Target} (C : Ctx T)

theorem repr_ext (X : List (Nat × Nat × Bool)) {bl : List (Nat × Nat × Bool)} :
    ∀ {v : Val}, Valid bl v → C.repr (bl ++ X) v = C.repr bl v
  | .w _, _ => rfl
  | .p 0 _, _ => rfl
  | .p 1 _, _ => rfl
  | .p (k + 2) _, ⟨a, sz, e, _⟩ => by
    simp only [repr]; rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 e).1]

/-- the IR memory's own invariant (no block freed) -/
structure MemOK (m : Mem) : Prop where
  inp : m.inp = C.input
  blks : ∀ (k a sz : Nat) (lv : Bool), m.blks[k]? = some (a, sz, lv) → a + sz ≤ m.cells.length ∧ lv = true
  cv : ∀ (g : Nat) (v : Val), m.cells[g]? = some (some v) → Valid m.blks v

/-- **the relation** of an IR memory and the registers of the current frame to a machine state -/
structure MR (m : Mem) (regs : Nat → Val) (s : T.S) : Prop where
  ok : T.ok s
  keep : T.keepC C.s0 s
  fr : T.fr s = BitVec.ofNat 64 C.F0
  rlim : T.get s RLim = BitVec.ofNat 64 C.F0
  rin : T.get s RIn = BitVec.ofNat 64 C.inA
  rhp : T.get s RHp = BitVec.ofNat 64 (C.wb + 8 * m.cells.length)
  cap : C.wb + 8 * m.cells.length ≤ C.F0
  /-- the frame, then the stub's two cells, below the top of the work block -/
  fit : C.F0 + 8 * (C.nS + 1) + 16 ≤ C.T0
  fal : C.F0 % 8 = 0
  nsl : C.nS ≤ T.maxSlots
  saved : bytes (T.mem s) C.F0 8 = (le8 C.sv).map some
  /-- the stub's cell with the caller's return address -/
  stub : bytes (T.mem s) (C.T0 - 16) 8 = (le8 (T.ra C.s0)).map some
  /-- nothing above the frame changes -/
  above : ∀ x, C.F0 + 8 * (C.nS + 1) ≤ x → x < C.T0 → T.mem s x = C.hm x
  slots : ∀ j, j < C.nS → bytes (T.mem s) (C.F0 + 8 * (j + 1)) 8 = (le8 (C.repr m.blks (regs j))).map some
  cells : ∀ g v, m.cells[g]? = some (some v) →
    bytes (T.mem s) (C.wb + 8 * g) 8 = (le8 (C.repr m.blks v)).map some
  out : ∀ i b, m.out[i]? = some (some b) → T.mem s (C.outA + i) = some b.toBitVec
  outL : m.out.length ≤ C.outL
  unch : C.Unch s
  valid : ∀ j, Valid m.blks (regs j)
  mok : C.MemOK m

variable {C}

theorem T0_le (C : Ctx T) : C.T0 ≤ C.wb + C.wl := by
  unfold T0; have := Nat.div_mul_le_self C.wl 8; omega

theorem T0_al (C : Ctx T) : C.T0 % 8 = 0 := by
  unfold T0; have := C.wal; have : C.wl / 8 * 8 % 8 = 0 := Nat.mul_mod_left _ _; omega

theorem MR.F0_lt {m : Mem} {regs : Nat → Val} {s : T.S} (h : C.MR m regs s) :
    C.F0 + 8 * (C.nS + 1) ≤ C.wb + C.wl := by
  have := h.fit; have := C.T0_le; omega

theorem MR.F0_al {m : Mem} {regs : Nat → Val} {s : T.S} (h : C.MR m regs s) : C.F0 % 8 = 0 := h.fal

theorem MR.hi {m : Mem} {regs : Nat → Val} {s : T.S} (_h : C.MR m regs s) : C.wb + C.wl < 2 ^ 64 :=
  Nat.lt_of_le_of_lt C.w_lt T.ramHi_lt

/-- a slot: in the work block, above the cells, aligned -/
theorem MR.slot {m : Mem} {regs : Nat → Val} {s : T.S} (h : C.MR m regs s) {j : Nat} (hj : j < C.nS) :
    (T.fr s).toNat + 8 * (j + 1) = C.F0 + 8 * (j + 1) ∧ T.inRAM (C.F0 + 8 * (j + 1)) 8 ∧
      (C.F0 + 8 * (j + 1)) % 8 = 0 ∧ C.wb + 8 * m.cells.length ≤ C.F0 ∧ C.F0 + 8 * (j + 1) + 8 ≤ C.wb + C.wl := by
  have h1 := h.F0_lt; have h2 := h.F0_al; have h3 := h.cap; have h4 := h.hi; have h5 := C.wR
  rw [h.fr, ofNat_toNat' (by omega)]
  refine ⟨rfl, ⟨by have := h5.1; omega, by have := h5.2; omega⟩, by omega, h3, by omega⟩

/-- register-only operations keep the relation -/
theorem MR.regs {m : Mem} {regs : Nat → Val} {s s' : T.S} (h : C.MR m regs s) (hok : T.ok s')
    (hk : T.keep s s') (hm : T.mem s' = T.mem s) (h10 : T.get s' RLim = T.get s RLim)
    (h11 : T.get s' RIn = T.get s RIn) (h13 : T.get s' RHp = T.get s RHp) : C.MR m regs s' where
  ok := hok
  keep := T.keepC_trans h.keep (T.keepC_of_keepF (T.keepF_of_keep hk))
  fr := by rw [T.keep_fr hk]; exact h.fr
  rlim := by rw [h10]; exact h.rlim
  rin := by rw [h11]; exact h.rin
  rhp := by rw [h13]; exact h.rhp
  cap := h.cap
  fit := h.fit
  fal := h.fal
  nsl := h.nsl
  saved := by rw [hm]; exact h.saved
  stub := by rw [hm]; exact h.stub
  above x h1 h2 := by rw [hm]; exact h.above x h1 h2
  slots j hj := by rw [hm]; exact h.slots j hj
  cells g v hg := by rw [hm]; exact h.cells g v hg
  out i b hi := by rw [hm]; exact h.out i b hi
  outL := h.outL
  unch a h1 h2 := by rw [hm]; exact h.unch a h1 h2
  valid := h.valid
  mok := h.mok

theorem MR.Set1 {m : Mem} {regs : Nat → Val} {s s' : T.S} {d : Reg} {v : BitVec 64} (h : C.MR m regs s)
    (hok : T.ok s') (hk : T.keep s s') (hm : T.mem s' = T.mem s) (hs : T.Set1 s s' d v) (hd : d.val < 10) :
    C.MR m regs s' :=
  h.regs hok hk hm (by rw [hs]; exact if_neg fun e => by rw [← e] at hd; exact absurd hd (by decide))
    (by rw [hs]; exact if_neg fun e => by rw [← e] at hd; exact absurd hd (by decide))
    (by rw [hs]; exact if_neg fun e => by rw [← e] at hd; exact absurd hd (by decide))

theorem MR.Same {m : Mem} {regs : Nat → Val} {s s' : T.S} (h : C.MR m regs s)
    (hok : T.ok s') (hk : T.keep s s') (hm : T.mem s' = T.mem s) (hs : T.Same s s') : C.MR m regs s' :=
  h.regs hok hk hm (hs _) (hs _) (hs _)

/-- an address in the work block -/
theorem unch_work {s s' : T.S} {a : Nat} {l : List (BitVec 8)} (h : C.Unch s) (hm : T.mem s' = (T.mem s).wr a l)
    (h1 : C.wb ≤ a) (h2 : a + l.length ≤ C.wb + C.wl) : C.Unch s' := by
  intro x hx1 hx2
  rw [hm, Proven.Mach.Mem.wr_out (by omega)]
  exact h x hx1 hx2

/-- **a store to slot `d`** -/
theorem MR.stS {m : Mem} {regs : Nat → Val} {s s' : T.S} {d : Nat} {v : Val} (h : C.MR m regs s)
    (hd : d < C.nS) (hok : T.ok s') (hk : T.keep s s') (hs : T.Same s s')
    (hm : T.mem s' = (T.mem s).wr (C.F0 + 8 * (d + 1)) (le8 (C.repr m.blks v))) (hv : Valid m.blks v) :
    C.MR m (upd regs d v) s' := by
  obtain ⟨-, -, hal, hcap, htop⟩ := h.slot hd
  have hl : (le8 (C.repr m.blks v)).length = 8 := length_le8 _
  have hO := C.dOW; have hoL := h.outL; unfold disjoint at hO; dsimp only at hO
  exact {
    ok := hok
    keep := T.keepC_trans h.keep (T.keepC_of_keepF (T.keepF_of_keep hk))
    fr := by rw [T.keep_fr hk]; exact h.fr
    rlim := by rw [hs]; exact h.rlim
    rin := by rw [hs]; exact h.rin
    rhp := by rw [hs]; exact h.rhp
    cap := h.cap
    fit := h.fit
    fal := h.fal
    nsl := h.nsl
    saved := by rw [hm, bytes_wr_out (.inl (by omega))]; exact h.saved
    stub := by rw [hm, bytes_wr_out (.inr (by have := h.fit; have := h.cap; simp only [length_le8]; omega))]; exact h.stub
    above := fun x h1 h2 => by have := h.fit; have := h.cap; rw [hm, Proven.Mach.Mem.wr_out (by simp only [length_le8]; omega)]; exact h.above x h1 h2
    slots := fun j hj => by
      rw [hm]
      by_cases e : j = d
      · subst e
        have e := @bytes_wr_self (T.mem s) (C.F0 + 8 * (j + 1)) (le8 (C.repr m.blks v))
        rw [hl] at e; rw [e]; simp [upd]
      · rw [bytes_wr_out (by rw [hl]; omega)]
        simpa [upd, e] using h.slots j hj
    cells := fun g w hg => by
      have : g < m.cells.length := (List.getElem?_eq_some_iff.1 hg).1
      rw [hm, bytes_wr_out (.inl (by omega))]; exact h.cells g w hg
    out := fun i b hi => by
      have : i < m.out.length := (List.getElem?_eq_some_iff.1 hi).1
      rw [hm, Proven.Mach.Mem.wr_out (by rw [hl]; omega)]; exact h.out i b hi
    outL := h.outL
    unch := unch_work h.unch hm (by omega) (by rw [hl]; omega)
    valid := fun j => by
      by_cases e : j = d
      · subst e; simpa [upd] using hv
      · simpa [upd, e] using h.valid j
    mok := h.mok }

theorem setOut_getElem? (out : List (Option UInt8)) (i j : Nat) (v : UInt8) :
    (setOut out i v)[j]? = if j = i then some (some v) else if j < out.length then out[j]? else
      if j < i then some none else none := by
  unfold setOut
  split
  · by_cases e : j = i
    · subst e; simp [*]
    · simp only [e, if_false]; rw [List.getElem?_set_ne (Ne.symm e)]
      split
      · rfl
      · rw [List.getElem?_eq_none (by omega)]; split <;> first | rfl | omega
  · simp only [List.getElem?_append, List.getElem?_replicate, List.length_append, List.length_replicate]
    by_cases e : j = i
    · subst e; simp
      rw [if_neg (by omega), show j - (out.length + (j - out.length)) = 0 by omega]; rfl
    · simp only [e, if_false]
      split <;> split <;> (try split) <;> (try split) <;> simp_all <;> omega

theorem setOut_get {out : List (Option UInt8)} {i j : Nat} {v b : UInt8}
    (h : (setOut out i v)[j]? = some (some b)) : (j = i ∧ b = v) ∨ (j ≠ i ∧ out[j]? = some (some b)) := by
  rw [setOut_getElem?] at h
  by_cases e : j = i
  · rw [if_pos e] at h; cases h; exact .inl ⟨e, rfl⟩
  · rw [if_neg e] at h
    split at h
    · exact .inr ⟨e, h⟩
    · split at h <;> cases h

theorem setOut_length_lt (out : List (Option UInt8)) (i : Nat) (v : UInt8) : i < (setOut out i v).length := by
  unfold setOut; split
  · simpa
  · simp; omega

/-- **a store to cell `g0`** -/
theorem MR.stCell {m : Mem} {regs : Nat → Val} {s s' : T.S} {g0 : Nat} {w : Val} (h : C.MR m regs s)
    (hg0 : g0 < m.cells.length) (hok : T.ok s') (hk : T.keep s s') (hs : T.Same s s')
    (hm : T.mem s' = (T.mem s).wr (C.wb + 8 * g0) (le8 (C.repr m.blks w))) (hw : Valid m.blks w) :
    C.MR { m with cells := m.cells.set g0 (some w) } regs s' := by
  have hl : (le8 (C.repr m.blks w)).length = 8 := length_le8 _
  have hO := C.dOW; have hoL := h.outL; unfold disjoint at hO; dsimp only at hO
  have hcap := h.cap; have hF := h.F0_lt
  exact {
    ok := hok
    keep := T.keepC_trans h.keep (T.keepC_of_keepF (T.keepF_of_keep hk))
    fr := by rw [T.keep_fr hk]; exact h.fr
    rlim := by rw [hs]; exact h.rlim
    rin := by rw [hs]; exact h.rin
    rhp := by rw [hs]; simpa using h.rhp
    cap := by simpa using h.cap
    fit := h.fit
    fal := h.fal
    nsl := h.nsl
    saved := by rw [hm, bytes_wr_out (.inr (by rw [hl]; omega))]; exact h.saved
    stub := by rw [hm, bytes_wr_out (.inr (by have := h.fit; have := h.cap; simp only [length_le8]; omega))]; exact h.stub
    above := fun x h1 h2 => by have := h.fit; have := h.cap; rw [hm, Proven.Mach.Mem.wr_out (by simp only [length_le8]; omega)]; exact h.above x h1 h2
    slots := fun j hj => by
      rw [hm, bytes_wr_out (.inr (by rw [hl]; omega))]; exact h.slots j hj
    cells := fun g u hg => by
      rw [hm]
      by_cases e : g = g0
      · subst e
        rw [List.getElem?_set_self hg0] at hg; cases hg
        have e := @bytes_wr_self (T.mem s) (C.wb + 8 * g) (le8 (C.repr m.blks w))
        rw [hl] at e; exact e
      · rw [List.getElem?_set_ne (Ne.symm e)] at hg
        have : g < m.cells.length := (List.getElem?_eq_some_iff.1 hg).1
        rw [bytes_wr_out (by rw [hl]; omega)]; exact h.cells g u hg
    out := fun i b hi => by
      have : i < m.out.length := (List.getElem?_eq_some_iff.1 hi).1
      rw [hm, Proven.Mach.Mem.wr_out (by rw [hl]; omega)]; exact h.out i b hi
    outL := h.outL
    unch := unch_work h.unch hm (by omega) (by rw [hl]; omega)
    valid := h.valid
    mok := ⟨h.mok.inp, fun k a sz lv e => by simpa using h.mok.blks k a sz lv e, fun g u hg => by
      by_cases e : g = g0
      · subst e; rw [List.getElem?_set_self hg0] at hg; cases hg; exact hw
      · rw [List.getElem?_set_ne (Ne.symm e)] at hg; exact h.mok.cv g u hg⟩ }

/-- **a store to output byte `i`** -/
theorem MR.stOut {m : Mem} {regs : Nat → Val} {s s' : T.S} {i : Nat} {y : BitVec 8} (h : C.MR m regs s)
    (hi : (setOut m.out i (UInt8.ofBitVec y)).length ≤ C.outL) (hok : T.ok s') (hk : T.keep s s') (hs : T.Same s s')
    (hm : T.mem s' = (T.mem s).upd (C.outA + i) y) :
    C.MR { m with out := setOut m.out i (UInt8.ofBitVec y) } regs s' := by
  have hO := C.dOW; unfold disjoint at hO; dsimp only at hO
  have hi' := setOut_length_lt m.out i (UInt8.ofBitVec y)
  have hcap := h.cap; have hF := h.F0_lt
  exact {
    ok := hok
    keep := T.keepC_trans h.keep (T.keepC_of_keepF (T.keepF_of_keep hk))
    fr := by rw [T.keep_fr hk]; exact h.fr
    rlim := by rw [hs]; exact h.rlim
    rin := by rw [hs]; exact h.rin
    rhp := by rw [hs]; exact h.rhp
    cap := h.cap
    fit := h.fit
    fal := h.fal
    nsl := h.nsl
    saved := by rw [hm, bytes_upd_out fun j hj => by omega]; exact h.saved
    stub := by have := h.fit; have := h.cap; have := C.T0_le; rw [hm, bytes_upd_out fun j hj => by omega]; exact h.stub
    above := fun x h1 h2 => by have := h.fit; have := h.cap; have := C.T0_le; rw [hm]; unfold Proven.Mach.Mem.upd; rw [if_neg (by omega)]; exact h.above x h1 h2
    slots := fun j hj => by
      have := h.slot hj
      rw [hm, bytes_upd_out fun j hj => by omega]; exact h.slots j hj
    cells := fun g u hg => by
      have : g < m.cells.length := (List.getElem?_eq_some_iff.1 hg).1
      rw [hm, bytes_upd_out fun j hj => by omega]; exact h.cells g u hg
    out := fun j b hj => by
      rw [hm]; unfold Proven.Mach.Mem.upd
      rcases setOut_get hj with ⟨rfl, rfl⟩ | ⟨ne, hj'⟩
      · rw [if_pos rfl]
      · rw [if_neg (by omega)]; exact h.out j b hj'
    outL := hi
    unch := fun x h1 h2 => by
      rw [hm]; unfold Proven.Mach.Mem.upd; rw [if_neg (by omega)]; exact h.unch x h1 h2
    valid := h.valid
    mok := ⟨h.mok.inp, h.mok.blks, h.mok.cv⟩ }

theorem getElem?_append_none {l : List (Option Val)} {c g : Nat} {u : Val}
    (h : (l ++ List.replicate c none)[g]? = some (some u)) : g < l.length ∧ l[g]? = some (some u) := by
  by_cases hg : g < l.length
  · rw [List.getElem?_append_left hg] at h; exact ⟨hg, h⟩
  · rw [List.getElem?_append_right (by omega), List.getElem?_replicate] at h
    split at h <;> cases h

/-- **an allocation**: the new block's base into slot `d`, the heap pointer moved -/
theorem MR.alloc {m : Mem} {regs : Nat → Val} {s s' : T.S} {d c : Nat} (h : C.MR m regs s) (hd : d < C.nS)
    (hcap : C.wb + 8 * (m.cells.length + c) ≤ C.F0) (hok : T.ok s') (hk : T.keep s s')
    (h10 : T.get s' RLim = T.get s RLim) (h11 : T.get s' RIn = T.get s RIn)
    (h13 : T.get s' RHp = BitVec.ofNat 64 (C.wb + 8 * (m.cells.length + c)))
    (hm : T.mem s' = (T.mem s).wr (C.F0 + 8 * (d + 1)) (le8 (BitVec.ofNat 64 (C.wb + 8 * m.cells.length)))) :
    C.MR { m with cells := m.cells ++ List.replicate c none, blks := m.blks ++ [(m.cells.length, c, true)] }
      (upd regs d (.p (m.blks.length + 2) 0)) s' := by
  obtain ⟨-, -, hal, -, htop⟩ := h.slot hd
  have hl : ∀ x : BitVec 64, (le8 x).length = 8 := length_le8
  have hO := C.dOW; have hoL := h.outL; unfold disjoint at hO; dsimp only at hO
  have hcap0 := h.cap
  have hnew : C.repr (m.blks ++ [(m.cells.length, c, true)]) (.p (m.blks.length + 2) 0) =
      BitVec.ofNat 64 (C.wb + 8 * m.cells.length) := by
    simp [repr]
  have hmok : C.MemOK ⟨m.inp, m.out, m.cells ++ List.replicate c none, m.blks ++ [(m.cells.length, c, true)]⟩ := by
    refine ⟨h.mok.inp, fun k a sz lv e => ?_, fun g u hg => ?_⟩
    · by_cases hk : k < m.blks.length
      · rw [List.getElem?_append_left hk] at e
        have := h.mok.blks k a sz lv e
        simp only [List.length_append, List.length_replicate]; exact ⟨by omega, this.2⟩
      · rw [List.getElem?_append_right (by omega)] at e
        have : k - m.blks.length = 0 := by
          by_cases hne : k - m.blks.length = 0
          · exact hne
          · rw [List.getElem?_eq_none (by simp; omega)] at e; cases e
        rw [this] at e; simp at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        simp
    · obtain ⟨-, hg''⟩ := getElem?_append_none hg
      exact Valid.ext _ (h.mok.cv g u hg'')
  exact {
    ok := hok
    keep := T.keepC_trans h.keep (T.keepC_of_keepF (T.keepF_of_keep hk))
    fr := by rw [T.keep_fr hk]; exact h.fr
    rlim := by rw [h10]; exact h.rlim
    rin := by rw [h11]; exact h.rin
    rhp := by rw [h13]; simp
    cap := by simpa using hcap
    fit := h.fit
    fal := h.fal
    nsl := h.nsl
    saved := by rw [hm, bytes_wr_out (.inl (by omega))]; exact h.saved
    stub := by rw [hm, bytes_wr_out (.inr (by have := h.fit; have := h.cap; simp only [length_le8]; omega))]; exact h.stub
    above := fun x h1 h2 => by have := h.fit; have := h.cap; rw [hm, Proven.Mach.Mem.wr_out (by simp only [length_le8]; omega)]; exact h.above x h1 h2
    slots := fun j hj => by
      rw [hm]
      by_cases e : j = d
      · subst e
        have e := @bytes_wr_self (T.mem s) (C.F0 + 8 * (j + 1)) (le8 (BitVec.ofNat 64 (C.wb + 8 * m.cells.length)))
        rw [hl] at e; rw [e]; simp only [upd]; rw [if_pos trivial, hnew]
      · rw [bytes_wr_out (by rw [hl]; omega)]
        simp only [upd, if_neg e]
        rw [C.repr_ext _ (h.valid j)]; exact h.slots j hj
    cells := fun g u hg => by
      obtain ⟨hg', hg''⟩ := getElem?_append_none hg
      rw [hm, bytes_wr_out (.inl (by omega)), C.repr_ext _ (h.mok.cv g u hg'')]
      exact h.cells g u hg''
    out := fun i b hi => by
      have : i < m.out.length := (List.getElem?_eq_some_iff.1 hi).1
      rw [hm, Proven.Mach.Mem.wr_out (by rw [hl]; omega)]; exact h.out i b hi
    outL := h.outL
    unch := unch_work h.unch hm (by omega) (by rw [hl]; omega)
    valid := fun j => by
      by_cases e : j = d
      · subst e; simp only [upd]; rw [if_pos trivial]; exact ⟨m.cells.length, c, by simp, Nat.zero_le _⟩
      · simp only [upd, if_neg e]; exact Valid.ext _ (h.valid j)
    mok := hmok }

end Ctx
end Proven.Ir

namespace Proven.Ir
open Proven.Mach Proven.Top.Alloc
namespace Ctx
variable {T : Target} {C : Ctx T}

/-- **a store of zero to the slot after the last**: the frame grows by one slot -/
theorem MR.grow {m : Mem} {regs : Nat → Val} {s s' : T.S} (h : C.MR m regs s) (hz : regs C.nS = .w 0)
    (hfit : C.F0 + 8 * (C.nS + 2) + 16 ≤ C.T0) (hn : C.nS + 1 ≤ T.maxSlots)
    (hok : T.ok s') (hk : T.keep s s') (hs : T.Same s s')
    (hm : T.mem s' = (T.mem s).wr (C.F0 + 8 * (C.nS + 1)) (le8 0)) :
    (C.fa (C.nS + 1) C.F0 C.sv C.hm).MR m regs s' := by
  have hl : (le8 (0 : BitVec 64)).length = 8 := length_le8 _
  have hO := C.dOW; have hoL := h.outL; unfold disjoint at hO; dsimp only at hO
  have hT := C.T0_le; have hcap := h.cap
  exact {
    ok := hok
    keep := T.keepC_trans h.keep (T.keepC_of_keepF (T.keepF_of_keep hk))
    fr := by rw [T.keep_fr hk]; exact h.fr
    rlim := by rw [hs]; exact h.rlim
    rin := by rw [hs]; exact h.rin
    rhp := by rw [hs]; exact h.rhp
    cap := h.cap
    fit := by show C.F0 + 8 * (C.nS + 1 + 1) + 16 ≤ C.T0; omega
    fal := h.fal
    nsl := hn
    saved := by
      change bytes (T.mem s') C.F0 8 = (le8 C.sv).map some
      rw [hm, bytes_wr_out (.inl (by omega))]; exact h.saved
    stub := by
      change bytes (T.mem s') (C.T0 - 16) 8 = _
      rw [hm, bytes_wr_out (.inr (by rw [hl]; omega))]; exact h.stub
    above := fun x h1 h2 => by
      change C.F0 + 8 * (C.nS + 1 + 1) ≤ x at h1
      rw [hm, Proven.Mach.Mem.wr_out (by rw [hl]; omega)]; exact h.above x (by omega) h2
    slots := fun j hj => by
      change j < C.nS + 1 at hj
      change bytes (T.mem s') (C.F0 + 8 * (j + 1)) 8 = _
      rw [hm]
      by_cases e : j = C.nS
      · subst e
        have e := @bytes_wr_self (T.mem s) (C.F0 + 8 * (C.nS + 1)) (le8 0)
        rw [hl] at e; rw [e, hz]; rfl
      · rw [bytes_wr_out (by rw [hl]; omega)]; exact h.slots j (by omega)
    cells := fun g v hg => by
      dsimp only [Ctx.fa]
      have : g < m.cells.length := (List.getElem?_eq_some_iff.1 hg).1
      rw [hm, bytes_wr_out (.inl (by omega))]; exact h.cells g v hg
    out := fun i b hi => by
      dsimp only [Ctx.fa]
      have : i < m.out.length := (List.getElem?_eq_some_iff.1 hi).1
      have := C.T0_le
      rw [hm, Proven.Mach.Mem.wr_out (by rw [hl]; omega)]; exact h.out i b hi
    outL := h.outL
    unch := by
      have := C.T0_le
      exact unch_work (C := C) h.unch hm (by omega) (by rw [hl]; omega)
    valid := h.valid
    mok := ⟨h.mok.inp, h.mok.blks, h.mok.cv⟩ }

end Ctx
end Proven.Ir
