/- Opus box E: the EXACT work bound of C's code.  `thr p x`: the least number of usable bytes (above the 16-byte
reserve) with which main does not run out of room at ANY admissible 8-aligned work position; `Msp p x` rounds
`16 + thr` up to the 8-byte granularity of the work block.  With it: room ⇒ below the bound (no hypothesis), and,
given `ShiftInv`, below the bound ⇒ room at every position.  `gen_implementsM`: Gen's code implements `Sem` with
space `Msp` (no hypothesis). -/
import Nano.V2Self.Proof.RunsShift
import Nano.V2Self.Proof.ParCapBnd
namespace NanoMain
open Templates ParSpec Classical

/-- the least `j ∈ [i, i + n]` with `P j` (or `i + n`) -/
noncomputable def lfind (P : Nat → Prop) (i : Nat) : Nat → Nat
  | 0 => i
  | n + 1 => if P i then i else lfind P (i + 1) n

theorem lfind_spec (P : Nat → Prop) : ∀ n i, P (i + n) → P (lfind P i n)
  | 0, i, h => by simpa [lfind] using h
  | n + 1, i, h => by
    unfold lfind; split
    · assumption
    · exact lfind_spec P n (i + 1) (by rwa [show i + 1 + n = i + (n + 1) by omega])

theorem lfind_min (P : Nat → Prop) : ∀ n i j, i ≤ j → j < lfind P i n → ¬ P j
  | 0, i, j, h1, h2 => by simp [lfind] at h2; omega
  | n + 1, i, j, h1, h2 => by
    unfold lfind at h2; split at h2
    · omega
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · assumption
      · exact lfind_min P n (i + 1) j h1 h2

/-- `u` usable bytes suffice at every admissible position -/
def GoodU (p : List DefA) (x : List UInt8) (u : Nat) : Prop :=
  ∀ (T : Buf) (hb : Nat), hb % 8 = 0 → 2 ^ 31 ≤ hb → hb + u ≤ 2 ^ 32 → RS p x T hb u ≠ .error .room

/-- the exact number of usable bytes main needs -/
noncomputable def thr (p : List DefA) (x : List UInt8) : Nat := lfind (GoodU p x) 0 (2 ^ 32)

/-- **the exact work bound** (bytes of the work block): out of memory iff the work length is below it -/
noncomputable def Msp (p : List DefA) (x : List UInt8) : Nat := (16 + thr p x + 7) / 8 * 8

theorem good_thr (p : List DefA) (x : List UInt8) : GoodU p x (thr p x) :=
  lfind_spec _ _ _ fun _ _ _ h1 h2 => by omega

theorem not_good {p : List DefA} {x : List UInt8} {u : Nat} (h : u < thr p x) : ¬ GoodU p x u :=
  lfind_min _ _ 0 u (Nat.zero_le _) h

/-- at least `thr` usable bytes: never out of room -/
theorem no_room {p : List DefA} {x : List UInt8} {T : Buf} {hb u : Nat} (h8 : hb % 8 = 0) (h31 : 2 ^ 31 ≤ hb)
    (h32 : hb + u ≤ 2 ^ 32) (hle : thr p x ≤ u) : RS p x T hb u ≠ .error .room := by
  have g := good_thr p x T hb h8 h31 (by omega)
  have e := semAtF_mo _ p (p.length - 1) [] (hb + thr p x) (hb + u) ⟨hb, fun _ => none⟩ (by omega)
    (by omega) g
  unfold RS at g ⊢; rw [e]; exact g

/-- out of room ⇒ fewer than `thr` usable bytes -/
theorem room_lt {p : List DefA} {x : List UInt8} {T : Buf} {hb u : Nat} (h8 : hb % 8 = 0) (h31 : 2 ^ 31 ≤ hb)
    (h32 : hb + u ≤ 2 ^ 32) (hr : RS p x T hb u = .error .room) : u < thr p x :=
  Nat.lt_of_not_le fun hle => no_room h8 h31 h32 hle hr

/-- fewer than `thr` usable bytes ⇒ out of room, at every admissible position (given `ShiftInv`) -/
theorem lt_room (HS : ShiftInv) {ts : List UInt64} {p : List DefA} (hp : ParsesProgram ts p)
    (hts : ts.length < 2 ^ 24) (hL : LinearK p) {x : List UInt8} (hx : x.length ≤ 2 ^ 20) {T : Buf} {hb u : Nat}
    (h8 : hb % 8 = 0) (h31 : 2 ^ 31 ≤ hb) (h32 : hb + u ≤ 2 ^ 32) (hlt : u < thr p x) :
    RS p x T hb u = .error .room := by
  have hn := not_good hlt
  simp only [GoodU, not_forall] at hn
  obtain ⟨T', hb', h8', h31', h32', hr⟩ := hn
  have hr' : RS p x T' hb' u = .error .room := Classical.not_not.1 hr
  have : RS p x T hb' u = .error .room := by
    unfold RS at hr' ⊢; rw [SimW.semAtF_pcT κC hb' _ _ T T' p]; exact hr'
  exact (HS ts p hp hts hL x hx T hb' hb u h8' h8 h31' h31 h32' h32).1 this

theorem Msp_ge (p : List DefA) (x : List UInt8) : 16 ≤ Msp p x := by unfold Msp; omega

/-- the semantic case split of `gen_implements` with the exact bound `Msp` -/
theorem gen_HDM {ts : List UInt64} {p : List DefA} (hp : ParsesProgram ts p) (hL : LinearK p) (x : List UInt8)
    (hx : x.length ≤ 2 ^ 20) (wb wl : Nat) (hw8 : wb % 8 = 0) (h31 : 2 ^ 31 ≤ wb) (h32 : wb + wl ≤ 2 ^ 32)
    (h16 : wb + 16 ≤ (wb + wl) / 8 * 8) : SimW.SemCases p (Msp p) x wb wl := by
  have e : (wb + wl) / 8 * 8 = wb + 16 + (wl / 8 * 8 - 16) := by omega
  obtain hc | hc | ⟨hc, hS⟩ := gen_all hp hL x hx [] (wb + 16) ((wb + wl) / 8 * 8) ⟨wb + 16, fun _ => none⟩
    (by show (wb + 16) % 8 = 0; omega) (Nat.le_refl _)
  · obtain ⟨a, l, H', e', -, hS⟩ := hc
    refine Or.inl ⟨_, hS, fun T => ⟨[a], H', ?_⟩⟩
    rw [SimW.semAt_pcT _ _ _ _ T [], ← oD_semAt]
    show toO (semAtF _ p _ [] _ _) = _
    rw [show (524288 : Nat) = κC from rfl, e']; rfl
  · refine Or.inr (Or.inr ⟨fun T => by rw [SimW.semAtF_pcT _ _ _ _ T []]; exact hc, ?_⟩)
    have hr : RS p x [] (wb + 16) (wl / 8 * 8 - 16) = .error .room := by unfold RS; rw [← e]; exact hc
    have := room_lt (by omega) (by omega) (by omega) hr
    unfold Msp; omega
  · exact Or.inr (Or.inl ⟨hS, fun T => by rw [SimW.semAtF_pcT _ _ _ _ T []]; exact hc⟩)

/-- **Gen's code implements `Sem` with the exact work bound** (no hypotheses beyond GenStage's) -/
theorem gen_implementsM (c : List UInt8) {ts : List UInt64} {p : List DefA} (hp : ParsesProgram ts p)
    (hts : ts.length < 2 ^ 24) (hL : LinearK p) (h : C.g41 c (serialize p) ≠ []) :
    ImplementsCW (C.g41 c (serialize p)) (Sem κC p) (fun x => max 16 (Msp p x)) := by
  obtain ⟨Ks, hO, hK2⟩ := hL
  exact SimW.gen_implements c hp Ks hO hK2 (ParSerLen.ser_lt hp hts) h
    (dbStage capStage c ts p hp hts ⟨Ks, hO, hK2⟩ h) (Msp p)
    (fun x hx wb wl h8 h31 h32 h16 => gen_HDM hp ⟨Ks, hO, hK2⟩ x hx wb wl h8 h31 h32 h16)

/-- **below the exact bound: the definite out-of-memory return** (given `ShiftInv`) -/
theorem gen_runs_oom (HS : ShiftInv) (c : List UInt8) {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p) (hts : ts.length < 2 ^ 24)
    (Ks : List (List Nat)) (hO : OwnSpec.progOk [] [] Ks p = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hXl : (serialize p).length < 2 ^ 31) (h : C.g41 c (serialize p) ≠ []) (hdb : ∀ d ∈ p, DB d)
    (x : List UInt8) (s : Proven.St) (entry ra : BitVec 64) (input output work : Proven.Region)
    (hxl : x.length ≤ 2 ^ 20) (hc : Proven.Cfg s) (hpc : s.regs.get? .PC = some entry) (he4 : entry.toNat % 4 = 0)
    (hB : Proven.bytesAt s entry.toNat (C.g41 c (serialize p)).length = (C.g41 c (serialize p)).map (some ·.toBitVec))
    (h10 : s.regs.get? .x10 = some (BitVec.ofNat 64 input.base))
    (h11 : s.regs.get? .x11 = some (BitVec.ofNat 64 x.length))
    (h12 : s.regs.get? .x12 = some (BitVec.ofNat 64 work.base))
    (h13 : s.regs.get? .x13 = some (BitVec.ofNat 64 output.base))
    (h2 : s.regs.get? .x2 = some (BitVec.ofNat 64 (work.base + work.len)))
    (h1 : s.regs.get? .x1 = some ra) (hra4 : ra.toNat % 4 = 0)
    (hin : Proven.bytesAt s input.base x.length = x.map (some ·.toBitVec)) (hil : input.len = x.length)
    (hout : ∀ y, Sem κC p x = .ok y → y.length ≤ output.len) (hw8 : work.base % 8 = 0)
    (hram : ∀ r ∈ [input, output, work, ⟨entry.toNat, (C.g41 c (serialize p)).length⟩], Proven.Region.inRAM r)
    (hdis : [input, output, work, ⟨entry.toNat, (C.g41 c (serialize p)).length⟩].Pairwise Proven.disjoint)
    (hMo : Proven.Mapped s output) (hMw : Proven.Mapped s work)
    (hlt : work.len < Msp p x) : Proven.runsTo s (SimW.OomOut s ra output work) := by
  have rW := hram work (by simp)
  simp only [Proven.Region.inRAM] at rW
  by_cases hsm : (work.base + work.len) / 8 * 8 < work.base + 16
  · exact SimW.gen_host_tinyX c hP Ks hO hK2 hXl h hdb x s entry ra input output work True hxl hc hpc he4 hB h10 h11 h12 h13 h2 h1 hra4 hin hil hout hw8 hram hdis hMo hMw hsm trivial (.error .stuck)
  have hL : LinearK p := ⟨Ks, hO, hK2⟩
  refine SimW.gen_host_oomX c hP Ks hO hK2 hXl h hdb x s entry ra input output work True hxl hc hpc he4 hB h10 h11 h12 h13 h2 h1 hra4 hin hil hout hw8 hram hdis hMo hMw (by omega) trivial fun T => ?_
  have e : (work.base + work.len) / 8 * 8 = work.base + 16 + (work.len / 8 * 8 - 16) := by omega
  have := lt_room HS hP hts hL hxl (T := T) (hb := work.base + 16) (u := work.len / 8 * 8 - 16) (by omega) (by omega)
    (by omega) (by unfold Msp at hlt; omega)
  unfold RS at this; rw [e]; exact this

/-- **at or above the exact bound: the normal return with the meaning's output** -/
theorem gen_runs_ok (c : List UInt8) {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p)
    (Ks : List (List Nat)) (hO : OwnSpec.progOk [] [] Ks p = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hXl : (serialize p).length < 2 ^ 31) (h : C.g41 c (serialize p) ≠ []) (hdb : ∀ d ∈ p, DB d)
    (x : List UInt8) (s : Proven.St) (entry ra : BitVec 64) (input output work : Proven.Region)
    (hxl : x.length ≤ 2 ^ 20) (hc : Proven.Cfg s) (hpc : s.regs.get? .PC = some entry) (he4 : entry.toNat % 4 = 0)
    (hB : Proven.bytesAt s entry.toNat (C.g41 c (serialize p)).length = (C.g41 c (serialize p)).map (some ·.toBitVec))
    (h10 : s.regs.get? .x10 = some (BitVec.ofNat 64 input.base))
    (h11 : s.regs.get? .x11 = some (BitVec.ofNat 64 x.length))
    (h12 : s.regs.get? .x12 = some (BitVec.ofNat 64 work.base))
    (h13 : s.regs.get? .x13 = some (BitVec.ofNat 64 output.base))
    (h2 : s.regs.get? .x2 = some (BitVec.ofNat 64 (work.base + work.len)))
    (h1 : s.regs.get? .x1 = some ra) (hra4 : ra.toNat % 4 = 0)
    (hin : Proven.bytesAt s input.base x.length = x.map (some ·.toBitVec)) (hil : input.len = x.length)
    (hout : ∀ y, Sem κC p x = .ok y → y.length ≤ output.len) (hw8 : work.base % 8 = 0)
    (hram : ∀ r ∈ [input, output, work, ⟨entry.toNat, (C.g41 c (serialize p)).length⟩], Proven.Region.inRAM r)
    (hdis : [input, output, work, ⟨entry.toNat, (C.g41 c (serialize p)).length⟩].Pairwise Proven.disjoint)
    (hMo : Proven.Mapped s output) (hMw : Proven.Mapped s work) (y : List UInt8) (hY : Sem κC p x = .ok y) (hge : Msp p x ≤ work.len) :
    Proven.runsTo s (Outcome s ra output work (Sem κC p x) False) := by
  have rW := hram work (by simp)
  simp only [Proven.Region.inRAM] at rW
  have hL : LinearK p := ⟨Ks, hO, hK2⟩
  have h16 := Msp_ge p x
  refine SimW.gen_host c hP Ks hO hK2 hXl h hdb x s entry ra input output work False hxl hc hpc he4 hB h10 h11 h12 h13 h2 h1 hra4 hin hil hout hw8 hram hdis hMo hMw (by omega) fun T => ?_
  have e : (work.base + work.len) / 8 * 8 = work.base + 16 + (work.len / 8 * 8 - 16) := by omega
  have hnr := no_room (p := p) (x := x) (T := []) (hb := work.base + 16) (u := work.len / 8 * 8 - 16) (by omega)
    (by omega) (by omega) (by unfold Msp at hge; omega)
  unfold RS at hnr; rw [← e] at hnr
  obtain hc | hc | ⟨-, hS⟩ := gen_all hP hL x hxl [] (work.base + 16) ((work.base + work.len) / 8 * 8)
    ⟨work.base + 16, fun _ => none⟩ (by show (work.base + 16) % 8 = 0; omega) (Nat.le_refl _)
  · obtain ⟨a, l, H', e', -⟩ := hc
    refine ⟨[a], H', ?_⟩
    rw [SimW.semAt_pcT _ _ _ _ T [], ← oD_semAt]
    show toO (semAtF _ p _ [] _ _) = _
    rw [show (524288 : Nat) = κC from rfl, e']; rfl
  · exact absurd hc hnr
  · rw [hY] at hS; cases hS

end NanoMain
