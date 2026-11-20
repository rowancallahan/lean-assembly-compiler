/- Opus box E: the EXACT work bound of C's code (below `MainTop`, which defines `spaceC` with it).  `thr p x`: the
least number of usable bytes (above the 16-byte reserve) with which main does not run out of room at ANY admissible
8-aligned work position; `Msp p x` rounds `16 + thr` up to the 8-byte granularity.  Room ⇒ below the bound (no
hypothesis); below the bound ⇒ room at every position (given `ShiftInv`); `Msp_le`: at most D's work bound + 30. -/
import Nano.V2Self.Proof.Machine.RunsShift
import Nano.V2Self.Proof.Machine.SemCases
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

theorem lfind_le (P : Nat → Prop) : ∀ n i j, i ≤ j → j ≤ i + n → P j → lfind P i n ≤ j
  | 0, i, j, h1, h2, _ => by simp [lfind]; omega
  | n + 1, i, j, h1, h2, hj => by
    unfold lfind; split
    · exact h1
    · rcases Nat.eq_or_lt_of_le h1 with rfl | h1
      · contradiction
      · exact lfind_le P n (i + 1) j h1 (by omega) hj

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

/-- **the exact bound is at most D's work bound + 30**: if every admissible block of at least `R` bytes gives the
meaning's result (ok or cap, as `gen_R` provides), then `Msp p x ≤ R + 30` -/
theorem Msp_le {ts : List UInt64} {p : List DefA} (hp : ParsesProgram ts p) (x : List UInt8) (R : Nat)
    (hR : ∀ (T : Buf) (base len : Nat), base % 8 = 0 → base + len ≤ 2 ^ 32 → R ≤ len →
      (∀ y, Sem κC p x = .ok y → ∃ vs H', semAt (pcOf κC (base + 16) (UInt64.ofNat x.length) (inpW x) T) p
        (p.length - 1) [] ((base + len) / 8 * 8) ⟨base + 16, fun _ => none⟩ = some (vs, H')) ∧
      (Sem κC p x = .error .cap → semAtF (pcOf κC (base + 16) (UInt64.ofNat x.length) (inpW x) T) p (p.length - 1)
        [] ((base + len) / 8 * 8) ⟨base + 16, fun _ => none⟩ = .error .cap)) :
    Msp p x ≤ R + 30 := by
  have hg : GoodU p x ((R + 7) / 8 * 8) := by
    intro T hb h8 h31 h32 hr
    have e : (hb - 16 + ((R + 7) / 8 * 8 + 16)) / 8 * 8 = hb + (R + 7) / 8 * 8 := by omega
    have hb16 : hb - 16 + 16 = hb := by omega
    obtain ⟨hok, hcap⟩ := hR T (hb - 16) ((R + 7) / 8 * 8 + 16) (by omega) (by omega) (by omega)
    rw [e, hb16] at hok hcap
    unfold RS at hr
    rcases SimW.sem3 (Sem κC p x) with ⟨y, hS⟩ | hS | hS
    · obtain ⟨vs, H', h⟩ := hok y hS
      rw [← oD_semAt] at h
      simp only [oD, hr, toO] at h; cases h
    · rw [hcap hS] at hr; cases hr
    · exact parsed_not_stuck hp _ x hS
  have := lfind_le (GoodU p x) (2 ^ 32) 0 ((R + 7) / 8 * 8) (Nat.zero_le _)
  by_cases hbig : (R + 7) / 8 * 8 ≤ 2 ^ 32
  · have := this (by omega) hg
    unfold Msp thr; omega
  · have : thr p x ≤ 2 ^ 32 := by
      unfold thr; exact lfind_le (GoodU p x) (2 ^ 32) 0 (2 ^ 32) (Nat.zero_le _) (by omega)
        (fun _ hb _ h31 h32 => by omega)
    unfold Msp; omega

end NanoMain
