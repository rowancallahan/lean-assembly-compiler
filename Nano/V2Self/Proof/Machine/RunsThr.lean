/- Opus box E: the exact work bound at the machine: `gen_implementsM` (Gen's code implements `Sem` with space
`max 16 ∘ Msp`, no hypothesis), `gen_runs_ok` (at or above `Msp`: the normal return), `gen_runs_oom` (below `Msp`:
the definite out-of-memory return, given `ShiftInv`). -/
import Nano.V2Self.Proof.Machine.RunsDef
import Nano.V2Self.Proof.Parser.ParCapBnd
namespace NanoMain
open Templates ParSpec Classical

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

/-- **`memoryNeeded` is finite and bounded**: for a text denoting a parsed linear program, C's explicit work bound is
at most D's uniform work bound `gen_R` + 30 bytes -/
theorem spaceC_le {x : List UInt8} {ts : List UInt64} {p : List DefA} (hpo : pOf x = some p)
    (hp : ParsesProgram ts p) (hL : LinearK p) (inp : List UInt8) (hin : inp.length ≤ 2 ^ 20) :
    spaceC x inp ≤ Classical.choose (gen_R hp hL inp hin) + 30 := by
  have hR := Classical.choose_spec (gen_R hp hL inp hin)
  have := Msp_le hp inp _ fun T base len h8 h32 hle => by
    obtain ⟨h1, h2⟩ := hR T base len h8 h32 hle
    exact ⟨fun y hy => by obtain ⟨a, l, H', e, -⟩ := h1 y hy; exact ⟨_, _, e⟩, h2⟩
  have h16 := Msp_ge p inp
  unfold spaceC; rw [hpo]; simp only; omega

end NanoMain
