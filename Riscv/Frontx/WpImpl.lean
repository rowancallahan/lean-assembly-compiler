/- Paged arrays (NOTES section 30), part 11: the machine statement with a work block whose size is the call's.

`Implements1Pg`: `Implements1With` where the work block has any length `L ≥ Lmin`; the code's first instruction
`mv a4, sp` tells the program where the work block ends (variable 4 = `work.base + L`, variable 2 = `work.base`), the
program derives its page pool from `L`; the result is the output (`fits a L`) or `a1 = -1` (`¬ fits a L`).
`pg_core` is `implements1_of_spec` (`Riscv/Back/Implements1Opt.lean`) for such a block; `pg_of_spec` adds the
instruction. -/
import Riscv.Back.Implements1Opt
import Riscv.Frontx.WpTop
import Riscv.Frontx.WpFlat

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Proven.Mach.Riscv
open Proven LeanRV64D

/-- **What a paged program satisfies**: any work length `L ≥ Lmin`; the output when the run fits (`fits a L`),
else `a1 = 2^64 - 1`; nothing outside the output and work blocks changes -/
def Implements1Pg {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (code : List (BitVec 32))
    (f : α → β) (Lmin : Nat) (fits : α → Nat → Prop) (maxLen : Nat := 2 ^ 20) (retLen : Bool := false) : Prop :=
  ∀ (a : α) (s : St) (entry ra : BitVec 64) (input output work : Proven.Region),
    let x := encA a
    let y := encB (f a)
    let codeR : Proven.Region := ⟨entry.toNat, 4 * code.length⟩
    x.length ≤ maxLen → Cfg s → s.regs.get? .PC = some entry → entry.toNat % 4 = 0 →
    bytesAt s entry.toNat (4 * code.length) = codeBytes code →
    s.regs.get? .x10 = some (BitVec.ofNat 64 input.base) →
    s.regs.get? .x11 = some (BitVec.ofNat 64 x.length) →
    s.regs.get? .x12 = some (BitVec.ofNat 64 work.base) →
    s.regs.get? .x13 = some (BitVec.ofNat 64 output.base) →
    s.regs.get? .x2 = some (BitVec.ofNat 64 (work.base + work.len)) →
    s.regs.get? .x1 = some ra → ra.toNat % 4 = 0 → Proven.disjoint ⟨ra.toNat, 4⟩ codeR →
    bytesAt s input.base x.length = x.map (some ·.toBitVec) →
    input.len = x.length → y.length ≤ output.len → Lmin ≤ work.len → work.base % 8 = 0 →
    (∀ r ∈ [input, output, work, codeR], r.inRAM) → [input, output, work, codeR].Pairwise Proven.disjoint →
    Mapped s output → Mapped s work →
    runsTo s fun s' => s'.regs.get? .PC = some ra ∧
      unchangedOutside s s' [⟨output.base, y.length⟩, work] ∧ abiSavedKept s s' ∧ Cfg s' ∧
      (fits a work.len → bytesAt s' output.base y.length = y.map (some ·.toBitVec) ∧
        (retLen = true → s'.regs.get? .x11 = some (BitVec.ofNat 64 y.length))) ∧
      (¬ fits a work.len → s'.regs.get? .x11 = some (BitVec.allOnes 64))

/-- **`Implements1Pg` and `a7` (variable 7, `vOk`) at the return**:: any work length `L ≥ Lmin`; the output when the run fits (`fits a L`),
else `a1 = 2^64 - 1`; nothing outside the output and work blocks changes -/
def Implements1PgQ {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (code : List (BitVec 32))
    (f : α → β) (Lmin : Nat) (fits : α → Nat → Prop) (Q : α → Nat → BitVec 64 → Prop) (maxLen : Nat := 2 ^ 20) (retLen : Bool := false) : Prop :=
  ∀ (a : α) (s : St) (entry ra : BitVec 64) (input output work : Proven.Region),
    let x := encA a
    let y := encB (f a)
    let codeR : Proven.Region := ⟨entry.toNat, 4 * code.length⟩
    x.length ≤ maxLen → Cfg s → s.regs.get? .PC = some entry → entry.toNat % 4 = 0 →
    bytesAt s entry.toNat (4 * code.length) = codeBytes code →
    s.regs.get? .x10 = some (BitVec.ofNat 64 input.base) →
    s.regs.get? .x11 = some (BitVec.ofNat 64 x.length) →
    s.regs.get? .x12 = some (BitVec.ofNat 64 work.base) →
    s.regs.get? .x13 = some (BitVec.ofNat 64 output.base) →
    s.regs.get? .x2 = some (BitVec.ofNat 64 (work.base + work.len)) →
    s.regs.get? .x1 = some ra → ra.toNat % 4 = 0 → Proven.disjoint ⟨ra.toNat, 4⟩ codeR →
    bytesAt s input.base x.length = x.map (some ·.toBitVec) →
    input.len = x.length → y.length ≤ output.len → Lmin ≤ work.len → work.base % 8 = 0 →
    (∀ r ∈ [input, output, work, codeR], r.inRAM) → [input, output, work, codeR].Pairwise Proven.disjoint →
    Mapped s output → Mapped s work →
    runsTo s fun s' => s'.regs.get? .PC = some ra ∧
      unchangedOutside s s' [⟨output.base, y.length⟩, work] ∧ abiSavedKept s s' ∧ Cfg s' ∧
      (fits a work.len → bytesAt s' output.base y.length = y.map (some ·.toBitVec) ∧
        (retLen = true → s'.regs.get? .x11 = some (BitVec.ofNat 64 y.length))) ∧
      (¬ fits a work.len → s'.regs.get? .x11 = some (BitVec.allOnes 64)) ∧
      ∃ v, s'.regs.get? .x17 = some v ∧ Q a work.len v

theorem Implements1PgQ.toPg {α β : Type} {encA : α → List UInt8} {encB : β → List UInt8} {code : List (BitVec 32)}
    {f : α → β} {Lmin : Nat} {fits : α → Nat → Prop} {Q : α → Nat → BitVec 64 → Prop} {maxLen : Nat} {retLen : Bool}
    (h : Implements1PgQ encA encB code f Lmin fits Q maxLen retLen) :
    Implements1Pg encA encB code f Lmin fits maxLen retLen := by
  intro a s entry ra input output work x y codeR hmax hc hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hol hws hwal hram hdis hmapO hmapW
  exact runsTo_mono (h a s entry ra input output work hmax hc hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hol hws hwal hram hdis hmapO hmapW) fun _ ⟨p1, p2, p3, p4, p5, p6, _⟩ => ⟨p1, p2, p3, p4, p5, p6⟩

theorem pg_core {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (f : α → β)
    (N : Nat) (hN : N ≤ NS) (prog : Mach.BStmt) (code : List (BitVec 32)) (hspec : BSpec N prog code)
    (wl : Nat → Nat) (hwl : ∀ L, 8192 ≤ L → 8 * wl L + 8 * (N + 1) + 7 ≤ L) (maxLen : Nat) (retLen : Bool)
    (fits : α → Nat → Prop) (Q : α → Nat → BitVec 64 → Prop)
    (hex : ∀ (a : α) (out : List (BitVec 8)) (tbl : List (BitVec 64)) (env : Mach.BEnv) (b L : Nat),
      env 1 = BitVec.ofNat 64 (encA a).length → env 2 = BitVec.ofNat 64 b → env 4 = BitVec.ofNat 64 (b + L) →
      b % 8 = 0 → 0x80000000 ≤ b → b + L ≤ 0x100000000 → 8192 ≤ L → (∀ j, 8 ≤ j → env j = 0) →
      (encA a).length ≤ maxLen → (encA a).length < 2 ^ 32 → (encB (f a)).length ≤ out.length →
      out.length < 2 ^ 32 → tbl.length = wl L →
      ∃ σ' out', Mach.BExec prog ⟨env, [(encA a).map (·.toBitVec), out], [tbl]⟩ σ' ∧
        σ'.heap = [(encA a).map (·.toBitVec), out'] ∧
        out'.drop (encB (f a)).length = out.drop (encB (f a)).length ∧
        (fits a L → out'.take (encB (f a)).length = (encB (f a)).map (·.toBitVec) ∧
          (retLen = true → σ'.env 1 = BitVec.ofNat 64 (encB (f a)).length)) ∧
        (¬ fits a L → σ'.env 1 = BitVec.allOnes 64) ∧ Q a L (σ'.env 7)) :
    ∀ (a : α) (s : St) (entry ra : BitVec 64) (input output work codeR : Proven.Region),
    let x := encA a
    let y := encB (f a)
    x.length ≤ maxLen → Cfg s → s.regs.get? .PC = some entry → entry.toNat % 4 = 0 →
    (codeR.base ≤ entry.toNat ∧ entry.toNat + 4 * code.length ≤ codeR.base + codeR.len) →
    codeAt s entry code →
    s.regs.get? .x10 = some (BitVec.ofNat 64 input.base) →
    s.regs.get? .x11 = some (BitVec.ofNat 64 x.length) →
    s.regs.get? .x12 = some (BitVec.ofNat 64 work.base) →
    s.regs.get? .x13 = some (BitVec.ofNat 64 output.base) →
    s.regs.get? .x2 = some (BitVec.ofNat 64 (work.base + work.len)) →
    s.regs.get? .x14 = some (BitVec.ofNat 64 (work.base + work.len)) →
    s.regs.get? .x1 = some ra → ra.toNat % 4 = 0 → Proven.disjoint ⟨ra.toNat, 4⟩ codeR →
    bytesAt s input.base x.length = x.map (some ·.toBitVec) →
    input.len = x.length → y.length ≤ output.len → 8192 ≤ work.len → work.base % 8 = 0 →
    (∀ r ∈ [input, output, work, codeR], r.inRAM) → [input, output, work, codeR].Pairwise Proven.disjoint →
    Mapped s output → Mapped s work →
    runsTo s fun s' => s'.regs.get? .PC = some ra ∧
      unchangedOutside s s' [⟨output.base, y.length⟩, work] ∧ abiSavedKept s s' ∧ Cfg s' ∧
      (fits a work.len → bytesAt s' output.base y.length = y.map (some ·.toBitVec) ∧
        (retLen = true → s'.regs.get? .x11 = some (BitVec.ofNat 64 y.length))) ∧
      (¬ fits a work.len → s'.regs.get? .x11 = some (BitVec.allOnes 64)) ∧
      ∃ v, s'.regs.get? .x17 = some v ∧ Q a work.len v := by
  intro a s entry ra input output work codeR x y hmax h hpc hal hcont hcode h10 h11 h12 h13 h2 h14 h1 hra hrad hx
    hil hol hws hwal hram hdis hmapO hmapW
  have hin : ∀ r ∈ [input, output, work, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  obtain ⟨ri, ro, rw', rc⟩ := hin
  unfold Region.inRAM at ri ro rw' rc
  unfold Proven.disjoint at d12 d13 d14 d23 d24 d34
  have hil' : input.len = x.length := hil
  have hol' : y.length ≤ output.len := hol
  have hwl' := hwl work.len hws
  have hxl : (x.map (·.toBitVec)).length = x.length := by simp
  -- the frame
  have hsp2 : getX s 2 = BitVec.ofNat 64 (work.base + work.len) := getX_of (h.x2.symm.trans h2) rfl
  have hspn : (getX s 2).toNat = work.base + work.len := by rw [hsp2]; exact toNat_ofNat' (by omega)
  have hfb : frameBase N (getX s 2) = (work.base + work.len) / 8 * 8 - 8 * (N + 1) := by
    unfold frameBase; rw [hspn]
  have hfb1 : work.base + 8 * wl work.len ≤ frameBase N (getX s 2) := by rw [hfb]; omega
  have hfb2 : frameBase N (getX s 2) + 8 * (N + 1) ≤ work.base + work.len := by rw [hfb]; omega
  have hf : FrOK N (frameBase N (getX s 2)) :=
    ⟨by rw [hfb]; omega, by omega, by omega, hN⟩
  -- the initial heap
  obtain ⟨out0, hout0l, ho⟩ : ∃ out0 : List (BitVec 8), out0.length = output.len ∧
      bytesAt s output.base output.len = out0.map some :=
    ⟨_, by simp [bytesAt], bytesAt_hosted fun i hi => hmapO i hi⟩
  obtain ⟨tbl0, htl, htb⟩ : ∃ tbl0 : List (BitVec 64), tbl0.length = wl work.len ∧
      bytesAt s work.base (8 * wl work.len) = (wbytes tbl0).map some := by
    obtain ⟨ws, hl, hw⟩ := exists_wbytes (wl work.len) ((bytesAt s work.base (8 * wl work.len)).map (·.getD 0))
      (by simp [bytesAt])
    exact ⟨ws, hl, by rw [hw]; exact bytesAt_hosted fun i hi => hmapW i (by omega)⟩
  obtain ⟨σ', out', hexec, hh, hdr, hfit, hnofit, hQ⟩ := hex a out0 tbl0 (envOf s) work.base work.len
    (getX_of (h.x11.symm.trans h11) rfl)
    (getX_of (h.x12.symm.trans h12) rfl)
    (getX_of (h.x14.symm.trans h14) rfl) hwal (by omega) (by omega) hws
    (fun j hj => by simp [envOf]; omega)
    hmax (by show x.length < 2 ^ 32; omega) (by show y.length ≤ out0.length; omega) (by omega) htl
  -- the layout
  let R : List Region := [⟨input.base, x.length⟩, ⟨output.base, output.len⟩]
  let W : List Region := [⟨work.base, 8 * wl work.len⟩]
  have hL : rvF.Lay N (rvF.frameAt s N) R W := by
    refine ⟨fun r hr => ?_, fun r hr => ?_, ?_, List.pairwise_singleton _ _, fun r hr w hw => ?_, fun r hr => ?_,
      fun w hw => ?_, fun w hw => ?_, fun r hr q h1 h2 _ _ => ?_, fun w hw q h1 h2 _ _ => ?_⟩
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (show _ ∧ _; dsimp only; show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; omega)
    · simp only [W, List.mem_singleton] at hr; subst hr
      show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; dsimp only; omega
    · simp only [R, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
        and_true, false_implies, implies_true]
      unfold Mach.disjoint; dsimp only; omega
    · simp only [W, List.mem_singleton] at hw; subst hw
      simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold Mach.disjoint; dsimp only; omega)
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      show Mach.disjoint ⟨frameBase N (getX s 2), _⟩ r
      rcases hr with rfl | rfl <;> (unfold Mach.disjoint; dsimp only; omega)
    · simp only [W, List.mem_singleton] at hw; subst hw
      show Mach.disjoint ⟨frameBase N (getX s 2), _⟩ _
      unfold Mach.disjoint; dsimp only; omega
    · simp only [W, List.mem_singleton] at hw; subst hw; exact hwal
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      show 0x80000000 ≤ q ∧ q + 1 ≤ 0x100000000
      rcases hr with rfl | rfl <;> (dsimp only at h1 h2; omega)
    · simp only [W, List.mem_singleton] at hw; subst hw
      show 0x80000000 ≤ q ∧ q + 1 ≤ 0x100000000; dsimp only at h1 h2; omega
  have hok : codeOK entry code.length := ⟨hal, by omega, by omega⟩
  have hcd : ∀ r ∈ R ++ W ++ [⟨rvF.frameAt s N, 8 * (N + 1)⟩],
      Mach.disjoint ⟨entry.toNat, 4 * code.length⟩ r := by
    intro r hr
    simp only [R, W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [show rvF.frameAt s N = frameBase N (getX s 2) from rfl] at hr
    show Mach.disjoint _ r
    rcases hr with rfl | rfl | rfl | rfl <;> (unfold Mach.disjoint; dsimp only)
    · omega
    · omega
    · omega
    · show _ ∨ frameBase N (getX s 2) + _ ≤ _; omega
  have hheap : rvF.HeapB [0, 3] [2] R W ⟨envOf s, [x.map (·.toBitVec), out0], [tbl0]⟩ s := by
    refine ⟨rfl, rfl, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, rfl, rfl, fun b hb => ?_, fun b hb => ?_,
      fun b hb => ?_⟩
    · obtain _ | _ | b := b
      · exact getX_of (h.x10.symm.trans h10) rfl
      · exact getX_of (h.x13.symm.trans h13) rfl
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega)
    · obtain _ | _ | b := b
      · simp [R]
      · simpa [R] using hout0l
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega)
    · obtain _ | _ | b := b
      · show bytes (rvF.mem s) input.base x.length = _
        exact (bytes_eq s _ _).trans (by simpa [List.map_map, Function.comp_def] using hx)
      · show bytes (rvF.mem s) output.base output.len = _
        exact (bytes_eq s _ _).trans (by simpa using ho)
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega)
    · obtain _ | b := b
      · exact getX_of (h.x12.symm.trans h12) rfl
      · exact absurd hb (by show ¬(b + 1 < 1); omega)
    · obtain _ | b := b
      · show 8 * tbl0.length = 8 * wl work.len; rw [htl]
      · exact absurd hb (by show ¬(b + 1 < 1); omega)
    · obtain _ | b := b
      · show bytes (rvF.mem s) work.base (8 * wl work.len) = _
        exact (bytes_eq s _ _).trans htb
      · exact absurd hb (by show ¬(b + 1 < 1); omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  refine runsTo_mono (hspec hexec ⟨h, hpc, hcode, hok⟩ hf hL hcd
    (fun i => by show getX s (phys (avar i)) = _; rw [phys_avar]; simp [envOf])
    (fun j hj => by simp only [envOf]; rw [dite_neg' (by omega)]) hheap (by show (getX s 1).toNat % 2 = 0; rw [hra']; omega)) ?_
  rintro s' ⟨p1, p2, p3, p4, p5, p6⟩
  have e0 := p3.rbytes 0 (by simp [R]); have e1 := p3.rbytes 1 (by simp [R])
  simp only [hh] at e0 e1
  have e1' : bytesAt s' output.base output.len = out'.map some := by
    have := (bytes_eq s' _ _).symm.trans e1; exact this
  refine ⟨by rw [← hra']; exact p1, ?_, abi_of_keep h p5 p6, p5, fun hf => ?_, fun hf => ?_,
    ⟨getX s' 17, p5.x17, ?_⟩⟩
  · intro q hq
    have a2 := hq ⟨output.base, y.length⟩ (by simp); have a3 := hq work (by simp)
    dsimp only at a2
    have e0' : bytesAt s' input.base x.length = (x.map (·.toBitVec)).map some := by
      have := (bytes_eq s' _ _).symm.trans e0; exact this
    by_cases hqi : input.base ≤ q ∧ q < input.base + input.len
    · have e0x : bytesAt s' input.base x.length = bytesAt s input.base x.length := by
        rw [e0', hx, List.map_map]; rfl
      have := congrArg (·[q - input.base]?) e0x
      simp only [bytesAt, List.getElem?_map, List.getElem?_range (show q - input.base < x.length by omega),
        Option.map_some, Option.some.injEq] at this
      rwa [Nat.add_sub_cancel' hqi.1] at this
    by_cases hqo : output.base ≤ q ∧ q < output.base + output.len
    · have e1x : (bytesAt s' output.base output.len)[q - output.base]? =
          (bytesAt s output.base output.len)[q - output.base]? := by
        rw [e1', ho, List.getElem?_map, List.getElem?_map]
        have := congrArg (·[q - output.base - y.length]?) hdr
        simp only [List.getElem?_drop] at this
        rw [show y.length + (q - output.base - y.length) = q - output.base by omega] at this
        rw [this]
      simp only [bytesAt, List.getElem?_map, List.getElem?_range (show q - output.base < output.len by omega),
        Option.map_some, Option.some.injEq] at e1x
      rwa [Nat.add_sub_cancel' hqo.1] at e1x
    · apply p4 q
      intro r hr
      simp only [R, W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only
      · omega
      · omega
      · omega
      · show q < frameBase N (getX s 2) ∨ frameBase N (getX s 2) + _ ≤ q; omega
  · obtain ⟨htk, hrl⟩ := hfit hf
    refine ⟨?_, fun hr => ?_⟩
    · rw [← bytesAt_take' s' output.base hol', e1', ← List.map_take, htk]; simp [List.map_map, y]
    · have := p2 ⟨1, by decide⟩
      rw [show rvF.get s' (avar ⟨1, by decide⟩) = getX s' 11 from rfl, hrl hr] at this
      rw [p5.x11, this]
  · have := p2 ⟨1, by decide⟩
    rw [show rvF.get s' (avar ⟨1, by decide⟩) = getX s' 11 from rfl, hnofit hf] at this
    rw [p5.x11, this]
  · have := p2 ⟨7, by decide⟩
    rw [show rvF.get s' (avar ⟨7, by decide⟩) = getX s' 17 from rfl] at this
    rw [this]; exact hQ

/-- `mv a4, sp` -/
def mvA4 : BitVec 32 := encI 0 0 14 2

/-- **`Implements1Pg` from a source-level run**: the code is `mv a4, sp` followed by the body -/
theorem pg_of_spec {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (f : α → β)
    (N : Nat) (hN : N ≤ NS) (prog : Mach.BStmt) (code : List (BitVec 32)) (hspec : BSpec N prog code)
    (wl : Nat → Nat) (hwl : ∀ L, 8192 ≤ L → 8 * wl L + 8 * (N + 1) + 7 ≤ L) (maxLen : Nat) (retLen : Bool)
    (fits : α → Nat → Prop) (Q : α → Nat → BitVec 64 → Prop)
    (hex : ∀ (a : α) (out : List (BitVec 8)) (tbl : List (BitVec 64)) (env : Mach.BEnv) (b L : Nat),
      env 1 = BitVec.ofNat 64 (encA a).length → env 2 = BitVec.ofNat 64 b → env 4 = BitVec.ofNat 64 (b + L) →
      b % 8 = 0 → 0x80000000 ≤ b → b + L ≤ 0x100000000 → 8192 ≤ L → (∀ j, 8 ≤ j → env j = 0) →
      (encA a).length ≤ maxLen → (encA a).length < 2 ^ 32 → (encB (f a)).length ≤ out.length →
      out.length < 2 ^ 32 → tbl.length = wl L →
      ∃ σ' out', Mach.BExec prog ⟨env, [(encA a).map (·.toBitVec), out], [tbl]⟩ σ' ∧
        σ'.heap = [(encA a).map (·.toBitVec), out'] ∧
        out'.drop (encB (f a)).length = out.drop (encB (f a)).length ∧
        (fits a L → out'.take (encB (f a)).length = (encB (f a)).map (·.toBitVec) ∧
          (retLen = true → σ'.env 1 = BitVec.ofNat 64 (encB (f a)).length)) ∧
        (¬ fits a L → σ'.env 1 = BitVec.allOnes 64) ∧ Q a L (σ'.env 7)) :
    Implements1PgQ encA encB (mvA4 :: code) f 8192 fits Q maxLen retLen := by
  intro a s entry ra input output work x y codeR hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hol hws hwal hram hdis hmapO hmapW
  have hin : ∀ r ∈ [input, output, work, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  obtain ⟨ri, ro, rw', rc⟩ := hin
  unfold Region.inRAM at rc
  simp only [codeR, List.length_cons] at rc
  have hok : codeOK entry (code.length + 1) := ⟨hal, rc.1, by omega⟩
  have hA : rvF.At s entry (mvA4 :: code) := ⟨h, hpc, codeAt_of_codeBytes hok hcode, hok⟩
  have sp := Core.At.split _ (l₁ := [mvA4]) (l₂ := code) hA
  obtain ⟨hh, hpc0, hok0, hi0⟩ := first1 sp.1
  obtain ⟨s1, hn⟩ := G.step_addi hh hpc0 hok0 14 2 0 hi0
  have hx1 : ∀ j, j ≠ 14 → getX s1 j = getX s j := fun j hj => by
    rw [hn.x j, if_neg (fun e => hj e.1)]
  have hx14 : getX s1 14 = getX s 2 := by
    rw [hn.x 14, if_pos ⟨rfl, by decide⟩, (by decide : (0 : BitVec 12).signExtend 64 = 0#64), BitVec.add_zero]
  have hmem : s1.mem = s.mem := hn.mem
  have hb : ∀ a n, bytesAt s1 a n = bytesAt s a n := fun a n => by simp [bytesAt, hmem]
  have hent : (entry + 4).toNat = entry.toNat + 4 := by
    have h4 : (4 : BitVec 64).toNat = 4 := rfl
    simp only [BitVec.toNat_add, h4]; omega
  have hcd1 : codeAt s1 (entry + 4) code := core.codeAt_mem (memOf hn) sp.2.1
  have h2' := Option.some.inj (h.x2.symm.trans h2)
  have core1 := pg_core encA encB f N hN prog code hspec wl hwl maxLen retLen fits Q hex a s1 (entry + 4) ra input
    output work codeR hmax hn.cfg hn.pc (by rw [hent]; omega) ⟨by rw [hent]; simp only [codeR]; omega,
      by rw [hent]; simp only [codeR, List.length_cons]; omega⟩ hcd1
    (by rw [hn.cfg.x10, hx1 10 (by decide)]; rw [Option.some.inj (h.x10.symm.trans h10)])
    (by rw [hn.cfg.x11, hx1 11 (by decide)]; rw [Option.some.inj (h.x11.symm.trans h11)])
    (by rw [hn.cfg.x12, hx1 12 (by decide)]; rw [Option.some.inj (h.x12.symm.trans h12)])
    (by rw [hn.cfg.x13, hx1 13 (by decide)]; rw [Option.some.inj (h.x13.symm.trans h13)])
    (by rw [hn.cfg.x2, hx1 2 (by decide)]; rw [h2'])
    (by rw [hn.cfg.x14, hx14, h2'])
    (by rw [hn.cfg.x1, hx1 1 (by decide)]; rw [Option.some.inj (h.x1.symm.trans h1)])
    hra hrad (by rw [hb]; exact hx) hil hol hws hwal hram hdis (fun i hi => by rw [hmem]; exact hmapO i hi)
    (fun i hi => by rw [hmem]; exact hmapW i hi)
  refine runsTo_next hn (runsTo_mono core1 ?_)
  rintro s' ⟨p1, p2, p3, p4, p5, p6, p7⟩
  refine ⟨p1, fun q hq => by rw [p2 q hq, hmem], ?_, p4, p5, p6, p7⟩
  intro r hr
  rw [p3 r hr]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | (rw [hn.cfg.x2, h.x2, hx1 2 (by decide)]) | (rw [hn.cfg.x3, h.x3, hx1 3 (by decide)]) | (rw [hn.cfg.x4, h.x4, hx1 4 (by decide)]) | (rw [hn.cfg.x8, h.x8, hx1 8 (by decide)]) | (rw [hn.cfg.x9, h.x9, hx1 9 (by decide)]) | (rw [hn.cfg.x18, h.x18, hx1 18 (by decide)]) | (rw [hn.cfg.x19, h.x19, hx1 19 (by decide)]) | (rw [hn.cfg.x20, h.x20, hx1 20 (by decide)]) | (rw [hn.cfg.x21, h.x21, hx1 21 (by decide)]) | (rw [hn.cfg.x22, h.x22, hx1 22 (by decide)]) | (rw [hn.cfg.x23, h.x23, hx1 23 (by decide)]) | (rw [hn.cfg.x24, h.x24, hx1 24 (by decide)]) | (rw [hn.cfg.x25, h.x25, hx1 25 (by decide)]) | (rw [hn.cfg.x26, h.x26, hx1 26 (by decide)]) | (rw [hn.cfg.x27, h.x27, hx1 27 (by decide)])

/-- **`Implements1Pg` for the optimised words**: `mv a4, sp`, then `compBFO` of the program -/
theorem pg_of_execOW {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (f : α → β)
    (N : Nat) (hN : N ≤ NS) (prog : Mach.BStmt) (hwf : rvF.wfB N [0, 3] [2] prog)
    (wl : Nat → Nat) (hwl : ∀ L, 8192 ≤ L → 8 * wl L + 8 * (N + 1) + 7 ≤ L) (maxLen : Nat) (retLen : Bool)
    (fits : α → Nat → Prop) (Q : α → Nat → BitVec 64 → Prop)
    (hex : ∀ (a : α) (out : List (BitVec 8)) (tbl : List (BitVec 64)) (env : Mach.BEnv) (b L : Nat),
      env 1 = BitVec.ofNat 64 (encA a).length → env 2 = BitVec.ofNat 64 b → env 4 = BitVec.ofNat 64 (b + L) →
      b % 8 = 0 → 0x80000000 ≤ b → b + L ≤ 0x100000000 → 8192 ≤ L → (∀ j, 8 ≤ j → env j = 0) →
      (encA a).length ≤ maxLen → (encA a).length < 2 ^ 32 → (encB (f a)).length ≤ out.length →
      out.length < 2 ^ 32 → tbl.length = wl L →
      ∃ σ' out', Mach.BExec prog ⟨env, [(encA a).map (·.toBitVec), out], [tbl]⟩ σ' ∧
        σ'.heap = [(encA a).map (·.toBitVec), out'] ∧
        out'.drop (encB (f a)).length = out.drop (encB (f a)).length ∧
        (fits a L → out'.take (encB (f a)).length = (encB (f a)).map (·.toBitVec) ∧
          (retLen = true → σ'.env 1 = BitVec.ofNat 64 (encB (f a)).length)) ∧
        (¬ fits a L → σ'.env 1 = BitVec.allOnes 64) ∧ Q a L (σ'.env 7)) :
    Implements1PgQ encA encB (mvA4 :: compBFO N [0, 3] [2] prog) f 8192 fits Q maxLen retLen :=
  pg_of_spec encA encB f N hN prog _
    (fun hexec hA hen hL hcd hreg hslot hheap hra => compBFO_ok' N [0, 3] [2] (by intro x hx; simp at hx; omega)
      (by intro x hx; simp at hx; omega) hwf hexec hA hen hL hcd hreg hslot hheap hra) wl hwl maxLen retLen fits Q hex

/-- **`Implements1PgQ` for the checked words** `mv a4, sp`, then `compBFC` with the register choice `(t, spl)` that
`optB` accepts (programs with `BStmt.mop`) -/
theorem pg_of_execOC {α β : Type} (encA : α → List UInt8) (encB : β → List UInt8) (f : α → β)
    (N : Nat) (hN : N ≤ NS) (prog : Mach.BStmt) (t : List (Nat × Reg)) (spl : List Nat)
    (hc : (rvwF.optB scB (tblG t) (fun j => spl.contains j) N [0, 3] [2] prog).isSome = true)
    (wl : Nat → Nat) (hwl : ∀ L, 8192 ≤ L → 8 * wl L + 8 * (N + 1) + 7 ≤ L) (maxLen : Nat) (retLen : Bool)
    (fits : α → Nat → Prop) (Q : α → Nat → BitVec 64 → Prop)
    (hex : ∀ (a : α) (out : List (BitVec 8)) (tbl : List (BitVec 64)) (env : Mach.BEnv) (b L : Nat),
      env 1 = BitVec.ofNat 64 (encA a).length → env 2 = BitVec.ofNat 64 b → env 4 = BitVec.ofNat 64 (b + L) →
      b % 8 = 0 → 0x80000000 ≤ b → b + L ≤ 0x100000000 → 8192 ≤ L → (∀ j, 8 ≤ j → env j = 0) →
      (encA a).length ≤ maxLen → (encA a).length < 2 ^ 32 → (encB (f a)).length ≤ out.length →
      out.length < 2 ^ 32 → tbl.length = wl L →
      ∃ σ' out', Mach.BExec prog ⟨env, [(encA a).map (·.toBitVec), out], [tbl]⟩ σ' ∧
        σ'.heap = [(encA a).map (·.toBitVec), out'] ∧
        out'.drop (encB (f a)).length = out.drop (encB (f a)).length ∧
        (fits a L → out'.take (encB (f a)).length = (encB (f a)).map (·.toBitVec) ∧
          (retLen = true → σ'.env 1 = BitVec.ofNat 64 (encB (f a)).length)) ∧
        (¬ fits a L → σ'.env 1 = BitVec.allOnes 64) ∧ Q a L (σ'.env 7)) :
    Implements1PgQ encA encB (mvA4 :: compBFC N [0, 3] [2] t spl prog) f 8192 fits Q maxLen retLen :=
  pg_of_spec encA encB f N hN prog _
    (fun hexec hA hen hL hcd hreg hslot hheap hra => compBFC_ok' N [0, 3] [2] hc hexec hA hen hL hcd hreg hslot
      hheap hra) wl hwl maxLen retLen fits Q hex

end Proven.Mach.Riscv

namespace Proven.WA
open Proven Proven.WP Proven.Top.Alloc Proven.Mach.Riscv
open Proven.Frontx (Res rN rN_toNat rN_lt rN_add rN_inj rB wrO wrO_length wrO_append wrO_nil wrO_take wrO_drop)

/-- work words of the pool for a work block of `L` bytes -/
def wlOf (L : Nat) : Nat := (L / 8192 - 1) * P

theorem wlOf_le (N : Nat) (hN : N ≤ NS) (L : Nat) (hL : 8192 ≤ L) :
    8 * wlOf L + 8 * (N + 1) + 7 ≤ L := by
  unfold wlOf P NS at *; omega

/-- scalar result: the program with the pool size from the work block (guards flattened, `flatG`) -/
def pgProgS {t : Ty} (p : Pg [.ar .ba] (.sc t)) (k : Nat) : MS := flatG (.seq capCode (wholeS p k))

def pgNS {t : Ty} (p : Pg [.ar .ba] (.sc t)) (k : Nat) : Nat := (pgProgS p k).maxv - 8

def pgCodeS {t : Ty} (p : Pg [.ar .ba] (.sc t)) (k : Nat) : List (BitVec 32) :=
  mvA4 :: compBFO (pgNS p k) [0, 3] [2] (pgProgS p k)

/-- the checked words with a register choice (programs with `mop`) -/
def pgCodeSC {t : Ty} (p : Pg [.ar .ba] (.sc t)) (k : Nat) (tb : List (Nat × Mach.Reg)) (spl : List Nat) :
    List (BitVec 32) :=
  mvA4 :: compBFC (pgNS p k) [0, 3] [2] tb spl (pgProgS p k)

/-- `a7` at the return: 1 when the run fits, 0 when not -/
def okQ {α : Type} (fits : α → Nat → Prop) (a : α) (L : Nat) (v : BitVec 64) : Prop :=
  (fits a L → v = 1) ∧ (¬ fits a L → v = 0)

/-- **A paged program with a scalar result ⇒ `Implements1PgQ`** (`a7` = 1 or 0 as `okQ`): for any work block of `L ≥ 8192` bytes the code
returns the result when its page events fit (`pk 0 E + 1 ≤ L / 8192`: the pages and one page for the frame), else
`a1 = -1` -/
theorem implements1_pgSQ {t : Ty} {β : Type} [Res β] (f : ByteArray → β) (p : Pg [.ar .ba] (.sc t))
    (cv : t.T → β) (hcv : ∀ y, Res.repr (cv y) = t.rep y) (hN : pgNS p (Res.k β) ≤ NS)
    (hwf : p.wfP [inLocP] 9 = true)
    (hmwf : rvF.wfB (pgNS p (Res.k β)) [0, 3] [2] (pgProgS p (Res.k β)))
    (fits : ByteArray → Nat → Prop) (maxLen : Nat)
    (hgood : ∀ xs : ByteArray, xs.size ≤ maxLen → ∃ y E, p.GoodE [inLocP] 9 (xs, ()) y E ∧ cv y = f xs ∧
      ∀ L, 8192 ≤ L → (fits xs L ↔ pk 0 E + 1 ≤ L / 8192)) :
    Implements1PgQ (fun xs : ByteArray => xs.data.toList) Res.enc (pgCodeS p (Res.k β)) f 8192 fits (okQ fits) maxLen := by
  refine pg_of_execOW _ Res.enc f (pgNS p (Res.k β)) hN (pgProgS p (Res.k β)) hmwf wlOf
    (wlOf_le _ hN) maxLen false fits (okQ fits) ?_
  intro a out tbl env b L h1 h2 h4 hb hb1 hb2 hL h8 hmax hlt hout hol htl
  have hsz : a.data.toList.length = a.size := Array.length_toList
  obtain ⟨y, E, hg, hy, hfit⟩ := hgood a (by rw [← hsz]; exact hmax)
  have hcap := capCode_ok env [a.data.toList.map (·.toBitVec), out] [tbl] b L h2 h4 hL (by omega)
  have htl' : tbl.length = (L / 8192 - 1) * P := htl
  obtain ⟨σ', out', hex', hh, hr⟩ := wholeS_ok (L / 8192 - 1) f p cv hcv a (env.set vCap (rN ((L / 8192 - 1) * P))) out tbl
    y E (by rw [set_ne (show 1 ≠ vCap by decide)]; exact h1) (by rw [← hsz]; exact hlt) (by rw [htl']; unfold P; omega)
    (by rw [htl']; exact Nat.le_refl _) (by simp only [set_eq]) hwf hg hy hout
  refine ⟨σ', out', flatG_exec _ (.seq hcap hex'), hh, ?_, ?_, ?_, ?_⟩
  · rcases hr with ⟨-, -, hd, -⟩ | ⟨-, -, rfl, -⟩
    · exact hd
    · rfl
  · intro hf
    rcases hr with ⟨hp, ht, hd, -⟩ | ⟨hp, -, -, -⟩
    · exact ⟨ht, fun h => nomatch h⟩
    · have := (hfit L hL).1 hf; omega
  · intro hf
    rcases hr with ⟨hp, -, -⟩ | ⟨-, h1', -⟩
    · exact absurd ((hfit L hL).2 (by omega)) hf
    · exact h1'
  · rcases hr with ⟨hp, -, -, h7⟩ | ⟨hp, -, -, h7⟩
    · exact ⟨fun _ => h7, fun hf => absurd ((hfit L hL).2 (by omega)) hf⟩
    · exact ⟨fun hf => by have := (hfit L hL).1 hf; omega, fun _ => h7⟩


theorem implements1_pgSQC {t : Ty} {β : Type} [Res β] (f : ByteArray → β) (p : Pg [.ar .ba] (.sc t))
    (cv : t.T → β) (hcv : ∀ y, Res.repr (cv y) = t.rep y) (hN : pgNS p (Res.k β) ≤ NS)
    (hwf : p.wfP [inLocP] 9 = true)
    (tb : List (Nat × Mach.Reg)) (spl : List Nat)
    (hc : (rvwF.optB scB (tblG tb) (fun j => spl.contains j) (pgNS p (Res.k β)) [0, 3] [2] (pgProgS p (Res.k β))).isSome = true)
    (fits : ByteArray → Nat → Prop) (maxLen : Nat)
    (hgood : ∀ xs : ByteArray, xs.size ≤ maxLen → ∃ y E, p.GoodE [inLocP] 9 (xs, ()) y E ∧ cv y = f xs ∧
      ∀ L, 8192 ≤ L → (fits xs L ↔ pk 0 E + 1 ≤ L / 8192)) :
    Implements1PgQ (fun xs : ByteArray => xs.data.toList) Res.enc (pgCodeSC p (Res.k β) tb spl) f 8192 fits (okQ fits) maxLen := by
  refine pg_of_execOC _ Res.enc f (pgNS p (Res.k β)) hN (pgProgS p (Res.k β)) tb spl hc wlOf
    (wlOf_le _ hN) maxLen false fits (okQ fits) ?_
  intro a out tbl env b L h1 h2 h4 hb hb1 hb2 hL h8 hmax hlt hout hol htl
  have hsz : a.data.toList.length = a.size := Array.length_toList
  obtain ⟨y, E, hg, hy, hfit⟩ := hgood a (by rw [← hsz]; exact hmax)
  have hcap := capCode_ok env [a.data.toList.map (·.toBitVec), out] [tbl] b L h2 h4 hL (by omega)
  have htl' : tbl.length = (L / 8192 - 1) * P := htl
  obtain ⟨σ', out', hex', hh, hr⟩ := wholeS_ok (L / 8192 - 1) f p cv hcv a (env.set vCap (rN ((L / 8192 - 1) * P))) out tbl
    y E (by rw [set_ne (show 1 ≠ vCap by decide)]; exact h1) (by rw [← hsz]; exact hlt) (by rw [htl']; unfold P; omega)
    (by rw [htl']; exact Nat.le_refl _) (by simp only [set_eq]) hwf hg hy hout
  refine ⟨σ', out', flatG_exec _ (.seq hcap hex'), hh, ?_, ?_, ?_, ?_⟩
  · rcases hr with ⟨-, -, hd, -⟩ | ⟨-, -, rfl, -⟩
    · exact hd
    · rfl
  · intro hf
    rcases hr with ⟨hp, ht, hd, -⟩ | ⟨hp, -, -, -⟩
    · exact ⟨ht, fun h => nomatch h⟩
    · have := (hfit L hL).1 hf; omega
  · intro hf
    rcases hr with ⟨hp, -, -⟩ | ⟨-, h1', -⟩
    · exact absurd ((hfit L hL).2 (by omega)) hf
    · exact h1'
  · rcases hr with ⟨hp, -, -, h7⟩ | ⟨hp, -, -, h7⟩
    · exact ⟨fun _ => h7, fun hf => absurd ((hfit L hL).2 (by omega)) hf⟩
    · exact ⟨fun hf => by have := (hfit L hL).1 hf; omega, fun _ => h7⟩

/-- array result: the program, the elements' bytes (`outLoopP`), `a1` = their number -/
def outBaseP {k : AK} (p : Pg [.ar .ba] (.ar k)) : Nat := max (p.compP [inLocP] 9).1.maxv 9

def pgProgA {k : AK} (p : Pg [.ar .ba] (.ar k)) : MS := flatG (.seq capCode (wholeA p (outBaseP p)))

def pgNA {k : AK} (p : Pg [.ar .ba] (.ar k)) : Nat := (pgProgA p).maxv - 8

def pgCodeA {k : AK} (p : Pg [.ar .ba] (.ar k)) : List (BitVec 32) :=
  mvA4 :: compBFO (pgNA p) [0, 3] [2] (pgProgA p)

def pgCodeAC {k : AK} (p : Pg [.ar .ba] (.ar k)) (tb : List (Nat × Mach.Reg)) (spl : List Nat) : List (BitVec 32) :=
  mvA4 :: compBFC (pgNA p) [0, 3] [2] tb spl (pgProgA p)

/-- **A paged program with an array result ⇒ `Implements1Pg`** (the elements' bytes, their number in `a1`) -/
theorem implements1_pgAQ {k : AK} (f : ByteArray → k.T) (p : Pg [.ar .ba] (.ar k)) (hN : pgNA p ≤ NS)
    (hob : (p.compP [inLocP] 9).2.v < outBaseP p ∧ (p.compP [inLocP] 9).2.pt < outBaseP p)
    (hwf : p.wfP [inLocP] 9 = true) (hmwf : rvF.wfB (pgNA p) [0, 3] [2] (pgProgA p))
    (fits : ByteArray → Nat → Prop) (maxLen : Nat)
    (hgood : ∀ xs : ByteArray, xs.size ≤ maxLen → ∃ E, p.GoodE [inLocP] 9 (xs, ()) (f xs) E ∧
      ∀ L, 8192 ≤ L → (fits xs L ↔ pk 0 E + 1 ≤ L / 8192)) :
    Implements1PgQ (fun xs : ByteArray => xs.data.toList) (encArr k) (pgCodeA p) f 8192 fits (okQ fits) maxLen
      (retLen := true) := by
  refine pg_of_execOW _ (encArr k) f (pgNA p) hN (pgProgA p) hmwf wlOf (wlOf_le _ hN) maxLen true fits (okQ fits) ?_
  intro a out tbl env b L h1 h2 h4 hb hb1 hb2 hL h8 hmax hlt hout hol htl
  have hsz : a.data.toList.length = a.size := Array.length_toList
  obtain ⟨E, hg, hfit⟩ := hgood a (by rw [← hsz]; exact hmax)
  have hcap := capCode_ok env [a.data.toList.map (·.toBitVec), out] [tbl] b L h2 h4 hL (by omega)
  have htl' : tbl.length = (L / 8192 - 1) * P := htl
  obtain ⟨σ', out', hex', hh, hr⟩ := wholeA_ok (L / 8192 - 1) p (outBaseP p) a
    (env.set vCap (rN ((L / 8192 - 1) * P))) out tbl (f a) E ⟨Nat.le_max_right _ _, hob.1, hob.2⟩
    (by rw [set_ne (show 1 ≠ vCap by decide)]; exact h1) (by rw [← hsz]; exact hlt) (by rw [htl']; unfold P; omega)
    (by rw [htl']; exact Nat.le_refl _) (by simp only [set_eq]) hwf hg hout hol
  refine ⟨σ', out', flatG_exec _ (.seq hcap hex'), hh, ?_, ?_, ?_, ?_⟩
  · rcases hr with ⟨-, -, hd, -, -⟩ | ⟨-, -, rfl, -⟩
    · exact hd
    · rfl
  · intro hf
    rcases hr with ⟨hp, ht, hd, hl, -⟩ | ⟨hp, -, -, -⟩
    · exact ⟨ht, fun _ => by rw [hl]; rfl⟩
    · have := (hfit L hL).1 hf; omega
  · intro hf
    rcases hr with ⟨hp, -, -, -, -⟩ | ⟨-, h1', -, -⟩
    · exact absurd ((hfit L hL).2 (by omega)) hf
    · exact h1'
  · rcases hr with ⟨hp, -, -, -, h7⟩ | ⟨hp, -, -, h7⟩
    · exact ⟨fun _ => h7, fun hf => absurd ((hfit L hL).2 (by omega)) hf⟩
    · exact ⟨fun hf => by have := (hfit L hL).1 hf; omega, fun _ => h7⟩


theorem implements1_pgAQC {k : AK} (f : ByteArray → k.T) (p : Pg [.ar .ba] (.ar k)) (hN : pgNA p ≤ NS)
    (hob : (p.compP [inLocP] 9).2.v < outBaseP p ∧ (p.compP [inLocP] 9).2.pt < outBaseP p)
    (hwf : p.wfP [inLocP] 9 = true) (tb : List (Nat × Mach.Reg)) (spl : List Nat)
    (hc : (rvwF.optB scB (tblG tb) (fun j => spl.contains j) (pgNA p) [0, 3] [2] (pgProgA p)).isSome = true)
    (fits : ByteArray → Nat → Prop) (maxLen : Nat)
    (hgood : ∀ xs : ByteArray, xs.size ≤ maxLen → ∃ E, p.GoodE [inLocP] 9 (xs, ()) (f xs) E ∧
      ∀ L, 8192 ≤ L → (fits xs L ↔ pk 0 E + 1 ≤ L / 8192)) :
    Implements1PgQ (fun xs : ByteArray => xs.data.toList) (encArr k) (pgCodeAC p tb spl) f 8192 fits (okQ fits) maxLen
      (retLen := true) := by
  refine pg_of_execOC _ (encArr k) f (pgNA p) hN (pgProgA p) tb spl hc wlOf (wlOf_le _ hN) maxLen true fits (okQ fits) ?_
  intro a out tbl env b L h1 h2 h4 hb hb1 hb2 hL h8 hmax hlt hout hol htl
  have hsz : a.data.toList.length = a.size := Array.length_toList
  obtain ⟨E, hg, hfit⟩ := hgood a (by rw [← hsz]; exact hmax)
  have hcap := capCode_ok env [a.data.toList.map (·.toBitVec), out] [tbl] b L h2 h4 hL (by omega)
  have htl' : tbl.length = (L / 8192 - 1) * P := htl
  obtain ⟨σ', out', hex', hh, hr⟩ := wholeA_ok (L / 8192 - 1) p (outBaseP p) a
    (env.set vCap (rN ((L / 8192 - 1) * P))) out tbl (f a) E ⟨Nat.le_max_right _ _, hob.1, hob.2⟩
    (by rw [set_ne (show 1 ≠ vCap by decide)]; exact h1) (by rw [← hsz]; exact hlt) (by rw [htl']; unfold P; omega)
    (by rw [htl']; exact Nat.le_refl _) (by simp only [set_eq]) hwf hg hout hol
  refine ⟨σ', out', flatG_exec _ (.seq hcap hex'), hh, ?_, ?_, ?_, ?_⟩
  · rcases hr with ⟨-, -, hd, -, -⟩ | ⟨-, -, rfl, -⟩
    · exact hd
    · rfl
  · intro hf
    rcases hr with ⟨hp, ht, hd, hl, -⟩ | ⟨hp, -, -, -⟩
    · exact ⟨ht, fun _ => by rw [hl]; rfl⟩
    · have := (hfit L hL).1 hf; omega
  · intro hf
    rcases hr with ⟨hp, -, -, -, -⟩ | ⟨-, h1', -, -⟩
    · exact absurd ((hfit L hL).2 (by omega)) hf
    · exact h1'
  · rcases hr with ⟨hp, -, -, -, h7⟩ | ⟨hp, -, -, h7⟩
    · exact ⟨fun _ => h7, fun hf => absurd ((hfit L hL).2 (by omega)) hf⟩
    · exact ⟨fun hf => by have := (hfit L hL).1 hf; omega, fun _ => h7⟩

theorem implements1_pgS {t : Ty} {β : Type} [Res β] (f : ByteArray → β) (p : Pg [.ar .ba] (.sc t))
    (cv : t.T → β) (hcv : ∀ y, Res.repr (cv y) = t.rep y) (hN : pgNS p (Res.k β) ≤ NS)
    (hwf : p.wfP [inLocP] 9 = true)
    (hmwf : rvF.wfB (pgNS p (Res.k β)) [0, 3] [2] (pgProgS p (Res.k β)))
    (fits : ByteArray → Nat → Prop) (maxLen : Nat)
    (hgood : ∀ xs : ByteArray, xs.size ≤ maxLen → ∃ y E, p.GoodE [inLocP] 9 (xs, ()) y E ∧ cv y = f xs ∧
      ∀ L, 8192 ≤ L → (fits xs L ↔ pk 0 E + 1 ≤ L / 8192)) :
    Implements1Pg (fun xs : ByteArray => xs.data.toList) Res.enc (pgCodeS p (Res.k β)) f 8192 fits maxLen :=
  (implements1_pgSQ f p cv hcv hN hwf hmwf fits maxLen hgood).toPg

theorem implements1_pgA {k : AK} (f : ByteArray → k.T) (p : Pg [.ar .ba] (.ar k)) (hN : pgNA p ≤ NS)
    (hob : (p.compP [inLocP] 9).2.v < outBaseP p ∧ (p.compP [inLocP] 9).2.pt < outBaseP p)
    (hwf : p.wfP [inLocP] 9 = true) (hmwf : rvF.wfB (pgNA p) [0, 3] [2] (pgProgA p))
    (fits : ByteArray → Nat → Prop) (maxLen : Nat)
    (hgood : ∀ xs : ByteArray, xs.size ≤ maxLen → ∃ E, p.GoodE [inLocP] 9 (xs, ()) (f xs) E ∧
      ∀ L, 8192 ≤ L → (fits xs L ↔ pk 0 E + 1 ≤ L / 8192)) :
    Implements1Pg (fun xs : ByteArray => xs.data.toList) (encArr k) (pgCodeA p) f 8192 fits maxLen
      (retLen := true) :=
  (implements1_pgAQ f p hN hob hwf hmwf fits maxLen hgood).toPg

end Proven.WA
