/- The extended interface `MachineF` (`Compiler/Frame.lean`, with `mid.patch`) on DeepMind's AArch64 semantics:
`apcF L : MachineF`.  Frame register `x28` (not an abstract register; the abstract registers are x0..x7, x9..x15).
`enter n` = `sub x9, sp, #8(n+1); str x28, [x9]; mov x28, x9; str xzr, [x28, #8(j+1)]` (j < n),
`leave` = `ldr x28, [x28]`, slot `j` = `[x28, #8(j+1)]` (`ldr`/`str`), `ld`/`sd` = `ldr xd, [xa]` / `str xv, [xa]`.
The frame is `[sp - 8(n+1), sp)` (sp itself is never moved; `enterOK` asks sp 8-aligned and the frame inside the
writable data range). -/
import Apc.Mem8
namespace Proven.Apc
open Proven Proven.Mach

/-! ## Words -/
def wLdr (t n k : Nat) : BitVec 32 := BitVec.ofNat 32 (0xF9400000 ||| k <<< 10 ||| n <<< 5 ||| t)   -- ldr xt, [xn, #8k]
def wStr (t n k : Nat) : BitVec 32 := BitVec.ofNat 32 (0xF9000000 ||| k <<< 10 ||| n <<< 5 ||| t)   -- str xt, [xn, #8k]
def wSubSp (n : Nat) : BitVec 32 := BitVec.ofNat 32 (0xD1000000 ||| (8 * (n + 1)) <<< 10 ||| 31 <<< 5 ||| 9)  -- sub x9, sp, #8(n+1)
def wMovFr : BitVec 32 := rrr 0xAA000000 28 31 9                                                      -- mov x28, x9
def zs (n : Nat) : List (BitVec 32) := (List.range n).map fun j => wStr 31 28 (j + 1)              -- str xzr, [x28, #8(j+1)]

def encX : FOp → List (BitVec 32)
  | .enter n => [wSubSp n, wStr 28 9 0, wMovFr] ++ zs n
  | .leave => [wLdr 28 28 0]
  | .ldS d j => [wLdr (xn d) 28 (j + 1)]
  | .stS j v => [wStr (xn v) 28 (j + 1)]
  | .ld d a => [wLdr (xn d) (xn a) 0]
  | .sd v a => [wStr (xn v) (xn a) 0]

/-! ## Decoding (by enumeration) -/
theorem dec_ldS : ∀ (d : Mach.Reg) (j : Fin 16), Arm64.decode (wLdr (xn d) 28 (j.val + 1)) =
    some (.ldr .W64 .X64 false (.gpr (xr d)) (.Offset (.gpr 28#5) (BitVec.ofNat 64 (8 * (j.val + 1))))) := by
  decide +kernel
theorem dec_stS : ∀ (v : Mach.Reg) (j : Fin 16), Arm64.decode (wStr (xn v) 28 (j.val + 1)) =
    some (.str .X64 (.gpr (xr v)) (.Offset (.gpr 28#5) (BitVec.ofNat 64 (8 * (j.val + 1))))) := by
  decide +kernel
theorem dec_ld : ∀ (d a : Mach.Reg), Arm64.decode (wLdr (xn d) (xn a) 0) =
    some (.ldr .W64 .X64 false (.gpr (xr d)) (.Offset (.gpr (xr a)) 0#64)) := by decide +kernel
theorem dec_sd : ∀ (v a : Mach.Reg), Arm64.decode (wStr (xn v) (xn a) 0) =
    some (.str .X64 (.gpr (xr v)) (.Offset (.gpr (xr a)) 0#64)) := by decide +kernel
theorem dec_leave : Arm64.decode (wLdr 28 28 0) = some (.ldr .W64 .X64 false (.gpr 28#5) (.Offset (.gpr 28#5) 0#64)) := by
  decide
theorem dec_subsp : ∀ n : Fin 17, Arm64.decode (wSubSp n.val) =
    some (.addSubImm .W64 .SUB (.gpr 9#5) .sp (BitVec.ofNat 12 (8 * (n.val + 1))) false) := by decide +kernel
theorem dec_str28 : Arm64.decode (wStr 28 9 0) = some (.str .X64 (.gpr 28#5) (.Offset (.gpr 9#5) 0#64)) := by decide
theorem dec_movfr : Arm64.decode wMovFr = some (.logicalShift .W64 .ORR (.gpr 28#5) .xzr (.gpr 9#5) .LSL 0) := by decide
theorem dec_zs : ∀ j : Fin 16, Arm64.decode (wStr 31 28 (j.val + 1)) =
    some (.str .X64 .xzr (.Offset (.gpr 28#5) (BitVec.ofNat 64 (8 * (j.val + 1))))) := by decide +kernel

/-! ## Evaluation -/
theorem ev_ldr (t n : BitVec 5) (off : BitVec 64) (s : Arm64.State) (ht : (t == 31#5) = false) (hn : (n == 31#5) = false)
    (hr : s.mem.canRead (s.regs.read n + off) 8 = true) :
    P.evalInst (.ldr .W64 .X64 false (.gpr t) (.Offset (.gpr n) off)) s =
      { s with regs := s.regs.write t (s.mem.read64 (s.regs.read n + off)), pc := s.pc + 4#64 } := by
  have hr' : s.mem.canRead (s.regs.regs n + off) 8 = true := hr
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.evalAddrMode,
    Arm64.State.readReg64, Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.Memory.readSized,
    ht, hn, Arm64.RegFile.read, hr', Arm64.MemWidth.bytes, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg]

theorem ev_str (t n : BitVec 5) (off : BitVec 64) (s : Arm64.State) (ht : (t == 31#5) = false) (hn : (n == 31#5) = false)
    (hw : s.mem.canWrite (s.regs.read n + off) 8 = true) :
    P.evalInst (.str .X64 (.gpr t) (.Offset (.gpr n) off)) s =
      { s with mem := s.mem.write64 (s.regs.read n + off) (s.regs.read t), pc := s.pc + 4#64 } := by
  have hw' : s.mem.canWrite (s.regs.regs n + off) 8 = true := hw
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.evalAddrMode,
    Arm64.State.readReg64, Arm64.State.setMem, Arm64.State.advancePC, Arm64.Memory.writeSized, ht, hn,
    Arm64.RegFile.read, hw', Arm64.MemWidth.bytes, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg]

theorem ev_strz (n : BitVec 5) (off : BitVec 64) (s : Arm64.State) (hn : (n == 31#5) = false)
    (hw : s.mem.canWrite (s.regs.read n + off) 8 = true) :
    P.evalInst (.str .X64 .xzr (.Offset (.gpr n) off)) s =
      { s with mem := s.mem.write64 (s.regs.read n + off) 0#64, pc := s.pc + 4#64 } := by
  have hw' : s.mem.canWrite (s.regs.regs n + off) 8 = true := hw
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.evalAddrMode,
    Arm64.State.readReg64, Arm64.State.setMem, Arm64.State.advancePC, Arm64.Memory.writeSized, hn,
    Arm64.RegFile.read, hw', Arm64.MemWidth.bytes, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg]

theorem ev_movr (t n : BitVec 5) (s : Arm64.State) (ht : (t == 31#5) = false) (hn : (n == 31#5) = false) :
    P.evalInst (.logicalShift .W64 .ORR (.gpr t) .xzr (.gpr n) .LSL 0) s =
      { s with regs := s.regs.write t (s.regs.read n), pc := s.pc + 4#64 } := by
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg, Arm64.State.readReg64,
    Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.evalLogical, Arm64.shiftVal,
    Arm64.shift64, ht, hn, Arm64.RegFile.read]

theorem ev_subsp (k : Nat) (hk : k < 4096) (s : Arm64.State) :
    P.evalInst (.addSubImm .W64 .SUB (.gpr 9#5) .sp (BitVec.ofNat 12 k) false) s =
      upd s 0 (s.sp - BitVec.ofNat 64 k) s.pstate := by
  evsimp
  rw [show xr 0 = 9#5 from rfl]; congr 2; apply BitVec.eq_of_toNat_eq; simp; omega

/-! ## The instance data -/
theorem xr_ne28 : ∀ a : Mach.Reg, xr a ≠ 28#5 := by decide
theorem xr_ne9 : ∀ a : Mach.Reg, 1 ≤ a.val → xr a ≠ 9#5 := by decide

def frameAt (s : Arm64.State) (n : Nat) : Nat := s.sp.toNat - 8 * (n + 1)
/-- `enter n`: at most 16 slots, `sp` 8-aligned, the frame `[sp - 8(n+1), sp)` inside the data range -/
def enterOK (L : Lay) (s : Arm64.State) (n : Nat) : Prop :=
  n ≤ 16 ∧ s.sp.toNat % 8 = 0 ∧ 8 * (n + 1) ≤ s.sp.toNat ∧ L.dLo ≤ frameAt s n ∧ frameAt s n + 8 * (n + 1) ≤ L.dHi ∧
    L.dHi < 2 ^ 64
def keepFS : Arm64.State → Arm64.State → Prop := keepX (· = 28#5)

theorem bv_toNat_add {a : BitVec 64} {k : Nat} (h : a.toNat + k < 2 ^ 64) : (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]; exact Nat.mod_eq_of_lt h

/-- one load step: `xt := read64 (xn + off)` -/
theorem ldr_run {L : Lay} {s : Arm64.State} {pc : BitVec 64} {w : BitVec 32} {t n : BitVec 5} {off : BitVec 64} {v : BitVec 64}
    (h : (base L).At s pc [w]) (hd : Arm64.decode w = some (.ldr .W64 .X64 false (.gpr t) (.Offset (.gpr n) off)))
    (ht : (t == 31#5) = false) (hn : (n == 31#5) = false) (ha : (s.regs.read n + off).toNat + 8 < 2 ^ 64)
    (hb : bytes (memV s) (s.regs.read n + off).toNat 8 = (le8 v).map some) {Q : Arm64.State → Prop}
    (hq : Q { s with regs := s.regs.write t v, pc := s.pc + 4#64 }) : runsTo s Q := by
  obtain ⟨hr, hv⟩ := read64_of hb
  refine run1 h hd ?_
  rw [ev_ldr t n off s ht hn hr, hv]; exact hq

/-- one store step: the 8 bytes at `xn + off` := `val` -/
theorem str_run {L : Lay} {s : Arm64.State} {pc : BitVec 64} {w : BitVec 32} {i : Arm64.Instr} {a val : BitVec 64}
    (h : (base L).At s pc [w]) (hd : Arm64.decode w = some i)
    (he : s.mem.canWrite a 8 = true → P.evalInst i s = { s with mem := s.mem.write64 a val, pc := s.pc + 4#64 })
    (ha : a.toNat + 8 < 2 ^ 64) (hw : ∀ i, i < 8 → L.dLo ≤ a.toNat + i ∧ a.toNat + i < L.dHi) :
    runsTo s fun s' => (base L).Done s s' (next pc 1) ∧ (base L).Same s s' ∧
      memV s' = Mem.wr (memV s) a.toNat (le8 val) := by
  obtain ⟨hcw, hp, hm⟩ := write64_ok h.ok ha hw val
  refine run1 h hd ?_
  rw [he hcw]
  exact ⟨⟨okS_pres h.ok rfl hp, ⟨fun _ _ _ => rfl, rfl⟩, by show s.pc + 4#64 = _; rw [h.hpc]; rfl⟩, fun _ => rfl, hm⟩

theorem e_add {a : BitVec 64} {k : Nat} (h : (base L).inRAM (a.toNat + k) 8) : (a + BitVec.ofNat 64 k).toNat = a.toNat + k :=
  bv_toNat_add (by have := h.2; simp only [base] at this; omega)

/-! ## The one-word laws -/
theorem law_ldS {L : Lay} {d : Mach.Reg} {j : Nat} {s : Arm64.State} {pc : BitVec 64} {v : BitVec 64} (_ : d.val < 7)
    (hj : j < 16) (h : (base L).At s pc (encX (.ldS d j)))
    (hr : (base L).inRAM ((s.regs.read 28#5).toNat + 8 * (j + 1)) 8) (_ : ((s.regs.read 28#5).toNat + 8 * (j + 1)) % 8 = 0)
    (hb : bytes ((base L).mem s) ((s.regs.read 28#5).toNat + 8 * (j + 1)) 8 = (le8 v).map some) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc (encX (.ldS d j)).length) ∧ (base L).Set1 s s' d v ∧
      (base L).mem s' = (base L).mem s := by
  have e := e_add (L := L) hr
  refine ldr_run h (dec_ldS d ⟨j, hj⟩) (xr_ne31 d) rfl (by rw [e]; have := hr.2; simp only [base] at this; omega)
    (by rw [e]; exact hb) ?_
  exact fin1 (post_upd h.ok h.hpc d v s.pstate)

theorem law_ld {L : Lay} {d a : Mach.Reg} {s : Arm64.State} {pc : BitVec 64} {v : BitVec 64} (_ : d.val = 0) (_ : a.val = 0)
    (h : (base L).At s pc (encX (.ld d a))) (hr : (base L).inRAM ((base L).get s a).toNat 8) (_ : ((base L).get s a).toNat % 8 = 0)
    (hb : bytes ((base L).mem s) ((base L).get s a).toNat 8 = (le8 v).map some) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc (encX (.ld d a)).length) ∧ (base L).Set1 s s' d v ∧
      (base L).mem s' = (base L).mem s := by
  have e : s.regs.read (xr a) + 0#64 = s.regs.read (xr a) := BitVec.add_zero _
  refine ldr_run h (dec_ld d a) (xr_ne31 d) (xr_ne31 a) (by rw [e]; have := hr.2; simp only [base] at this; exact
    (by simp only [getR] at this; omega)) (by rw [e]; exact hb) ?_
  exact fin1 (post_upd h.ok h.hpc d v s.pstate)

theorem law_stS {L : Lay} {j : Nat} {v : Mach.Reg} {s : Arm64.State} {pc : BitVec 64} (_ : v.val = 0) (hj : j < 16)
    (h : (base L).At s pc (encX (.stS j v))) (hr : (base L).inRAM ((s.regs.read 28#5).toNat + 8 * (j + 1)) 8)
    (_ : ((s.regs.read 28#5).toNat + 8 * (j + 1)) % 8 = 0)
    (hw : ∀ i, i < 8 → (base L).writable s ((s.regs.read 28#5).toNat + 8 * (j + 1) + i)) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc (encX (.stS j v)).length) ∧ (base L).Same s s' ∧
      (base L).mem s' = ((base L).mem s).wr ((s.regs.read 28#5).toNat + 8 * (j + 1)) (le8 ((base L).get s v)) := by
  have e := e_add (L := L) hr
  have := str_run (val := s.regs.read (xr v)) h (dec_stS v ⟨j, hj⟩) (fun hc => ev_str _ _ _ s (xr_ne31 v) rfl hc)
    (by rw [e]; have := hr.2; simp only [base] at this; omega) (fun i hi => by rw [e]; exact hw i hi)
  rw [e] at this; exact this

theorem law_sd {L : Lay} {v a : Mach.Reg} {s : Arm64.State} {pc : BitVec 64} (_ : v.val = 1) (_ : a.val = 0)
    (h : (base L).At s pc (encX (.sd v a))) (hr : (base L).inRAM ((base L).get s a).toNat 8) (_ : ((base L).get s a).toNat % 8 = 0)
    (hw : ∀ i, i < 8 → (base L).writable s (((base L).get s a).toNat + i)) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc (encX (.sd v a)).length) ∧ (base L).Same s s' ∧
      (base L).mem s' = ((base L).mem s).wr ((base L).get s a).toNat (le8 ((base L).get s v)) := by
  have e : s.regs.read (xr a) + 0#64 = s.regs.read (xr a) := BitVec.add_zero _
  have := str_run (val := s.regs.read (xr v)) h (dec_sd v a) (fun hc => ev_str _ _ _ s (xr_ne31 v) (xr_ne31 a) hc)
    (by rw [e]; have := hr.2; simp only [base] at this; exact (by simp only [getR] at this; omega))
    (fun i hi => by rw [e]; exact hw i hi)
  rw [e] at this; exact this

theorem law_leave {L : Lay} {s : Arm64.State} {pc : BitVec 64} {w : BitVec 64} (h : (base L).At s pc (encX .leave))
    (hr : (base L).inRAM (s.regs.read 28#5).toNat 8) (_ : (s.regs.read 28#5).toNat % 8 = 0)
    (hb : bytes ((base L).mem s) (s.regs.read 28#5).toNat 8 = (le8 w).map some) :
    (base L).runsTo s fun s' => (base L).ok s' ∧ keepFS s s' ∧ (base L).pcIs s' (next pc (encX .leave).length) ∧
      s'.regs.read 28#5 = w ∧ (base L).Same s s' ∧ (base L).mem s' = (base L).mem s := by
  have e : s.regs.read 28#5 + 0#64 = s.regs.read 28#5 := BitVec.add_zero _
  refine ldr_run h dec_leave rfl rfl (by rw [e]; have := hr.2; simp only [base] at this; omega) (by rw [e]; exact hb) ?_
  refine ⟨okS_of h.ok rfl rfl, ⟨fun x _ hx => ?_, rfl⟩, ?_, ?_, fun r => ?_, rfl⟩
  · simp [Arm64.RegFile.read, Arm64.RegFile.write, hx]
  · show s.pc + 4#64 = next pc 1; rw [h.hpc]; rfl
  · simp [Arm64.RegFile.read, Arm64.RegFile.write]
  · simp [base, getR, Arm64.RegFile.read, Arm64.RegFile.write, xr_ne28 r]

/-! ## `enter` -/
theorem wr_zero (M : Mem) (a x : Nat) :
    (a ≤ x → x < a + 8 → Mem.wr M a (le8 0) x = some 0#8) ∧ ((x < a ∨ a + 8 ≤ x) → Mem.wr M a (le8 0) x = M x) := by
  refine ⟨fun h1 h2 => ?_, fun h => Mem.wr_out (by rw [length_le8]; exact h)⟩
  obtain ⟨i, rfl⟩ : ∃ i, x = a + i := ⟨x - a, by omega⟩
  rw [Mem.wr_in (by rw [length_le8]; omega)]
  have : i < 8 := by omega
  simp [le8]

/-- the zeroing stores `str xzr, [x28, #8(j+1)]`, `i ≤ j < i + k` -/
theorem zs_run (L : Lay) (F : BitVec 64) : ∀ (k i : Nat) (t : Arm64.State) (q : BitVec 64), i + k ≤ 16 → okS L t →
    t.pc = q → q.toNat % 4 = 0 →
    (∀ m, m < k → instrAt L t (q + BitVec.ofNat 64 (4 * m)) (wStr 31 28 (i + m + 1))) → t.regs.read 28#5 = F →
    (∀ x, F.toNat + 8 * (i + 1) ≤ x → x < F.toNat + 8 * (i + k + 1) → L.dLo ≤ x ∧ x < L.dHi) →
    F.toNat + 8 * (i + k + 1) < 2 ^ 64 →
    ∃ t', Arm64.Steps P t t' ∧ t'.regs = t.regs ∧ t'.sp = t.sp ∧ t'.status = t.status ∧
      t'.pc = q + BitVec.ofNat 64 (4 * k) ∧ Pres t.mem t'.mem ∧
      ∀ x, (F.toNat + 8 * (i + 1) ≤ x → x < F.toNat + 8 * (i + k + 1) → memM t'.mem x = some 0#8) ∧
        ((x < F.toNat + 8 * (i + 1) ∨ F.toNat + 8 * (i + k + 1) ≤ x) → memM t'.mem x = memM t.mem x)
  | 0, i, t, q, _, _, hpc, _, _, _, _, _ =>
    ⟨t, .refl _, rfl, rfl, rfl, by rw [hpc]; simp, Pres.refl _, fun x => ⟨fun h1 h2 => by omega, fun _ => rfl⟩⟩
  | k + 1, i, t, q, hk, hok, hpc, hal, hcode, hF, hreg, hlt => by
    have hi0 := hcode 0 (by omega)
    rw [show q + BitVec.ofNat 64 (4 * 0) = q by simp, show i + 0 + 1 = i + 1 from rfl] at hi0
    have eA : (F + BitVec.ofNat 64 (8 * (i + 1))).toNat = F.toNat + 8 * (i + 1) := bv_toNat_add (by omega)
    have hw : ∀ j, j < 8 → L.dLo ≤ (F + BitVec.ofNat 64 (8 * (i + 1))).toNat + j ∧
        (F + BitVec.ofNat 64 (8 * (i + 1))).toNat + j < L.dHi := fun j hj => by
      rw [eA]; exact hreg _ (by omega) (by omega)
    obtain ⟨hcw, hp, hm⟩ := write64_ok hok (by rw [eA]; omega) hw 0#64
    have hst := exec_ok hok hpc hal hi0 (dec_zs ⟨i, by omega⟩)
    rw [ev_strz 28#5 _ t rfl (by rw [hF]; exact hcw), hF] at hst
    have hcw1 : ∀ j, j < 8 → t.mem.canWrite (F + BitVec.ofNat 64 (8 * (i + 1)) + BitVec.ofNat 64 j) 1 = true :=
      fun j hj => by rw [← ofNat_add']; exact (hok.2.2 _ (hw j hj).1 (hw j hj).2).2
    have hc := w64_code hok hcw1 0#64
    obtain ⟨t', st', r', sp', stt', pc', p', m'⟩ := zs_run L F k (i + 1)
      { t with mem := t.mem.write64 (F + BitVec.ofNat 64 (8 * (i + 1))) 0#64, pc := t.pc + 4#64 } (q + 4#64)
      (by omega) (okS_pres hok rfl hp) (by rw [hpc]) (by rw [BitVec.toNat_add]; simp; omega)
      (fun m hm => by
        have := instrAt_pres (s' := { t with mem := t.mem.write64 (F + BitVec.ofNat 64 (8 * (i + 1))) 0#64, pc := t.pc + 4#64 })
          hok hc (hcode (m + 1) (by omega))
        rw [show q + BitVec.ofNat 64 (4 * (m + 1)) = q + 4#64 + BitVec.ofNat 64 (4 * m) by
          rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega,
          show i + (m + 1) + 1 = i + 1 + m + 1 by omega] at this
        exact this) hF
      (fun x h1 h2 => hreg x (by omega) (by omega)) (by omega)
    refine ⟨t', .step hst st', r', sp', stt', ?_, hp.trans p', fun x => ⟨fun h1 h2 => ?_, fun h => ?_⟩⟩
    · rw [pc', BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    · by_cases hx : x < F.toNat + 8 * (i + 1 + 1)
      · rw [(m' x).2 (.inl hx)]; show memM (t.mem.write64 _ 0#64) x = _
        rw [hm, eA]; exact (wr_zero _ _ _).1 (by omega) (by omega)
      · exact (m' x).1 (by omega) (by omega)
    · rw [(m' x).2 (by omega)]; show memM (t.mem.write64 _ 0#64) x = _
      rw [hm, eA]; exact (wr_zero _ _ _).2 (by omega)

theorem bytes_zero8 {M : Mem} {a : Nat} (h : ∀ i, i < 8 → M (a + i) = some 0#8) : bytes M a 8 = (le8 0).map some := by
  apply List.ext_getElem (by rw [length_bytes, List.length_map, length_le8])
  intro i h1 h2
  rw [bytes_getElem, h i (by rw [length_bytes] at h1; exact h1), List.getElem_map]
  have : i < 8 := by rw [length_bytes] at h1; exact h1
  simp [le8]

theorem len_enter (n : Nat) : (encX (.enter n)).length = 3 + n := by
  simp [encX, zs]; omega

theorem law_enter {L : Lay} {n : Nat} {s : Arm64.State} {pc : BitVec 64} (hen : enterOK L s n)
    (h : (base L).At s pc (encX (.enter n))) :
    (base L).runsTo s fun s' => (base L).ok s' ∧ keepFS s s' ∧ (base L).pcIs s' (next pc (encX (.enter n)).length) ∧
      s'.regs.read 28#5 = BitVec.ofNat 64 (frameAt s n) ∧ (∀ r : Mach.Reg, 7 ≤ r.val → (base L).get s' r = (base L).get s r) ∧
      Out [⟨frameAt s n, 8 * (n + 1)⟩] ((base L).mem s) ((base L).mem s') ∧
      bytes ((base L).mem s') (frameAt s n) 8 = (le8 (s.regs.read 28#5)).map some ∧
      ∀ j, j < n → bytes ((base L).mem s') (frameAt s n + 8 * (j + 1)) 8 = (le8 0).map some := by
  obtain ⟨hn, hsp8, hspn, hlo, hhi, hd⟩ := hen
  generalize hfb : frameAt s n = fb at hlo hhi ⊢
  have hfb' : fb = s.sp.toNat - 8 * (n + 1) := hfb.symm
  have eF : (BitVec.ofNat 64 fb).toNat = fb := by simp; omega
  obtain ⟨hok, hpc, hc, hal, -, hcok⟩ := h
  rw [len_enter] at hcok; simp only [base] at hcok
  have hc' : ∀ i (hi : i < 3 + n), instrAt L s (pc + BitVec.ofNat 64 (4 * i)) ((encX (.enter n))[i]'(by rw [len_enter]; exact hi)) :=
    fun i hi => hc i _
  have i0 := hc' 0 (by omega); have i1 := hc' 1 (by omega); have i2 := hc' 2 (by omega)
  simp only [encX, List.cons_append, List.getElem_cons_zero, List.getElem_cons_succ] at i0 i1 i2
  rw [show pc + BitVec.ofNat 64 (4 * 0) = pc by simp] at i0
  have iz : ∀ m, m < n → instrAt L s (pc + BitVec.ofNat 64 (4 * (3 + m))) (wStr 31 28 (m + 1)) := fun m hm => by
    have := hc' (3 + m) (by omega)
    have e : (encX (.enter n))[3 + m]'(by rw [len_enter]; omega) = wStr 31 28 (m + 1) := by
      simp only [encX]; rw [List.getElem_append_right (by simp)]; simp [zs]
    exact e ▸ this
  have hL := L.hc
  have e4 : ∀ k, k ≤ 3 → (pc + BitVec.ofNat 64 (4 * k)).toNat = pc.toNat + 4 * k := fun k hk => by
    rw [BitVec.toNat_add]; simp; omega
  -- 1: sub x9, sp, #8(n+1)
  have st1 := exec_ok hok hpc hal i0 (dec_subsp ⟨n, by omega⟩)
  rw [ev_subsp _ (by omega)] at st1
  have eF' : s.sp - BitVec.ofNat 64 (8 * (n + 1)) = BitVec.ofNat 64 fb := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp; omega
  rw [eF'] at st1
  generalize hs1 : upd s 0 (BitVec.ofNat 64 fb) s.pstate = s1 at st1
  have ok1 : okS L s1 := by rw [← hs1]; exact okS_of hok rfl rfl
  have pc1 : s1.pc = pc + BitVec.ofNat 64 (4 * 1) := by rw [← hs1]; show s.pc + 4#64 = _; rw [show s.pc = pc from hpc]
  have r9 : s1.regs.read 9#5 = BitVec.ofNat 64 fb := by rw [← hs1]; simp [upd, xr, xn, Arm64.RegFile.read, Arm64.RegFile.write]
  have r28 : s1.regs.read 28#5 = s.regs.read 28#5 := by rw [← hs1]; simp [upd, xr, xn, Arm64.RegFile.read, Arm64.RegFile.write]
  have m1 : s1.mem = s.mem := by rw [← hs1]; rfl
  -- 2: str x28, [x9]
  have hw : ∀ j, j < 8 → L.dLo ≤ (s1.regs.read 9#5 + 0#64).toNat + j ∧ (s1.regs.read 9#5 + 0#64).toNat + j < L.dHi :=
    fun j hj => by rw [BitVec.add_zero, r9, eF]; omega
  obtain ⟨hcw2, hp2, hm2⟩ := write64_ok ok1 (by rw [BitVec.add_zero, r9, eF]; omega) hw (s1.regs.read 28#5)
  have st2 := exec_ok ok1 pc1 (by rw [e4 1 (by omega)]; omega) (instrAt_of (by rw [m1]) i1) dec_str28
  rw [ev_str 28#5 9#5 0#64 s1 rfl rfl hcw2] at st2
  generalize hs2 : ({ s1 with mem := s1.mem.write64 (s1.regs.read 9#5 + 0#64) (s1.regs.read 28#5), pc := s1.pc + 4#64 } :
    Arm64.State) = s2 at st2
  have ok2 : okS L s2 := by rw [← hs2]; exact okS_pres ok1 rfl hp2
  have hcw1 : ∀ j, j < 8 → s1.mem.canWrite (s1.regs.read 9#5 + 0#64 + BitVec.ofNat 64 j) 1 = true := fun j hj => by
    rw [← ofNat_add']; exact (ok1.2.2 _ (hw j hj).1 (hw j hj).2).2
  have hcode2 : ∀ x, L.cLo ≤ x → x < L.cHi → memM s2.mem x = memM s.mem x := fun x a b => by
    rw [← hs2, ← m1]; exact w64_code ok1 hcw1 _ x a b
  have pc2 : s2.pc = pc + BitVec.ofNat 64 (4 * 2) := by
    rw [← hs2]; show s1.pc + 4#64 = _; rw [pc1, BitVec.add_assoc]; rfl
  -- 3: mov x28, x9
  have st3 := exec_ok ok2 pc2 (by rw [e4 2 (by omega)]; omega) (instrAt_pres hok hcode2 i2) dec_movfr
  rw [ev_movr 28#5 9#5 s2 rfl rfl] at st3
  generalize hs3 : ({ s2 with regs := s2.regs.write 28#5 (s2.regs.read 9#5), pc := s2.pc + 4#64 } : Arm64.State) = s3 at st3
  have ok3 : okS L s3 := by rw [← hs3]; exact okS_of ok2 rfl rfl
  have pc3 : s3.pc = pc + BitVec.ofNat 64 (4 * 3) := by
    rw [← hs3]; show s2.pc + 4#64 = _; rw [pc2, BitVec.add_assoc]; rfl
  have g3 : s3.regs = (s.regs.write 9#5 (BitVec.ofNat 64 fb)).write 28#5 (BitVec.ofNat 64 fb) := by
    rw [← hs3, ← hs2, r9, ← hs1]; rfl
  have m3 : memM s3.mem = Mem.wr (memM s.mem) fb (le8 (s.regs.read 28#5)) := by
    rw [← hs3]; show memM s2.mem = _; rw [← hs2]; show memM (s1.mem.write64 _ _) = _
    rw [hm2, BitVec.add_zero, r9, eF, r28, m1]
  -- 4: zero the slots
  have r28' : s3.regs.read 28#5 = BitVec.ofNat 64 fb := by rw [g3]; simp [Arm64.RegFile.read, Arm64.RegFile.write]
  obtain ⟨t, st, rt, spt, stt, pct, pt, mt⟩ := zs_run L (BitVec.ofNat 64 fb) n 0 s3 (pc + BitVec.ofNat 64 (4 * 3)) (by omega)
    ok3 pc3 (by rw [e4 3 (by omega)]; omega)
    (fun m hm => by
      have := iz m hm
      rw [show pc + BitVec.ofNat 64 (4 * (3 + m)) = pc + BitVec.ofNat 64 (4 * 3) + BitVec.ofNat 64 (4 * m) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega, show m + 1 = 0 + m + 1 by omega] at this
      exact instrAt_pres hok (fun x a b => by rw [← hs3]; exact hcode2 x a b) this) r28'
    (fun x h1 h2 => by rw [eF] at h1 h2; omega) (by rw [eF]; omega)
  rw [eF] at mt
  have stt3 : s3.status = s.status := by rw [← hs3, ← hs2, ← hs1]; rfl
  have sp3 : s3.sp = s.sp := by rw [← hs3, ← hs2, ← hs1]; rfl
  have pres3 : Pres s.mem s3.mem := by rw [← hs3]; show Pres s.mem s2.mem; rw [← hs2, ← m1]; exact hp2
  have hout : ∀ x, (x < fb ∨ fb + 8 * (n + 1) ≤ x) → memM t.mem x = memM s.mem x := fun x hx => by
    rw [(mt x).2 (by omega), m3]; exact Mem.wr_out (by rw [length_le8]; omega)
  refine ⟨t, steps_trans (.step st1 (.step st2 (.step st3 (.refl _)))) st, okS_pres hok (stt.trans stt3) (pres3.trans pt),
    ⟨fun x hx hx28 => ?_, spt.trans sp3⟩, ?_, by rw [rt, r28'], fun r hr => ?_, fun x hx => ?_, ?_, fun j hj => ?_⟩
  · rw [rt, g3]
    have : x ≠ 9#5 := fun e => hx 0 (e ▸ rfl)
    simp [Arm64.RegFile.read, Arm64.RegFile.write, hx28, this]
  · show t.pc = _; rw [pct, len_enter, BitVec.add_assoc]; unfold next; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  · show t.regs.read (xr r) = s.regs.read (xr r)
    rw [rt, g3]; simp [Arm64.RegFile.read, Arm64.RegFile.write, xr_ne28 r, xr_ne9 r (by omega)]
  · simp only [List.mem_singleton, forall_eq] at hx; exact hout x hx
  · rw [show (base L).mem t = memM t.mem from rfl, bytes_congr (m := memM s3.mem) fun j hj => (mt _).2 (by omega), m3]
    have := bytes_wr_self (m := memM s.mem) (a := fb) (l := le8 (s.regs.read 28#5))
    rwa [length_le8] at this
  · exact bytes_zero8 fun i hi => (mt _).1 (by omega) (by omega)

/-- **The extended interface (frames, spill slots, 8-byte memory) on DeepMind's AArch64 semantics.** -/
def apcF (L : Lay) : MachineF where
  toMachine := apc L
  encX := encX
  fr s := s.regs.read 28#5
  keepF := keepFS
  frameAt := frameAt
  enterOK := enterOK L
  maxSlots := 16
  keepF_of_keep h := ⟨fun x hx _ => h.1 x hx id, h.2⟩
  keepF_trans h₁ h₂ := ⟨fun x hx he => (h₂.1 x hx he).trans (h₁.1 x hx he), h₂.2.trans h₁.2⟩
  keep_fr h := h.1 28#5 (fun r => xr_ne28 r) id
  keep_of_keepF h hf := ⟨fun x hx _ => if e : x = 28#5 then e ▸ hf else h.1 x hx e, h.2⟩
  keepF_ra h := h.1 30#5 (fun r => xr_ne30 r) (by decide)
  enterOK_frame := fun ⟨hn, hsp8, hspn, hlo, hhi, hd⟩ => ⟨hn, ⟨Nat.zero_le _, by show _ ≤ 2 ^ 64 - 1; omega⟩,
    by unfold frameAt; omega, fun a h1 h2 _ _ => ⟨by omega, by omega⟩⟩
  law_enter hen h _ := law_enter hen h
  law_leave := law_leave
  law_ldS := law_ldS
  law_stS := law_stS
  law_ld := law_ld
  law_sd := law_sd

end Proven.Apc
