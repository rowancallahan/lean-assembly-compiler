/- Our machine interface (`Compiler/Iface.lean`, with the data-range proposal) on the AlphaProof-Code AArch64
user-mode semantics (google-deepmind/code-verification b0f729a, `Arm64.Step`). -/
import Arm64
import Compiler.Arr
import Apc.Flags
namespace Proven.Apc
open Proven Proven.Mach

/-- layout: code in `[cLo, cHi)` (mapped executable), data in `[dLo, dHi)` (mapped readable + writable) -/
structure Lay where
  cLo : Nat
  cHi : Nat
  dLo : Nat
  dHi : Nat
  hc : cHi < 2 ^ 64
  hd : dHi < 2 ^ 64

/-- hook-free program, every `svc` traps -/
def P : Arm64.Program := Arm64.Program.ofSvc Arm64.noSyscalls

def xn (r : Mach.Reg) : Nat :=
  match r.val with
  | 0 => 9 | 1 => 10 | 2 => 11 | 3 => 12 | 4 => 13 | 5 => 14 | 6 => 15 | 7 => 4 | 8 => 5 | 9 => 6 | 10 => 7
  | 11 => 0 | 12 => 1 | 13 => 2 | _ => 3
def xr (r : Mach.Reg) : BitVec 5 := BitVec.ofNat 5 (xn r)
theorem xr_inj : ∀ a b : Mach.Reg, xr a = xr b → a = b := by decide
theorem xr_ne30 : ∀ a : Mach.Reg, xr a ≠ 30#5 := by decide
theorem xr_ne31 : ∀ a : Mach.Reg, (xr a == 31#5) = false := by decide

/-- the bytes our interface sees: readable bytes -/
def memV (s : Arm64.State) : Mem := fun a =>
  if a < 2 ^ 64 ∧ s.mem.canRead (BitVec.ofNat 64 a) 1 = true then some (s.mem.read8 (BitVec.ofNat 64 a)) else none
def instrAt (s : Arm64.State) (pc : BitVec 64) (w : BitVec 32) : Prop :=
  ∀ j, j < 4 → memV s (pc.toNat + j) = some (w.extractLsb' (8 * j) 8)
def okS (L : Lay) (s : Arm64.State) : Prop :=
  s.status = .Running ∧ (∀ a, L.cLo ≤ a → a < L.cHi → s.mem.canExec (BitVec.ofNat 64 a) 1 = true) ∧
  (∀ a, L.dLo ≤ a → a < L.dHi → s.mem.canRead (BitVec.ofNat 64 a) 1 = true ∧ s.mem.canWrite (BitVec.ofNat 64 a) 1 = true)
def keepS (s s' : Arm64.State) : Prop := s'.regs.read 30#5 = s.regs.read 30#5 ∧ s'.sp = s.sp
def getR (s : Arm64.State) (r : Mach.Reg) : BitVec 64 := s.regs.read (xr r)
def runsTo (s : Arm64.State) (Q : Arm64.State → Prop) : Prop := ∃ s', Arm64.Steps P s s' ∧ Q s'

theorem steps_trans {s₁ s₂ s₃ : Arm64.State} (h : Arm64.Steps P s₁ s₂) (h' : Arm64.Steps P s₂ s₃) : Arm64.Steps P s₁ s₃ := by
  induction h with
  | refl => exact h'
  | step h1 _ ih => exact .step h1 (ih h')

theorem bytes4 (w : BitVec 32) :
    w.extractLsb' 24 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 0 8 = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  have hi' : i < 32 := hi
  by_cases h1 : i < 8
  · simp [h1]
  · by_cases h2 : i < 16
    · simp [h1, show i - 8 < 8 by omega, show 8 + (i - 8) = i by omega]
    · by_cases h3 : i < 24
      · simp [h1, show ¬ i - 8 < 8 by omega, show i - 8 - 8 < 8 by omega, show 16 + (i - 8 - 8) = i by omega]
      · simp [h1, show ¬ i - 8 < 8 by omega, show ¬ i - 8 - 8 < 8 by omega, show i - 8 - 8 - 8 < 8 by omega,
          show 24 + (i - 8 - 8 - 8) = i by omega]

theorem memV_read {s : Arm64.State} {a : Nat} {b : BitVec 8} (h : memV s a = some b) :
    s.mem.read8 (BitVec.ofNat 64 a) = b := by
  unfold memV at h; split at h
  · exact Option.some.inj h
  · exact absurd h (by simp)

theorem instr_read32 {s : Arm64.State} {pc : BitVec 64} {w : BitVec 32} (h : instrAt s pc w) : s.mem.read32 pc = w := by
  have e : ∀ j : Nat, pc + BitVec.ofNat 64 j = BitVec.ofNat 64 (pc.toNat + j) := fun j => by
    apply BitVec.eq_of_toNat_eq; simp
  have h0 := memV_read (h 0 (by omega)); have h1 := memV_read (h 1 (by omega))
  have h2 := memV_read (h 2 (by omega)); have h3 := memV_read (h 3 (by omega))
  rw [← e] at h0 h1 h2 h3
  unfold Arm64.Memory.read32
  simp only [h0, h1, h2, h3]
  exact bytes4 w

/-! ## Encoding -/
def rrr (base rd rn rm : Nat) : BitVec 32 := BitVec.ofNat 32 (base ||| rm <<< 16 ||| rn <<< 5 ||| rd)
def wCmp (a b : Mach.Reg) : BitVec 32 := rrr 0xEB000000 31 (xn a) (xn b)             -- cmp xa, xb
def wCset (inv : Nat) (d : Mach.Reg) : BitVec 32 := rrr (0x9A800400 ||| inv <<< 12) (xn d) 31 31  -- cset xd, !inv
def opW (op : Op) (d a b : Mach.Reg) : List (BitVec 32) :=
  let r base := [rrr base (xn d) (xn a) (xn b)]
  match op with
  | .add => r 0x8B000000 | .sub => r 0xCB000000 | .and => r 0x8A000000 | .or => r 0xAA000000
  | .xor => r 0xCA000000 | .shl => r 0x9AC02000 | .lshr => r 0x9AC02400 | .ashr => r 0x9AC02800
  | .ult => [wCmp a b, wCset 2 d] | .slt => [wCmp a b, wCset 10 d] | .eq => [wCmp a b, wCset 1 d]
/-- `movz` / `movk` with halfword index in the 11-bit opcode -/
def wMov (opc : BitVec 11) (d : Mach.Reg) (imm : BitVec 16) : BitVec 32 := opc ++ imm ++ xr d
def wCbz (c : Mach.Reg) (n : Nat) : BitVec 32 := 0xB4#8 ++ BitVec.ofNat 19 n ++ xr c       -- cbz xc, +4n
def wB (n : Nat) : BitVec 32 := 0x05#6 ++ BitVec.ofNat 26 (2 ^ 26 - n)                      -- b -4n
def enc : AOp → List (BitVec 32)
  | .mov d a => [rrr 0xAA000000 (xn d) 31 (xn a)]
  | .li d c => [wMov 0x694#11 d (c.extractLsb' 0 16), wMov 0x795#11 d (c.extractLsb' 16 16),
      wMov 0x796#11 d (c.extractLsb' 32 16), wMov 0x797#11 d (c.extractLsb' 48 16)]
  | .bin op d a b => opW op d a b
  | .sel d c a b => [BitVec.ofNat 32 (0xF100001F ||| xn c <<< 5), rrr 0x9A801000 (xn d) (xn a) (xn b)]
  | .lbu d a => [BitVec.ofNat 32 (0x39400000 ||| xn a <<< 5 ||| xn d)]
  | .sb v a => [BitVec.ofNat 32 (0x39000000 ||| xn a <<< 5 ||| xn v)]
  | .bz c n => [wCbz c n]
  | .jmp n => [wB n]
  | .ret => [0xD65F03C0#32]

/-! ## The instance data -/
def base (L : Lay) : Base where
  S := Arm64.State
  runsTo := runsTo
  ok := okS L
  keep := keepS
  pcIs s pc := s.pc = pc
  get := getR
  mem := memV
  ra s := s.regs.read 30#5
  retOK _ := True
  instrAt := instrAt
  ramLo := L.cLo
  ramHi := L.cHi
  datLo := L.dLo
  datHi := L.dHi
  bzOK n := n < 2 ^ 18
  jmpOK n := 0 < n ∧ n ≤ 2 ^ 25
  enc := enc
  lenBz := 1
  lenJmp := 1

def core (L : Lay) : Core where
  toBase := base L
  runsTo_of h := ⟨_, .refl _, h⟩
  runsTo_trans := fun ⟨s₁, h₁, p₁⟩ h => let ⟨s₂, h₂, p₂⟩ := h s₁ p₁; ⟨s₂, steps_trans h₁ h₂, p₂⟩
  keep_refl _ := ⟨rfl, rfl⟩
  keep_trans h₁ h₂ := ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩
  keep_ra h := h.1
  instrAt_frame h hi := fun j hj => (h j hj).trans (hi j hj)
  ramHi_lt := L.hc
  datHi_lt := L.hd
  len_bz _ _ := rfl
  len_jmp _ := rfl

/-! ## One step -/
theorem exec_ok {L : Lay} {s : Arm64.State} {pc : BitVec 64} {w : BitVec 32} {i : Arm64.Instr}
    (hok : okS L s) (hpc : s.pc = pc) (hal : pc.toNat % 4 = 0) (hlo : L.cLo ≤ pc.toNat) (hhi : pc.toNat + 4 ≤ L.cHi)
    (hi : instrAt s pc w) (hd : Arm64.decode w = some i) : Arm64.Step P s (P.evalInst i s) := by
  refine .exec hok.1 ?_
  have he : P.externAt? s.pc = none := rfl
  have e : ∀ j : Nat, pc + BitVec.ofNat 64 j = BitVec.ofNat 64 (pc.toNat + j) := fun j => by
    apply BitVec.eq_of_toNat_eq; simp
  have g : ∀ j, j < 4 → s.mem.canExec (pc + BitVec.ofNat 64 j) 1 = true := fun j hj => by
    rw [e j]; exact hok.2.1 _ (by omega) (by omega)
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega); have g3 := g 3 (by omega)
  have hx : s.mem.canExec pc 4 = true := by
    simp [Arm64.Memory.canExec, Arm64.Memory.allPerm, BitVec.add_assoc] at g0 g1 g2 g3 ⊢
    exact ⟨g0, g1, g2, g3⟩
  unfold Arm64.Program.fetchMem
  rw [he, hpc]
  simp [hal, hx, instr_read32 hi, hd]

/-- register `d` := `v`, flags := `ps`, PC + 4: the shape of every non-memory, non-branch step -/
def upd (s : Arm64.State) (d : Mach.Reg) (v : BitVec 64) (ps : Arm64.PState) : Arm64.State :=
  { s with regs := s.regs.write (xr d) v, pstate := ps, pc := s.pc + 4#64 }

theorem post_upd {L : Lay} {s : Arm64.State} {pc : BitVec 64} (hok : okS L s) (hpc : s.pc = pc) (d : Mach.Reg)
    (v : BitVec 64) (ps : Arm64.PState) :
    (okS L (upd s d v ps) ∧ keepS s (upd s d v ps) ∧ (upd s d v ps).pc = next pc 1) ∧
      (∀ r, getR (upd s d v ps) r = if r = d then v else getR s r) ∧ memV (upd s d v ps) = memV s := by
  refine ⟨⟨hok, ⟨?_, rfl⟩, ?_⟩, ?_, rfl⟩
  · simp [upd, Arm64.RegFile.read, Arm64.RegFile.write, (xr_ne30 d).symm]
  · simp [upd, next, hpc]
  · intro r
    by_cases h : r = d
    · subst h; simp [getR, upd, Arm64.RegFile.read, Arm64.RegFile.write]
    · have : xr r ≠ xr d := fun e => h (xr_inj _ _ e)
      simp [getR, upd, Arm64.RegFile.read, Arm64.RegFile.write, h, this]

/-- unpack `At` for a one-word operation -/
theorem at1 {L : Lay} {s : Arm64.State} {pc : BitVec 64} {w : BitVec 32} (h : (base L).At s pc [w]) :
    okS L s ∧ s.pc = pc ∧ pc.toNat % 4 = 0 ∧ L.cLo ≤ pc.toNat ∧ pc.toNat + 4 ≤ L.cHi ∧ instrAt s pc w := by
  obtain ⟨hok, hpc, hc, hal, hlo, hhi⟩ := h
  have h0 := hc 0 (by simp)
  have hlo' : L.cLo ≤ pc.toNat := hlo
  have hhi' : pc.toNat + 4 * 1 ≤ L.cHi := hhi
  simp at h0
  exact ⟨hok, hpc, hal, hlo', by omega, h0⟩

theorem run1 {L : Lay} {s : Arm64.State} {pc : BitVec 64} {w : BitVec 32} {i : Arm64.Instr}
    (h : (base L).At s pc [w]) (hd : Arm64.decode w = some i) {Q : Arm64.State → Prop} (hq : Q (P.evalInst i s)) :
    runsTo s Q := by
  obtain ⟨hok, hpc, hal, hlo, hhi, hi⟩ := at1 h
  exact ⟨_, .step (exec_ok hok hpc hal hlo hhi hi hd) (.refl _), hq⟩

theorem dec_mov : ∀ d a : Mach.Reg, Arm64.decode (rrr 0xAA000000 (xn d) 31 (xn a)) =
    some (.logicalShift .W64 .ORR (.gpr (xr d)) .xzr (.gpr (xr a)) .LSL 0) := by decide
theorem dec_ret : Arm64.decode 0xD65F03C0#32 = some (.ret (.gpr 30#5)) := by decide

theorem ev_mov (d a : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.logicalShift .W64 .ORR (.gpr (xr d)) .xzr (.gpr (xr a)) .LSL 0) s = upd s d (getR s a) s.pstate := by
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg, Arm64.State.readReg64,
    Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.evalLogical, Arm64.shiftVal,
    Arm64.shift64, upd, getR, xr_ne31, Arm64.RegFile.read]

theorem law_mov {L : Lay} {d a : Mach.Reg} {s : Arm64.State} {pc : BitVec 64} (_ : MovOK d a)
    (h : (base L).At s pc ((base L).enc (.mov d a))) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc ((base L).enc (.mov d a)).length) ∧
      (base L).Set1 s s' d ((base L).get s a) ∧ (base L).mem s' = (base L).mem s := by
  obtain ⟨hok, hpc, -⟩ := at1 h
  refine run1 h (dec_mov d a) ?_
  rw [ev_mov]
  obtain ⟨⟨a1, a2, a3⟩, a4, a5⟩ := post_upd hok hpc d (getR s a) s.pstate
  exact ⟨⟨a1, a2, a3⟩, a4, a5⟩

theorem law_ret {L : Lay} {s : Arm64.State} {pc : BitVec 64} (_ : (base L).retOK ((base L).ra s))
    (h : (base L).At s pc ((base L).enc .ret)) :
    (base L).runsTo s fun s' => (base L).Done s s' ((base L).ra s) ∧ (base L).Same s s' ∧
      (base L).mem s' = (base L).mem s := by
  obtain ⟨hok, hpc, -⟩ := at1 h
  refine run1 h dec_ret ?_
  refine ⟨⟨hok, ⟨rfl, rfl⟩, ?_⟩, fun r => rfl, rfl⟩
  simp [base, Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg64, Arm64.State.setPC, Arm64.RegFile.read]
end Proven.Apc
