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

theorem fin1 {L : Lay} {s s' : Arm64.State} {pc' : BitVec 64} {d : Mach.Reg} {v : BitVec 64}
    (h : (okS L s' ∧ keepS s s' ∧ s'.pc = pc') ∧ (∀ r, getR s' r = if r = d then v else getR s r) ∧ memV s' = memV s) :
    (base L).Done s s' pc' ∧ (base L).Set1 s s' d v ∧ (base L).mem s' = (base L).mem s :=
  ⟨⟨h.1.1, h.1.2.1, h.1.2.2⟩, h.2.1, h.2.2⟩

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
  exact fin1 (post_upd hok hpc d (getR s a) s.pstate)

theorem law_ret {L : Lay} {s : Arm64.State} {pc : BitVec 64} (_ : (base L).retOK ((base L).ra s))
    (h : (base L).At s pc ((base L).enc .ret)) :
    (base L).runsTo s fun s' => (base L).Done s s' ((base L).ra s) ∧ (base L).Same s s' ∧
      (base L).mem s' = (base L).mem s := by
  obtain ⟨hok, hpc, -⟩ := at1 h
  refine run1 h dec_ret ?_
  refine ⟨⟨hok, ⟨rfl, rfl⟩, ?_⟩, fun r => rfl, rfl⟩
  simp [base, Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg64, Arm64.State.setPC, Arm64.RegFile.read]

/-! ## `bin` -/
def toR (d : Fin 10) : Mach.Reg := ⟨d.val, by omega⟩
def sucR (d : Fin 10) : Mach.Reg := ⟨d.val + 1, by omega⟩

/-- NZCV after `cmp x, y` -/
def subF (x y : BitVec 64) : Arm64.PState :=
  { n := (x - y).msb, z := x - y == 0#64, c := decide (y.toNat ≤ x.toNat),
    v := (1#65 + (~~~BitVec.signExtend 65 y + BitVec.signExtend 65 x)).msb != (x - y).msb }
/-- flags := `ps`, PC + 4 -/
def flg (s : Arm64.State) (ps : Arm64.PState) : Arm64.State := { s with pstate := ps, pc := s.pc + 4#64 }

macro "evsimp" : tactic => `(tactic|
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg, Arm64.State.readReg64,
    Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.State.setPState, Arm64.evalLogical,
    Arm64.evalAddSub, Arm64.AddWithCarry64, Arm64.shiftVal, Arm64.shift64, upd, flg, subF, getR, xr_ne31,
    Arm64.RegFile.read, add_res, sub_res, sub_c, imm0_res, imm0_c, imm0_v, Op.eval])

theorem dec_add : ∀ d : Fin 10, Arm64.decode (rrr 0x8B000000 (xn (toR d)) (xn (toR d)) (xn (sucR d))) =
    some (.addSubShift .W64 .ADD (.gpr (xr (toR d))) (.gpr (xr (toR d))) (.gpr (xr (sucR d))) .LSL 0) := by decide
theorem dec_sub : ∀ d : Fin 10, Arm64.decode (rrr 0xCB000000 (xn (toR d)) (xn (toR d)) (xn (sucR d))) =
    some (.addSubShift .W64 .SUB (.gpr (xr (toR d))) (.gpr (xr (toR d))) (.gpr (xr (sucR d))) .LSL 0) := by decide
theorem dec_and : ∀ d : Fin 10, Arm64.decode (rrr 0x8A000000 (xn (toR d)) (xn (toR d)) (xn (sucR d))) =
    some (.logicalShift .W64 .AND (.gpr (xr (toR d))) (.gpr (xr (toR d))) (.gpr (xr (sucR d))) .LSL 0) := by decide
theorem dec_or : ∀ d : Fin 10, Arm64.decode (rrr 0xAA000000 (xn (toR d)) (xn (toR d)) (xn (sucR d))) =
    some (.logicalShift .W64 .ORR (.gpr (xr (toR d))) (.gpr (xr (toR d))) (.gpr (xr (sucR d))) .LSL 0) := by decide
theorem dec_xor : ∀ d : Fin 10, Arm64.decode (rrr 0xCA000000 (xn (toR d)) (xn (toR d)) (xn (sucR d))) =
    some (.logicalShift .W64 .EOR (.gpr (xr (toR d))) (.gpr (xr (toR d))) (.gpr (xr (sucR d))) .LSL 0) := by decide
theorem dec_shl : ∀ d : Fin 10, Arm64.decode (rrr 0x9AC02000 (xn (toR d)) (xn (toR d)) (xn (sucR d))) =
    some (.dataProc2 .W64 .LSLV (.gpr (xr (toR d))) (.gpr (xr (toR d))) (.gpr (xr (sucR d)))) := by decide
theorem dec_lshr : ∀ d : Fin 10, Arm64.decode (rrr 0x9AC02400 (xn (toR d)) (xn (toR d)) (xn (sucR d))) =
    some (.dataProc2 .W64 .LSRV (.gpr (xr (toR d))) (.gpr (xr (toR d))) (.gpr (xr (sucR d)))) := by decide
theorem dec_ashr : ∀ d : Fin 10, Arm64.decode (rrr 0x9AC02800 (xn (toR d)) (xn (toR d)) (xn (sucR d))) =
    some (.dataProc2 .W64 .ASRV (.gpr (xr (toR d))) (.gpr (xr (toR d))) (.gpr (xr (sucR d)))) := by decide
theorem dec_cmp : ∀ d : Fin 10, Arm64.decode (wCmp (toR d) (sucR d)) =
    some (.addSubShift .W64 .SUBS .xzr (.gpr (xr (toR d))) (.gpr (xr (sucR d))) .LSL 0) := by decide
theorem dec_cset_lo : ∀ d : Fin 10, Arm64.decode (wCset 2 (toR d)) =
    some (.condSelect .W64 .CSINC (.gpr (xr (toR d))) .xzr .xzr .CS) := by decide
theorem dec_cset_lt : ∀ d : Fin 10, Arm64.decode (wCset 10 (toR d)) =
    some (.condSelect .W64 .CSINC (.gpr (xr (toR d))) .xzr .xzr .GE) := by decide
theorem dec_cset_eq : ∀ d : Fin 10, Arm64.decode (wCset 1 (toR d)) =
    some (.condSelect .W64 .CSINC (.gpr (xr (toR d))) .xzr .xzr .NE) := by decide

theorem ev_add (d a b : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.addSubShift .W64 .ADD (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b)) .LSL 0) s =
      upd s d (Op.add.eval (getR s a) (getR s b)) s.pstate := by
  evsimp
theorem ev_sub (d a b : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.addSubShift .W64 .SUB (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b)) .LSL 0) s =
      upd s d (Op.sub.eval (getR s a) (getR s b)) s.pstate := by evsimp
theorem ev_and (d a b : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.logicalShift .W64 .AND (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b)) .LSL 0) s =
      upd s d (Op.and.eval (getR s a) (getR s b)) s.pstate := by evsimp
theorem ev_or (d a b : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.logicalShift .W64 .ORR (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b)) .LSL 0) s =
      upd s d (Op.or.eval (getR s a) (getR s b)) s.pstate := by evsimp
theorem ev_xor (d a b : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.logicalShift .W64 .EOR (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b)) .LSL 0) s =
      upd s d (Op.xor.eval (getR s a) (getR s b)) s.pstate := by evsimp
theorem ev_shl (d a b : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.dataProc2 .W64 .LSLV (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b))) s =
      upd s d (Op.shl.eval (getR s a) (getR s b)) s.pstate := by evsimp
theorem ev_lshr (d a b : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.dataProc2 .W64 .LSRV (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b))) s =
      upd s d (Op.lshr.eval (getR s a) (getR s b)) s.pstate := by evsimp
theorem ev_ashr (d a b : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.dataProc2 .W64 .ASRV (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b))) s =
      upd s d (Op.ashr.eval (getR s a) (getR s b)) s.pstate := by evsimp
theorem ev_cmp (a b : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.addSubShift .W64 .SUBS .xzr (.gpr (xr a)) (.gpr (xr b)) .LSL 0) s =
      flg s (subF (getR s a) (getR s b)) := by
  evsimp
  first | rfl | (apply propext; exact Iff.rfl) | (congr 1) | (apply Bool.decide_congr; exact Iff.rfl)
theorem ev_cset (d : Mach.Reg) (c : Arm64.CondCode) (s : Arm64.State) :
    P.evalInst (.condSelect .W64 .CSINC (.gpr (xr d)) .xzr .xzr c) s =
      upd s d (if Arm64.ConditionHolds c s.pstate then 0#64 else 1#64) s.pstate := by evsimp

theorem okS_of {L : Lay} {s s' : Arm64.State} (h : okS L s) (hm : s'.mem = s.mem) (hs : s'.status = s.status) :
    okS L s' := by unfold okS at *; rw [hm, hs]; exact h
theorem instrAt_of {s s' : Arm64.State} {pc : BitVec 64} {w : BitVec 32} (hm : s'.mem = s.mem) (h : instrAt s pc w) :
    instrAt s' pc w := by unfold instrAt memV at *; rw [hm]; exact h

/-- unpack `At` for a two-word operation -/
theorem at2 {L : Lay} {s : Arm64.State} {pc : BitVec 64} {w₁ w₂ : BitVec 32} (h : (base L).At s pc [w₁, w₂]) :
    okS L s ∧ s.pc = pc ∧ pc.toNat % 4 = 0 ∧ L.cLo ≤ pc.toNat ∧ pc.toNat + 8 ≤ L.cHi ∧ instrAt s pc w₁ ∧
      instrAt s (pc + 4#64) w₂ := by
  obtain ⟨hok, hpc, hc, hal, hlo, hhi⟩ := h
  have h0 := hc 0 (by simp)
  have h1 := hc 1 (by simp)
  have hlo' : L.cLo ≤ pc.toNat := hlo
  have hhi' : pc.toNat + 4 * 2 ≤ L.cHi := hhi
  simp at h0 h1
  exact ⟨hok, hpc, hal, hlo', by omega, h0, h1⟩

/-- two steps, the first of which only changes flags and PC -/
theorem run2 {L : Lay} {s : Arm64.State} {pc : BitVec 64} {w₁ w₂ : BitVec 32} {i₁ i₂ : Arm64.Instr}
    (h : (base L).At s pc [w₁, w₂]) (hd₁ : Arm64.decode w₁ = some i₁) (hd₂ : Arm64.decode w₂ = some i₂)
    {ps : Arm64.PState} (e₁ : P.evalInst i₁ s = flg s ps) {Q : Arm64.State → Prop}
    (hq : Q (P.evalInst i₂ (flg s ps))) : runsTo s Q := by
  obtain ⟨hok, hpc, hal, hlo, hhi, hi₁, hi₂⟩ := at2 h
  have hlt := L.hc
  have e4 : (pc + 4#64).toNat = pc.toNat + 4 := by rw [BitVec.toNat_add]; simp; omega
  have s1 := exec_ok hok hpc hal hlo (by omega) hi₁ hd₁
  rw [e₁] at s1
  have s2 := exec_ok (s := flg s ps) (pc := pc + 4#64) (okS_of hok rfl rfl) (by simp [flg, hpc]) (by omega) (by omega)
    (by omega) (instrAt_of rfl hi₂) hd₂
  exact ⟨_, .step s1 (.step s2 (.refl _)), hq⟩

theorem post_flg_upd {L : Lay} {s : Arm64.State} {pc : BitVec 64} (hok : okS L s) (hpc : s.pc = pc) (d : Mach.Reg)
    (v : BitVec 64) (ps ps' : Arm64.PState) :
    (okS L (upd (flg s ps) d v ps') ∧ keepS s (upd (flg s ps) d v ps') ∧ (upd (flg s ps) d v ps').pc = next pc 2) ∧
      (∀ r, getR (upd (flg s ps) d v ps') r = if r = d then v else getR s r) ∧ memV (upd (flg s ps) d v ps') = memV s := by
  obtain ⟨⟨a1, a2, a3⟩, a4, a5⟩ := post_upd (L := L) (s := flg s ps) (pc := pc + 4#64) (okS_of hok rfl rfl)
    (by simp [flg, hpc]) d v ps'
  refine ⟨⟨a1, a2, ?_⟩, a4, a5⟩
  rw [a3]; simp only [next]; bv_omega

theorem ult_val (x y : BitVec 64) :
    (if Arm64.ConditionHolds .CS (subF x y) then 0#64 else 1#64) = Op.ult.eval x y := by
  simp only [Arm64.ConditionHolds, subF, Op.eval]
  by_cases h : y.toNat ≤ x.toNat
  · simp [h, BitVec.lt_def]
  · simp [h, BitVec.lt_def]
theorem eq_val (x y : BitVec 64) :
    (if Arm64.ConditionHolds .NE (subF x y) then 0#64 else 1#64) = Op.eq.eval x y := by
  simp only [Arm64.ConditionHolds, subF, Op.eval]
  by_cases h : x = y
  · subst h; simp
  · have : x - y ≠ 0#64 := fun e => h (by bv_omega)
    simp [h, this]
theorem slt_val (x y : BitVec 64) :
    (if Arm64.ConditionHolds .GE (subF x y) then 0#64 else 1#64) = Op.slt.eval x y := by
  have h1 := BitVec.toInt_lt (x := x); have h2 := BitVec.le_toInt (x := x)
  have h3 := BitVec.toInt_lt (x := y); have h4 := BitVec.le_toInt (x := y)
  simp only [Arm64.ConditionHolds, subF, Op.eval, sub_v, BitVec.slt]
  by_cases h : x.toInt < y.toInt
  · have : x.toInt - y.toInt < 0 := by omega
    cases (x - y).msb <;> simp [h, this]
  · have : ¬ x.toInt - y.toInt < 0 := by omega
    cases (x - y).msb <;> simp [h, this]

theorem law_bin {L : Lay} {op : Op} {d a b : Mach.Reg} {s : Arm64.State} {pc : BitVec 64} (hd : d.val < 10)
    (ha : a = d) (hb : b.val = d.val + 1) (h : (base L).At s pc ((base L).enc (.bin op d a b))) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc ((base L).enc (.bin op d a b)).length) ∧
      (base L).Set1 s s' d (op.eval ((base L).get s a) ((base L).get s b)) ∧ (base L).mem s' = (base L).mem s := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin 10, d = toR k := ⟨⟨d.val, hd⟩, rfl⟩
  obtain rfl : b = sucR k := Fin.ext hb
  subst ha
  have hok : okS L s := h.ok
  have hpc : s.pc = pc := h.hpc
  cases op
  case add => exact run1 h (dec_add k) (by rw [ev_add]; exact fin1 (post_upd hok hpc _ _ _))
  case sub => exact run1 h (dec_sub k) (by rw [ev_sub]; exact fin1 (post_upd hok hpc _ _ _))
  case and => exact run1 h (dec_and k) (by rw [ev_and]; exact fin1 (post_upd hok hpc _ _ _))
  case or => exact run1 h (dec_or k) (by rw [ev_or]; exact fin1 (post_upd hok hpc _ _ _))
  case xor => exact run1 h (dec_xor k) (by rw [ev_xor]; exact fin1 (post_upd hok hpc _ _ _))
  case shl => exact run1 h (dec_shl k) (by rw [ev_shl]; exact fin1 (post_upd hok hpc _ _ _))
  case lshr => exact run1 h (dec_lshr k) (by rw [ev_lshr]; exact fin1 (post_upd hok hpc _ _ _))
  case ashr => exact run1 h (dec_ashr k) (by rw [ev_ashr]; exact fin1 (post_upd hok hpc _ _ _))
  case ult =>
    refine run2 h (dec_cmp k) (dec_cset_lo k) (ev_cmp _ _ s) ?_
    rw [ev_cset, show (flg s (subF (getR s (toR k)) (getR s (sucR k)))).pstate = subF (getR s (toR k)) (getR s (sucR k)) from rfl, ult_val]
    exact fin1 (post_flg_upd hok hpc _ _ _ _)
  case slt =>
    refine run2 h (dec_cmp k) (dec_cset_lt k) (ev_cmp _ _ s) ?_
    rw [ev_cset, show (flg s (subF (getR s (toR k)) (getR s (sucR k)))).pstate = subF (getR s (toR k)) (getR s (sucR k)) from rfl, slt_val]
    exact fin1 (post_flg_upd hok hpc _ _ _ _)
  case eq =>
    refine run2 h (dec_cmp k) (dec_cset_eq k) (ev_cmp _ _ s) ?_
    rw [ev_cset, show (flg s (subF (getR s (toR k)) (getR s (sucR k)))).pstate = subF (getR s (toR k)) (getR s (sucR k)) from rfl, eq_val]
    exact fin1 (post_flg_upd hok hpc _ _ _ _)

/-! ## `sel` -/
def r9 (d : Fin 9) (j : Fin 3) : Mach.Reg := ⟨d.val + j.val, by omega⟩
/-- NZCV after `cmp x, #0` -/
def zF (x : BitVec 64) : Arm64.PState := { n := x.msb, z := x == 0#64, c := true, v := false }
theorem dec_cmp0 : ∀ d : Fin 9, Arm64.decode (BitVec.ofNat 32 (0xF100001F ||| xn (r9 d 0) <<< 5)) =
    some (.addSubImm .W64 .SUBS .xzr (.gpr (xr (r9 d 0))) 0#12 false) := by decide
theorem dec_csel : ∀ d : Fin 9, Arm64.decode (rrr 0x9A801000 (xn (r9 d 0)) (xn (r9 d 1)) (xn (r9 d 2))) =
    some (.condSelect .W64 .CSEL (.gpr (xr (r9 d 0))) (.gpr (xr (r9 d 1))) (.gpr (xr (r9 d 2))) .NE) := by decide
theorem ev_cmp0 (c : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.addSubImm .W64 .SUBS .xzr (.gpr (xr c)) 0#12 false) s = flg s (zF (getR s c)) := by
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg, Arm64.State.readReg64,
    Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, Arm64.State.setPState,
    Arm64.evalAddSub, Arm64.AddWithCarry64, flg, zF, getR, xr_ne31,
    Arm64.RegFile.read, imm0_res, imm0_c, imm0_v]
theorem ev_csel (d a b : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.condSelect .W64 .CSEL (.gpr (xr d)) (.gpr (xr a)) (.gpr (xr b)) .NE) s =
      upd s d (if Arm64.ConditionHolds .NE s.pstate then getR s a else getR s b) s.pstate := by
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg, Arm64.State.readReg64,
    Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.advancePC, upd, getR, xr_ne31, Arm64.RegFile.read]

theorem law_sel {L : Lay} {d c a b : Mach.Reg} {s : Arm64.State} {pc : BitVec 64} (hd : d.val < 9) (hc : c = d)
    (ha : a.val = d.val + 1) (hb : b.val = d.val + 2) (h : (base L).At s pc ((base L).enc (.sel d c a b))) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc ((base L).enc (.sel d c a b)).length) ∧
      (base L).get s' d = (if (base L).get s c = 0 then (base L).get s b else (base L).get s a) ∧
      (∀ r, r ≠ d → r ≠ a → (base L).get s' r = (base L).get s r) ∧ (base L).mem s' = (base L).mem s := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin 9, d = r9 k 0 := ⟨⟨d.val, hd⟩, rfl⟩
  obtain rfl : a = r9 k 1 := Fin.ext ha
  obtain rfl : b = r9 k 2 := Fin.ext hb
  subst hc
  have hok : okS L s := h.ok
  have hpc : s.pc = pc := h.hpc
  refine run2 h (dec_cmp0 k) (dec_csel k) (ev_cmp0 _ s) ?_
  rw [ev_csel]
  obtain ⟨⟨a1, a2, a3⟩, a4, a5⟩ := post_flg_upd hok hpc (r9 k 0)
    (if Arm64.ConditionHolds .NE (flg s (zF (getR s (r9 k 0)))).pstate then getR (flg s (zF (getR s (r9 k 0)))) (r9 k 1)
      else getR (flg s (zF (getR s (r9 k 0)))) (r9 k 2)) (zF (getR s (r9 k 0))) (flg s (zF (getR s (r9 k 0)))).pstate
  refine ⟨⟨a1, a2, a3⟩, ?_, fun r hr _ => by rw [show (base L).get = getR from rfl, a4 r, Mach.ite_neg hr], a5⟩
  rw [show (base L).get = getR from rfl, a4 (r9 k 0), Mach.ite_pos rfl]
  show (if Arm64.ConditionHolds .NE (zF (getR s (r9 k 0))) then getR s (r9 k 1) else getR s (r9 k 2)) = _
  simp only [Arm64.ConditionHolds, zF]
  by_cases hz : getR s (r9 k 0) = 0#64 <;> simp [hz]

/-! ## memory: `lbu`, `sb` -/
theorem perm_w8 (m : Arm64.Memory) (a b : BitVec 64) (v : BitVec 8) : (m.write8 a v).perm b = m.perm b := by
  by_cases h : b = a
  · subst h
    simp only [Arm64.Memory.perm, Arm64.Memory.write8, Arm64.Memory.rawPerm]
    cases hc : m.cells b with
    | none => simp
    | some pv =>
      obtain ⟨p, x⟩ := pv
      cases p <;> simp [Arm64.Perm.rwx]
  · simp [Arm64.Memory.perm, Arm64.Memory.write8, h]
theorem lazy_w8 (m : Arm64.Memory) (a b : BitVec 64) (v : BitVec 8) (h : m.isLazyFree b = false) :
    (m.write8 a v).isLazyFree b = false := by
  by_cases hb : b = a
  · subst hb
    simp only [Arm64.Memory.isLazyFree, Arm64.Memory.write8, Arm64.Memory.rawPerm]
    cases hc : m.cells b with
    | none => simp
    | some pv =>
      obtain ⟨p, x⟩ := pv
      cases p <;> simp
  · simpa [Arm64.Memory.isLazyFree, Arm64.Memory.write8, hb] using h
theorem read_w8 (m : Arm64.Memory) (a b : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).read8 b = if b = a then v else m.read8 b := by
  by_cases h : b = a <;> simp [Arm64.Memory.read8, Arm64.Memory.write8, h]

theorem canExec_w8 (m : Arm64.Memory) (a b : BitVec 64) (v : BitVec 8) : (m.write8 a v).canExec b 1 = m.canExec b 1 := by
  simp [Arm64.Memory.canExec, Arm64.Memory.allPerm, perm_w8]
theorem canWrite_w8 (m : Arm64.Memory) (a b : BitVec 64) (v : BitVec 8) : (m.write8 a v).canWrite b 1 = m.canWrite b 1 := by
  simp [Arm64.Memory.canWrite, Arm64.Memory.allPerm, perm_w8]
theorem canRead_w8 (m : Arm64.Memory) (a b : BitVec 64) (v : BitVec 8) (h : m.canRead b 1 = true) :
    (m.write8 a v).canRead b 1 = true := by
  simp [Arm64.Memory.canRead, Arm64.Memory.allPerm, Arm64.Memory.allNoLazyFree, perm_w8] at h ⊢
  exact ⟨h.1, lazy_w8 m a b v h.2⟩
theorem lazy_w8_ne (m : Arm64.Memory) (a b : BitVec 64) (v : BitVec 8) (h : b ≠ a) :
    (m.write8 a v).isLazyFree b = m.isLazyFree b := by
  simp [Arm64.Memory.isLazyFree, Arm64.Memory.write8, h]
/-- conversely, away from the written byte readability is unchanged -/
theorem canRead_w8_ne (m : Arm64.Memory) (a b : BitVec 64) (v : BitVec 8) (h : b ≠ a) :
    (m.write8 a v).canRead b 1 = m.canRead b 1 := by
  simp only [Arm64.Memory.canRead, Arm64.Memory.allPerm, Arm64.Memory.allNoLazyFree, perm_w8, lazy_w8_ne _ _ _ _ h]

/-- memory := one byte written, PC + 4 -/
def stb (s : Arm64.State) (a : BitVec 64) (v : BitVec 8) : Arm64.State :=
  { s with mem := s.mem.write8 a v, pc := s.pc + 4#64 }

theorem memV_stb (s : Arm64.State) (a : BitVec 64) (v : BitVec 8) (hr : s.mem.canRead a 1 = true) :
    memV (stb s a v) = (memV s).upd a.toNat v := by
  funext x
  unfold memV Mem.upd stb
  by_cases hx : x = a.toNat
  · subst hx
    have : BitVec.ofNat 64 a.toNat = a := by simp
    simp [this, canRead_w8 _ _ _ _ hr, read_w8, a.isLt]
  · have hne : x < 2 ^ 64 → BitVec.ofNat 64 x ≠ a := fun hlt e => hx (by rw [← e]; simp; omega)
    by_cases hlt : x < 2 ^ 64
    · simp [hx, hlt, canRead_w8_ne _ _ _ _ (hne hlt), read_w8, hne hlt]
    · simp [hx, hlt]

theorem okS_stb {L : Lay} {s : Arm64.State} (h : okS L s) (a : BitVec 64) (v : BitVec 8) : okS L (stb s a v) := by
  refine ⟨h.1, fun x h1 h2 => ?_, fun x h1 h2 => ⟨?_, ?_⟩⟩
  · show (s.mem.write8 a v).canExec _ 1 = true; rw [canExec_w8]; exact h.2.1 x h1 h2
  · exact canRead_w8 _ _ _ _ (h.2.2 x h1 h2).1
  · show (s.mem.write8 a v).canWrite _ 1 = true; rw [canWrite_w8]; exact (h.2.2 x h1 h2).2

theorem dec_ldrb : Arm64.decode (BitVec.ofNat 32 (0x39400000 ||| xn 0 <<< 5 ||| xn 0)) =
    some (.ldr .W32 .B8 false (.gpr (xr 0)) (.Offset (.gpr (xr 0)) 0#64)) := by decide
theorem dec_strb : Arm64.decode (BitVec.ofNat 32 (0x39000000 ||| xn 0 <<< 5 ||| xn 1)) =
    some (.str .B8 (.gpr (xr 1)) (.Offset (.gpr (xr 0)) 0#64)) := by decide

theorem ev_ldrb (s : Arm64.State) (hr : s.mem.canRead (getR s 0) 1 = true) :
    P.evalInst (.ldr .W32 .B8 false (.gpr (xr 0)) (.Offset (.gpr (xr 0)) 0#64)) s =
      upd s 0 ((s.mem.read8 (getR s 0)).setWidth 64) s.pstate := by
  have hr' : s.mem.canRead (s.regs.regs (xr 0)) 1 = true := hr
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.evalAddrMode,
    Arm64.State.readReg64, Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.writeReg32,
    Arm64.State.advancePC, Arm64.Memory.readSized, upd, getR, xr_ne31, Arm64.RegFile.read, hr', Arm64.MemWidth.bytes, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg]

theorem ev_strb (s : Arm64.State) (hw : s.mem.canWrite (getR s 0) 1 = true) :
    P.evalInst (.str .B8 (.gpr (xr 1)) (.Offset (.gpr (xr 0)) 0#64)) s =
      stb s (getR s 0) ((getR s 1).setWidth 8) := by
  have hw' : s.mem.canWrite (s.regs.regs (xr 0)) 1 = true := hw
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.evalAddrMode,
    Arm64.State.readReg64, Arm64.State.setMem, Arm64.State.advancePC, Arm64.Memory.writeSized, stb, getR, xr_ne31,
    Arm64.RegFile.read, hw', Arm64.MemWidth.bytes, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg]


theorem dat_ok {L : Lay} {s : Arm64.State} (hok : okS L s) {x : BitVec 64} (hr : (base L).inDat x.toNat 1) :
    s.mem.canRead x 1 = true ∧ s.mem.canWrite x 1 = true := by
  have h1 : L.dLo ≤ x.toNat := hr.1
  have h2 : x.toNat + 1 ≤ L.dHi := hr.2
  have := hok.2.2 x.toNat h1 (by omega)
  rwa [show BitVec.ofNat 64 x.toNat = x by simp] at this

theorem law_lbu {L : Lay} {d a : Mach.Reg} {s : Arm64.State} {pc : BitVec 64} {v : BitVec 8} (hd : d.val = 0)
    (ha : a.val = 0) (h : (base L).At s pc ((base L).enc (.lbu d a)))
    (hr : (base L).inDat ((base L).get s a).toNat 1) (hm : (base L).mem s ((base L).get s a).toNat = some v) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc ((base L).enc (.lbu d a)).length) ∧
      (base L).Set1 s s' d (v.setWidth 64) ∧ (base L).mem s' = (base L).mem s := by
  obtain rfl : d = 0 := Fin.ext hd
  obtain rfl : a = 0 := Fin.ext ha
  have hok : okS L s := h.ok
  have hpc : s.pc = pc := h.hpc
  have hv : s.mem.read8 (getR s 0) = v := by
    have := memV_read hm
    rwa [show BitVec.ofNat 64 ((base L).get s 0).toNat = getR s 0 by simp [base]] at this
  refine run1 h dec_ldrb ?_
  rw [ev_ldrb s (dat_ok hok hr).1, hv]
  exact fin1 (post_upd hok hpc _ _ _)

theorem law_sb {L : Lay} {v a : Mach.Reg} {s : Arm64.State} {pc : BitVec 64} (hv : v.val = 1) (ha : a.val = 0)
    (h : (base L).At s pc ((base L).enc (.sb v a))) (hr : (base L).inDat ((base L).get s a).toNat 1) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc ((base L).enc (.sb v a)).length) ∧
      (base L).Same s s' ∧ (base L).mem s' = ((base L).mem s).upd ((base L).get s a).toNat (((base L).get s v).setWidth 8) := by
  obtain rfl : v = 1 := Fin.ext hv
  obtain rfl : a = 0 := Fin.ext ha
  have hok : okS L s := h.ok
  have hpc : s.pc = pc := h.hpc
  refine run1 h dec_strb ?_
  rw [ev_strb s (dat_ok hok hr).2]
  refine ⟨⟨okS_stb hok _ _, ⟨rfl, rfl⟩, ?_⟩, fun r => rfl, memV_stb s _ _ (dat_ok hok hr).1⟩
  show s.pc + 4#64 = next pc 1
  simp [next, hpc]
end Proven.Apc
