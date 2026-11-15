/- The wide interface `Wide` / `WideF` (`Compiler/Wide.lean`, `Compiler/Opt/BFn.lean`) on
DeepMind's AArch64 semantics: `apcw L : Wide`, `apcwF L : WideF`.  Every operation takes ARBITRARY abstract
registers (decoding by enumeration, `Apc/WideDec.lean`).  Encodings: `mov` = `orr d, xzr, a`; `li` = `movz` (+ 3 `movk`); `bin` = the 3-register instruction (`ult/slt/eq` = `cmp;
cset`); `bini`: no immediate forms (`immOK = false`: the lowering puts the constant into the scratch register);
`lbu/sb/ld/sd` = `ldrb/strb/ldr/str [a]` (`offOK off := off = 0`, the only offset the selection emits);
`br c a b` = `cmp a, b|xzr; b.cond` (forward `1 ≤ n ≤ 2^18`, back `n < 2^18`); `jmp` = `b` (`n < 2^25` / back `0 < n ≤ 2^25`); `ret`;
`ldS/stS` = `ldr/str [x28, #8(j+1)]`; `enter`/`leave` as `apcF`. -/
import Apc.Frame
import Apc.WideDec
import Compiler.Opt.BFn
namespace Proven.Apc
open Proven Proven.Mach

/-- `b.cond` with a 19-bit word offset `imm` (two's complement) -/
def wBc (c : Cond) (imm : Nat) : BitVec 32 := 0x54#8 ++ BitVec.ofNat 19 imm ++ 0#1 ++ BitVec.ofNat 4 (ccN c)
/-- `b +4n` -/
def wBf (n : Nat) : BitVec 32 := 0x05#6 ++ BitVec.ofNat 26 n

theorem decBc (c : Cond) (imm : Nat) :
    Arm64.decode (wBc c imm) = some (.bCond (ccC c) (((BitVec.ofNat 19 imm).signExtend 64) <<< 2)) := by
  rw [wBc, dec_bcsym _ _ (by cases c <;> decide)]
  cases c <;> rfl
theorem decBcF (c : Cond) (n : Nat) (hn : n < 2 ^ 18) :
    Arm64.decode (wBc c n) = some (.bCond (ccC c) (BitVec.ofNat 64 (4 * n))) := by
  rw [decBc, off_fwd (w := 19) (by decide) (by decide) hn]
theorem decBcB (c : Cond) (n : Nat) (hn : n < 2 ^ 18) :
    Arm64.decode (wBc c (2 ^ 19 - (n + 1))) = some (.bCond (ccC c) (BitVec.ofNat 64 (2 ^ 64 - 4 * (n + 1)))) := by
  rw [decBc, off_back (w := 19) (by decide) (by decide) (by omega) (by omega)]
theorem decBf (n : Nat) (hn : n < 2 ^ 25) : Arm64.decode (wBf n) = some (.b (BitVec.ofNat 64 (4 * n))) := by
  rw [wBf, dec_bsym, off_fwd (w := 26) (by decide) (by decide) hn]

def wencA : WOp → List (BitVec 32)
  | .mov d a => [rrr 0xAA000000 (xn d) 31 (xn a)]
  | .li d c => liA d c
  | .bin op d a b => opW op d a b
  | .bini _ _ _ _ => []
  | .lbu d a _ => [wLdrb d a]
  | .sb v a _ => [wStrb v a]
  | .br c a b k n => [wCmpO a b, wBc c (if k then 2 ^ 19 - (n + 1) else n - 1)]
  | .jmp k n => [if k then wB n else wBf n]
  | .ret => [0xD65F03C0#32]
  | .ldS d j => [wLdr (xn d) 28 (j + 1)]
  | .stS j v => [wStr (xn v) 28 (j + 1)]
  | .ld d a _ => [wLdr (xn d) (xn a) 0]
  | .sd v a _ => [wStr (xn v) (xn a) 0]

/-! ## Evaluation, any registers -/
theorem ev_ldrbW (d a : Mach.Reg) (s : Arm64.State) (hr : s.mem.canRead (getR s a) 1 = true) :
    P.evalInst (.ldr .W32 .B8 false (.gpr (xr d)) (.Offset (.gpr (xr a)) 0#64)) s =
      upd s d ((s.mem.read8 (getR s a)).setWidth 64) s.pstate := by
  have hr' : s.mem.canRead (s.regs.regs (xr a)) 1 = true := hr
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.evalAddrMode,
    Arm64.State.readReg64, Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.writeReg32,
    Arm64.State.advancePC, Arm64.Memory.readSized, upd, getR, xr_ne31, Arm64.RegFile.read, hr', Arm64.MemWidth.bytes,
    Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg]

theorem ev_strbW (v a : Mach.Reg) (s : Arm64.State) (hw : s.mem.canWrite (getR s a) 1 = true) :
    P.evalInst (.str .B8 (.gpr (xr v)) (.Offset (.gpr (xr a)) 0#64)) s = stb s (getR s a) ((getR s v).setWidth 8) := by
  have hw' : s.mem.canWrite (s.regs.regs (xr a)) 1 = true := hw
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.evalAddrMode,
    Arm64.State.readReg64, Arm64.State.setMem, Arm64.State.advancePC, Arm64.Memory.writeSized, stb, getR, xr_ne31,
    Arm64.RegFile.read, hw', Arm64.MemWidth.bytes, Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg]

theorem ev_cmpZ (a : Mach.Reg) (s : Arm64.State) :
    P.evalInst (.addSubShift .W64 .SUBS .xzr (.gpr (xr a)) .xzr .LSL 0) s = flg s (subF (getR s a) 0) := by
  evsimp

theorem ev_bc (cc : Arm64.CondCode) (off : BitVec 64) (s : Arm64.State) :
    P.evalInst (.bCond cc off) s = { s with pc := if Arm64.ConditionHolds cc s.pstate then s.pc + off else s.pc + 4#64 } := by
  by_cases h : Arm64.ConditionHolds cc s.pstate = true <;>
    simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.setPC, Arm64.State.advancePC, h]

theorem ite01 (b : Bool) (p : Prop) [Decidable p] (h : (if b = true then 0#64 else 1#64) = (if p then 1#64 else 0#64)) :
    b = !decide p := by
  cases b <;> by_cases hp : p <;> simp_all

theorem cc_eval (c : Cond) (x y : BitVec 64) : Arm64.ConditionHolds (ccC c) (subF x y) = c.eval x y := by
  have hu := ite01 _ _ (ult_val x y); have he := ite01 _ _ (eq_val x y); have hs := ite01 _ _ (slt_val x y)
  have nlt : ∀ ps : Arm64.PState, Arm64.ConditionHolds .LT ps = !Arm64.ConditionHolds .GE ps := fun ps => by
    simp only [Arm64.ConditionHolds]; cases ps.n <;> cases ps.v <;> rfl
  have ncc : ∀ ps : Arm64.PState, Arm64.ConditionHolds .CC ps = !Arm64.ConditionHolds .CS ps := fun _ => rfl
  have neq : ∀ ps : Arm64.PState, Arm64.ConditionHolds .EQ ps = !Arm64.ConditionHolds .NE ps := fun ps => by
    simp only [Arm64.ConditionHolds, Bool.not_not]
  cases c <;> simp only [ccC, Cond.eval, nlt, ncc, neq, hu, he, hs, Bool.not_not]
  all_goals simp

/-! ## The laws -/
def immOKA (_ : Op) (_ : BitVec 64) : Bool := false
def offOKA (off : BitVec 64) : Bool := off == 0
def brOKA (k : Bool) (n : Nat) : Bool := if k then decide (n < 2 ^ 18) else decide (1 ≤ n ∧ n ≤ 2 ^ 18)
def jOKA (k : Bool) (n : Nat) : Bool := if k then decide (0 < n ∧ n ≤ 2 ^ 25) else decide (n < 2 ^ 25)

theorem w_mov {L : Lay} {d a : Mach.Reg} {s : Arm64.State} {pc : BitVec 64} (h : (base L).At s pc (wencA (.mov d a))) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc (wencA (.mov d a)).length) ∧
      (base L).Set1 s s' d ((base L).get s a) ∧ (base L).mem s' = (base L).mem s :=
  run1 h (dec_mov d a) (by rw [ev_mov]; exact fin1 (post_upd h.ok h.hpc d (getR s a) s.pstate))

theorem w_li {L : Lay} {d : Mach.Reg} {c : BitVec 64} {s : Arm64.State} {pc : BitVec 64}
    (h : (base L).At s pc (wencA (.li d c))) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc (wencA (.li d c)).length) ∧
      (base L).Set1 s s' d c ∧ (base L).mem s' = (base L).mem s := by
  exact li_ok d c h

theorem w_bin {L : Lay} {op : Op} {d a b : Mach.Reg} {s : Arm64.State} {pc : BitVec 64}
    (h : (base L).At s pc (wencA (.bin op d a b))) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc (wencA (.bin op d a b)).length) ∧
      (base L).Set1 s s' d (op.eval ((base L).get s a) ((base L).get s b)) ∧ (base L).mem s' = (base L).mem s := by
  have hok : okS L s := h.ok
  have hpc : s.pc = pc := h.hpc
  cases op
  case add => exact run1 h (decAdd3 d a b) (by rw [ev_add]; exact fin1 (post_upd hok hpc _ _ _))
  case sub => exact run1 h (decSub3 d a b) (by rw [ev_sub]; exact fin1 (post_upd hok hpc _ _ _))
  case and => exact run1 h (decAnd3 d a b) (by rw [ev_and]; exact fin1 (post_upd hok hpc _ _ _))
  case or => exact run1 h (decOr3 d a b) (by rw [ev_or]; exact fin1 (post_upd hok hpc _ _ _))
  case xor => exact run1 h (decXor3 d a b) (by rw [ev_xor]; exact fin1 (post_upd hok hpc _ _ _))
  case shl => exact run1 h (decShl3 d a b) (by rw [ev_shl]; exact fin1 (post_upd hok hpc _ _ _))
  case lshr => exact run1 h (decLshr3 d a b) (by rw [ev_lshr]; exact fin1 (post_upd hok hpc _ _ _))
  case ashr => exact run1 h (decAshr3 d a b) (by rw [ev_ashr]; exact fin1 (post_upd hok hpc _ _ _))
  case ult =>
    refine run2 h (decCmp2 a b) (decCset2 d) (ev_cmp _ _ s) ?_
    rw [ev_cset, show (flg s (subF (getR s a) (getR s b))).pstate = subF (getR s a) (getR s b) from rfl, ult_val]
    exact fin1 (post_flg_upd hok hpc _ _ _ _)
  case slt =>
    refine run2 h (decCmp2 a b) (decCset10 d) (ev_cmp _ _ s) ?_
    rw [ev_cset, show (flg s (subF (getR s a) (getR s b))).pstate = subF (getR s a) (getR s b) from rfl, slt_val]
    exact fin1 (post_flg_upd hok hpc _ _ _ _)
  case eq =>
    refine run2 h (decCmp2 a b) (decCset1 d) (ev_cmp _ _ s) ?_
    rw [ev_cset, show (flg s (subF (getR s a) (getR s b))).pstate = subF (getR s a) (getR s b) from rfl, eq_val]
    exact fin1 (post_flg_upd hok hpc _ _ _ _)

theorem off0 {off : BitVec 64} (h : offOKA off = true) : off = 0 := by simpa [offOKA] using h

theorem w_lbu {L : Lay} {d a : Mach.Reg} {off : BitVec 64} {s : Arm64.State} {pc : BitVec 64} {v : BitVec 8}
    (ho : offOKA off = true) (h : (base L).At s pc (wencA (.lbu d a off))) (_ : (base L).inRAM ((base L).get s a + off).toNat 1)
    (hm : (base L).mem s ((base L).get s a + off).toNat = some v) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc (wencA (.lbu d a off)).length) ∧
      (base L).Set1 s s' d (v.setWidth 64) ∧ (base L).mem s' = (base L).mem s := by
  obtain rfl := off0 ho
  have e0 : ∀ x : BitVec 64, x + 0 = x := fun x => by simp
  simp only [e0] at hm ⊢
  have hv : s.mem.read8 (getR s a) = v := by
    have := memV_read hm
    rwa [show BitVec.ofNat 64 ((base L).get s a).toNat = getR s a by simp [base]] at this
  refine run1 h (decLdrbW d a) ?_
  rw [ev_ldrbW d a s (memV_canRead hm), hv]
  exact fin1 (post_upd h.ok h.hpc _ _ _)

theorem w_sb {L : Lay} {v a : Mach.Reg} {off : BitVec 64} {s : Arm64.State} {pc : BitVec 64}
    (ho : offOKA off = true) (h : (base L).At s pc (wencA (.sb v a off))) (hr : (base L).writable s ((base L).get s a + off).toNat) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc (wencA (.sb v a off)).length) ∧
      (base L).Same s s' ∧ (base L).mem s' = ((base L).mem s).upd ((base L).get s a + off).toNat (((base L).get s v).setWidth 8) := by
  obtain rfl := off0 ho
  have e0 : ∀ x : BitVec 64, x + 0 = x := fun x => by simp
  simp only [e0] at hr ⊢
  have hok : okS L s := h.ok
  have hpc : s.pc = pc := h.hpc
  refine run1 h (decStrbW v a) ?_
  rw [ev_strbW v a s (wr_ok hok hr).2]
  refine ⟨⟨okS_stb hok _ _, ⟨fun _ _ _ => rfl, rfl⟩, ?_⟩, fun r => rfl, memV_stb s _ _ (wr_ok hok hr).1⟩
  show s.pc + 4#64 = next pc 1
  simp [next, hpc]

def cmpI (a : Mach.Reg) : Option Mach.Reg → Arm64.Instr
  | some b => .addSubShift .W64 .SUBS .xzr (.gpr (xr a)) (.gpr (xr b)) .LSL 0
  | none => .addSubShift .W64 .SUBS .xzr (.gpr (xr a)) .xzr .LSL 0
theorem decCmpO (a : Mach.Reg) : ∀ b, Arm64.decode (wCmpO a b) = some (cmpI a b)
  | some b => decCmp2 a b
  | none => decCmpZ a
theorem ev_cmpO {L : Lay} (a : Mach.Reg) (s : Arm64.State) : ∀ b,
    P.evalInst (cmpI a b) s = flg s (subF (getR s a) ((base L).getO s b))
  | some b => ev_cmp a b s
  | none => ev_cmpZ a s

theorem w_br {L : Lay} {c : Cond} {a : Mach.Reg} {b : Option Mach.Reg} {k : Bool} {n : Nat} {s : Arm64.State}
    {pc : BitVec 64} (hb : brOKA k n = true) (h : (base L).At s pc (wencA (.br c a b k n))) :
    (base L).runsTo s fun s' => (base L).Done s s'
        (if c.eval ((base L).get s a) ((base L).getO s b) = true then tgt pc k n else next pc 2) ∧
      (base L).Same s s' ∧ (base L).mem s' = (base L).mem s := by
  obtain ⟨hok, hpc, hal, i1, i2⟩ := at2 h
  have hco : pc.toNat + 4 * 2 ≤ 2 ^ 64 - 1 := h.codeOK.2.2
  have e4 : (pc + 4#64).toNat = pc.toNat + 4 := by rw [BitVec.toNat_add]; simp; omega
  have st1 := exec_ok hok hpc hal i1 (decCmpO a b)
  rw [ev_cmpO (L := L) a s b] at st1
  generalize hF : subF (getR s a) ((base L).getO s b) = F at st1
  have hcc : Arm64.ConditionHolds (ccC c) F = c.eval ((base L).get s a) ((base L).getO s b) := by rw [← hF, cc_eval]; rfl
  have ok1 : okS L (flg s F) := okS_of hok rfl rfl
  have pc1 : (flg s F).pc = pc + 4#64 := by show s.pc + 4#64 = _; rw [hpc]
  have al1 : (pc + 4#64).toNat % 4 = 0 := by rw [e4]; omega
  cases k
  · have hn : 1 ≤ n ∧ n ≤ 2 ^ 18 := by simpa [brOKA] using hb
    have st2 := exec_ok ok1 pc1 al1 (instrAt_of rfl i2) (decBcF c (n - 1) (by omega))
    rw [ev_bc] at st2
    refine ⟨_, .step st1 (.step st2 (.refl _)), ⟨okS_of hok rfl rfl, ⟨fun _ _ _ => rfl, rfl⟩, ?_⟩, fun r => rfl, rfl⟩
    show (if Arm64.ConditionHolds (ccC c) F = true then (flg s F).pc + _ else (flg s F).pc + 4#64) = _
    rw [hcc, pc1]
    cases c.eval ((base L).get s a) ((base L).getO s b)
    · simp only [Bool.false_eq_true, ite_false]; unfold next; rw [BitVec.add_assoc]; rfl
    · simp only [ite_true, tgt, Bool.false_eq_true, ite_false]; unfold next; rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp; omega
  · have hn : n < 2 ^ 18 := by simpa [brOKA] using hb
    have st2 := exec_ok ok1 pc1 al1 (instrAt_of rfl i2) (decBcB c n hn)
    rw [ev_bc] at st2
    refine ⟨_, .step st1 (.step st2 (.refl _)), ⟨okS_of hok rfl rfl, ⟨fun _ _ _ => rfl, rfl⟩, ?_⟩, fun r => rfl, rfl⟩
    show (if Arm64.ConditionHolds (ccC c) F = true then (flg s F).pc + _ else (flg s F).pc + 4#64) = _
    rw [hcc, pc1]
    cases c.eval ((base L).get s a) ((base L).getO s b)
    · simp only [Bool.false_eq_true, ite_false]; unfold next; rw [BitVec.add_assoc]; rfl
    · simp only [ite_true, tgt]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp; omega

theorem w_jmp {L : Lay} {k : Bool} {n : Nat} {s : Arm64.State} {pc : BitVec 64} (hj : jOKA k n = true)
    (h : (base L).At s pc (wencA (.jmp k n))) :
    (base L).runsTo s fun s' => (base L).Done s s' (tgt pc k n) ∧ (base L).Same s s' ∧ (base L).mem s' = (base L).mem s := by
  have hok : okS L s := h.ok
  have hpc : s.pc = pc := h.hpc
  cases k
  · have hn : n < 2 ^ 25 := by simpa [jOKA] using hj
    have h' : (base L).At s pc [wBf n] := h
    refine run1 h' (decBf n hn) ?_
    refine ⟨⟨hok, ⟨fun _ _ _ => rfl, rfl⟩, ?_⟩, fun r => rfl, rfl⟩
    show s.pc + BitVec.ofNat 64 (4 * n) = next pc n
    rw [hpc]; rfl
  · have hn : 0 < n ∧ n ≤ 2 ^ 25 := by simpa [jOKA] using hj
    have h' : (base L).At s pc [wB n] := h
    refine run1 h' (dec_b n hn.1 hn.2) ?_
    refine ⟨⟨hok, ⟨fun _ _ _ => rfl, rfl⟩, ?_⟩, fun r => rfl, rfl⟩
    show s.pc + BitVec.ofNat 64 (2 ^ 64 - 4 * n) = pc - BitVec.ofNat 64 (4 * n)
    have := hn.2; rw [hpc]; bv_omega

theorem w_ld {L : Lay} {d a : Mach.Reg} {off : BitVec 64} {s : Arm64.State} {pc : BitVec 64} {v : BitVec 64}
    (ho : offOKA off = true) (h : (base L).At s pc (wencA (.ld d a off))) (hr : (base L).inRAM ((base L).get s a + off).toNat 8)
    (hal : ((base L).get s a + off).toNat % 8 = 0) (hb : bytes ((base L).mem s) ((base L).get s a + off).toNat 8 = (le8 v).map some) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc (wencA (.ld d a off)).length) ∧ (base L).Set1 s s' d v ∧
      (base L).mem s' = (base L).mem s := by
  obtain rfl := off0 ho
  have e0 : ∀ x : BitVec 64, x + 0 = x := fun x => by simp
  simp only [e0] at hr hal hb ⊢
  exact law_ld h hr hal hb

theorem w_sd {L : Lay} {v a : Mach.Reg} {off : BitVec 64} {s : Arm64.State} {pc : BitVec 64}
    (ho : offOKA off = true) (h : (base L).At s pc (wencA (.sd v a off))) (hr : (base L).inRAM ((base L).get s a + off).toNat 8)
    (hal : ((base L).get s a + off).toNat % 8 = 0) (hw : ∀ i, i < 8 → (base L).writable s (((base L).get s a + off).toNat + i)) :
    (base L).runsTo s fun s' => (base L).Done s s' (next pc (wencA (.sd v a off)).length) ∧ (base L).Same s s' ∧
      (base L).mem s' = ((base L).mem s).wr ((base L).get s a + off).toNat (le8 ((base L).get s v)) := by
  obtain rfl := off0 ho
  have e0 : ∀ x : BitVec 64, x + 0 = x := fun x => by simp
  simp only [e0] at hr hal hw ⊢
  exact law_sd h hr hal hw

/-- **The wide interface on DeepMind's AArch64 semantics** (any registers). -/
def apcw (L : Lay) : Wide where
  toCore := core L
  wenc := wencA
  immOK := immOKA
  offOK := offOKA
  brOK := brOKA
  jOK := jOKA
  lenBr := 2
  lenJ := 1
  len_br _ _ _ _ _ := rfl
  len_j _ _ := rfl
  w_mov := w_mov
  w_li := w_li
  w_bin := w_bin
  w_bini h := absurd h (by simp [immOKA])
  w_lbu := w_lbu
  w_sb := w_sb
  w_br := w_br
  w_jmp := w_jmp
  w_ret := law_ret
  fr s := s.regs.read 28#5
  maxSlots := 16
  keep_fr h := h.1 28#5 (fun r => xr_ne28 r) id
  w_ldS := law_ldS
  w_stS := law_stS
  w_ld := w_ld
  w_sd := w_sd

/-- **... with frames** (`enter`/`leave` of `apcF`). -/
def apcwF (L : Lay) : WideF where
  toWide := apcw L
  encE n := encX (.enter n)
  encL := encX .leave
  keepF := keepFS
  frameAt := frameAt
  enterOK := enterOK L
  keepF_of_keep := (apcF L).keepF_of_keep
  keepF_trans := (apcF L).keepF_trans
  keep_of_keepF := (apcF L).keep_of_keepF
  keepF_ra := (apcF L).keepF_ra
  enterOK_frame := (apcF L).enterOK_frame
  f_enter hen h _ := law_enter hen h
  f_leave := law_leave

end Proven.Apc
