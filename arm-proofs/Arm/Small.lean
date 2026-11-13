/- L2 machinery: a small AArch64 machine (`AState`, `armStep`), the abstraction relation `Abs` from model
states, the configuration `ArmCfg`, and the family lemmas that turn a per-word decode lemma plus a generic
execute lemma (`Arm/Exec.lean`) into "the model agrees with `armStep` on this word" (`Step`). -/
import Arm.Exec
import Arm.Flags
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

namespace ArmProof

/-! ## The small machine -/

/-- general registers `x0..x30` (`x i` for `i ≥ 31` is unused) and the NZCV flags -/
structure AState where
  x : Nat → BitVec 64
  n : Bool
  z : Bool
  c : Bool
  v : Bool

namespace AState
/-- read `x r`; `31` is `xzr` in every instruction modelled here -/
def rd (a : AState) (r : Nat) : BitVec 64 := if r = 31 then 0 else a.x r
/-- write `x d`; writes to `31` (`xzr`) are dropped -/
def setX (a : AState) (d : Nat) (v : BitVec 64) : AState :=
  if d = 31 then a else { a with x := fun i => if i = d then v else a.x i }
/-- NZCV as set by `subs _, x, y` -/
def setSub (a : AState) (x y : BitVec 64) : AState :=
  { a with n := (x - y).msb, z := x - y = 0, c := y.toNat ≤ x.toNat, v := (x - y).toInt ≠ x.toInt - y.toInt }
/-- the A64 condition `c` (ARM ARM `ConditionHolds`) -/
def cond (a : AState) (c : BitVec 4) : Bool :=
  let r := match (c >>> 1).toNat with
    | 0 => a.z | 1 => a.c | 2 => a.n | 3 => a.v | 4 => a.c && !a.z | 5 => a.n == a.v
    | 6 => a.n == a.v && !a.z | _ => true
  if c.getLsbD 0 && c != 15 then !r else r
end AState

/-- One instruction of the small machine. Covers the instructions `Arm.compile` emits (except `ret`);
any other word leaves the state unchanged (not modelled). -/
def armStep (w : BitVec 32) (a : AState) : AState :=
  let d := (w.extractLsb' 0 5).toNat
  let n := (w.extractLsb' 5 5).toNat
  let m := (w.extractLsb' 16 5).toNat
  let X := a.rd
  let imm12 : BitVec 64 := (w.extractLsb' 10 12).setWidth 64
  let is (mask v : BitVec 32) : Bool := w &&& mask == v
  if is 0xFFE0FC00 0x8B000000 then a.setX d (X n + X m)                                  -- add  xd, xn, xm
  else if is 0xFFE0FC00 0xCB000000 then a.setX d (X n - X m)                             -- sub  xd, xn, xm
  else if is 0xFFE0FC00 0xEB000000 then (a.setSub (X n) (X m)).setX d (X n - X m)        -- subs xd, xn, xm
  else if is 0xFFE0FC00 0x8A000000 then a.setX d (X n &&& X m)                           -- and  xd, xn, xm
  else if is 0xFFE0FC00 0xAA000000 then a.setX d (X n ||| X m)                           -- orr  xd, xn, xm
  else if is 0xFFE0FC00 0xCA000000 then a.setX d (X n ^^^ X m)                           -- eor  xd, xn, xm
  else if is 0xFFE0FC00 0x9AC02000 then a.setX d (X n <<< ((X m).toNat % 64))            -- lslv xd, xn, xm
  else if is 0xFFE0FC00 0x9AC02400 then a.setX d (X n >>> ((X m).toNat % 64))            -- lsrv xd, xn, xm
  else if is 0xFFE0FC00 0x9AC02800 then a.setX d ((X n).sshiftRight ((X m).toNat % 64))  -- asrv xd, xn, xm
  else if is 0xFFE00C00 0x9A800000 then                                                  -- csel  xd, xn, xm, c
    a.setX d (if a.cond (w.extractLsb' 12 4) then X n else X m)
  else if is 0xFFE00C00 0x9A800400 then                                                  -- csinc xd, xn, xm, c
    a.setX d (if a.cond (w.extractLsb' 12 4) then X n else X m + 1)
  else if is 0xFFE00000 0xD2800000 then a.setX d ((w.extractLsb' 5 16).setWidth 64)      -- movz xd, #imm16
  else if is 0xFFC00000 0x91000000 && n != 31 && d != 31 then a.setX d (X n + imm12)     -- add  xd, xn, #imm12
  else if is 0xFFC00000 0xF1000000 && n != 31 then                                       -- subs xd, xn, #imm12
    (a.setSub (X n) imm12).setX d (X n - imm12)
  else a

/-! ## Relating model states to small states -/

/-- The only configuration the emitted instructions need: no statistical-profiling sample in flight
(`csel`/`csinc` consult `SPESampleInFlight` after writing their result). -/
def ArmCfg (s : St) : Prop := s.regs.get? .SPESampleInFlight = some false

/-- `s` holds `x0..x30` and NZCV of `a` -/
structure Abs (s : St) (a : AState) : Prop where
  x : ∀ i < 31, xget s.regs i = some (a.x i)
  p : ∃ p : ProcState, s.regs.get? .PSTATE = some p ∧
    p.N = .ofBool a.n ∧ p.Z = .ofBool a.z ∧ p.C = .ofBool a.c ∧ p.V = .ofBool a.v

/-- `s'` differs from `s` at most in `x0..x30`, PSTATE and SEE; memory is unchanged -/
def Frame (s s' : St) : Prop :=
  s'.mem = s.mem ∧ ∀ r : Register, (∀ i < 31, xreg i ≠ r) → r ≠ .PSTATE → r ≠ .SEE → s'.regs.get? r = s.regs.get? r

/-- what `step_model` does before decoding: `SEE := -1` -/
def reset (s : St) : St := { s with regs := s.regs.insert .SEE (-1 : Int) }

/-- the model's decode+execute of `w` (after `SEE := -1`) succeeds and agrees with `armStep` -/
def Step (pc : Int) (w : BitVec 32) (s : St) (a : AState) : Prop :=
  ∃ s', __DecodeA64 pc w (reset s) = .ok () s' ∧ Abs s' (armStep w a) ∧ ArmCfg s' ∧ Frame s s'

/-- `__DecodeA64 pc w` dispatches (with `SEE = -1`) to the decode function call `f`, setting `SEE := k` -/
def DecodeTo (pc : Int) (w : BitVec 32) (f : SailM Unit) (k : Int) : Prop :=
  ∀ s : St, s.regs.get? .SEE = some (-1) → __DecodeA64 pc w s = f { s with regs := s.regs.insert .SEE k }

/-! ## Family lemmas -/

section
variable {pc : Int} {w : BitVec 32} {s : St} {a : AState} {f : SailM Unit} {k : Int}

theorem Abs.insert {s : St} {a : AState} (h : Abs s a) (r : Register) (v : RegisterType r)
    (hr : ∀ i < 31, xreg i ≠ r) (hp : r ≠ .PSTATE) : Abs { s with regs := s.regs.insert r v } a :=
  ⟨fun i hi => by simp only [xget_insert _ _ _ hr]; exact h.x i hi,
   by obtain ⟨p, h1, h2⟩ := h.p; exact ⟨p, by simp [Std.ExtDHashMap.get?_insert, hp, h1], h2⟩⟩

theorem Abs.xset {s : St} {a : AState} (h : Abs s a) {d : Nat} (hd : d < 31) (v : BitVec 64) :
    Abs { s with regs := xset s.regs d v } (a.setX d v) := by
  refine ⟨fun i hi => ?_, ?_⟩
  · simp only [xget_xset _ hd, AState.setX, show d ≠ 31 by omega, ite_false]
    split <;> simp_all [h.x i hi]
  · obtain ⟨p, h1, h2⟩ := h.p
    exact ⟨p, by rw [xset_get_ne _ _ _ _ (by decide), h1], by simpa [AState.setX, show d ≠ 31 by omega] using h2⟩

theorem see_get (s : St) : (reset s).regs.get? .SEE = some (-1) := by simp [reset]

theorem cfg_insert {s : St} (h : ArmCfg s) (r : Register) (v : RegisterType r) (hr : r ≠ .SPESampleInFlight) :
    ArmCfg { s with regs := s.regs.insert r v } := by
  simp [ArmCfg, Std.ExtDHashMap.get?_insert, hr]; exact h

theorem Abs.pstate {s : St} {a : AState} (hx : ∀ i < 31, xget s.regs i = some (a.x i)) (p : ProcState)
    (hN : p.N = .ofBool a.n) (hZ : p.Z = .ofBool a.z) (hC : p.C = .ofBool a.c) (hV : p.V = .ofBool a.v) :
    Abs { s with regs := s.regs.insert .PSTATE p } a :=
  ⟨fun i hi => by rw [xget_insert _ .PSTATE _ (by decide)]; exact hx i hi, p, by simp, hN, hZ, hC, hV⟩

/-- `reset s` followed by the decoder's `SEE := k` -/
def seen (s : St) (k : Int) : St := { reset s with regs := (reset s).regs.insert .SEE k }

theorem seen_abs {s : St} {a : AState} (ha : Abs s a) (k : Int) : Abs (seen s k) a :=
  (ha.insert .SEE _ (by decide) (by decide)).insert .SEE _ (by decide) (by decide)

theorem seen_cfg {s : St} (hc : ArmCfg s) (k : Int) : ArmCfg (seen s k) :=
  cfg_insert (cfg_insert hc .SEE _ (by decide)) .SEE _ (by decide)

/-- a word whose decode function writes `X[d] := v` and nothing else (besides SEE) -/
theorem step_x {d : Nat} {v : BitVec 64} (hd : d < 31) (hdec : DecodeTo pc w f k)
    (hexec : ∀ s₀ : St, Abs s₀ a → ArmCfg s₀ → f s₀ = .ok () { s₀ with regs := xset s₀.regs d v })
    (hstep : armStep w a = a.setX d v) (hc : ArmCfg s) (ha : Abs s a) : Step pc w s a := by
  refine ⟨{ seen s k with regs := xset (seen s k).regs d v }, ?_, ?_, ?_, rfl, ?_⟩
  · rw [hdec _ (see_get s)]; exact hexec _ (seen_abs ha k) (seen_cfg hc k)
  · rw [hstep]; exact (seen_abs ha k).xset hd v
  · have := seen_cfg hc k; simp only [ArmCfg] at this ⊢; rw [xset_get_ne _ _ _ _ (by decide)]; exact this
  · intro r hr hp hs
    simp [seen, reset, xset_get_ne _ _ _ _ hr, Std.ExtDHashMap.get?_insert, Ne.symm hs]

/-- a flag-setting `subs xzr, x, y` (`cmp`): writes PSTATE.NZCV and nothing else (besides SEE) -/
theorem step_cmp {x y : BitVec 64} (hdec : DecodeTo pc w f k)
    (hexec : ∀ (s₀ : St) (p : ProcState), Abs s₀ a → s₀.regs.get? .PSTATE = some p →
      f s₀ = .ok () { s₀ with regs := s₀.regs.insert .PSTATE (setFlags p (AddWithCarry x (~~~y) 1#1).2) })
    (hstep : armStep w a = a.setSub x y) (hc : ArmCfg s) (ha : Abs s a) : Step pc w s a := by
  obtain ⟨p, hp, -⟩ := (seen_abs ha k).p
  refine ⟨{ seen s k with regs := (seen s k).regs.insert .PSTATE (setFlags p (AddWithCarry x (~~~y) 1#1).2) },
    ?_, ?_, ?_, rfl, ?_⟩
  · rw [hdec _ (see_get s)]; exact hexec _ p (seen_abs ha k) hp
  · rw [hstep, sub_flags]
    exact Abs.pstate (a := a.setSub x y) (seen_abs ha k).x _ rfl rfl rfl rfl
  · exact cfg_insert (seen_cfg hc k) .PSTATE _ (by decide)
  · intro r hr hp hs
    simp [seen, reset, Std.ExtDHashMap.get?_insert, Ne.symm hs, Ne.symm hp]

theorem cond_cs (a : AState) : a.cond 2#4 = a.c := by simp [AState.cond]
theorem cond_ge (a : AState) : a.cond 10#4 = (a.n == a.v) := by simp [AState.cond]
theorem cond_ne (a : AState) : a.cond 1#4 = !a.z := by simp [AState.cond]
theorem ofBool_beq (x y : Bool) : (BitVec.ofBool x == BitVec.ofBool y) = (x == y) := by
  cases x <;> cases y <;> rfl
@[simp] theorem setX_31 (a : AState) (v : BitVec 64) : a.setX 31 v = a := by simp [AState.setX]

/-- `cset xd, lo` -/
theorem step_cset_lo {d : Nat} (hd : d < 31)
    (hdec : DecodeTo pc w (decode_csinc_aarch64_instrs_integer_conditional_select (BitVec.ofNat 5 d) 31#5 1#1 2#4 31#5 0#1 1#1) k)
    (hstep : armStep w a = a.setX d (if a.cond 2#4 then 0 else 1)) (hc : ArmCfg s) (ha : Abs s a) : Step pc w s a :=
  step_x hd hdec (fun s₀ h₀ hc₀ => by
    obtain ⟨p, hp, -, -, hC, -⟩ := h₀.p
    rw [cset_lo_exec hp hc₀ hd, hC, cond_cs]; cases a.c <;> rfl) hstep hc ha

/-- `cset xd, lt` -/
theorem step_cset_lt {d : Nat} (hd : d < 31)
    (hdec : DecodeTo pc w (decode_csinc_aarch64_instrs_integer_conditional_select (BitVec.ofNat 5 d) 31#5 1#1 10#4 31#5 0#1 1#1) k)
    (hstep : armStep w a = a.setX d (if a.cond 10#4 then 0 else 1)) (hc : ArmCfg s) (ha : Abs s a) : Step pc w s a :=
  step_x hd hdec (fun s₀ h₀ hc₀ => by
    obtain ⟨p, hp, hN, -, -, hV⟩ := h₀.p
    rw [cset_lt_exec hp hc₀ hd, hN, hV, cond_ge, ofBool_beq]) hstep hc ha

/-- `cset xd, eq` -/
theorem step_cset_eq {d : Nat} (hd : d < 31)
    (hdec : DecodeTo pc w (decode_csinc_aarch64_instrs_integer_conditional_select (BitVec.ofNat 5 d) 31#5 1#1 1#4 31#5 0#1 1#1) k)
    (hstep : armStep w a = a.setX d (if a.cond 1#4 then 0 else 1)) (hc : ArmCfg s) (ha : Abs s a) : Step pc w s a :=
  step_x hd hdec (fun s₀ h₀ hc₀ => by
    obtain ⟨p, hp, -, hZ, -, -⟩ := h₀.p
    rw [cset_eq_exec hp hc₀ hd, hZ, cond_ne]; cases a.z <;> rfl) hstep hc ha

/-- `csel xd, xn, xm, ne` -/
theorem step_csel {d n m : Nat} (hd : d < 31) (hn : n < 31) (hm : m < 31)
    (hdec : DecodeTo pc w (decode_csel_aarch64_instrs_integer_conditional_select (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 0#1 1#4
      (BitVec.ofNat 5 m) 0#1 1#1) k)
    (hstep : armStep w a = a.setX d (if a.cond 1#4 then a.x n else a.x m)) (hc : ArmCfg s) (ha : Abs s a) : Step pc w s a :=
  step_x hd hdec (fun s₀ h₀ hc₀ => by
    obtain ⟨p, hp, -, hZ, -, -⟩ := h₀.p
    rw [csel_ne_exec hp hc₀ hd hn hm (h₀.x n hn) (h₀.x m hm), hZ, cond_ne]; cases a.z <;> rfl) hstep hc ha
end

end ArmProof
