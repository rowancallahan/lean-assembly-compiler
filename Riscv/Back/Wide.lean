/- The RISC-V instance of the WIDE interface (`Compiler/Wide.lean`): every wide operation for arbitrary
abstract registers, proved from the register-generic step lemmas (`Riscv/Steps/Gen*.lean`).

Encodings: `mov` = `add d,x0,a`; `bin` = the R-type word (`eq`: `xor; sltiu 1`); `bini` = the I-type word
(`sub c` = `addi -c`, shifts = `slli/srli/srai`, `eq` = `xori; sltiu 1`); `lbu/sb` with a 12-bit offset;
`br` = `beq/bne/blt/bge/bltu/bgeu a, b|x0, ±4n`; `jmp` = `jal x0, ±4n`; `li` = a short `addi`/`lui`/`slli`
plan found by an untrusted search and CHECKED by evaluation (fallback: one bit at a time). -/
import Compiler.Wide
import Riscv.Steps.GenUse
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv
open Proven.G

/-! ## Constants -/

/-- `c` is a sign-extended 12-bit value -/
def fits12 (c : BitVec 64) : Bool := (c.setWidth 12).signExtend 64 == c

theorem fits12_eq {c : BitVec 64} (h : fits12 c = true) : (c.setWidth 12).signExtend 64 = c := eq_of_beq h

/-- one step of a constant-building plan for a register `d` -/
inductive LiStep where
  /-- `addi d, x0, i` -/
  | set (i : BitVec 12)
  /-- `lui d, i` -/
  | lui (i : BitVec 20)
  /-- `addi d, d, i` -/
  | add (i : BitVec 12)
  /-- `slli d, d, n` -/
  | shl (n : BitVec 6)
  deriving Repr

def LiStep.eval : LiStep → BitVec 64 → BitVec 64
  | .set i, _ => i.signExtend 64
  | .lui i, _ => (i ++ 0#12).signExtend 64
  | .add i, a => a + i.signExtend 64
  | .shl n, a => a <<< n.toNat

def LiStep.word (d : Fin 32) : LiStep → BitVec 32
  | .set i => encI 0 i.toNat d 0
  | .lui i => encU 0x37 d i
  | .add i => encI 0 i.toNat d d
  | .shl n => encI 1 (0 <<< 6 ||| n.toNat) d d

def LiStep.init : LiStep → Bool
  | .set _ | .lui _ => true
  | _ => false

def runLi (p : List LiStep) (a : BitVec 64) : BitVec 64 := p.foldl (fun a st => st.eval a) a

/-- 32-bit plan: `addi`, or `lui` (+ `addi`) -/
def liPlan32 (c : BitVec 64) : List LiStep :=
  if fits12 c then [.set (c.setWidth 12)]
  else if c.setWidth 12 = 0 then [.lui ((c >>> 12).setWidth 20)]
  else [.lui (((c - (c.setWidth 12).signExtend 64) >>> 12).setWidth 20), .add (c.setWidth 12)]

/-- number of trailing zero bits (at most `fuel`) -/
def tz : Nat → BitVec 64 → Nat
  | 0, _ => 0
  | fuel + 1, c => if c.getLsbD 0 then 0 else 1 + tz fuel (c >>> 1)

/-- untrusted search for a short plan (the result is checked by `liCode`) -/
def liPlan : Nat → BitVec 64 → List LiStep
  | 0, c => liPlan32 c
  | fuel + 1, c =>
    if runLi (liPlan32 c) 0 = c then liPlan32 c
    else
      let lo := (c.setWidth 12).signExtend 64
      let hi := (c - lo).sshiftRight 12
      let z := tz 40 hi
      liPlan fuel (hi.sshiftRight z) ++ [.shl (BitVec.ofNat 6 (12 + z))] ++
        (if c.setWidth 12 = 0 then [] else [.add (c.setWidth 12)])

/-- always correct: zero, then one bit at a time -/
def liSlow (n : Nat) : List LiStep :=
  if n = 0 then [.set 0] else liSlow (n / 2) ++ [.shl 1] ++ (if n % 2 = 1 then [.add 1] else [])

def liGood (p : List LiStep) (c : BitVec 64) : Bool :=
  (match p with | st :: _ => st.init | [] => false) && runLi p 0 == c

/-- the plan used for `li d c` -/
def liCode (c : BitVec 64) : List LiStep := if liGood (liPlan 6 c) c = true then liPlan 6 c else liSlow c.toNat

theorem runLi_append (p q : List LiStep) (a : BitVec 64) : runLi (p ++ q) a = runLi q (runLi p a) :=
  List.foldl_append ..

theorem runLi_slow : ∀ (n : Nat) (a : BitVec 64), runLi (liSlow n) a = BitVec.ofNat 64 n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a
    rw [liSlow]
    by_cases hn : n = 0
    · subst hn; rfl
    · rw [ite_neg hn, runLi_append, runLi_append, ih (n / 2) (by omega)]
      by_cases hodd : n % 2 = 1
      · rw [ite_pos hodd]
        show (BitVec.ofNat 64 (n / 2) <<< 1) + (1 : BitVec 12).signExtend 64 = _
        rw [shl_ofNat, show (1 : BitVec 12).signExtend 64 = 1 by decide, inc_ofNat]; congr 1; omega
      · rw [ite_neg hodd]
        show BitVec.ofNat 64 (n / 2) <<< 1 = _
        rw [shl_ofNat]; congr 1; omega

theorem runLi_code (c a : BitVec 64) : runLi (liCode c) a = c := by
  unfold liCode
  by_cases h : liGood (liPlan 6 c) c = true
  · rw [ite_pos h]
    unfold liGood at h
    cases hp : liPlan 6 c with
    | nil => rw [hp] at h; exact absurd h (by simp)
    | cons st rest =>
      rw [hp] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      have e : st.eval a = st.eval 0 := by cases st <;> first | rfl | exact absurd h.1 (by simp [LiStep.init])
      rw [← h.2]; show runLi rest (st.eval a) = runLi rest (st.eval 0); rw [e]
  · rw [ite_neg h, runLi_slow, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## Encoding -/

def condF3 : Cond → BitVec 3
  | .eq => 0 | .ne => 1 | .lt => 4 | .ge => 5 | .ltu => 6 | .geu => 7

def brOff (back : Bool) (n : Nat) : BitVec 12 :=
  if back then BitVec.ofNat 12 (2 ^ 12 - 2 * n) else BitVec.ofNat 12 (2 * n)

def jOff (back : Bool) (n : Nat) : BitVec 20 :=
  if back then BitVec.ofNat 20 (2 ^ 20 - 2 * n) else BitVec.ofNat 20 (2 * n)

def physO : Option Reg → Fin 32
  | some b => phys b
  | none => 0

def immWords (op : Op) (d a : Fin 32) (c : BitVec 64) : List (BitVec 32) :=
  match op with
  | .add => [encI 0 (c.setWidth 12).toNat d a]
  | .sub => [encI 0 ((-c).setWidth 12).toNat d a]
  | .and => [encI 7 (c.setWidth 12).toNat d a]
  | .or => [encI 6 (c.setWidth 12).toNat d a]
  | .xor => [encI 4 (c.setWidth 12).toNat d a]
  | .slt => [encI 2 (c.setWidth 12).toNat d a]
  | .ult => [encI 3 (c.setWidth 12).toNat d a]
  | .shl => [encI 1 (0 <<< 6 ||| (c.setWidth 6).toNat) d a]
  | .lshr => [encI 5 (0 <<< 6 ||| (c.setWidth 6).toNat) d a]
  | .ashr => [encI 5 (0x10 <<< 6 ||| (c.setWidth 6).toNat) d a]
  | .eq => [encI 4 (c.setWidth 12).toNat d a, encI 3 (1 : BitVec 12).toNat d d]

def immOK (op : Op) (c : BitVec 64) : Bool :=
  match op with
  | .shl | .lshr | .ashr => true
  | .sub => fits12 (-c)
  | _ => fits12 c

def wenc : WOp → List (BitVec 32)
  | .mov d a => [encR 0 0 (phys d) 0 (phys a)]
  | .li d c => (liCode c).map (LiStep.word (phys d))
  | .bin op d a b =>
      if op = .eq then [encR 0 4 (phys d) (phys a) (phys b), encI 3 (1 : BitVec 12).toNat (phys d) (phys d)]
      else [encR op.f7 op.f3 (phys d) (phys a) (phys b)]
  | .bini op d a c => immWords op (phys d) (phys a) c
  | .lbu d a off => [encL 4 (off.setWidth 12) (phys d) (phys a)]
  | .sb v a off => [encS 0 (off.setWidth 12) (phys v) (phys a)]
  | .br c a b k n => [wB (condF3 c) (.ofFin (phys a)) (.ofFin (physO b)) (brOff k n)]
  | .jmp k n => [wJ 0 (jOff k n)]
  | .ret => [iRet]

def brOK (k : Bool) (n : Nat) : Bool := if k then decide (0 < n ∧ 2 * n ≤ 2 ^ 11) else decide (2 * n < 2048)
def jOK (k : Bool) (n : Nat) : Bool := if k then decide (0 < n ∧ 2 * n ≤ 2 ^ 19) else decide (2 * n < 2 ^ 19)

/-! ## Laws -/

/-- a one-word operation writing `d` -/
theorem one {d : Reg} {v : BitVec 64} {w : BitVec 32} {s : St} {pc : BitVec 64} (hA : core.At s pc [w])
    (hstep : Cfg s → s.regs.get? .PC = some pc → pcOK pc → instrAt s pc w →
      ∃ s', Next s s' (pc + 4) (phys d) v s.mem) :
    core.runsTo s fun s' => core.Done s s' (next pc 1) ∧ core.Set1 s s' d v ∧ core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨s', hn⟩ := hstep h hpc hok hi
  exact run1 hn ⟨ofNext hn (.inr ⟨d, rfl⟩), set1Of hn, memOf hn⟩

/-- a two-word operation writing `d` twice -/
theorem two {d : Reg} {v₁ v₂ : BitVec 64} {w₁ w₂ : BitVec 32} {s : St} {pc : BitVec 64}
    (hA : core.At s pc [w₁, w₂])
    (h₁ : Cfg s → s.regs.get? .PC = some pc → pcOK pc → instrAt s pc w₁ →
      ∃ s', Next s s' (pc + 4) (phys d) v₁ s.mem)
    (h₂ : ∀ (s₁ : St) (pc₁ : BitVec 64), getX s₁ (phys d) = v₁ → Cfg s₁ → s₁.regs.get? .PC = some pc₁ →
      pcOK pc₁ → instrAt s₁ pc₁ w₂ → ∃ s', Next s₁ s' (pc₁ + 4) (phys d) v₂ s₁.mem) :
    core.runsTo s fun s' => core.Done s s' (next pc 2) ∧ core.Set1 s s' d v₂ ∧ core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first hA
  obtain ⟨s₁, hn⟩ := h₁ h hpc hok hi
  refine chain hA hn (.inr ⟨d, rfl⟩) fun hA' => ?_
  have e₁ : getX s₁ (phys d) = v₁ := Core.Set1.same _ (set1Of hn)
  exact core.runsTo_mono (one hA' (h₂ s₁ _ e₁)) fun s₂ ⟨d₂, st₂, m₂⟩ =>
    ⟨d₂, Core.Set1.trans _ (set1Of hn) st₂, m₂.trans (memOf hn)⟩

theorem sltiu1 (x : BitVec 64) :
    (if x < (1 : BitVec 12).signExtend 64 then (1 : BitVec 64) else 0) = if x = 0 then 1 else 0 := by
  have e : (1 : BitVec 12).signExtend 64 = 1 := by decide
  rw [e]
  by_cases h : x = 0
  · subst h; rfl
  · rw [if_neg h, if_neg]
    intro hlt
    apply h
    apply BitVec.eq_of_toNat_eq
    have := BitVec.lt_def.1 hlt
    simp at this ⊢; omega

theorem w_mov {d a : Reg} {s : St} {pc : BitVec 64} (hA : core.At s pc (wenc (.mov d a))) :
    core.runsTo s fun s' => core.Done s s' (next pc (wenc (.mov d a)).length) ∧
      core.Set1 s s' d (core.get s a) ∧ core.mem s' = core.mem s :=
  one hA fun h hpc hok hi => step_mv h hpc hok _ _ (phys_ne0 d) hi

theorem li_run (d : Reg) : ∀ (p : List LiStep) {s : St} {pc : BitVec 64},
    core.At s pc (p.map (LiStep.word (phys d))) →
    core.runsTo s fun s' => core.Done s s' (next pc (p.map (LiStep.word (phys d))).length) ∧
      core.Set1 s s' d (runLi p (core.get s d)) ∧ core.mem s' = core.mem s
  | [], s, pc, hA => runsTo_of ⟨⟨hA.ok, core.keep_refl s, by rw [List.map_nil, List.length_nil, next_zero]; exact hA.hpc⟩,
      fun r => by by_cases hr : r = d <;> simp [hr, runLi], rfl⟩
  | st :: rest, s, pc, hA => by
    rw [List.map_cons] at hA ⊢
    obtain ⟨h, hpc, hok, hi⟩ := first hA
    obtain ⟨s₁, hn⟩ : ∃ s₁, Next s s₁ (pc + 4) (phys d) (st.eval (getX s (phys d))) s.mem := by
      cases st with
      | set i => have := step_addi h hpc hok (phys d) 0 i hi; simpa [LiStep.eval] using this
      | lui i => exact step_lui h hpc hok (phys d) i hi
      | add i => exact step_addi h hpc hok (phys d) (phys d) i hi
      | shl n => exact step_slli h hpc hok (phys d) (phys d) n hi
    refine chain hA hn (.inr ⟨d, rfl⟩) fun hA' => ?_
    refine core.runsTo_mono (li_run d rest hA') fun s₂ ⟨d₂, st₂, m₂⟩ => ⟨d₂, ?_, m₂.trans (memOf hn)⟩
    rw [show core.get s₁ d = st.eval (getX s (phys d)) from Core.Set1.same _ (set1Of hn)] at st₂
    exact Core.Set1.trans _ (set1Of hn) st₂

theorem w_li {d : Reg} {c : BitVec 64} {s : St} {pc : BitVec 64} (hA : core.At s pc (wenc (.li d c))) :
    core.runsTo s fun s' => core.Done s s' (next pc (wenc (.li d c)).length) ∧
      core.Set1 s s' d c ∧ core.mem s' = core.mem s := by
  have := li_run d (liCode c) hA
  rwa [runLi_code] at this

theorem w_bin {op : Op} {d a b : Reg} {s : St} {pc : BitVec 64} (hA : core.At s pc (wenc (.bin op d a b))) :
    core.runsTo s fun s' => core.Done s s' (next pc (wenc (.bin op d a b)).length) ∧
      core.Set1 s s' d (op.eval (core.get s a) (core.get s b)) ∧ core.mem s' = core.mem s := by
  unfold wenc at hA ⊢
  by_cases he : op = .eq
  · subst he
    rw [ite_pos rfl] at hA ⊢
    refine two hA (fun h hpc hok hi => step_xor h hpc hok _ _ _ hi) fun s₁ pc₁ e₁ h hpc hok hi => ?_
    have := step_sltiu h hpc hok (phys d) (phys d) 1 hi
    rw [e₁, sltiu1] at this
    simpa only [Op.eval, xor_eq_zero] using this
  · rw [ite_neg he] at hA ⊢
    exact one hA fun h hpc hok hi => step_rop h hpc hok op he _ _ _ (phys_ne0 d) hi

theorem toNat6 (c : BitVec 64) : (c.setWidth 6).toNat = c.toNat % 64 := by simp

theorem w_bini {op : Op} {d a : Reg} {c : BitVec 64} {s : St} {pc : BitVec 64} (hc : immOK op c = true)
    (hA : core.At s pc (wenc (.bini op d a c))) :
    core.runsTo s fun s' => core.Done s s' (next pc (wenc (.bini op d a c)).length) ∧
      core.Set1 s s' d (op.eval (core.get s a) c) ∧ core.mem s' = core.mem s := by
  unfold wenc at hA ⊢
  cases op <;> simp only [immWords, immOK] at hA hc ⊢
  · exact one hA fun h hpc hok hi => by
      have := step_addi h hpc hok (phys d) (phys a) _ hi; rwa [fits12_eq hc] at this
  · exact one hA fun h hpc hok hi => by
      have := step_addi h hpc hok (phys d) (phys a) _ hi
      rwa [fits12_eq hc, ← BitVec.sub_eq_add_neg] at this
  · exact one hA fun h hpc hok hi => by
      have := step_andi h hpc hok (phys d) (phys a) _ hi; rwa [fits12_eq hc] at this
  · exact one hA fun h hpc hok hi => by
      have := step_ori h hpc hok (phys d) (phys a) _ (phys_ne0 d) hi; rwa [fits12_eq hc] at this
  · exact one hA fun h hpc hok hi => by
      have := step_xori h hpc hok (phys d) (phys a) _ hi; rwa [fits12_eq hc] at this
  · exact one hA fun h hpc hok hi => by
      have := step_slli h hpc hok (phys d) (phys a) _ hi; rwa [toNat6] at this
  · exact one hA fun h hpc hok hi => by
      have := step_srli h hpc hok (phys d) (phys a) _ hi; rwa [toNat6] at this
  · exact one hA fun h hpc hok hi => by
      have := step_srai h hpc hok (phys d) (phys a) _ hi; rwa [toNat6] at this
  · exact one hA fun h hpc hok hi => by
      have := step_sltiu h hpc hok (phys d) (phys a) _ hi; rwa [fits12_eq hc] at this
  · exact one hA fun h hpc hok hi => by
      have := step_slti h hpc hok (phys d) (phys a) _ hi; rwa [fits12_eq hc] at this
  · refine two hA (fun h hpc hok hi => step_xori h hpc hok _ _ _ hi) fun s₁ pc₁ e₁ h hpc hok hi => ?_
    have := step_sltiu h hpc hok (phys d) (phys d) 1 hi
    rw [e₁, sltiu1, fits12_eq hc] at this
    simpa only [Op.eval, xor_eq_zero] using this

theorem w_lbu {d a : Reg} {off : BitVec 64} {s : St} {pc : BitVec 64} {v : BitVec 8} (ho : fits12 off = true)
    (hA : core.At s pc (wenc (.lbu d a off))) (hr : core.inRAM (core.get s a + off).toNat 1)
    (hm : core.mem s (core.get s a + off).toNat = some v) :
    core.runsTo s fun s' => core.Done s s' (next pc (wenc (.lbu d a off)).length) ∧
      core.Set1 s s' d (v.setWidth 64) ∧ core.mem s' = core.mem s :=
  one hA fun h hpc hok hi => step_lbu h hpc hok (phys d) (phys a) _ hi (by rw [fits12_eq ho]) hr hm

theorem w_sb {v a : Reg} {off : BitVec 64} {s : St} {pc : BitVec 64} (ho : fits12 off = true)
    (hA : core.At s pc (wenc (.sb v a off))) (hr : core.inRAM (core.get s a + off).toNat 1) :
    core.runsTo s fun s' => core.Done s s' (next pc (wenc (.sb v a off)).length) ∧
      core.Same s s' ∧ core.mem s' = (core.mem s).upd (core.get s a + off).toNat ((core.get s v).setWidth 8) := by
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨s', hn⟩ := step_sb h hpc hok (phys v) (phys a) _ hi (A := getX s (phys a) + off) (by rw [fits12_eq ho]) hr
  refine run1 hn ⟨ofNext hn (.inl rfl), sameOf hn, ?_⟩
  funext x
  show s'.mem[x]? = Mem.upd (fun y => s.mem[y]?) (getX s (phys a) + off).toNat ((getX s (phys v)).setWidth 8) x
  rw [hn.mem, Std.ExtHashMap.getElem?_insert]
  unfold Mem.upd
  by_cases hx : x = (getX s (phys a) + off).toNat
  · subst hx; simp
  · simp only [getX_eq] at hx; simp [Ne.symm hx, hx]

theorem boff_back (n : Nat) (h0 : 0 < n) (hn : 2 * n ≤ 2 ^ 11) :
    boff (BitVec.ofNat 12 (2 ^ 12 - 2 * n)) = 0 - BitVec.ofNat 64 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [boff, sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend]
  simp [BitVec.msb_eq_decide, BitVec.toNat_sub, app0_toNat]
  split <;> omega

theorem joff_fwd (n : Nat) (hn : 2 * n < 2 ^ 19) : joff (BitVec.ofNat 20 (2 * n)) = BitVec.ofNat 64 (4 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [joff, sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend]
  simp [BitVec.msb_eq_decide, app0_toNat]
  split <;> omega

theorem br_tgt {k : Bool} {n : Nat} (h : brOK k n = true) (pc : BitVec 64) : pc + boff (brOff k n) = tgt pc k n := by
  cases k
  · have hn : 2 * n < 2048 := of_decide_eq_true h
    simp only [brOff, tgt]; rw [boff_fwd n hn]; rfl
  · have hn : 0 < n ∧ 2 * n ≤ 2 ^ 11 := of_decide_eq_true h
    simp only [brOff, tgt, ite_true]; rw [boff_back n hn.1 hn.2]; bv_omega

theorem j_tgt {k : Bool} {n : Nat} (h : jOK k n = true) (pc : BitVec 64) : pc + joff (jOff k n) = tgt pc k n := by
  cases k
  · have hn : 2 * n < 2 ^ 19 := of_decide_eq_true h
    simp only [jOff, tgt]; rw [joff_fwd n hn]; rfl
  · have hn : 0 < n ∧ 2 * n ≤ 2 ^ 19 := of_decide_eq_true h
    simp only [jOff, tgt, ite_true]; rw [joff_back n hn.1 hn.2]; bv_omega

theorem getO_phys (s : St) (b : Option Reg) : core.getO s b = getX s (physO b) := by cases b <;> rfl

theorem w_br {c : Cond} {a : Reg} {b : Option Reg} {k : Bool} {n : Nat} {s : St} {pc : BitVec 64}
    (hk : brOK k n = true) (hA : core.At s pc (wenc (.br c a b k n))) :
    core.runsTo s fun s' => core.Done s s'
        (if c.eval (core.get s a) (core.getO s b) = true then tgt pc k n else next pc 1) ∧
      core.Same s s' ∧ core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  rw [getO_phys]
  show core.runsTo s fun s' => core.Done s s'
    (if c.eval (getX s (phys a)) (getX s (physO b)) = true then tgt pc k n else next pc 1) ∧ _
  by_cases hc : c.eval (getX s (phys a)) (getX s (physO b)) = true
  · rw [ite_pos hc]
    obtain ⟨s', hx⟩ : ∃ s', Next s s' (pc + boff (brOff k n)) 0 0 s.mem := by
      cases c <;> simp only [Cond.eval, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at hc
      · exact beq_t h hpc hok _ _ _ hi hc
      · exact bne_t h hpc hok _ _ _ hi hc
      · exact bltu_t h hpc hok _ _ _ hi (BitVec.lt_def.1 hc)
      · exact bgeu_t h hpc hok _ _ _ hi (fun h' => hc (BitVec.lt_def.2 h'))
      · exact blt_t h hpc hok _ _ _ hi ((slt_iff _ _).1 hc)
      · exact bge_t h hpc hok _ _ _ hi (fun h' => by rw [(slt_iff _ _).2 h'] at hc; exact nomatch hc)
    rw [br_tgt hk] at hx
    exact run1 hx ⟨ofNext hx (.inl rfl), sameOf hx, memOf hx⟩
  · rw [ite_neg hc]
    obtain ⟨s', hx⟩ : ∃ s', Next s s' (pc + 4) 0 0 s.mem := by
      rw [Bool.not_eq_true] at hc
      cases c <;> simp only [Cond.eval, Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at hc
      · exact beq_n h hpc hok _ _ _ hi hc
      · exact bne_n h hpc hok _ _ _ hi hc
      · exact bltu_n h hpc hok _ _ _ hi (fun h' => hc (BitVec.lt_def.2 h'))
      · exact bgeu_n h hpc hok _ _ _ hi (BitVec.lt_def.1 hc)
      · exact blt_n h hpc hok _ _ _ hi (fun h' => by rw [(slt_iff _ _).2 h'] at hc; exact nomatch hc)
      · exact bge_n h hpc hok _ _ _ hi ((slt_iff _ _).1 hc)
    exact run1 hx ⟨ofNext hx (.inl rfl), sameOf hx, memOf hx⟩

theorem w_jmp {k : Bool} {n : Nat} {s : St} {pc : BitVec 64} (hk : jOK k n = true)
    (hA : core.At s pc (wenc (.jmp k n))) :
    core.runsTo s fun s' => core.Done s s' (tgt pc k n) ∧ core.Same s s' ∧ core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨s', hx⟩ := step_jal_0' h hpc hok _ hi
  rw [j_tgt hk] at hx
  exact run1 hx ⟨ofNext hx (.inl rfl), sameOf hx, memOf hx⟩

theorem w_ret {s : St} {pc : BitVec 64} (hr : core.retOK (core.ra s)) (hA : core.At s pc (wenc .ret)) :
    core.runsTo s fun s' => core.Done s s' (core.ra s) ∧ core.Same s s' ∧ core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨s', hx⟩ := step_ret h hpc hok hi hr
  exact run1 hx ⟨ofNext hx (.inl rfl), sameOf hx, memOf hx⟩

/-- **The Sail RV64 model is a `Wide` machine.** -/
def rvw : Wide where
  toCore := core
  wenc := wenc
  immOK := immOK
  offOK := fits12
  brOK := brOK
  jOK := jOK
  lenBr := 1
  lenJ := 1
  len_br _ _ _ _ _ := rfl
  len_j _ _ := rfl
  w_mov := w_mov
  w_li := w_li
  w_bin := w_bin
  w_bini := w_bini
  w_lbu := w_lbu
  w_sb := w_sb
  w_br := w_br
  w_jmp := w_jmp
  w_ret := w_ret

end Proven.Mach.Riscv
