/- `armDM`: a `Proven.Top.Machine` on DeepMind's AArch64 semantics (outside `Spec/`; interim target). The step is
DeepMind's `Arm64.Step Pg` made a function (`Pg` has no extern hooks, so a running `Step` is the `exec` case);
`observe` shows the pc, x0..x30 (register 31 = sp) and the mapped bytes. -/
import Spec.Top
import Blocks.A64Defs
import Blocks.MemLem
import Blocks.Imm
import Blocks.Reg
import Blocks.Branch
import Blocks.Mem
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Proven.Apc.Blocks
open Proven.Top Proven.Arm

/-- DeepMind's step as a function: fetch, decode, execute while running -/
def stepDM (t : Arm64.State) : Option Arm64.State :=
  match t.status with
  | .Running => (Pg.fetchMem t.mem t.pc).map fun i => Pg.evalInst i t
  | _ => none

/-- what `Spec` observes: pc, x0..x30, sp as register 31, and the mapped bytes -/
def obsDM (t : Arm64.State) : MachineState where
  programCounter := UInt64.ofBitVec t.pc
  register r := if r < 31 then UInt64.ofBitVec ((abs t).x r) else if r = 31 then UInt64.ofBitVec t.sp else 0
  memory u := if (t.mem.perm u.toBitVec).isSome then some (UInt8.ofBitVec (t.mem.read8 u.toBitVec)) else none

/-- the machine; RAM window [2^31, 3·2^30) as `A64Sem`'s users assume -/
def armDM : Machine where
  State := Arm64.State
  step := stepDM
  observe := obsDM
  configured t := t.status = .Running
  mapping := armMapping
  ramStart := 2 ^ 31
  ramEnd := 3 * 2 ^ 30

/-- a DeepMind step that stays running is an `armDM` step -/
theorem stepDM_of {t t' : Arm64.State} (h : Arm64.Step Pg t t') (hr : t'.status = .Running) : stepDM t = some t' := by
  cases h with
  | exec hrun hf => simp [stepDM, hrun, hf]
  | halt_unmapped _ _ _ => simp at hr
  | extern _ he _ _ => have : Pg.externAt? t.pc = none := rfl; rw [this] at he; cases he
  | extern_fault _ he _ => have : Pg.externAt? t.pc = none := rfl; rw [this] at he; cases he

theorem runs_one {t t' : Arm64.State} (h : Arm64.Step Pg t t') (hr : t'.status = .Running) : Runs armDM t t' :=
  .step (stepDM_of h hr) .stop

theorem runs_trans : ∀ {a b c : Arm64.State}, Runs armDM a b → Runs armDM b c → Runs armDM a c
  | _, _, _, .stop, h2 => h2
  | _, _, _, .step hs h1, h2 => .step hs (runs_trans h1 h2)

theorem pc_obs (t : Arm64.State) : (obsDM t).programCounter.toNat = t.pc.toNat := by simp [obsDM]

/-- an observed byte that is mapped is DeepMind's `read8` -/
theorem byte_obs {t : Arm64.State} {a : Nat} {b : UInt8} (ha : a < 2 ^ 64)
    (h : (obsDM t).memory (UInt64.ofNat a) = some b) : t.mem.read8 (ad a) = b.toBitVec := by
  simp only [obsDM] at h
  have e : (UInt64.ofNat a).toBitVec = ad a := rfl
  rw [e] at h; split at h
  · cases h; rfl
  · cases h

/-- **fetch**: the observed word at the pc, with its 4 bytes executable, is DeepMind's fetch -/
theorem fetch {t : Arm64.State} {w : Nat} (hc : t.status = .Running) (hp : JT.PcOK armDM (obsDM t))
    (hw : JT.WordAt (obsDM t) (obsDM t).programCounter.toNat w)
    (hx : ∀ k < 4, t.mem.canExec (ad (t.pc.toNat + k)) 1 = true) : At t (wd w) := by
  obtain ⟨h4, hlo, hhi⟩ := hp
  rw [pc_obs] at h4 hlo hhi hw
  have hl : t.pc.toNat + 4 < 2 ^ 64 := by simp [armDM] at hhi; omega
  have ep : ∀ k < 4, t.pc + BitVec.ofNat 64 k = ad (t.pc.toNat + k) := fun k hk => by
    apply BitVec.eq_of_toNat_eq; simp
  have hb : ∀ k < 4, t.mem.read8 (t.pc + BitVec.ofNat 64 k) = (wd w).extractLsb' (8 * k) 8 := fun k hk => by
    rw [ep k hk, byte_obs (by omega) (hw k hk)]; rfl
  refine ⟨hc, h4, ?_, ?_⟩
  · exact allPerm_of _ _ 4 _ fun k hk => by rw [ep k hk]; exact hx k hk
  · unfold Arm64.Memory.read32
    simp only [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, hb 0 (by omega), hb 1 (by omega),
      hb 2 (by omega), hb 3 (by omega)]
    exact bytes4 _

/-- one DeepMind step that stays running and lands on observation `o` is `Goes` -/
theorem goes1 {t : Arm64.State} {o : MachineState} (h : ∃ t', Arm64.Step Pg t t' ∧ t'.status = .Running ∧ obsDM t' = o) :
    JT.Goes armDM t o :=
  let ⟨t', hs, hr, ho⟩ := h; ⟨t', runs_one hs hr, hr, ho⟩

theorem obs_setX {t t' : Arm64.State} {d : Nat} {v : BitVec 64} (hd : d < 31) (ha : abs t' = (abs t).setX d v)
    (hpc : t'.pc = t.pc + 4) (hm : t'.mem = t.mem) (hsp : t'.sp = t.sp) :
    obsDM t' = JT.setReg (obsDM t) d (UInt64.ofBitVec v) := by
  simp only [obsDM, JT.setReg, ha, hpc, hm, hsp]
  congr 1
  funext r
  by_cases e : r = d
  · subst e; simp [hd, AState.setX, show r ≠ 31 by omega]
  · simp only [e, ite_false]; split
    · rename_i hr; simp [AState.setX, e, show d ≠ 31 by omega]
    · rfl

theorem obs_jump {t t' : Arm64.State} {p : BitVec 64} (ha : abs t' = abs t) (hpc : t'.pc = p) (hm : t'.mem = t.mem)
    (hsp : t'.sp = t.sp) : obsDM t' = JT.jumpTo (obsDM t) (UInt64.ofBitVec p) := by
  simp only [obsDM, JT.jumpTo, ha, hpc, hm, hsp]

/-- the executable-bytes premise at the pc (what `A64Sem`'s fetch needs on DeepMind) -/
def XAt (t : Arm64.State) : Prop := ∀ k < 4, t.mem.canExec (ad (t.pc.toNat + k)) 1 = true

theorem F_movz (t : Arm64.State) (d i : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (armDM.observe t))
    (hx : XAt t) (hd : d < 31) (hi : i < 2 ^ 16)
    (hw : JT.WordAt (armDM.observe t) (armDM.observe t).programCounter.toNat (ArmEnc.movz d i)) :
    JT.Goes armDM t (JT.setReg (armDM.observe t) d (UInt64.ofNat i)) := by
  have hA := fetch hc hp hw hx; simp only [ArmEnc.movz] at hA
  obtain ⟨t', s1, a1, P1⟩ := dm_movz (by mask32) (by fldt) hA
  refine goes1 ⟨t', s1, P1.run, ?_⟩
  rw [obs_setX (d := d) hd (by rw [a1]; congr 1; fldt) P1.pc P1.mem P1.sp]
  congr 1; apply UInt64.toBitVec_inj.mp
  show _ = BitVec.ofNat 64 i
  rw [show ((wd (0xD2800000 + i * 2 ^ 5 + d)).extractLsb' 21 2).toNat = 0 by fldt,
    show ((wd (0xD2800000 + i * 2 ^ 5 + d)).extractLsb' 5 16).setWidth 64 = BitVec.ofNat 64 i by immt]
  simp

end Proven.Apc.Blocks
