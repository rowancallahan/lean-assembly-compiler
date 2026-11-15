/- Run-time memory checks in the generated code (machine-independent, `MachineM`): the code of a program with
calls (`Compiler/CStmt.lean`, `Compiler/CProg.lean`) with
* before every access of word block 0 (the heap) at index `i`: if `i < u` (the heap length, in global 7)
  go on (one compare and branch); else if the word `i` fits below the current frame, zero the words
  `u .. i` and set `u := i + 1`; else jump to the out-of-memory exit;
* before every call: if the callee's frame would reach into the heap, jump to the out-of-memory exit;
* the out-of-memory exit: the caller's return address from the entry stub's frame, the status register
  `:= -1`, return.
`MachineM` adds to `MachineC` the operations the checks need (compare-and-branch on two registers, read
the frame register, read the stub's frame address, the exit) with one law each.

The layout of the work block: the heap at the bottom (`[wbase, wbase + 8 u)`), the stack of frames at the
top, between them free space.  A run is out of memory exactly when its cells in use (`Compiler/MemRun.lean`)
exceed the cells of the work block. -/
import Compiler.CProg
import Compiler.MemRun

set_option linter.unusedVariables false

namespace Proven.Mach
open MachineF

inductive KOp where
  /-- if `a < b` (unsigned) jump `n` words forward (from the start of this op), else fall through -/
  | bltu (a b : Reg) (n : Nat)
  /-- if `a ≥ b` (unsigned) jump `n` words forward, else fall through -/
  | bgeu (a b : Reg) (n : Nat)
  /-- `d := fr` -/
  | getFr (d : Reg)
  /-- `d := frameAt s 0` (the entry stub's frame) -/
  | getTop (d : Reg)
  /-- out of memory: return to the address saved in the cell below the stub's frame, status `-1` -/
  | exit

inductive ZOp where
  | y (o : YOp)
  | m (o : KOp)

structure MachineM extends MachineC where
  encM : KOp → List (BitVec 32)
  lenBr : Nat
  len_bltu : ∀ a b n, (encM (.bltu a b n)).length = lenBr
  len_bgeu : ∀ a b n, (encM (.bgeu a b n)).length = lenBr
  law_bltu : ∀ {a b : Reg} {n : Nat} {s : S} {pc : BitVec 64}, bzOK n → toBase.At s pc (encM (.bltu a b n)) →
    runsTo s fun s' => toBase.Done s s'
        (if (get s a).toNat < (get s b).toNat then next pc n else next pc lenBr) ∧
      toBase.Same s s' ∧ mem s' = mem s
  law_bgeu : ∀ {a b : Reg} {n : Nat} {s : S} {pc : BitVec 64}, bzOK n → toBase.At s pc (encM (.bgeu a b n)) →
    runsTo s fun s' => toBase.Done s s'
        (if (get s b).toNat ≤ (get s a).toNat then next pc n else next pc lenBr) ∧
      toBase.Same s s' ∧ mem s' = mem s
  law_getFr : ∀ {d : Reg} {s : S} {pc : BitVec 64}, d.val < 7 → toBase.At s pc (encM (.getFr d)) →
    runsTo s fun s' => toBase.Done s s' (next pc (encM (.getFr d)).length) ∧ toBase.Set1 s s' d (fr s) ∧
      mem s' = mem s
  law_getTop : ∀ {d : Reg} {s : S} {pc : BitVec 64}, d.val < 7 → toBase.At s pc (encM (.getTop d)) →
    runsTo s fun s' => toBase.Done s s' (next pc (encM (.getTop d)).length) ∧
      toBase.Set1 s s' d (BitVec.ofNat 64 (frameAt s 0)) ∧ mem s' = mem s
  law_exit : ∀ {s : S} {pc w : BitVec 64}, toBase.At s pc (encM .exit) → 8 ≤ frameAt s 0 →
    toBase.inRAM (frameAt s 0 - 8) 8 → (frameAt s 0 - 8) % 8 = 0 →
    bytes (mem s) (frameAt s 0 - 8) 8 = (le8 w).map some → retOK w →
    runsTo s fun s' => ok s' ∧ pcIs s' w ∧ get s' (avar 0) = BitVec.allOnes 64 ∧ mem s' = mem s
  frameAt_keepC : ∀ {s s' : S} {n : Nat}, keepC s s' → frameAt s' n = frameAt s n

namespace MachineM
variable (M : MachineM)

def encZ : ZOp → List (BitVec 32)
  | .y o => M.encY o
  | .m o => M.encM o

def codeZ : List ZOp → List (BitVec 32)
  | [] => []
  | o :: os => M.encZ o ++ codeZ os

theorem codeZ_append : ∀ (a b : List ZOp), M.codeZ (a ++ b) = M.codeZ a ++ M.codeZ b
  | [], _ => rfl
  | o :: os, b => by
    show M.encZ o ++ M.codeZ (os ++ b) = (M.encZ o ++ M.codeZ os) ++ M.codeZ b
    rw [codeZ_append os b, List.append_assoc]

theorem codeZ_one (o : ZOp) : M.codeZ [o] = M.encZ o := List.append_nil _

theorem codeZ_nil : M.codeZ [] = [] := rfl

theorem codeZ_cons (o : ZOp) (os : List ZOp) : M.codeZ (o :: os) = M.encZ o ++ M.codeZ os := rfl

theorem codeZ_y (os : List YOp) : M.codeZ (os.map .y) = M.codeC os := by
  induction os with
  | nil => rfl
  | cons o os ih => show M.encY o ++ M.codeZ (os.map .y) = M.encY o ++ M.codeC os; rw [ih]

theorem codeZ_x (os : List XOp) : M.codeZ (os.map (.y ∘ .x)) = M.codeF os := by
  rw [← List.map_map, codeZ_y, MachineC.codeC_map]

theorem keep_keepC {s s' : M.S} (h : M.keep s s') : M.keepC s s' := M.keepC_of_keepF (M.keepF_of_keep h)

theorem frameAt_keep {s s' : M.S} {n : Nat} (h : M.keep s s') : M.frameAt s' n = M.frameAt s n :=
  M.frameAt_keepC (M.keep_keepC h)

/-! ## straight-line register code -/

/-- a register-only operation the checks use -/
def simpleOK : ZOp → Prop
  | .y (.x (.a (.mov d a))) => MovOK d a
  | .y (.x (.a (.li d _))) => d.val < 11
  | .y (.x (.a (.bin _ d a b))) => d.val < 10 ∧ a = d ∧ b.val = d.val + 1
  | .m (.getFr d) => d.val < 7
  | .m (.getTop d) => d.val < 7
  | _ => False

/-- its effect on the registers (`f` the frame register, `t` the stub frame address) -/
def sEff (f t : BitVec 64) : ZOp → (Reg → BitVec 64) → (Reg → BitVec 64)
  | .y (.x (.a (.mov d a))), g => fun r => if r = d then g a else g r
  | .y (.x (.a (.li d c))), g => fun r => if r = d then c else g r
  | .y (.x (.a (.bin op d a b))), g => fun r => if r = d then op.eval (g a) (g b) else g r
  | .m (.getFr d), g => fun r => if r = d then f else g r
  | .m (.getTop d), g => fun r => if r = d then t else g r
  | _, g => g

def sEffs (f t : BitVec 64) : List ZOp → (Reg → BitVec 64) → (Reg → BitVec 64)
  | [], g => g
  | o :: os, g => sEffs f t os (sEff f t o g)

theorem step_simple {o : ZOp} (ho : simpleOK o) {s : M.S} {pc : BitVec 64} (hA : M.At s pc (M.encZ o)) :
    M.runsTo s fun s' => M.Done s s' (next pc (M.encZ o).length) ∧
      (∀ r, M.get s' r = sEff (M.fr s) (BitVec.ofNat 64 (M.frameAt s 0)) o (M.get s) r) ∧ M.mem s' = M.mem s := by
  match o, ho with
  | .y (.x (.a (.mov d a))), ho =>
    exact M.runsTo_mono (M.law_mov ho hA) fun s' ⟨d', st, m⟩ => ⟨d', fun r => by rw [st r]; rfl, m⟩
  | .y (.x (.a (.li d c))), ho =>
    exact M.runsTo_mono (M.law_li ho hA) fun s' ⟨d', st, m⟩ => ⟨d', fun r => by rw [st r]; rfl, m⟩
  | .y (.x (.a (.bin op d a b))), ⟨h1, h2, h3⟩ =>
    exact M.runsTo_mono (M.law_bin h1 h2 h3 hA) fun s' ⟨d', st, m⟩ => ⟨d', fun r => by rw [st r]; rfl, m⟩
  | .m (.getFr d), ho =>
    exact M.runsTo_mono (M.law_getFr ho hA) fun s' ⟨d', st, m⟩ => ⟨d', fun r => by rw [st r]; rfl, m⟩
  | .m (.getTop d), ho =>
    exact M.runsTo_mono (M.law_getTop ho hA) fun s' ⟨d', st, m⟩ => ⟨d', fun r => by rw [st r]; rfl, m⟩

theorem run_simple : ∀ (os : List ZOp), (∀ o ∈ os, simpleOK o) → ∀ {s : M.S} {pc : BitVec 64},
    M.At s pc (M.codeZ os) →
    M.runsTo s fun s' => M.Done s s' (next pc (M.codeZ os).length) ∧
      (∀ r, M.get s' r = sEffs (M.fr s) (BitVec.ofNat 64 (M.frameAt s 0)) os (M.get s) r) ∧ M.mem s' = M.mem s
  | [], _, s, pc, hA => M.runsTo_of ⟨by
      show M.Done s s (next pc 0); rw [next_zero]; exact Core.Done.refl _ hA.ok hA.hpc, fun _ => rfl, rfl⟩
  | o :: os, ho, s, pc, hA => by
    rw [codeZ_cons] at hA
    obtain ⟨hA1, hc2, ho2⟩ := Core.At.split _ hA
    refine M.runsTo_trans (M.step_simple (ho o List.mem_cons_self) hA1) fun s₁ ⟨d₁, g₁, m₁⟩ => ?_
    refine M.runsTo_mono (run_simple os (fun o' h => ho o' (List.mem_cons_of_mem _ h))
      (Core.Done.at _ d₁ (M.codeAt_mem m₁ hc2) ho2)) fun s₂ ⟨d₂, g₂, m₂⟩ => ⟨?_, fun r => ?_, by rw [m₂, m₁]⟩
    · rw [codeZ_cons, List.length_append, ← next_add]; exact Core.Done.trans _ d₁ d₂
    · rw [g₂ r, M.keep_fr d₁.keep, M.frameAt_keep d₁.keep]
      show sEffs _ _ os (M.get s₁) r = sEffs _ _ os (sEff _ _ o (M.get s)) r
      congr 1; funext q; exact g₁ q

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF

/-! ## the check code -/

/-- the heap length register: global 7 -/
def regU : Reg := avar ⟨7, by decide⟩
abbrev opA (o : AOp) : ZOp := .y (.x (.a o))
abbrev opF (o : FOp) : ZOp := .y (.x (.f o))
abbrev opC (o : COp) : ZOp := .y (.c o)
def xs (os : List XOp) : List ZOp := os.map (.y ∘ .x)

theorem regU_eq : regU = ⟨10, by decide⟩ := rfl
theorem rk0_eq : rk 0 = ⟨0, by decide⟩ := rfl
theorem rk1_eq : rk 1 = ⟨1, by decide⟩ := rfl
theorem rk2_eq : rk 2 = ⟨2, by decide⟩ := rfl
theorem rk01 : rk 0 ≠ rk 1 := by decide
theorem rk02 : rk 0 ≠ rk 2 := by decide
theorem rk12 : rk 1 ≠ rk 2 := by decide
theorem rk10 : rk 1 ≠ rk 0 := by decide
theorem rk20 : rk 2 ≠ rk 0 := by decide
theorem rk21 : rk 2 ≠ rk 1 := by decide

/-- zero heap word `u` and count it: `mem[wbase + 8 u] := 0; u := u + 1` (first half: the address) -/
def zb1 (wb : Fin 8) : List ZOp :=
  [opA (.mov (rk 0) regU), opA (.li (rk 1) 3), opA (.bin .shl (rk 0) (rk 0) (rk 1)), opA (.mov (rk 1) (avar wb)),
    opA (.bin .add (rk 0) (rk 0) (rk 1)), opA (.li (rk 1) 0)]
def zb2 : List ZOp :=
  [opA (.mov (rk 0) regU), opA (.li (rk 1) 1), opA (.bin .add (rk 0) (rk 0) (rk 1)), opA (.mov regU (rk 0))]
def zbody (wb : Fin 8) : List ZOp := zb1 wb ++ [opF (.sd (rk 1) (rk 0))] ++ zb2

/-- the slow path's first part: `r1 := (fr - wbase) >> 3`, the heap words that fit below the frame -/
def sh1 (wb : Fin 8) : List ZOp :=
  [.m (.getFr (rk 1)), opA (.mov (rk 2) (avar wb)), opA (.bin .sub (rk 1) (rk 1) (rk 2)), opA (.li (rk 2) 3),
    opA (.bin .lshr (rk 1) (rk 1) (rk 2))]

/-- the call check's register part: `r0 := fr - 8 (n + 1)` (the callee's frame), `r1 := wbase + 8 u` -/
def cc1 (wb : Fin 8) (n : Nat) : List ZOp :=
  [.m (.getFr (rk 0)), opA (.li (rk 1) (BitVec.ofNat 64 (8 * (n + 1)))), opA (.bin .sub (rk 0) (rk 0) (rk 1)),
    opA (.mov (rk 1) regU), opA (.li (rk 2) 3), opA (.bin .shl (rk 1) (rk 1) (rk 2)), opA (.mov (rk 2) (avar wb)),
    opA (.bin .add (rk 1) (rk 1) (rk 2))]

namespace MachineM
variable (M : MachineM)

/-- the zeroing loop: while `u ≤ i` zero word `u` -/
def zloop (wb : Fin 8) (i : BExp) : List ZOp :=
  xs (mgenB i 0) ++ [.m (.bltu (rk 0) regU (M.lenBr + (M.codeZ (zbody wb)).length + M.lenJmp))] ++ zbody wb ++
    [opA (.jmp ((M.codeF (mgenB i 0)).length + M.lenBr + (M.codeZ (zbody wb)).length))]

def lenSlow (wb : Fin 8) (i : BExp) : Nat :=
  (M.codeZ (sh1 wb)).length + M.lenBr + M.lenCall + (M.codeZ (M.zloop wb i)).length

/-- **the access check** of word `i` of the heap, placed at word `pos`; the exit is at word `hp` -/
def chkA (wb : Fin 8) (hp pos : Nat) (i : BExp) : List ZOp :=
  xs (mgenB i 0) ++ [.m (.bltu (rk 0) regU (M.lenBr + M.lenSlow wb i))] ++ sh1 wb ++
    [.m (.bltu (rk 0) (rk 1) (M.lenBr + M.lenCall)),
      opC (.call ((hp : Int) - ((pos + (M.codeF (mgenB i 0)).length + M.lenBr + (M.codeZ (sh1 wb)).length +
        M.lenBr : Nat) : Int)))] ++ M.zloop wb i

def lenChkA (wb : Fin 8) (i : BExp) : Nat := (M.codeF (mgenB i 0)).length + M.lenBr + M.lenSlow wb i

/-- **the call check** for a callee with `n` locals, placed at word `pos` -/
def chkF (wb : Fin 8) (hp pos n : Nat) : List ZOp :=
  cc1 wb n ++ [.m (.bgeu (rk 0) (rk 1) (M.lenBr + M.lenCall)),
    opC (.call ((hp : Int) - ((pos + (M.codeZ (cc1 wb n)).length + M.lenBr : Nat) : Int)))]

def lenChkF (wb : Fin 8) (n : Nat) : Nat := (M.codeZ (cc1 wb n)).length + M.lenBr + M.lenCall

theorem codeZ_xs (os : List XOp) : M.codeZ (xs os) = M.codeF os := M.codeZ_x os

theorem encZ_m (o : KOp) : M.encZ (.m o) = M.encM o := rfl
theorem encZ_C (o : COp) : M.encZ (opC o) = M.encC o := rfl
theorem encZ_A (o : AOp) : M.encZ (opA o) = M.enc o := rfl
theorem encZ_F (o : FOp) : M.encZ (opF o) = M.encX o := rfl

theorem len_chkA (wb : Fin 8) (hp pos : Nat) (i : BExp) : (M.codeZ (M.chkA wb hp pos i)).length = M.lenChkA wb i := by
  simp only [chkA, lenChkA, lenSlow, codeZ_append, codeZ_xs, codeZ_cons, codeZ_nil, encZ_m, encZ_C, M.len_bltu,
    M.len_call, List.length_append, List.length_nil]
  omega

theorem len_chkF (wb : Fin 8) (hp pos n : Nat) : (M.codeZ (M.chkF wb hp pos n)).length = M.lenChkF wb n := by
  simp only [chkF, lenChkF, codeZ_append, codeZ_cons, codeZ_nil, encZ_m, encZ_C, M.len_bgeu, M.len_call,
    List.length_append, List.length_nil]
  omega

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF

theorem avar_ne_rk (i : Fin 8) {k : Nat} (hk : k < 7) : avar i ≠ rk k := by
  intro h; have := avar_ge i; rw [h, rk_val (by omega)] at this; omega
theorem rk_ne_avar (i : Fin 8) {k : Nat} (hk : k < 7) : rk k ≠ avar i := fun h => avar_ne_rk i hk h.symm
theorem regU_ne_rk {k : Nat} (hk : k < 7) : regU ≠ rk k := avar_ne_rk _ hk
theorem rk_ne_regU {k : Nat} (hk : k < 7) : rk k ≠ regU := rk_ne_avar _ hk

theorem bv_sub_toNat {x y : Nat} (hy : y ≤ x) (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y).toNat = x - y := by
  have hy' : y < 2 ^ 64 := by omega
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy']
  rw [show 2 ^ 64 - y + x = (x - y) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem bv_add_toNat {x y : Nat} (h : x + y < 2 ^ 64) :
    (BitVec.ofNat 64 x + BitVec.ofNat 64 y).toNat = x + y := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x) (by omega),
    Nat.mod_eq_of_lt (a := y) (by omega), Nat.mod_eq_of_lt h]

theorem bv_shl3_toNat {x : Nat} (h : 8 * x < 2 ^ 64) :
    (Op.eval .shl (BitVec.ofNat 64 x) 3).toNat = 8 * x := by
  simp only [Op.eval]
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  have : (3 : BitVec 64).toNat % 64 = 3 := rfl
  rw [this, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := x) (by omega)]
  rw [show 2 ^ 3 = 8 from rfl, Nat.mul_comm, Nat.mod_eq_of_lt h]

theorem bv_lshr3_toNat (x : BitVec 64) : (Op.eval .lshr x 3).toNat = x.toNat / 8 := by
  simp only [Op.eval]
  rw [BitVec.toNat_ushiftRight]
  have : (3 : BitVec 64).toNat % 64 = 3 := rfl
  rw [this, Nat.shiftRight_eq_div_pow]

end Proven.Mach

namespace Proven.Mach
open MachineF

theorem movOK_rk_avar {k : Nat} (hk : k < 7) (i : Fin 8) : MovOK (rk k) (avar i) := by
  have hv := avar_ge i
  unfold MovOK; rw [rk_val (by omega)]
  by_cases h : (avar i).val < 11
  · exact .inr (.inl ⟨hk, hv, h⟩)
  · exact .inl ⟨by omega, by omega⟩

theorem movOK_avar_rk0 (i : Fin 8) : MovOK (avar i) (rk 0) := .inr (.inr ⟨rfl, avar_ge i⟩)

theorem cc1_simple (wb : Fin 8) (n : Nat) : ∀ o ∈ cc1 wb n, MachineM.simpleOK o := by
  intro o ho
  simp only [cc1, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact (show (rk 0).val < 7 from by decide)
    | exact (show (rk 1).val < 11 from by decide)
    | exact (show (rk 2).val < 11 from by decide)
    | exact ⟨by decide, rfl, rfl⟩
    | exact movOK_rk_avar (by decide) _

theorem sh1_simple (wb : Fin 8) : ∀ o ∈ sh1 wb, MachineM.simpleOK o := by
  intro o ho
  simp only [sh1, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact (show (rk 1).val < 7 from by decide)
    | exact (show (rk 2).val < 11 from by decide)
    | exact ⟨by decide, rfl, rfl⟩
    | exact movOK_rk_avar (by decide) _

theorem zb1_simple (wb : Fin 8) : ∀ o ∈ zb1 wb, MachineM.simpleOK o := by
  intro o ho
  simp only [zb1, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact (show (rk 1).val < 11 from by decide)
    | exact ⟨by decide, rfl, rfl⟩
    | exact movOK_rk_avar (by decide) _

theorem zb2_simple : ∀ o ∈ zb2, MachineM.simpleOK o := by
  intro o ho
  simp only [zb2, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  all_goals first
    | exact (show (rk 1).val < 11 from by decide)
    | exact ⟨by decide, rfl, rfl⟩
    | exact movOK_rk_avar (by decide) _
    | exact movOK_avar_rk0 _

namespace MachineM
variable (M : MachineM)

theorem cc1_eff (wb : Fin 8) (n : Nat) (f t : BitVec 64) (g : Reg → BitVec 64) :
    sEffs f t (cc1 wb n) g (rk 0) = f - BitVec.ofNat 64 (8 * (n + 1)) ∧
    sEffs f t (cc1 wb n) g (rk 1) = Op.eval .add (Op.eval .shl (g regU) 3) (g (avar wb)) ∧
    ∀ r : Reg, 7 ≤ r.val → sEffs f t (cc1 wb n) g r = g r := by
  refine ⟨?_, ?_, fun r hr => ?_⟩
  · simp [sEffs, sEff, cc1, avar_ne_rk, regU_ne_rk, Op.eval, rk01, rk02, rk12, rk10, rk20, rk21]
  · simp [sEffs, sEff, cc1, avar_ne_rk, regU_ne_rk, Op.eval, rk01, rk02, rk12, rk10, rk20, rk21]
  · have h0 : r ≠ rk 0 := fun e => by subst e; simp [rk] at hr
    have h1 : r ≠ rk 1 := fun e => by subst e; simp [rk] at hr
    have h2 : r ≠ rk 2 := fun e => by subst e; simp [rk] at hr
    simp [sEffs, sEff, cc1, h0, h1, h2]

/-- **the call check runs**: on to the call if the callee's frame stays above the heap, else to the exit -/
theorem chkF_ok {cb : BitVec 64} {Wc : List (BitVec 32)} (hok : M.codeOK cb Wc.length) {wb : Fin 8} {hp pos n : Nat}
    (hsub : Sub Wc pos (M.codeZ (M.chkF wb hp pos n)))
    (hcall : M.callOK ((hp : Int) - ((pos + (M.codeZ (cc1 wb n)).length + M.lenBr : Nat) : Int)))
    (hbz : M.bzOK (M.lenBr + M.lenCall))
    {s : M.S} (hc : M.codeAt s cb Wc) (ho : M.ok s) (hpc : M.pcIs s (next cb pos))
    {u wbase fp : Nat} (hU : M.get s regU = BitVec.ofNat 64 u) (hW : M.get s (avar wb) = BitVec.ofNat 64 wbase)
    (hfr : M.fr s = BitVec.ofNat 64 fp) (hfp : 8 * (n + 1) ≤ fp) (hfp64 : fp < 2 ^ 64)
    (hbig : wbase + 8 * u < 2 ^ 64) :
    M.runsTo s fun s' => (wbase + 8 * u ≤ fp - 8 * (n + 1) ∧ M.Done s s' (next cb (pos + M.lenChkF wb n)) ∧
        (∀ r : Reg, 7 ≤ r.val → M.get s' r = M.get s r) ∧ M.mem s' = M.mem s) ∨
      (fp - 8 * (n + 1) < wbase + 8 * u ∧ M.ok s' ∧ M.keepC s s' ∧ M.pcIs s' (next cb hp) ∧ M.mem s' = M.mem s) := by
  simp only [chkF, codeZ_append, codeZ_cons, codeZ_nil, List.append_nil] at hsub
  obtain ⟨h1, h23⟩ := hsub.split
  obtain ⟨h2, h3⟩ := h23.split
  rw [encZ_m, M.len_bgeu] at h3
  refine M.runsTo_trans (M.run_simple (cc1 wb n) (cc1_simple wb n) (M.at_sub hok hc h1 ho hpc))
    fun s₁ ⟨d₁, g₁, m₁⟩ => ?_
  rw [next_add] at d₁
  obtain ⟨e0, e1, e7⟩ := cc1_eff wb n (M.fr s) (BitVec.ofNat 64 (M.frameAt s 0)) (M.get s)
  have v0 : (M.get s₁ (rk 0)).toNat = fp - 8 * (n + 1) := by
    rw [g₁, e0, hfr]; exact bv_sub_toNat hfp hfp64
  have v1 : (M.get s₁ (rk 1)).toNat = wbase + 8 * u := by
    rw [g₁, e1, hU, hW]
    show (Op.eval .shl (BitVec.ofNat 64 u) 3 + BitVec.ofNat 64 wbase).toNat = _
    rw [BitVec.toNat_add, bv_shl3_toNat (x := u) (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wbase) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  have hc₁ := M.codeAt_mem m₁ hc
  refine M.runsTo_trans (M.law_bgeu hbz (M.at_sub hok hc₁ h2 d₁.ok d₁.hpc)) fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
  rw [v0, v1] at d₂
  by_cases hfit : wbase + 8 * u ≤ fp - 8 * (n + 1)
  · rw [if_pos hfit, next_add] at d₂
    refine M.runsTo_of (.inl ⟨hfit, ?_, fun r hr => by rw [st₂, g₁, e7 r hr], by rw [m₂, m₁]⟩)
    have := Core.Done.trans _ d₁ d₂
    exact M.done_cast this (by simp only [lenChkF]; omega)
  · rw [if_neg hfit, next_add] at d₂
    refine M.runsTo_mono (M.law_call hcall (M.at_sub hok (M.codeAt_mem m₂ hc₁) h3 d₂.ok d₂.hpc))
      fun s₃ ⟨ok₃, kc₃, pc₃, _, _, _, m₃⟩ => .inr ⟨by omega, ok₃, ?_, ?_, by rw [m₃, m₂, m₁]⟩
    · exact M.keepC_trans (M.kC d₁) (M.keepC_trans (M.kC d₂) kc₃)
    · rw [MachineC.next_call] at pc₃; exact pc₃

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF

theorem grow_getElem? (W : List (BitVec 64)) (n q : Nat) :
    (grow W n)[q]? = if q < W.length then W[q]? else if q < n then some 0 else none := by
  unfold grow
  by_cases h : q < W.length
  · rw [if_pos h, List.getElem?_append_left h]
  · rw [if_neg h, List.getElem?_append_right (by omega), List.getElem?_replicate]
    by_cases h2 : q < n
    · rw [if_pos (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2]

theorem grow_self (W : List (BitVec 64)) : grow W W.length = W := by simp [grow]

theorem grow_of_le {W : List (BitVec 64)} {n : Nat} (h : n ≤ W.length) : grow W n = W := by
  simp [grow, show n - W.length = 0 by omega]

/-- zeroing word `k` extends the heap image from `grow W k` to `grow W (k + 1)` -/
theorem heap_extend {m : Mem} {a k : Nat} {W : List (BitVec 64)} (hk : W.length ≤ k)
    (h : bytes m a (8 * k) = (wbytes (grow W k)).map some) :
    bytes (m.wr (a + 8 * k) (le8 0)) a (8 * (k + 1)) = (wbytes (grow W (k + 1))).map some := by
  have hl : ∀ n, (grow W n).length = max W.length n := grow_length W
  refine bytes_of_mem (by rw [length_wbytes, hl]; omega) fun J hJ => ?_
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 8 ∧ J = 8 * q + r := ⟨J / 8, J % 8, by omega, by omega⟩
  rw [getElem?_wbytes _ q r hr]
  by_cases hq : q = k
  · subst hq
    rw [show a + (8 * q + r) = a + 8 * q + r by omega, Mem.wr_in (by rw [length_le8]; exact hr), grow_getElem?,
      if_neg (by omega), if_pos (by omega)]
    simp only [Option.bind_some]
    rw [List.getElem?_eq_getElem (by rw [length_le8]; exact hr)]
  · rw [Mem.wr_out (by rw [length_le8]; omega), mem_of_bytes h (by omega), getElem?_wbytes _ q r hr,
      grow_getElem?, grow_getElem?]
    by_cases h1 : q < W.length
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1, if_pos (show q < k by omega), if_pos (show q < k + 1 by omega)]

open MachineM in
theorem zb1_eff (wb : Fin 8) (f t : BitVec 64) (g : Reg → BitVec 64) :
    sEffs f t (zb1 wb) g (rk 0) = Op.eval .add (Op.eval .shl (g regU) 3) (g (avar wb)) ∧
    sEffs f t (zb1 wb) g (rk 1) = 0 ∧
    ∀ r : Reg, 7 ≤ r.val → sEffs f t (zb1 wb) g r = g r := by
  refine ⟨?_, ?_, fun r hr => ?_⟩
  · simp [sEffs, sEff, zb1, avar_ne_rk, regU_ne_rk, Op.eval, rk01, rk02, rk12, rk10, rk20, rk21]
  · simp [sEffs, sEff, zb1, avar_ne_rk, regU_ne_rk, Op.eval, rk01, rk02, rk12, rk10, rk20, rk21]
  · have h0 : r ≠ rk 0 := fun e => by subst e; simp [rk] at hr
    have h1 : r ≠ rk 1 := fun e => by subst e; simp [rk] at hr
    simp [sEffs, sEff, zb1, h0, h1]

open MachineM in
theorem zb2_eff (f t : BitVec 64) (g : Reg → BitVec 64) :
    sEffs f t zb2 g regU = g regU + 1 ∧
    ∀ r : Reg, 7 ≤ r.val → r ≠ regU → sEffs f t zb2 g r = g r := by
  refine ⟨?_, fun r hr hu => ?_⟩
  · simp [sEffs, sEff, zb2, avar_ne_rk, regU_ne_rk, Op.eval, rk01, rk02, rk12, rk10, rk20, rk21]
  · have h0 : r ≠ rk 0 := fun e => by subst e; simp [rk] at hr
    have h1 : r ≠ rk 1 := fun e => by subst e; simp [rk] at hr
    simp [sEffs, sEff, zb2, h0, h1, hu]

open MachineM in
theorem sh1_eff (wb : Fin 8) (f t : BitVec 64) (g : Reg → BitVec 64) :
    sEffs f t (sh1 wb) g (rk 1) = Op.eval .lshr (f - g (avar wb)) 3 ∧
    sEffs f t (sh1 wb) g (rk 0) = g (rk 0) ∧
    ∀ r : Reg, 7 ≤ r.val → sEffs f t (sh1 wb) g r = g r := by
  refine ⟨?_, ?_, fun r hr => ?_⟩
  · simp [sEffs, sEff, sh1, avar_ne_rk, regU_ne_rk, Op.eval, rk01, rk02, rk12, rk10, rk20, rk21]
  · simp [sEffs, sEff, sh1, avar_ne_rk, regU_ne_rk, Op.eval, rk01, rk02, rk12, rk10, rk20, rk21]
  · have h1 : r ≠ rk 1 := fun e => by subst e; simp [rk] at hr
    have h2 : r ≠ rk 2 := fun e => by subst e; simp [rk] at hr
    simp [sEffs, sEff, sh1, h1, h2]

end Proven.Mach

namespace Proven.Mach
open MachineF

namespace MachineM
variable (M : MachineM)

theorem zbody_len (wb : Fin 8) :
    (M.codeZ (zbody wb)).length = (M.codeZ (zb1 wb)).length + (M.encX (.sd (rk 1) (rk 0))).length +
      (M.codeZ zb2).length := by
  simp only [zbody, codeZ_append, codeZ_one, List.length_append]; rfl

theorem bv_succ {k : Nat} : BitVec.ofNat 64 k + 1 = BitVec.ofNat 64 (k + 1) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

/-- **the zeroing loop**: from heap image `grow W k` (`k` in global 7) to `grow W (j + 1)` -/
theorem zloop_ok {cb : BitVec 64} {Wc : List (BitVec 32)} (hok : M.codeOK cb Wc.length) {wb : Fin 8} {i : BExp}
    {posL : Nat} (hsub : Sub Wc posL (M.codeZ (M.zloop wb i)))
    (hbz : M.bzOK (M.lenBr + (M.codeZ (zbody wb)).length + M.lenJmp))
    (hjmp : M.jmpOK ((M.codeF (mgenB i 0)).length + M.lenBr + (M.codeZ (zbody wb)).length))
    {N fp : Nat} (hF : M.Frm N fp) (hid : i.depth < 7) (hiv : i.vlt (8 + N)) (hic : i.clean = true)
    {env : BEnv} {W : List (BitVec 64)} {wbase : Nat} (hwb7 : wb ≠ ⟨7, by decide⟩)
    (hwbase : env wb.val = BitVec.ofNat 64 wbase)
    (hju : W.length ≤ (i.denote env).toNat) (hfit : wbase + 8 * ((i.denote env).toNat + 1) ≤ fp)
    (hal : wbase % 8 = 0) (hram : M.inRAM wbase (fp - wbase))
    (hwr : ∀ a, wbase ≤ a → a < fp → ∀ s, M.ok s → M.writable s a)
    (hcd : disjoint ⟨cb.toNat, 4 * Wc.length⟩ ⟨wbase, fp - wbase⟩) (s₀ : M.S) :
    ∀ s, (∃ k, W.length ≤ k ∧ k ≤ (i.denote env).toNat + 1 ∧ M.ok s ∧ M.pcIs s (next cb posL) ∧
        M.codeAt s cb Wc ∧ M.keep s₀ s ∧ M.EnvB N fp (env.set hvar (BitVec.ofNat 64 k)) s ∧
        bytes (M.mem s) wbase (8 * k) = (wbytes (grow W k)).map some ∧
        Out [⟨wbase + 8 * W.length, fp - (wbase + 8 * W.length)⟩] (M.mem s₀) (M.mem s)) →
      M.runsTo s fun s' => M.pcIs s' (next cb (posL + (M.codeZ (M.zloop wb i)).length)) ∧
        (M.ok s' ∧ M.keep s₀ s' ∧ M.codeAt s' cb Wc ∧
          M.EnvB N fp (env.set hvar (BitVec.ofNat 64 ((i.denote env).toNat + 1))) s' ∧
          bytes (M.mem s') wbase (8 * ((i.denote env).toNat + 1)) =
            (wbytes (grow W ((i.denote env).toNat + 1))).map some ∧
          Out [⟨wbase + 8 * W.length, fp - (wbase + 8 * W.length)⟩] (M.mem s₀) (M.mem s')) := by
  generalize hj : (i.denote env).toNat = j at *
  have hj64 : j < 2 ^ 64 := by rw [← hj]; exact BitVec.isLt _
  have hlt := M.ramHi_lt
  unfold Base.inRAM at hram
  simp only [zloop, codeZ_append, codeZ_xs, codeZ_cons, codeZ_nil, List.append_nil, encZ_m] at hsub
  obtain ⟨h123, h4⟩ := hsub.split
  obtain ⟨h12, h3⟩ := h123.split
  obtain ⟨h1, h2⟩ := h12.split
  simp only [M.len_bltu, List.length_append] at h2 h3 h4
  have ez : M.codeZ (zbody wb) = M.codeZ (zb1 wb) ++ M.encZ (opF (.sd (rk 1) (rk 0))) ++ M.codeZ zb2 := by
    simp only [zbody, codeZ_append, codeZ_one]
  rw [ez] at h3
  obtain ⟨h3ab, h3c⟩ := h3.split
  obtain ⟨h3a, h3b⟩ := h3ab.split
  simp only [M.len_bltu, List.length_append] at h3a h3b h3c h4
  have hzl : (M.codeZ (M.zloop wb i)).length = (M.codeF (mgenB i 0)).length + M.lenBr +
      (M.codeZ (zbody wb)).length + (M.encZ (opA (.jmp ((M.codeF (mgenB i 0)).length + M.lenBr +
        (M.codeZ (zbody wb)).length)))).length := by
    simp only [zloop, codeZ_append, codeZ_xs, codeZ_cons, codeZ_nil, List.append_nil, encZ_m, M.len_bltu,
      List.length_append]
  refine M.runsTo_while (Inv := fun s => ∃ k, W.length ≤ k ∧ k ≤ j + 1 ∧ M.ok s ∧ M.pcIs s (next cb posL) ∧
        M.codeAt s cb Wc ∧ M.keep s₀ s ∧ M.EnvB N fp (env.set hvar (BitVec.ofNat 64 k)) s ∧
        bytes (M.mem s) wbase (8 * k) = (wbytes (grow W k)).map some ∧
        Out [⟨wbase + 8 * W.length, fp - (wbase + 8 * W.length)⟩] (M.mem s₀) (M.mem s))
    (next cb posL) _ (fun s => j + 1 - (M.get s regU).toNat) (fun s ⟨_, _, _, _, hpc, _⟩ => hpc) ?_
  intro s ⟨k, hk1, hk2, ho, hpc, hc, hks, henv, hheap, hout⟩
  have hie : i.denote (env.set hvar (BitVec.ofNat 64 k)) = i.denote env :=
    BExp.denote_clean hic fun x hx => by
      simp only [BEnv.set]; rw [if_neg (fun e => hx (by rw [e]; exact hvar_unread))]
  have hUk : M.get s regU = BitVec.ofNat 64 k := by
    rw [show regU = avar ⟨7, by decide⟩ from rfl, henv.reg]; simp [BEnv.set, hvar]
  have hk64 : k < 2 ^ 64 := by omega
  have hUn : (M.get s regU).toNat = k := by rw [hUk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  -- 1. `r0 := i`
  refine M.runsTo_trans (M.genB_ok hF _ i 0 (by omega) hiv (M.at_sub hok hc h1 ho hpc) henv)
    fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
  rw [next_add] at d₁
  rw [hie] at v₁
  have hc₁ := M.codeAt_mem m₁ hc
  have hU₁ : M.get s₁ regU = BitVec.ofNat 64 k := by rw [k₁ _ (.inr (by decide)), hUk]
  -- 2. `u > i`: done
  refine M.runsTo_trans (M.law_bltu hbz (M.at_sub hok hc₁ h2 d₁.ok d₁.hpc)) fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
  have hr0 : (M.get s₁ (rk 0)).toNat = j := by rw [v₁, hj]
  rw [hr0, hU₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64] at d₂
  by_cases hjk : j < k
  · rw [if_pos hjk, next_add] at d₂
    have hkj : k = j + 1 := by omega
    subst hkj
    refine M.runsTo_of (.inl ⟨M.pcIs_cast d₂.hpc (by rw [hzl, encZ_A, M.len_jmp]; omega), d₂.ok,
      M.keep_trans hks (M.keep_trans d₁.keep d₂.keep), M.codeAt_mem (by rw [m₂, m₁]) hc,
      EnvB.of M.toMachineF henv (by rw [m₂, m₁]) (M.keep_trans d₁.keep d₂.keep)
        (fun i' => by rw [st₂, k₁ _ (.inr (avar_ge i'))]), by rw [m₂, m₁]; exact hheap,
      by rw [m₂, m₁]; exact hout⟩)
  rw [if_neg hjk, next_add] at d₂
  have hc₂ := M.codeAt_mem m₂ hc₁
  -- 3. `r0 := wbase + 8 k`, `r1 := 0`
  refine M.runsTo_trans (M.run_simple (zb1 wb) (zb1_simple wb) (M.at_sub hok hc₂ h3a d₂.ok
    (M.pcIs_cast d₂.hpc (by omega))))
    fun s₃ ⟨d₃, g₃, m₃⟩ => ?_
  rw [next_add] at d₃
  obtain ⟨e30, e31, e37⟩ := zb1_eff wb (M.fr s₂) (BitVec.ofNat 64 (M.frameAt s₂ 0)) (M.get s₂)
  have hW₂ : M.get s₂ (avar wb) = BitVec.ofNat 64 wbase := by
    rw [st₂, k₁ _ (.inr (avar_ge _)), henv.reg]; simp only [BEnv.set]
    rw [if_neg (fun e => hwb7 (Fin.ext (by rw [e]; rfl)))]; exact hwbase
  have ha₃ : (M.get s₃ (rk 0)).toNat = wbase + 8 * k := by
    have hU₂ : M.get s₂ regU = BitVec.ofNat 64 k := by rw [st₂, hU₁]
    rw [g₃, e30, hU₂, hW₂]
    show (Op.eval .shl (BitVec.ofNat 64 k) 3 + BitVec.ofNat 64 wbase).toNat = _
    rw [BitVec.toNat_add, bv_shl3_toNat (x := k) (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := wbase) (by omega),
      Nat.mod_eq_of_lt (by omega)]; omega
  have hv₃ : M.get s₃ (rk 1) = 0 := by rw [g₃, e31]
  have hc₃ := M.codeAt_mem m₃ hc₂
  -- 4. `mem[r0] := 0`
  refine M.runsTo_trans (M.law_sd (rk_val (by omega)) (rk_val (by omega)) (M.at_sub hok hc₃ h3b d₃.ok d₃.hpc)
    (by rw [ha₃]; unfold Base.inRAM; omega) (by rw [ha₃]; omega)
    (fun x hx => by rw [ha₃]; exact hwr _ (by omega) (by omega) _ d₃.ok)) fun s₄ ⟨d₄, st₄, m₄⟩ => ?_
  rw [next_add] at d₄
  rw [ha₃, hv₃, m₃, m₂, m₁] at m₄
  have hcd₄ : Out [⟨wbase + 8 * k, 8⟩] (M.mem s) (M.mem s₄) := by
    rw [m₄]; exact Out.wr (List.mem_singleton_self _) (Nat.le_refl _) (by rw [length_le8]; exact Nat.le_refl _)
  have hk8 : wbase + 8 * k + 8 ≤ fp := by omega
  have hcdk : disjoint ⟨cb.toNat, 4 * Wc.length⟩ ⟨wbase + 8 * k, 8⟩ := by
    unfold disjoint at hcd ⊢; dsimp only at hcd ⊢; omega
  have hc₄ : M.codeAt s₄ cb Wc := M.codeAt_out hc₃ hok (fun r hr => by
    rw [List.mem_singleton] at hr; rw [hr]; exact hcdk)
    (by rw [m₃, m₂, m₁]; exact hcd₄)
  -- 5. `u := u + 1`
  refine M.runsTo_trans (M.run_simple zb2 zb2_simple (M.at_sub hok hc₄ h3c d₄.ok
    (M.pcIs_cast d₄.hpc (by rw [encZ_F]; omega))))
    fun s₅ ⟨d₅, g₅, m₅⟩ => ?_
  rw [next_add] at d₅
  obtain ⟨e5U, e57⟩ := zb2_eff (M.fr s₄) (BitVec.ofNat 64 (M.frameAt s₄ 0)) (M.get s₄)
  have hU₅ : M.get s₅ regU = BitVec.ofNat 64 (k + 1) := by
    rw [g₅, e5U, st₄, g₃, e37 _ (by decide), st₂, hU₁, bv_succ]
  have hc₅ := M.codeAt_mem m₅ hc₄
  -- 6. back to the head
  refine M.runsTo_mono (M.law_jmp hjmp (M.at_sub hok hc₅ h4 d₅.ok
    (M.pcIs_cast d₅.hpc (by rw [M.zbody_len wb, encZ_F]; omega)))) fun s₆ ⟨d₆, st₆, m₆⟩ => .inr ⟨⟨k + 1,
    by omega, by omega, d₆.ok, M.pcIs_jmp d₆.hpc (by omega),
    M.codeAt_mem (by rw [m₆, m₅]) hc₄, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact M.keep_trans hks (M.keep_trans d₁.keep (M.keep_trans d₂.keep (M.keep_trans d₃.keep
      (M.keep_trans d₄.keep (M.keep_trans d₅.keep d₆.keep)))))
  · have hkk := M.keep_trans d₁.keep (M.keep_trans d₂.keep (M.keep_trans d₃.keep
      (M.keep_trans d₄.keep (M.keep_trans d₅.keep d₆.keep))))
    refine ⟨fun i' => ?_, by rw [M.keep_fr hkk, henv.fr], fun jj hjj => ?_⟩
    · by_cases h7 : i' = ⟨7, by decide⟩
      · subst h7; rw [st₆]; simp only [BEnv.set, hvar, if_true]; exact hU₅
      · have hne : avar i' ≠ regU := fun e => h7 (avar_inj e)
        rw [st₆, g₅, e57 _ (avar_ge i') hne, st₄, g₃, e37 _ (avar_ge i'), st₂, k₁ _ (.inr (avar_ge i')), henv.reg]
        simp only [BEnv.set]
        rw [if_neg (fun e => h7 (Fin.ext (by rw [e]; rfl))), if_neg (fun e => h7 (Fin.ext (by rw [e]; rfl)))]
    · rw [m₆, m₅, m₄, bytes_wr_out (.inr (by rw [length_le8]; omega))]
      have := henv.slot jj hjj
      simp only [BEnv.set] at this ⊢
      rw [if_neg (by unfold hvar; omega)] at this ⊢; exact this
  · rw [m₆, m₅, m₄]; exact heap_extend hk1 hheap
  · rw [m₆, m₅]
    exact hout.trans (Out.mono hcd₄ fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by dsimp only; omega, by dsimp only; omega⟩)
  · show j + 1 - (M.get s₆ regU).toNat < j + 1 - (M.get s regU).toNat
    rw [st₆, hU₅, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hUn]; omega

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF

namespace MachineM
variable (M : MachineM)

theorem set_self (env : BEnv) (v : Nat) : env.set v (env v) = env := by
  funext x; simp only [BEnv.set]; split
  · next h => rw [h]
  · rfl

/-- **the access check runs**: with the heap grown to cover word `i` (zeroed), or to the exit when that word
would reach the current frame -/
theorem chkA_ok {cb : BitVec 64} {Wc : List (BitVec 32)} (hok : M.codeOK cb Wc.length) {wb : Fin 8}
    {hp pos : Nat} {i : BExp} (hsub : Sub Wc pos (M.codeZ (M.chkA wb hp pos i)))
    (hcall : M.callOK ((hp : Int) - ((pos + (M.codeF (mgenB i 0)).length + M.lenBr + (M.codeZ (sh1 wb)).length +
        M.lenBr : Nat) : Int)))
    (hbz1 : M.bzOK (M.lenBr + M.lenSlow wb i)) (hbz2 : M.bzOK (M.lenBr + M.lenCall))
    (hbz3 : M.bzOK (M.lenBr + (M.codeZ (zbody wb)).length + M.lenJmp))
    (hjmp : M.jmpOK ((M.codeF (mgenB i 0)).length + M.lenBr + (M.codeZ (zbody wb)).length))
    {N fp : Nat} (hF : M.Frm N fp) (hid : i.depth < 7) (hiv : i.vlt (8 + N)) (hic : i.clean = true)
    {env : BEnv} {W : List (BitVec 64)} {wbase : Nat} (hwb7 : wb ≠ ⟨7, by decide⟩)
    (hwbase : env wb.val = BitVec.ofNat 64 wbase) (hU : env hvar = BitVec.ofNat 64 W.length)
    (hlay : wbase + 8 * W.length ≤ fp) (hal : wbase % 8 = 0) (hram : M.inRAM wbase (fp - wbase))
    (hwr : ∀ a, wbase ≤ a → a < fp → ∀ s, M.ok s → M.writable s a)
    (hcd : disjoint ⟨cb.toNat, 4 * Wc.length⟩ ⟨wbase, fp - wbase⟩)
    {s : M.S} (hc : M.codeAt s cb Wc) (ho : M.ok s) (hpc : M.pcIs s (next cb pos)) (henv : M.EnvB N fp env s)
    (hheap : bytes (M.mem s) wbase (8 * W.length) = (wbytes W).map some) :
    M.runsTo s fun s' =>
      (wbase + 8 * (grow W ((i.denote env).toNat + 1)).length ≤ fp ∧ M.ok s' ∧ M.keep s s' ∧
        M.pcIs s' (next cb (pos + M.lenChkA wb i)) ∧ M.codeAt s' cb Wc ∧
        M.EnvB N fp (env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length)) s' ∧
        bytes (M.mem s') wbase (8 * (grow W ((i.denote env).toNat + 1)).length) =
          (wbytes (grow W ((i.denote env).toNat + 1))).map some ∧
        Out [⟨wbase + 8 * W.length, fp - (wbase + 8 * W.length)⟩] (M.mem s) (M.mem s')) ∨
      (fp < wbase + 8 * ((i.denote env).toNat + 1) ∧ M.ok s' ∧ M.keepC s s' ∧ M.pcIs s' (next cb hp) ∧
        M.mem s' = M.mem s) := by
  have hgl := grow_length W ((i.denote env).toNat + 1)
  generalize hj : (i.denote env).toNat = j at *
  have hj64 : j < 2 ^ 64 := by rw [← hj]; exact BitVec.isLt _
  have hlt := M.ramHi_lt
  have hfr := MachineF.Frm.fr M.toMachineF hF henv.fr
  unfold Base.inRAM at hram
  have hwl : W.length < 2 ^ 64 := by omega
  rw [chkA] at hsub
  simp only [codeZ_append, codeZ_xs, codeZ_cons, codeZ_nil, List.append_nil] at hsub
  obtain ⟨hX, h6⟩ := hsub.split
  obtain ⟨hABS, hBC⟩ := hX.split
  obtain ⟨hAB, h3⟩ := hABS.split
  obtain ⟨h1, h2⟩ := hAB.split
  obtain ⟨h4, h5⟩ := hBC.split
  simp only [encZ_m, encZ_C, M.len_bltu, M.len_call, List.length_append] at h2 h3 h4 h5 h6
  -- 1. `r0 := i`
  refine M.runsTo_trans (M.genB_ok hF env i 0 (by omega) hiv (M.at_sub hok hc h1 ho hpc) henv)
    fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
  rw [next_add] at d₁
  have hc₁ := M.codeAt_mem m₁ hc
  have hU₁ : M.get s₁ regU = BitVec.ofNat 64 W.length := by
    rw [k₁ _ (.inr (by decide)), show regU = avar ⟨7, by decide⟩ from rfl, henv.reg]; exact hU
  have hr0 : (M.get s₁ (rk 0)).toNat = j := by rw [v₁, hj]
  refine M.runsTo_trans (M.law_bltu hbz1 (M.at_sub hok hc₁ h2 d₁.ok d₁.hpc)) fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
  rw [hr0, hU₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwl] at d₂
  by_cases hfast : j < W.length
  · -- the word is in the heap
    rw [if_pos hfast, next_add] at d₂
    have hg : grow W (j + 1) = W := grow_of_le (by omega)
    rw [hg]
    refine M.runsTo_of (.inl ⟨hlay, d₂.ok, M.keep_trans d₁.keep d₂.keep,
      M.pcIs_cast d₂.hpc (by simp only [lenChkA]; omega), M.codeAt_mem m₂ hc₁, ?_, by rw [m₂, m₁]; exact hheap,
      Out.of_eq (by rw [m₂, m₁])⟩)
    rw [← hU, set_self]
    exact EnvB.of M.toMachineF henv (by rw [m₂, m₁]) (M.keep_trans d₁.keep d₂.keep)
      (fun i' => by rw [st₂, k₁ _ (.inr (avar_ge i'))])
  rw [if_neg hfast, next_add] at d₂
  have hc₂ := M.codeAt_mem m₂ hc₁
  -- 2. `r1 := (fr - wbase) >> 3`
  refine M.runsTo_trans (M.run_simple (sh1 wb) (sh1_simple wb) (M.at_sub hok hc₂ h3 d₂.ok
    (M.pcIs_cast d₂.hpc (by omega))))
    fun s₃ ⟨d₃, g₃, m₃⟩ => ?_
  rw [next_add] at d₃
  obtain ⟨e31, e30, e37⟩ := sh1_eff wb (M.fr s₂) (BitVec.ofNat 64 (M.frameAt s₂ 0)) (M.get s₂)
  have hfr₂ : M.fr s₂ = BitVec.ofNat 64 fp := by rw [M.keep_fr d₂.keep, M.keep_fr d₁.keep, henv.fr]
  have hW₂ : M.get s₂ (avar wb) = BitVec.ofNat 64 wbase := by
    rw [st₂, k₁ _ (.inr (avar_ge _)), henv.reg]; exact hwbase
  have hq : (M.get s₃ (rk 1)).toNat = (fp - wbase) / 8 := by
    rw [g₃, e31, hfr₂, hW₂, bv_lshr3_toNat, bv_sub_toNat (by omega) (by omega)]
  have hr0₃ : (M.get s₃ (rk 0)).toNat = j := by rw [g₃, e30, st₂, hr0]
  have hc₃ := M.codeAt_mem m₃ hc₂
  refine M.runsTo_trans (M.law_bltu hbz2 (M.at_sub hok hc₃ h4 d₃.ok (M.pcIs_cast d₃.hpc (by omega))))
    fun s₄ ⟨d₄, st₄, m₄⟩ => ?_
  rw [hr0₃, hq] at d₄
  by_cases hfit : j < (fp - wbase) / 8
  · -- 3. zero the new words
    rw [if_pos hfit, next_add] at d₄
    have hfit' : wbase + 8 * (j + 1) ≤ fp := by omega
    have hkk := M.keep_trans d₁.keep (M.keep_trans d₂.keep (M.keep_trans d₃.keep d₄.keep))
    have hmm : M.mem s₄ = M.mem s := by rw [m₄, m₃, m₂, m₁]
    have henv₄ : M.EnvB N fp (env.set hvar (BitVec.ofNat 64 W.length)) s₄ := by
      rw [← hU, set_self]
      exact EnvB.of M.toMachineF henv hmm hkk fun i' => by
        rw [st₄, g₃, e37 _ (avar_ge i'), st₂, k₁ _ (.inr (avar_ge i'))]
    have hz := M.zloop_ok hok (wb := wb) (i := i) (posL := pos + (M.codeF (mgenB i 0)).length + M.lenBr +
      (M.codeZ (sh1 wb)).length + (M.lenBr + M.lenCall)) (h6.cast (by omega)) hbz3 hjmp hF hid hiv hic
      (env := env) (W := W) hwb7 hwbase (by omega) (by omega) hal (by unfold Base.inRAM; omega) hwr hcd s
    rw [hj] at hz
    refine M.runsTo_mono (hz s₄ ⟨W.length, Nat.le_refl _, by omega, d₄.ok, M.pcIs_cast d₄.hpc (by omega),
      M.codeAt_mem hmm hc, hkk, henv₄, by rw [hmm, grow_self]; exact hheap, Out.of_eq hmm⟩)
      fun s₅ ⟨pc₅, ok₅, kp₅, hc₅, env₅, heap₅, out₅⟩ => .inl ⟨?_, ok₅, kp₅, M.pcIs_cast pc₅ ?_, hc₅, ?_, ?_, out₅⟩
    · rw [hgl]; omega
    · simp only [lenChkA, lenSlow]; omega
    · rw [hgl, show max W.length (j + 1) = j + 1 by omega]; exact env₅
    · rw [hgl, show max W.length (j + 1) = j + 1 by omega]; exact heap₅
  · -- 4. out of memory
    rw [if_neg hfit, next_add] at d₄
    refine M.runsTo_mono (M.law_call hcall (M.at_sub hok (M.codeAt_mem m₄ hc₃) h5 d₄.ok d₄.hpc))
      fun s₅ ⟨ok₅, kc₅, pc₅, _, _, _, m₅⟩ => .inr ⟨by omega, ok₅, ?_, ?_, by rw [m₅, m₄, m₃, m₂, m₁]⟩
    · exact M.keepC_trans (M.kC d₁) (M.keepC_trans (M.kC d₂) (M.keepC_trans (M.kC d₃) (M.keepC_trans (M.kC d₄) kc₅)))
    · rw [show pos + ((M.codeF (mgenB i 0)).length + M.lenBr + (M.codeZ (sh1 wb)).length) + M.lenBr =
        pos + (M.codeF (mgenB i 0)).length + M.lenBr + (M.codeZ (sh1 wb)).length + M.lenBr by omega,
        MachineC.next_call] at pc₅; exact pc₅

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF

namespace MachineM
variable (M : MachineM) (P : Prog) (bv : List Nat) (wb : Fin 8) (off : Nat → Nat) (hp : Nat)

/-! ## the compiler with checks -/

/-- the words of a call-free statement with the access checks -/
def lenBM : BStmt → Nat
  | .assign v e => (M.codeF (M.compB bv [wb.val] (.assign v e))).length
  | .load v b i => (M.codeF (M.compB bv [wb.val] (.load v b i))).length
  | .store b i e => (M.codeF (M.compB bv [wb.val] (.store b i e))).length
  | .seq p q => lenBM p + lenBM q
  | .loop c b => (M.codeF (mgenB c 0)).length + M.lenBz + lenBM b + M.lenJmp
  | .load64 v b i => M.lenChkA wb i + (M.codeF (M.compB bv [wb.val] (.load64 v b i))).length
  | .store64 b i e => M.lenChkA wb i + (M.codeF (M.compB bv [wb.val] (.store64 b i e))).length
  | .mop m v a b => (M.codeF (M.compB bv [wb.val] (.mop m v a b))).length

/-- a call-free statement with the access checks, placed at word `pos` -/
def compBM : Nat → BStmt → List ZOp
  | _, .assign v e => xs (M.compB bv [wb.val] (.assign v e))
  | _, .load v b i => xs (M.compB bv [wb.val] (.load v b i))
  | _, .store b i e => xs (M.compB bv [wb.val] (.store b i e))
  | pos, .seq p q => compBM pos p ++ compBM (pos + M.lenBM bv wb p) q
  | pos, .loop c b => xs (mgenB c 0) ++ [opA (.bz (rk 0) (M.lenBz + M.lenBM bv wb b + M.lenJmp))] ++
      compBM (pos + (M.codeF (mgenB c 0)).length + M.lenBz) b ++
      [opA (.jmp ((M.codeF (mgenB c 0)).length + M.lenBz + M.lenBM bv wb b))]
  | pos, .load64 v b i => M.chkA wb hp pos i ++ xs (M.compB bv [wb.val] (.load64 v b i))
  | pos, .store64 b i e => M.chkA wb hp pos i ++ xs (M.compB bv [wb.val] (.store64 b i e))
  | _, .mop m v a b => xs (M.compB bv [wb.val] (.mop m v a b))

theorem len_compBM : ∀ (p : BStmt) (pos : Nat), (M.codeZ (M.compBM bv wb hp pos p)).length = M.lenBM bv wb p
  | .assign .., _ | .load .., _ | .store .., _ | .mop .., _ => by simp only [compBM, lenBM, codeZ_xs]
  | .seq p q, pos => by
    simp only [compBM, lenBM, codeZ_append, List.length_append, len_compBM p, len_compBM q]
  | .loop c b, pos => by
    simp only [compBM, lenBM, codeZ_append, codeZ_xs, codeZ_one, encZ_A, List.length_append, len_compBM b,
      M.len_bz, M.len_jmp]
  | .load64 v b i, pos => by
    simp only [compBM, lenBM, codeZ_append, codeZ_xs, List.length_append, len_chkA]
  | .store64 b i e, pos => by
    simp only [compBM, lenBM, codeZ_append, codeZ_xs, List.length_append, len_chkA]

/-- the access check is well formed -/
def chkOK (pos : Nat) (i : BExp) : Prop :=
  M.callOK ((hp : Int) - ((pos + (M.codeF (mgenB i 0)).length + M.lenBr + (M.codeZ (sh1 wb)).length +
    M.lenBr : Nat) : Int)) ∧ M.bzOK (M.lenBr + M.lenSlow wb i) ∧ M.bzOK (M.lenBr + M.lenCall) ∧
  M.bzOK (M.lenBr + (M.codeZ (zbody wb)).length + M.lenJmp) ∧
  M.jmpOK ((M.codeF (mgenB i 0)).length + M.lenBr + (M.codeZ (zbody wb)).length)

def wfBM (N : Nat) : Nat → BStmt → Prop
  | _, .assign v e => M.wfB N bv [wb.val] (.assign v e)
  | _, .load v b i => M.wfB N bv [wb.val] (.load v b i)
  | _, .store b i e => M.wfB N bv [wb.val] (.store b i e)
  | pos, .seq p q => wfBM N pos p ∧ wfBM N (pos + M.lenBM bv wb p) q
  | pos, .loop c b => c.depth < 7 ∧ c.vlt (8 + N) ∧ M.bzOK (M.lenBz + M.lenBM bv wb b + M.lenJmp) ∧
      M.jmpOK ((M.codeF (mgenB c 0)).length + M.lenBz + M.lenBM bv wb b) ∧
      wfBM N (pos + (M.codeF (mgenB c 0)).length + M.lenBz) b
  | pos, .load64 v b i => M.wfB N bv [wb.val] (.load64 v b i) ∧ M.chkOK wb hp pos i
  | pos, .store64 b i e => M.wfB N bv [wb.val] (.store64 b i e) ∧ M.chkOK wb hp pos i
  | _, .mop m v a b => False

/-- the words of a statement with calls -/
def lenCM : CStmt → Nat
  | .base p => M.lenBM bv wb p
  | .seq p q => lenCM p + lenCM q
  | .ite c p q => (M.codeF (mgenB c 0)).length + M.lenBz + lenCM p + (M.lenLi + M.lenBz) + lenCM q
  | .loop c b => (M.codeF (mgenB c 0)).length + M.lenBz + lenCM b + M.lenJmp
  | .call res f args => M.lenChkF wb (nlOf P f) + M.lenArgs (nlOf P f) args + M.lenCall + (M.codeF (setV res)).length

/-- a statement with calls and checks, placed at word `pos`; function `f` at word `off f` -/
def compCM : Nat → CStmt → List ZOp
  | pos, .base p => M.compBM bv wb hp pos p
  | pos, .seq p q => compCM pos p ++ compCM (pos + M.lenCM P bv wb p) q
  | pos, .ite c p q =>
      xs (mgenB c 0) ++ [opA (.bz (rk 0) (M.lenBz + M.lenCM P bv wb p + (M.lenLi + M.lenBz)))] ++
      compCM (pos + (M.codeF (mgenB c 0)).length + M.lenBz) p ++
      [opA (.li (rk 0) 0), opA (.bz (rk 0) (M.lenBz + M.lenCM P bv wb q))] ++
      compCM (pos + (M.codeF (mgenB c 0)).length + M.lenBz + M.lenCM P bv wb p + (M.lenLi + M.lenBz)) q
  | pos, .loop c b =>
      xs (mgenB c 0) ++ [opA (.bz (rk 0) (M.lenCM P bv wb b + M.lenBz + M.lenJmp))] ++
      compCM (pos + (M.codeF (mgenB c 0)).length + M.lenBz) b ++
      [opA (.jmp ((M.codeF (mgenB c 0)).length + M.lenBz + M.lenCM P bv wb b))]
  | pos, .call res f args =>
      M.chkF wb hp pos (nlOf P f) ++
      (argsC (nlOf P f) 0 (padArgs (nlOf P f) args)).map .y ++
      [opC (.call ((off f : Int) - ((pos + M.lenChkF wb (nlOf P f) + M.lenArgs (nlOf P f) args : Nat) : Int)))] ++
      xs (setV res)

theorem len_compCM : ∀ (p : CStmt) (pos : Nat), (M.codeZ (M.compCM P bv wb off hp pos p)).length = M.lenCM P bv wb p
  | .base p, pos => by simp only [compCM, lenCM, len_compBM]
  | .seq p q, pos => by
    simp only [compCM, lenCM, codeZ_append, List.length_append, len_compCM p, len_compCM q]
  | .ite c p q, pos => by
    simp only [compCM, lenCM, codeZ_append, codeZ_xs, codeZ_one, codeZ_cons, codeZ_nil, List.append_nil, encZ_A,
      List.length_append, len_compCM p, len_compCM q, M.len_bz, MachineC.lenLi_eq]
  | .loop c b, pos => by
    simp only [compCM, lenCM, codeZ_append, codeZ_xs, codeZ_one, encZ_A, List.length_append, len_compCM b,
      M.len_bz, M.len_jmp]
  | .call res f args, pos => by
    simp only [compCM, lenCM, MachineC.lenArgs, codeZ_append, codeZ_xs, codeZ_y, codeZ_one, encZ_C, List.length_append,
      M.len_call, len_chkF]

def wfCM (N : Nat) : Nat → CStmt → Prop
  | pos, .base p => M.wfBM bv wb hp N pos p
  | pos, .seq p q => wfCM N pos p ∧ wfCM N (pos + M.lenCM P bv wb p) q
  | pos, .ite c p q => c.depth < 7 ∧ c.vlt (8 + N) ∧
      M.bzOK (M.lenBz + M.lenCM P bv wb p + (M.lenLi + M.lenBz)) ∧ M.bzOK (M.lenBz + M.lenCM P bv wb q) ∧
      wfCM N (pos + (M.codeF (mgenB c 0)).length + M.lenBz) p ∧
      wfCM N (pos + (M.codeF (mgenB c 0)).length + M.lenBz + M.lenCM P bv wb p + (M.lenLi + M.lenBz)) q
  | pos, .loop c b => c.depth < 7 ∧ c.vlt (8 + N) ∧ M.bzOK (M.lenCM P bv wb b + M.lenBz + M.lenJmp) ∧
      M.jmpOK ((M.codeF (mgenB c 0)).length + M.lenBz + M.lenCM P bv wb b) ∧
      wfCM N (pos + (M.codeF (mgenB c 0)).length + M.lenBz) b
  | pos, .call res f args => f < P.length ∧ args.length ≤ nlOf P f ∧ (∀ e ∈ args, e.depth < 7 ∧ e.vlt (8 + N)) ∧
      res < 8 + N ∧ res ∉ bv ∧ res ∉ [wb.val] ∧
      M.callOK ((off f : Int) - ((pos + M.lenChkF wb (nlOf P f) + M.lenArgs (nlOf P f) args : Nat) : Int)) ∧
      M.callOK ((hp : Int) - ((pos + (M.codeZ (cc1 wb (nlOf P f))).length + M.lenBr : Nat) : Int)) ∧
      M.bzOK (M.lenBr + M.lenCall)

/-- a function with checks, placed at word `pos` -/
def fnCM (pos : Nat) (F : Fn) : List ZOp :=
  [opC (.enterC F.nlocals)] ++ M.compCM P bv wb off hp (pos + (M.encC (.enterC F.nlocals)).length) F.body ++
    xs (mgenB F.ret 0) ++ [opC (.leaveC F.nlocals), opA .ret]

def lenFM (F : Fn) : Nat :=
  (M.encC (.enterC F.nlocals)).length + M.lenCM P bv wb F.body + (M.codeF (mgenB F.ret 0)).length +
    ((M.encC (.leaveC F.nlocals)).length + (M.enc .ret).length)

theorem len_fnCM (pos : Nat) (F : Fn) : (M.codeZ (M.fnCM P bv wb off hp pos F)).length = M.lenFM P bv wb F := by
  simp only [fnCM, lenFM, codeZ_append, codeZ_xs, codeZ_one, codeZ_cons, codeZ_nil, List.append_nil, encZ_A,
    encZ_C, List.length_append, len_compCM]

def wfFM (pos : Nat) (F : Fn) : Prop :=
  F.nlocals ≤ M.maxSlots ∧ F.ret.depth < 7 ∧ F.ret.vlt (8 + F.nlocals) ∧
    M.wfCM P bv wb off hp F.nlocals (pos + (M.encC (.enterC F.nlocals)).length) F.body

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF

namespace MachineM
variable (M : MachineM) (P : Prog) (bv : List Nat) (wb : Fin 8) (off : Nat → Nat) (hp : Nat)

/-- the static context of a run: the program's words `Wc` at `cb`, the byte blocks `R`, the work area
`[wbase, hi)` (heap from the bottom, frames from the top); the exit at word `hp` -/
structure CtxM (cb : BitVec 64) (Wc : List (BitVec 32)) (R : List Region) (wbase hi : Nat) : Prop where
  codeOK : M.codeOK cb Wc.length
  fns : ∀ f (hf : f < P.length), Sub Wc (off f) (M.codeZ (M.fnCM P bv wb off hp (off f) P[f]))
  wf : ∀ f (hf : f < P.length), M.wfFM P bv wb off hp (off f) P[f]
  bvlt : ∀ x ∈ bv, x < 8
  wb7 : wb ≠ ⟨7, by decide⟩
  wbv : wb.val ∉ bv
  hbv : hvar ∉ bv
  ram : ∀ r ∈ R, M.inRAM r.base r.len
  rp : R.Pairwise disjoint
  wr : ∀ r ∈ R, ∀ a, r.base ≤ a → a < r.base + r.len → ∀ s, M.ok s → M.writable s a
  wal : wbase % 8 = 0
  lohi : wbase ≤ hi
  stk : M.inRAM wbase (hi - wbase)
  sR : ∀ r ∈ R, disjoint ⟨wbase, hi - wbase⟩ r
  cd : ∀ r ∈ R ++ [⟨wbase, hi - wbase⟩], disjoint ⟨cb.toNat, 4 * Wc.length⟩ r
  stw : ∀ a, wbase ≤ a → a < hi → ∀ s, M.ok s → M.writable s a

/-- what a statement in the frame `(N, fp)` may write: the byte blocks, its slots, the work area below `fp` -/
def WrtM (N fp : Nat) (R : List Region) (wbase : Nat) : List Region := R ++ slots N fp ++ [⟨wbase, fp - wbase⟩]

/-- the machine holds `σ` with its heap `W` (length in global 7) below the frame -/
structure InvM (N fp : Nat) (R : List Region) (wbase : Nat) (σ : BState) (s : M.S) (W : List (BitVec 64)) : Prop where
  wh : σ.wheap = [W]
  hv : σ.env hvar = BitVec.ofNat 64 W.length
  below : wbase + 8 * W.length ≤ fp
  rel : M.RelB N fp bv [wb.val] R [⟨wbase, 8 * W.length⟩] σ s

variable {M P bv wb off hp}
variable {cb : BitVec 64} {Wc : List (BitVec 32)} {R : List Region} {wbase hi : Nat}

theorem CtxM.lay (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {N fp u : Nat} (h1 : wbase + 8 * u ≤ fp)
    (h2 : fp + 8 * (N + 1) ≤ hi) : M.Lay N fp R [⟨wbase, 8 * u⟩] := by
  have hstk := C.stk; unfold Base.inRAM at hstk
  refine ⟨C.ram, fun r hr => ?_, C.rp, List.pairwise_singleton _ _, fun r hr w hw => ?_, fun r hr => ?_,
    fun w hw => ?_, fun w hw => ?_, C.wr, fun w hw a ha1 ha2 => ?_⟩
  · rw [List.mem_singleton] at hr; subst hr; unfold Base.inRAM; dsimp only; omega
  · rw [List.mem_singleton] at hw; subst hw
    have := C.sR r hr; unfold disjoint at this ⊢; dsimp only at this ⊢; omega
  · have := C.sR r hr; unfold disjoint at this ⊢; dsimp only at this ⊢; omega
  · rw [List.mem_singleton] at hw; subst hw; unfold disjoint; dsimp only; omega
  · rw [List.mem_singleton] at hw; subst hw; exact C.wal
  · rw [List.mem_singleton] at hw; subst hw; dsimp only at ha1 ha2; exact C.stw a ha1 (by omega)

/-- the code is disjoint from every part of the work area -/
theorem CtxM.cd_in (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {a l : Nat} (h1 : wbase ≤ a) (h2 : a + l ≤ hi) :
    disjoint ⟨cb.toNat, 4 * Wc.length⟩ ⟨a, l⟩ := by
  have := C.cd _ memLast; unfold disjoint at this ⊢; dsimp only at this ⊢; omega

theorem CtxM.cdW (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {N fp : Nat} (h1 : wbase ≤ fp)
    (h2 : fp + 8 * (N + 1) ≤ hi) : ∀ r ∈ WrtM N fp R wbase, disjoint ⟨cb.toNat, 4 * Wc.length⟩ r := by
  intro r hr
  unfold WrtM at hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with (hr | hr) | hr
  · exact C.cd r (List.mem_append_left _ hr)
  · obtain ⟨j, hj, rfl⟩ := mem_slots hr; exact C.cd_in (by omega) (by omega)
  · subst hr; exact C.cd_in (Nat.le_refl _) (by omega)

theorem CtxM.codeAt_W (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {N fp : Nat} (h1 : wbase ≤ fp)
    (h2 : fp + 8 * (N + 1) ≤ hi) {s s' : M.S} (hc : M.codeAt s cb Wc)
    (o : Out (WrtM N fp R wbase) (M.mem s) (M.mem s')) : M.codeAt s' cb Wc :=
  M.codeAt_out hc C.codeOK (C.cdW h1 h2) o

theorem allR_wrtM {N fp wbase u : Nat} {R : List Region} {m m' : Mem} (h : wbase + 8 * u ≤ fp)
    (o : Out (AllR N fp R [⟨wbase, 8 * u⟩]) m m') : Out (WrtM N fp R wbase) m m' :=
  Out.mono o fun r hr => by
    unfold AllR at hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (hr | hr) | hr
    · exact ⟨r, List.mem_append_left _ (List.mem_append_left _ hr), Nat.le_refl _, Nat.le_refl _⟩
    · subst hr; exact ⟨_, memLast, Nat.le_refl _, by dsimp only; omega⟩
    · exact ⟨r, List.mem_append_left _ (List.mem_append_right _ hr), Nat.le_refl _, Nat.le_refl _⟩

theorem grow_wrtM {N fp wbase u : Nat} {R : List Region} {m m' : Mem}
    (o : Out [⟨wbase + 8 * u, fp - (wbase + 8 * u)⟩] m m') (h : wbase + 8 * u ≤ fp) :
    Out (WrtM N fp R wbase) m m' :=
  Out.mono o fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact ⟨_, memLast, by dsimp only; omega, by dsimp only; omega⟩

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF

namespace MachineM
variable {M : MachineM} {P : Prog} {bv : List Nat} {wb : Fin 8} {off : Nat → Nat} {hp : Nat}
variable {cb : BitVec 64} {Wc : List (BitVec 32)} {R : List Region} {wbase hi : Nat}

theorem CtxM.cdAll (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {N fp u : Nat} (h0 : wbase + 8 * u ≤ fp)
    (h2 : fp + 8 * (N + 1) ≤ hi) : ∀ r ∈ AllR N fp R [⟨wbase, 8 * u⟩], disjoint ⟨cb.toNat, 4 * Wc.length⟩ r := by
  intro r hr
  unfold AllR at hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with (hr | hr) | hr
  · exact C.cd r (List.mem_append_left _ hr)
  · subst hr; exact C.cd_in (Nat.le_refl _) (by omega)
  · obtain ⟨j, hj, rfl⟩ := mem_slots hr; exact C.cd_in (by omega) (by omega)

/-- the relation after the heap grew: the environment with the new length, the heap image, the rest as before -/
theorem relB_grow (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {N fp : Nat} {σ : BState} {s s' : M.S}
    {W W' : List (BitVec 64)} (r : M.RelB N fp bv [wb.val] R [⟨wbase, 8 * W.length⟩] σ s)
    (henv : M.EnvB N fp (σ.env.set hvar (BitVec.ofNat 64 W'.length)) s')
    (hheap : bytes (M.mem s') wbase (8 * W'.length) = (wbytes W').map some)
    (ho : Out [⟨wbase + 8 * W.length, fp - (wbase + 8 * W.length)⟩] (M.mem s) (M.mem s'))
    (hfp : fp ≤ hi) (hlay : wbase + 8 * W.length ≤ fp) :
    M.RelB N fp bv [wb.val] R [⟨wbase, 8 * W'.length⟩]
      ⟨σ.env.set hvar (BitVec.ofNat 64 W'.length), σ.heap, [W']⟩ s' := by
  refine ⟨henv, r.hlen, r.bvlen, fun b hb => ?_, r.blen, fun b hb => ?_, rfl, rfl, fun b hb => ?_,
    fun b hb => ?_, fun b hb => ?_⟩
  · have : bv.getD b 0 ≠ hvar := fun e => C.hbv (e ▸ getD_memN (r.bvlen ▸ hb))
    show (if bv.getD b 0 = hvar then _ else σ.env (bv.getD b 0)) = _
    rw [ite_neg this]; exact r.base b hb
  · rw [bytes_out ho (fun r' hr' => by
      rw [List.mem_singleton] at hr'; subst hr'
      have := C.sR _ (List.getElem_mem hb); unfold disjoint at this ⊢; dsimp only at this ⊢; omega)]
    exact r.rbytes b hb
  · have hb0 : b = 0 := by simp at hb; omega
    subst hb0
    show (if wb.val = hvar then _ else σ.env wb.val) = _
    rw [ite_neg (fun e => C.wb7 (Fin.ext (by rw [e]; rfl)))]
    exact r.wbase 0 (by simp)
  · have hb0 : b = 0 := by simp at hb; omega
    subst hb0; simp [length_wbytes]
  · have hb0 : b = 0 := by simp at hb; omega
    subst hb0; simpa using hheap

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF Proven.Top.Alloc

namespace MachineM
variable {M : MachineM} {P : Prog} {bv : List Nat} {wb : Fin 8} {off : Nat → Nat} {hp : Nat}
variable {cb : BitVec 64} {Wc : List (BitVec 32)} {R : List Region} {wbase hi : Nat}

theorem peak_nil (c : Nat) : peak ([] ++ [MemEvent.alloc c]) = c := by simp [peak, inUse]
theorem inUse_nil (c : Nat) : inUse ([] ++ [MemEvent.alloc c]) = c := by simp [inUse]

/-- an atom (assignment, byte load or store) runs as before -/
theorem atom_ok (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {N fp : Nat} (hF : M.Frm N fp)
    (hhi : fp + 8 * (N + 1) ≤ hi) {p : BStmt} {σ σ' : BState} (hb : BExec p σ σ') (hwf : M.wfB N bv [wb.val] p)
    {pos : Nat} (hsub : Sub Wc pos (M.codeF (M.compB bv [wb.val] p))) {s : M.S} {W : List (BitVec 64)}
    (hcode : M.codeAt s cb Wc) (ho : M.ok s) (hpc : M.pcIs s (next cb pos)) (inv : M.InvM bv wb N fp R wbase σ s W)
    {W' : List (BitVec 64)} (hwh : σ'.wheap = [W']) (hl : W'.length = W.length)
    (hhv : σ'.env hvar = σ.env hvar) :
    M.runsTo s fun s' => M.ok s' ∧ M.keepC s s' ∧ M.pcIs s' (next cb (pos + (M.codeF (M.compB bv [wb.val] p)).length)) ∧
      M.codeAt s' cb Wc ∧ Out (WrtM N fp R wbase) (M.mem s) (M.mem s') ∧ M.InvM bv wb N fp R wbase σ' s' W' := by
  have hL := C.lay inv.below hhi
  refine M.runsTo_mono (M.execB_ok hF bv [wb.val] (fun x hx => by have := C.bvlt x hx; omega)
    (fun x hx => by simp at hx; omega) hL hb hwf (M.at_sub C.codeOK hcode hsub ho hpc)
    (M.sub_disj C.codeOK hsub (C.cdAll inv.below hhi)) inv.rel) fun s' ⟨d, o, r⟩ => ?_
  have o' := allR_wrtM inv.below o
  exact ⟨d.ok, M.kC d, by rw [← next_add]; exact d.hpc, C.codeAt_W (by have := inv.below; omega) hhi hcode o', o',
    ⟨hwh, by rw [hhv, hl]; exact inv.hv, by rw [hl]; exact inv.below, by rw [hl]; exact r⟩⟩

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF Proven.Top.Alloc

namespace MachineM
variable {M : MachineM} {P : Prog} {bv : List Nat} {wb : Fin 8} {off : Nat → Nat} {hp : Nat}
variable {cb : BitVec 64} {Wc : List (BitVec 32)} {R : List Region} {wbase hi : Nat}

/-- a word access (`load64` / `store64` of word `i`): the check, then the access on the grown heap -/
theorem acc_ok (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {N fp : Nat} (hF : M.Frm N fp)
    (hhi : fp + 8 * (N + 1) ≤ hi) {p : BStmt} {i : BExp} {env : BEnv} {H : Heap} {W : List (BitVec 64)}
    {σ' : BState} (hic : i.clean = true) (hid : i.depth < 6) (hiv : i.vlt (8 + N))
    (hb : BExec p ⟨env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length), H,
      [grow W ((i.denote env).toNat + 1)]⟩ σ')
    (hwf : M.wfB N bv [wb.val] p) (hchk : M.chkOK wb hp pos i)
    (hsub : Sub Wc pos (M.codeZ (M.chkA wb hp pos i ++ xs (M.compB bv [wb.val] p)))) {s : M.S}
    (hcode : M.codeAt s cb Wc) (ho : M.ok s) (hpc : M.pcIs s (next cb pos))
    (inv : M.InvM bv wb N fp R wbase ⟨env, H, [W]⟩ s W)
    {W' : List (BitVec 64)} (hwh : σ'.wheap = [W']) (hl : W'.length = (grow W ((i.denote env).toNat + 1)).length)
    (hhv : σ'.env hvar = BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length) (b : Nat) :
    M.runsTo s fun s' =>
      (peak (growE W ((i.denote env).toNat + 1) ++ [.alloc (b + W.length)]) ≤ b + (fp - wbase) / 8 ∧ M.ok s' ∧
        M.keepC s s' ∧ M.pcIs s' (next cb (pos + (M.lenChkA wb i + (M.codeF (M.compB bv [wb.val] p)).length))) ∧
        M.codeAt s' cb Wc ∧ Out (WrtM N fp R wbase) (M.mem s) (M.mem s') ∧
        ∃ W', inUse (growE W ((i.denote env).toNat + 1) ++ [.alloc (b + W.length)]) = b + W'.length ∧
          M.InvM bv wb N fp R wbase σ' s' W') ∨
      (b + (fp - wbase) / 8 < peak (growE W ((i.denote env).toNat + 1) ++ [.alloc (b + W.length)]) ∧
        M.ok s' ∧ M.keepC s s' ∧ M.pcIs s' (next cb hp) ∧ Out (WrtM N fp R wbase) (M.mem s) (M.mem s')) := by
  obtain ⟨hk1, hk2, hk3, hk4, hk5⟩ := hchk
  rw [codeZ_append, codeZ_xs] at hsub
  obtain ⟨h1, h2⟩ := hsub.split
  rw [len_chkA] at h2
  have hstk := C.stk; unfold Base.inRAM at hstk
  have hbel := inv.below
  have hwbase : env wb.val = BitVec.ofNat 64 wbase := by
    have := inv.rel.wbase 0 (by simp); simpa using this
  have hheap : bytes (M.mem s) wbase (8 * W.length) = (wbytes W).map some := by
    have := inv.rel.wbyts 0 (by simp); simpa using this
  have hgl := grow_length W ((i.denote env).toNat + 1)
  refine M.runsTo_trans (M.chkA_ok C.codeOK h1 hk1 hk2 hk3 hk4 hk5 hF (by omega) hiv hic C.wb7 hwbase inv.hv
    inv.below C.wal (by unfold Base.inRAM; omega) (fun a h1 h2 s hs => C.stw a h1 (by omega) s hs)
    (C.cd_in (Nat.le_refl _) (by omega)) hcode ho hpc inv.rel.env hheap) fun s₁ h => ?_
  rcases h with ⟨hfit, ok₁, kp₁, pc₁, hc₁, env₁, heap₁, out₁⟩ | ⟨hno, ok₁, kc₁, pc₁, m₁⟩
  · have r₁ := relB_grow C inv.rel env₁ heap₁ out₁ (by omega) inv.below
    have inv₁ : M.InvM bv wb N fp R wbase ⟨env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length),
        H, [grow W ((i.denote env).toNat + 1)]⟩ s₁ (grow W ((i.denote env).toNat + 1)) :=
      ⟨rfl, by simp [BEnv.set], hfit, r₁⟩
    refine M.runsTo_mono (atom_ok C hF hhi hb hwf h2 hc₁ ok₁ pc₁ inv₁ hwh hl (by rw [hhv]; simp [BEnv.set]))
      fun s₂ ⟨ok₂, kc₂, pc₂, hc₂, o₂, inv₂⟩ => .inl ⟨?_, ok₂, M.keepC_trans (M.keep_keepC kp₁) kc₂,
        by rw [← Nat.add_assoc]; exact pc₂, hc₂, (grow_wrtM out₁ inv.below).trans o₂, _, ?_, inv₂⟩
    · rw [peak_growE]; omega
    · rw [inUse_growE, hl]; omega
  · refine M.runsTo_of (.inr ⟨?_, ok₁, kc₁, pc₁, Out.of_eq m₁⟩)
    rw [peak_growE, hgl]; omega

theorem execBM_ok (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {N fp : Nat} (hF : M.Frm N fp)
    (hhi : fp + 8 * (N + 1) ≤ hi) :
    ∀ {p : BStmt} {σ σ' : BState} {E : List MemEvent}, TExecB p σ E σ' → p.clean = true →
    ∀ {pos : Nat} {s : M.S} {W : List (BitVec 64)} {b : Nat},
    M.wfBM bv wb hp N pos p → Sub Wc pos (M.codeZ (M.compBM bv wb hp pos p)) →
    M.codeAt s cb Wc → M.ok s → M.pcIs s (next cb pos) → M.InvM bv wb N fp R wbase σ s W →
    M.runsTo s fun s' =>
      (peak (E ++ [.alloc (b + W.length)]) ≤ b + (fp - wbase) / 8 ∧ M.ok s' ∧ M.keepC s s' ∧
        M.pcIs s' (next cb (pos + M.lenBM bv wb p)) ∧ M.codeAt s' cb Wc ∧
        Out (WrtM N fp R wbase) (M.mem s) (M.mem s') ∧
        ∃ W', inUse (E ++ [.alloc (b + W.length)]) = b + W'.length ∧ M.InvM bv wb N fp R wbase σ' s' W') ∨
      (b + (fp - wbase) / 8 < peak (E ++ [.alloc (b + W.length)]) ∧ M.ok s' ∧ M.keepC s s' ∧
        M.pcIs s' (next cb hp) ∧ Out (WrtM N fp R wbase) (M.mem s) (M.mem s')) := by
  intro p σ σ' E h
  induction h with
  | @assign v e σ =>
    intro hc pos s W b hwf hsub hcode ho hpc inv
    simp only [BStmt.clean, Bool.and_eq_true] at hc
    have hv := ne_hvar (not_unread hc.1)
    simp only [compBM, lenBM, codeZ_xs] at hsub ⊢
    refine M.runsTo_mono (atom_ok C hF hhi .assign hwf hsub hcode ho hpc inv inv.wh rfl (by simp [BEnv.set, Ne.symm hv]))
      fun s' ⟨ok', kc', pc', hc', o', inv'⟩ => .inl ⟨?_, ok', kc', pc', hc', o', W, by rw [inUse_nil], inv'⟩
    rw [peak_nil]; have := inv.below; omega
  | @load v b' i σ hb hi =>
    intro hc pos s W b hwf hsub hcode ho hpc inv
    simp only [BStmt.clean, Bool.and_eq_true] at hc
    have hv := ne_hvar (not_unread hc.1.1)
    simp only [compBM, lenBM, codeZ_xs] at hsub ⊢
    refine M.runsTo_mono (atom_ok C hF hhi (.load hb hi) hwf hsub hcode ho hpc inv inv.wh rfl
      (by simp [BEnv.set, Ne.symm hv])) fun s' ⟨ok', kc', pc', hc', o', inv'⟩ =>
        .inl ⟨?_, ok', kc', pc', hc', o', W, by rw [inUse_nil], inv'⟩
    rw [peak_nil]; have := inv.below; omega
  | @store b' i e σ hb hi =>
    intro hc pos s W b hwf hsub hcode ho hpc inv
    simp only [compBM, lenBM, codeZ_xs] at hsub ⊢
    refine M.runsTo_mono (atom_ok C hF hhi (.store hb hi) hwf hsub hcode ho hpc inv inv.wh rfl rfl)
      fun s' ⟨ok', kc', pc', hc', o', inv'⟩ => .inl ⟨?_, ok', kc', pc', hc', o', W, by rw [inUse_nil], inv'⟩
    rw [peak_nil]; have := inv.below; omega
  | @seq p q σ σ₁ σ₂ E₁ E₂ _ _ ih₁ ih₂ =>
    intro hc pos s W b hwf hsub hcode ho hpc inv
    simp only [BStmt.clean, Bool.and_eq_true] at hc
    simp only [compBM, codeZ_append, wfBM] at hsub hwf
    obtain ⟨h1, h2⟩ := hsub.split
    rw [len_compBM] at h2
    refine M.runsTo_trans (ih₁ hc.1 hwf.1 h1 hcode ho hpc inv (b := b)) fun s₁ h => ?_
    rcases h with ⟨pk₁, ok₁, kc₁, pc₁, hc₁, o₁, W₁, iu₁, inv₁⟩ | ⟨pk₁, ok₁, kc₁, pc₁, o₁⟩
    · refine M.runsTo_mono (ih₂ hc.2 hwf.2 h2 hc₁ ok₁ pc₁ inv₁ (b := b)) fun s₂ h => ?_
      rcases h with ⟨pk₂, ok₂, kc₂, pc₂, hc₂, o₂, W₂, iu₂, inv₂⟩ | ⟨pk₂, ok₂, kc₂, pc₂, o₂⟩
      · refine .inl ⟨?_, ok₂, M.keepC_trans kc₁ kc₂, M.pcIs_cast pc₂ (by simp only [lenBM]; omega), hc₂, o₁.trans o₂,
          W₂, ?_, inv₂⟩
        · rw [peak_seq, iu₁]; omega
        · rw [inUse_seq, iu₁, iu₂]
      · refine .inr ⟨?_, ok₂, M.keepC_trans kc₁ kc₂, pc₂, o₁.trans o₂⟩
        rw [peak_seq, iu₁]; omega
    · refine M.runsTo_of (.inr ⟨?_, ok₁, kc₁, pc₁, o₁⟩)
      rw [peak_seq]; omega
  | @loopF c bd σ hc0 =>
    intro hc pos s W b hwf hsub hcode ho hpc inv
    simp only [compBM, codeZ_append, codeZ_xs, codeZ_one, encZ_A, wfBM] at hsub hwf
    obtain ⟨hw1, hw2, hw3, hw4, hw5⟩ := hwf
    obtain ⟨h123, h4⟩ := hsub.split
    obtain ⟨h12, h3⟩ := h123.split
    obtain ⟨h1, h2⟩ := h12.split
    refine M.runsTo_trans (M.genB_ok hF σ.env c 0 (by omega) hw2 (M.at_sub C.codeOK hcode h1 ho hpc) inv.rel.env)
      fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    rw [next_add] at d₁
    refine M.runsTo_mono (M.law_bz (rk_val (by omega)) hw3 (M.at_sub C.codeOK (M.codeAt_mem m₁ hcode) h2 d₁.ok d₁.hpc))
      fun s₂ ⟨d₂, st₂, m₂⟩ => .inl ⟨?_, d₂.ok, M.keepC_trans (M.kC d₁) (M.kC d₂), ?_,
        M.codeAt_mem (by rw [m₂, m₁]) hcode, Out.of_eq (by rw [m₂, m₁]), W, by rw [inUse_nil],
        ⟨inv.wh, inv.hv, inv.below, RelB.same M.toMachineF inv.rel (by rw [m₂, m₁]) (M.keep_trans d₁.keep d₂.keep)
          fun i => by rw [st₂, k₁ _ (.inr (avar_ge i))]⟩⟩
    · rw [peak_nil]; have := inv.below; omega
    · rw [v₁, ite_pos hc0, next_add] at d₂
      exact M.pcIs_cast d₂.hpc (by simp only [lenBM]; omega)
  | @loopT c bd σ σ₁ σ₂ E₁ E₂ hc0 _ _ ih₁ ih₂ =>
    intro hc pos s W b hwf hsub hcode ho hpc inv
    have hc' := hc
    simp only [BStmt.clean, Bool.and_eq_true] at hc'
    have hwf0 := hwf
    have hsub0 := hsub
    simp only [compBM, codeZ_append, codeZ_xs, codeZ_one, encZ_A, wfBM] at hsub hwf
    obtain ⟨hw1, hw2, hw3, hw4, hw5⟩ := hwf
    obtain ⟨h123, h4⟩ := hsub.split
    obtain ⟨h12, h3⟩ := h123.split
    obtain ⟨h1, h2⟩ := h12.split
    simp only [List.length_append, M.len_bz, len_compBM] at h3 h4
    refine M.runsTo_trans (M.genB_ok hF σ.env c 0 (by omega) hw2 (M.at_sub C.codeOK hcode h1 ho hpc) inv.rel.env)
      fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    rw [next_add] at d₁
    refine M.runsTo_trans (M.law_bz (rk_val (by omega)) hw3 (M.at_sub C.codeOK (M.codeAt_mem m₁ hcode) h2 d₁.ok d₁.hpc))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    rw [v₁, ite_neg hc0, M.len_bz, next_add] at d₂
    have inv₂ : M.InvM bv wb N fp R wbase σ s₂ W :=
      ⟨inv.wh, inv.hv, inv.below, RelB.same M.toMachineF inv.rel (by rw [m₂, m₁]) (M.keep_trans d₁.keep d₂.keep)
        fun i => by rw [st₂, k₁ _ (.inr (avar_ge i))]⟩
    refine M.runsTo_trans (ih₁ hc'.2 hw5 (h3.cast (by omega)) (M.codeAt_mem (by rw [m₂, m₁]) hcode) d₂.ok
      (M.pcIs_cast d₂.hpc (by omega)) inv₂ (b := b)) fun s₃ h => ?_
    rcases h with ⟨pk₃, ok₃, kc₃, pc₃, hc₃, o₃, W₃, iu₃, inv₃⟩ | ⟨pk₃, ok₃, kc₃, pc₃, o₃⟩
    · refine M.runsTo_trans (M.law_jmp hw4 (M.at_sub C.codeOK hc₃ h4 ok₃ (M.pcIs_cast pc₃ (by omega))))
        fun s₄ ⟨d₄, st₄, m₄⟩ => ?_
      have pc₄ : M.pcIs s₄ (next cb pos) := M.pcIs_jmp d₄.hpc (by omega)
      refine M.runsTo_mono (ih₂ hc hwf0 hsub0 (M.codeAt_mem m₄ hc₃) d₄.ok pc₄
        ⟨inv₃.wh, inv₃.hv, inv₃.below, RelB.same M.toMachineF inv₃.rel m₄ d₄.keep fun i => st₄ _⟩ (b := b))
        fun s₅ h => ?_
      have kc := M.keepC_trans (M.kC d₁) (M.keepC_trans (M.kC d₂) (M.keepC_trans kc₃ (M.kC d₄)))
      have o := (Out.of_eq (show M.mem s₂ = M.mem s by rw [m₂, m₁])).trans (o₃.trans (Out.of_eq m₄))
      rcases h with ⟨pk₅, ok₅, kc₅, pc₅, hc₅, o₅, W₅, iu₅, inv₅⟩ | ⟨pk₅, ok₅, kc₅, pc₅, o₅⟩
      · refine .inl ⟨?_, ok₅, M.keepC_trans kc kc₅, pc₅, hc₅, o.trans o₅, W₅, ?_, inv₅⟩
        · rw [peak_seq, iu₃]; omega
        · rw [inUse_seq, iu₃, iu₅]
      · refine .inr ⟨?_, ok₅, M.keepC_trans kc kc₅, pc₅, o.trans o₅⟩
        rw [peak_seq, iu₃]; omega
    · refine M.runsTo_of (.inr ⟨?_, ok₃, M.keepC_trans (M.kC d₁) (M.keepC_trans (M.kC d₂) kc₃), pc₃,
        (Out.of_eq (show M.mem s₂ = M.mem s by rw [m₂, m₁])).trans o₃⟩)
      rw [peak_seq]; omega
  | @load64 v i env H W₀ =>
    intro hc pos s W b hwf hsub hcode ho hpc inv
    obtain rfl : W = W₀ := by have := inv.wh; simp at this; exact this.symm
    simp only [BStmt.clean, Bool.and_eq_true, beq_iff_eq] at hc
    have hv := ne_hvar (not_unread hc.1.1)
    simp only [compBM, lenBM, wfBM] at hsub hwf ⊢
    obtain ⟨hwfa, hchk⟩ := hwf
    have hie : i.denote (env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length)) = i.denote env :=
      BExp.denote_clean hc.2 fun x hx => by simp only [BEnv.set]; rw [if_neg (fun e => hx (by rw [e]; exact hvar_unread))]
    have hjl : (i.denote env).toNat < (grow W ((i.denote env).toNat + 1)).length := by rw [grow_length]; omega
    have hb : BExec (.load64 v 0 i) ⟨env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length), H,
        [grow W ((i.denote env).toNat + 1)]⟩
        ⟨(env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length)).set v
          ((grow W ((i.denote env).toNat + 1)).getD (i.denote env).toNat 0), H, [grow W ((i.denote env).toNat + 1)]⟩ := by
      have := BExec.load64 (v := v) (b := 0) (i := i) (σ := ⟨env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat
        + 1)).length), H, [grow W ((i.denote env).toNat + 1)]⟩) (by simp) (by simp only [hie]; simpa using hjl)
      simp only [hie, List.getElem_singleton] at this
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
    exact acc_ok C hF hhi hc.2 hwfa.1 hwfa.2.1 hb hwfa hchk hsub hcode ho hpc inv rfl rfl
      (by simp [BEnv.set, Ne.symm hv]) b
  | @store64 i e env H W₀ =>
    intro hc pos s W b hwf hsub hcode ho hpc inv
    obtain rfl : W = W₀ := by have := inv.wh; simp at this; exact this.symm
    simp only [BStmt.clean, Bool.and_eq_true, beq_iff_eq] at hc
    simp only [compBM, lenBM, wfBM] at hsub hwf ⊢
    obtain ⟨hwfa, hchk⟩ := hwf
    have hu : ∀ x, x ∉ unread → env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length) x = env x :=
      fun x hx => by simp only [BEnv.set]; rw [if_neg (fun e => hx (by rw [e]; exact hvar_unread))]
    have hie := BExp.denote_clean hc.1.2 hu
    have hee := BExp.denote_clean hc.2 hu
    have hjl : (i.denote env).toNat < (grow W ((i.denote env).toNat + 1)).length := by rw [grow_length]; omega
    have hb : BExec (.store64 0 i e) ⟨env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length), H,
        [grow W ((i.denote env).toNat + 1)]⟩
        ⟨env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length), H,
          [(grow W ((i.denote env).toNat + 1)).set (i.denote env).toNat (e.denote env)]⟩ := by
      have := BExec.store64 (b := 0) (i := i) (e := e) (σ := ⟨env.set hvar (BitVec.ofNat 64 (grow W ((i.denote env).toNat
        + 1)).length), H, [grow W ((i.denote env).toNat + 1)]⟩) (by simp) (by simp only [hie]; simpa using hjl)
      simp only [hie, hee, List.getElem_singleton, List.set_cons_zero] at this
      exact this
    exact acc_ok C hF hhi hc.1.2 hwfa.1 hwfa.2.2.1 hb hwfa hchk hsub hcode ho hpc inv rfl (List.length_set ..) rfl b

end MachineM
end Proven.Mach
