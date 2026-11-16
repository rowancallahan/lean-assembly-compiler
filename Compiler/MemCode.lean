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
  law_getTop : ∀ {d : Reg} {s : S} {pc : BitVec 64}, d.val < 7 → 8 ≤ frameAt s 0 → toBase.At s pc (encM (.getTop d)) →
    runsTo s fun s' => toBase.Done s s' (next pc (encM (.getTop d)).length) ∧
      toBase.Set1 s s' d (BitVec.ofNat 64 (frameAt s 0)) ∧ mem s' = mem s
  law_exit : ∀ {s : S} {pc w : BitVec 64}, toBase.At s pc (encM .exit) → 8 ≤ frameAt s 0 →
    toBase.inRAM (frameAt s 0 - 8) 8 → (frameAt s 0 - 8) % 8 = 0 →
    bytes (mem s) (frameAt s 0 - 8) 8 = (le8 w).map some → retOK w →
    runsTo s fun s' => ok s' ∧ pcIs s' w ∧ get s' (avar 0) = BitVec.allOnes 64 ∧ mem s' = mem s
  frameAt_keepC : ∀ {s s' : S} {n : Nat}, keepC s s' → frameAt s' n = frameAt s n
  enterOK_keep : ∀ {s s' : S} {n : Nat}, keep s s' → enterOK s n → enterOK s' n

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
  slotsLe : 8 * (M.maxSlots + 1) ≤ wbase

/-- what a statement in the frame `(N, fp)` may write: the byte blocks, its slots, the work area below `fp` -/
def WrtM (N fp : Nat) (R : List Region) (wbase : Nat) : List Region :=
  R.drop 1 ++ slots N fp ++ [⟨wbase, fp - wbase⟩]

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
  · exact C.cd r (List.mem_append_left _ (List.mem_of_mem_drop hr))
  · obtain ⟨j, hj, rfl⟩ := mem_slots hr; exact C.cd_in (by omega) (by omega)
  · subst hr; exact C.cd_in (Nat.le_refl _) (by omega)

theorem CtxM.codeAt_W (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {N fp : Nat} (h1 : wbase ≤ fp)
    (h2 : fp + 8 * (N + 1) ≤ hi) {s s' : M.S} (hc : M.codeAt s cb Wc)
    (o : Out (WrtM N fp R wbase) (M.mem s) (M.mem s')) : M.codeAt s' cb Wc :=
  M.codeAt_out hc C.codeOK (C.cdW h1 h2) o

/-- block 0 (the input) unchanged -/
def B0 (R : List Region) (m m' : Mem) : Prop := ∀ r ∈ R.head?, bytes m' r.base r.len = bytes m r.base r.len

theorem mem_eq_of_bytes {m m' : Mem} {a n x : Nat} (h : bytes m' a n = bytes m a n) (h1 : a ≤ x) (h2 : x < a + n) :
    m' x = m x := by
  have hl : x - a < (bytes m' a n).length := by rw [length_bytes]; omega
  have hl' : x - a < (bytes m a n).length := by rw [length_bytes]; omega
  have := congrArg (·[x - a]?) h
  simp only [List.getElem?_eq_getElem hl, List.getElem?_eq_getElem hl', bytes_getElem, Option.some.injEq] at this
  rwa [Nat.add_sub_cancel' h1] at this

theorem allR_wrtM {N fp wbase u : Nat} {R : List Region} {m m' : Mem} (h : wbase + 8 * u ≤ fp)
    (o : Out (AllR N fp R [⟨wbase, 8 * u⟩]) m m') (h0 : B0 R m m') : Out (WrtM N fp R wbase) m m' := by
  intro a ha
  have hw := ha _ memLast
  dsimp only at hw
  have hs : ∀ r ∈ slots N fp, a < r.base ∨ r.base + r.len ≤ a := fun r hr =>
    ha r (List.mem_append_left _ (List.mem_append_right _ hr))
  have hd : ∀ r ∈ R.drop 1, a < r.base ∨ r.base + r.len ≤ a := fun r hr =>
    ha r (List.mem_append_left _ (List.mem_append_left _ hr))
  cases R with
  | nil =>
    refine o a fun r hr => ?_
    unfold AllR at hr; simp only [List.nil_append, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | hr
    · subst hr; dsimp only; omega
    · exact hs r hr
  | cons r0 rs =>
    by_cases hin : r0.base ≤ a ∧ a < r0.base + r0.len
    · exact mem_eq_of_bytes (h0 r0 rfl) hin.1 hin.2
    · refine o a fun r hr => ?_
      unfold AllR at hr
      simp only [List.mem_append, List.mem_cons, List.mem_singleton] at hr
      rcases hr with ((rfl | hr) | hr) | hr
      · omega
      · exact hd r (by simpa using hr)
      · rcases hr with hr | hr
        · subst hr; dsimp only; omega
        · simp at hr
      · exact hs r hr

theorem B0_of_rel {M : MachineM} {N fp N' fp' : Nat} {bv wv : List Nat} {R W W' : List Region} {σ σ' : BState}
    {s s' : M.S} (r : M.RelB N fp bv wv R W σ s) (r' : M.RelB N' fp' bv wv R W' σ' s')
    (hh : σ'.heap[0]? = σ.heap[0]?) : B0 R (M.mem s) (M.mem s') := by
  intro r0 hr0
  match R, r, r', hr0 with
  | r0' :: rs, r, r', hr0 =>
    have e : r0 = r0' := (Option.some.inj hr0).symm
    subst e
    have h1 := r.rbytes 0 (by simp)
    have h2 := r'.rbytes 0 (by simp)
    simp only [List.getElem_cons_zero] at h1 h2
    rw [h2, h1, hh]

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
    (hhv : σ'.env hvar = σ.env hvar) (hh0 : σ'.heap[0]? = σ.heap[0]?) :
    M.runsTo s fun s' => M.ok s' ∧ M.keepC s s' ∧ M.pcIs s' (next cb (pos + (M.codeF (M.compB bv [wb.val] p)).length)) ∧
      M.codeAt s' cb Wc ∧ Out (WrtM N fp R wbase) (M.mem s) (M.mem s') ∧ M.InvM bv wb N fp R wbase σ' s' W' := by
  have hL := C.lay inv.below hhi
  refine M.runsTo_mono (M.execB_ok hF bv [wb.val] (fun x hx => by have := C.bvlt x hx; omega)
    (fun x hx => by simp at hx; omega) hL hb hwf (M.at_sub C.codeOK hcode hsub ho hpc)
    (M.sub_disj C.codeOK hsub (C.cdAll inv.below hhi)) inv.rel) fun s' ⟨d, o, r⟩ => ?_
  have o' := allR_wrtM inv.below o (B0_of_rel inv.rel r hh0)
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
    (hhv : σ'.env hvar = BitVec.ofNat 64 (grow W ((i.denote env).toNat + 1)).length)
    (hh0 : σ'.heap[0]? = H[0]?) (b : Nat) :
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
    refine M.runsTo_mono (atom_ok C hF hhi hb hwf h2 hc₁ ok₁ pc₁ inv₁ hwh hl (by rw [hhv]; simp [BEnv.set]) hh0)
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
    refine M.runsTo_mono (atom_ok C hF hhi .assign hwf hsub hcode ho hpc inv inv.wh rfl (by simp [BEnv.set, Ne.symm hv])
      rfl)
      fun s' ⟨ok', kc', pc', hc', o', inv'⟩ => .inl ⟨?_, ok', kc', pc', hc', o', W, by rw [inUse_nil], inv'⟩
    rw [peak_nil]; have := inv.below; omega
  | @load v b' i σ hb hi =>
    intro hc pos s W b hwf hsub hcode ho hpc inv
    simp only [BStmt.clean, Bool.and_eq_true] at hc
    have hv := ne_hvar (not_unread hc.1.1)
    simp only [compBM, lenBM, codeZ_xs] at hsub ⊢
    refine M.runsTo_mono (atom_ok C hF hhi (.load hb hi) hwf hsub hcode ho hpc inv inv.wh rfl
      (by simp [BEnv.set, Ne.symm hv]) rfl) fun s' ⟨ok', kc', pc', hc', o', inv'⟩ =>
        .inl ⟨?_, ok', kc', pc', hc', o', W, by rw [inUse_nil], inv'⟩
    rw [peak_nil]; have := inv.below; omega
  | @store b' i e σ hb hi =>
    intro hc pos s W b hwf hsub hcode ho hpc inv
    simp only [compBM, lenBM, codeZ_xs] at hsub ⊢
    simp only [BStmt.clean, Bool.and_eq_true, bne_iff_ne] at hc
    refine M.runsTo_mono (atom_ok C hF hhi (.store hb hi) hwf hsub hcode ho hpc inv inv.wh rfl rfl
      (List.getElem?_set_ne hc.1.1))
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
      (by simp [BEnv.set, Ne.symm hv]) rfl b
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
    exact acc_ok C hF hhi hc.1.2 hwfa.1 hwfa.2.2.1 hb hwfa hchk hsub hcode ho hpc inv rfl (List.length_set ..) rfl rfl b

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF Proven.Top.Alloc

namespace MachineM
variable {M : MachineM} {P : Prog} {bv : List Nat} {wb : Fin 8} {off : Nat → Nat} {hp : Nat}
variable {cb : BitVec 64} {Wc : List (BitVec 32)} {R : List Region} {wbase hi : Nat}

/-- a callee's writes are writes of the caller -/
theorem wrtM_callee {n fp' N fp : Nat} {m m' : Mem} (o : Out (WrtM n fp' R wbase) m m')
    (h : fp' + 8 * (n + 1) ≤ fp) (hw : wbase ≤ fp') : Out (WrtM N fp R wbase) m m' :=
  Out.mono o fun r hr => by
    unfold WrtM at hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (hr | hr) | hr
    · exact ⟨r, List.mem_append_left _ (List.mem_append_left _ hr), Nat.le_refl _, Nat.le_refl _⟩
    · obtain ⟨j, hj, rfl⟩ := mem_slots hr
      exact ⟨_, memLast, by dsimp only; omega, by dsimp only; omega⟩
    · subst hr; exact ⟨_, memLast, Nat.le_refl _, by dsimp only; omega⟩

theorem out_wrtM {a l N fp : Nat} {m m' : Mem} (o : Out [⟨a, l⟩] m m') (h1 : wbase ≤ a) (h2 : a + l ≤ fp) :
    Out (WrtM N fp R wbase) m m' :=
  Out.mono o fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact ⟨_, memLast, h1, by dsimp only; omega⟩

/-- the saved return address (cell 0) is not written by the body -/
theorem CtxM.cell0M (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {N fp : Nat} (h1 : wbase ≤ fp)
    (h2 : fp + 8 * (N + 1) ≤ hi) : ∀ r ∈ WrtM N fp R wbase, disjoint ⟨fp, 8⟩ r := by
  intro r hr
  unfold WrtM at hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with (hr | hr) | hr
  · have := C.sR r (List.mem_of_mem_drop hr); unfold disjoint at this ⊢; dsimp only at this ⊢; omega
  · obtain ⟨j, hj, rfl⟩ := mem_slots hr; unfold disjoint; dsimp only; omega
  · subst hr; unfold disjoint; dsimp only; omega

/-- the caller's slots are not written by a callee -/
theorem CtxM.slotM (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {n fp' N fp : Nat} (h1 : wbase ≤ fp')
    (h2 : fp' + 8 * (n + 1) ≤ fp) (h3 : fp + 8 * (N + 1) ≤ hi) {j : Nat} (hj : j < N) :
    ∀ r ∈ WrtM n fp' R wbase, disjoint ⟨fp + 8 * (j + 1), 8⟩ r := by
  intro r hr
  unfold WrtM at hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with (hr | hr) | hr
  · have := C.sR r (List.mem_of_mem_drop hr); unfold disjoint at this ⊢; dsimp only at this ⊢; omega
  · obtain ⟨j', hj', rfl⟩ := mem_slots hr; unfold disjoint; dsimp only; omega
  · subst hr; unfold disjoint; dsimp only; omega

/-- the byte blocks are not in the work area -/
theorem CtxM.rWrk (C : M.CtxM P bv wb off hp cb Wc R wbase hi) {a l : Nat} (h1 : wbase ≤ a) (h2 : a + l ≤ hi)
    {r : Region} (hr : r ∈ R) : disjoint r ⟨a, l⟩ := by
  have := C.sR r hr; unfold disjoint at this ⊢; dsimp only at this ⊢; omega

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF Proven.Top.Alloc

namespace MachineM
variable {M : MachineM} {P : Prog} {bv : List Nat} {wb : Fin 8} {off : Nat → Nat} {hp : Nat}
variable {cb : BitVec 64} {Wc : List (BitVec 32)} {R : List Region} {wbase hi : Nat}

/-- **Statements with calls and run-time checks**, by induction on the run with events: from `b + |W|` cells
in use (`b`: the frames above and the entry stub) in a work area of `b + (fp - wbase) / 8` cells, the code of
`p` runs to its end with `σ'` (the events never exceed the cells), or to the exit (they do). -/
theorem execCM_ok (C : M.CtxM P bv wb off hp cb Wc R wbase hi) (hP : progClean P = true) :
    ∀ {p : CStmt} {σ σ' : BState} {E : List MemEvent}, TExec P p σ E σ' → p.clean = true →
    ∀ {N fp pos : Nat} {s : M.S} {W : List (BitVec 64)} {b : Nat}, M.Frm N fp → fp + 8 * (N + 1) ≤ hi →
    M.wfCM P bv wb off hp N pos p → Sub Wc pos (M.codeZ (M.compCM P bv wb off hp pos p)) →
    M.codeAt s cb Wc → M.ok s → M.pcIs s (next cb pos) → M.InvM bv wb N fp R wbase σ s W →
    M.runsTo s fun s' =>
      (peak (E ++ [.alloc (b + W.length)]) ≤ b + (fp - wbase) / 8 ∧ M.ok s' ∧ M.keepC s s' ∧
        M.pcIs s' (next cb (pos + M.lenCM P bv wb p)) ∧ M.codeAt s' cb Wc ∧
        Out (WrtM N fp R wbase) (M.mem s) (M.mem s') ∧
        ∃ W', inUse (E ++ [.alloc (b + W.length)]) = b + W'.length ∧ M.InvM bv wb N fp R wbase σ' s' W') ∨
      (b + (fp - wbase) / 8 < peak (E ++ [.alloc (b + W.length)]) ∧ M.ok s' ∧ M.keepC s s' ∧
        M.pcIs s' (next cb hp) ∧ Out (WrtM N fp R wbase) (M.mem s) (M.mem s')) := by
  intro p σ σ' E h
  induction h with
  | base hx =>
    intro hc N fp pos s W b hF hhi hwf hsub hcode ho hpc inv
    exact execBM_ok C hF hhi hx hc hwf hsub hcode ho hpc inv
  | @seq p q σ σ₁ σ₂ E₁ E₂ _ _ ih₁ ih₂ =>
    intro hc N fp pos s W b hF hhi hwf hsub hcode ho hpc inv
    simp only [CStmt.clean, Bool.and_eq_true] at hc
    simp only [compCM, codeZ_append, wfCM] at hsub hwf
    obtain ⟨h1, h2⟩ := hsub.split
    rw [len_compCM] at h2
    refine M.runsTo_trans (ih₁ hc.1 hF hhi hwf.1 h1 hcode ho hpc inv (b := b)) fun s₁ h => ?_
    rcases h with ⟨pk₁, ok₁, kc₁, pc₁, hc₁, o₁, W₁, iu₁, inv₁⟩ | ⟨pk₁, ok₁, kc₁, pc₁, o₁⟩
    · refine M.runsTo_mono (ih₂ hc.2 hF hhi hwf.2 h2 hc₁ ok₁ pc₁ inv₁ (b := b)) fun s₂ h => ?_
      rcases h with ⟨pk₂, ok₂, kc₂, pc₂, hc₂, o₂, W₂, iu₂, inv₂⟩ | ⟨pk₂, ok₂, kc₂, pc₂, o₂⟩
      · refine .inl ⟨?_, ok₂, M.keepC_trans kc₁ kc₂, M.pcIs_cast pc₂ (by simp only [lenCM]; omega), hc₂, o₁.trans o₂,
          W₂, ?_, inv₂⟩
        · rw [peak_seq, iu₁]; omega
        · rw [inUse_seq, iu₁, iu₂]
      · refine .inr ⟨?_, ok₂, M.keepC_trans kc₁ kc₂, pc₂, o₁.trans o₂⟩
        rw [peak_seq, iu₁]; omega
    · refine M.runsTo_of (.inr ⟨?_, ok₁, kc₁, pc₁, o₁⟩)
      rw [peak_seq]; omega
  | @iteT c p q σ E σ' hc0 _ ih =>
    intro hc N fp pos s W b hF hhi hwf hsub hcode ho hpc inv
    simp only [CStmt.clean, Bool.and_eq_true] at hc
    simp only [compCM, codeZ_append, codeZ_xs, codeZ_one, codeZ_cons, codeZ_nil, List.append_nil, encZ_A, wfCM]
      at hsub hwf
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6⟩ := hwf
    obtain ⟨h1234, h5⟩ := hsub.split
    obtain ⟨h123, h4⟩ := h1234.split
    obtain ⟨h12, h3⟩ := h123.split
    obtain ⟨h1, h2⟩ := h12.split
    obtain ⟨h4a, h4b⟩ := h4.split
    simp only [List.length_append, M.len_bz, len_compCM, MachineC.lenLi_eq] at h2 h3 h4a h4b h5
    refine M.runsTo_trans (M.genB_ok hF σ.env c 0 (by omega) hw2 (M.at_sub C.codeOK hcode h1 ho hpc) inv.rel.env)
      fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    rw [next_add] at d₁
    refine M.runsTo_trans (M.law_bz (rk_val (by omega)) hw3 (M.at_sub C.codeOK (M.codeAt_mem m₁ hcode) h2 d₁.ok d₁.hpc))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    rw [v₁, ite_neg hc0, M.len_bz, next_add] at d₂
    have inv₂ : M.InvM bv wb N fp R wbase σ s₂ W :=
      ⟨inv.wh, inv.hv, inv.below, RelB.same M.toMachineF inv.rel (by rw [m₂, m₁]) (M.keep_trans d₁.keep d₂.keep)
        fun i => by rw [st₂, k₁ _ (.inr (avar_ge i))]⟩
    have kc₂ := M.keepC_trans (M.kC d₁) (M.kC d₂)
    have om₂ : M.mem s₂ = M.mem s := by rw [m₂, m₁]
    refine M.runsTo_trans (ih hc.1.2 hF hhi hw5 (h3.cast (by omega)) (M.codeAt_mem om₂ hcode) d₂.ok
      (M.pcIs_cast d₂.hpc (by omega)) inv₂ (b := b)) fun s₃ h => ?_
    rcases h with ⟨pk₃, ok₃, kc₃, pc₃, hc₃, o₃, W₃, iu₃, inv₃⟩ | ⟨pk₃, ok₃, kc₃, pc₃, o₃⟩
    · refine M.runsTo_trans (M.law_li (d := rk 0) (c := 0) (by rw [rk_val (by omega)]; omega)
        (M.at_sub C.codeOK hc₃ h4a ok₃ (M.pcIs_cast pc₃ (by omega)))) fun s₄ ⟨d₄, st₄, m₄⟩ => ?_
      rw [next_add] at d₄
      refine M.runsTo_mono (M.law_bz (c := rk 0) (rk_val (by omega)) hw4
        (M.at_sub C.codeOK (M.codeAt_mem m₄ hc₃) h4b d₄.ok (M.pcIs_cast d₄.hpc (by rw [MachineC.lenLi_eq]))))
        fun s₅ ⟨d₅, st₅, m₅⟩ => ?_
      rw [Core.Set1.same _ st₄, ite_pos rfl, next_add] at d₅
      refine .inl ⟨pk₃, d₅.ok, M.keepC_trans kc₂ (M.keepC_trans kc₃ (M.keepC_trans (M.kC d₄) (M.kC d₅))),
        M.pcIs_cast d₅.hpc (by simp only [lenCM]; omega), M.codeAt_mem (by rw [m₅, m₄]) hc₃,
        (Out.of_eq om₂).trans (o₃.trans (Out.of_eq (by rw [m₅, m₄]))), W₃, iu₃,
        ⟨inv₃.wh, inv₃.hv, inv₃.below, RelB.same M.toMachineF inv₃.rel (by rw [m₅, m₄])
          (M.keep_trans d₄.keep d₅.keep) fun i => by rw [st₅, Core.Set1.other _ st₄ (avar_ne_rk0 i)]⟩⟩
    · exact M.runsTo_of (.inr ⟨pk₃, ok₃, M.keepC_trans kc₂ kc₃, pc₃, (Out.of_eq om₂).trans o₃⟩)
  | @iteF c p q σ E σ' hc0 _ ih =>
    intro hc N fp pos s W b hF hhi hwf hsub hcode ho hpc inv
    simp only [CStmt.clean, Bool.and_eq_true] at hc
    simp only [compCM, codeZ_append, codeZ_xs, codeZ_one, codeZ_cons, codeZ_nil, List.append_nil, encZ_A, wfCM]
      at hsub hwf
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6⟩ := hwf
    obtain ⟨h1234, h5⟩ := hsub.split
    obtain ⟨h123, h4⟩ := h1234.split
    obtain ⟨h12, h3⟩ := h123.split
    obtain ⟨h1, h2⟩ := h12.split
    simp only [List.length_append, M.len_bz, len_compCM, MachineC.lenLi_eq] at h2 h5
    refine M.runsTo_trans (M.genB_ok hF σ.env c 0 (by omega) hw2 (M.at_sub C.codeOK hcode h1 ho hpc) inv.rel.env)
      fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    rw [next_add] at d₁
    refine M.runsTo_trans (M.law_bz (rk_val (by omega)) hw3 (M.at_sub C.codeOK (M.codeAt_mem m₁ hcode) h2 d₁.ok d₁.hpc))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    rw [v₁, ite_pos hc0, next_add] at d₂
    have inv₂ : M.InvM bv wb N fp R wbase σ s₂ W :=
      ⟨inv.wh, inv.hv, inv.below, RelB.same M.toMachineF inv.rel (by rw [m₂, m₁]) (M.keep_trans d₁.keep d₂.keep)
        fun i => by rw [st₂, k₁ _ (.inr (avar_ge i))]⟩
    have kc₂ := M.keepC_trans (M.kC d₁) (M.kC d₂)
    have om₂ : M.mem s₂ = M.mem s := by rw [m₂, m₁]
    refine M.runsTo_mono (ih hc.2 hF hhi hw6 (h5.cast (by omega)) (M.codeAt_mem om₂ hcode) d₂.ok
      (M.pcIs_cast d₂.hpc (by omega)) inv₂ (b := b)) fun s₃ h => ?_
    rcases h with ⟨pk₃, ok₃, kc₃, pc₃, hc₃, o₃, W₃, iu₃, inv₃⟩ | ⟨pk₃, ok₃, kc₃, pc₃, o₃⟩
    · exact .inl ⟨pk₃, ok₃, M.keepC_trans kc₂ kc₃, M.pcIs_cast pc₃ (by simp only [lenCM]; omega), hc₃,
        (Out.of_eq om₂).trans o₃, W₃, iu₃, inv₃⟩
    · exact .inr ⟨pk₃, ok₃, M.keepC_trans kc₂ kc₃, pc₃, (Out.of_eq om₂).trans o₃⟩
  | @loopF c bd σ hc0 =>
    intro hc N fp pos s W b hF hhi hwf hsub hcode ho hpc inv
    simp only [compCM, codeZ_append, codeZ_xs, codeZ_one, encZ_A, wfCM] at hsub hwf
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
      exact M.pcIs_cast d₂.hpc (by simp only [lenCM]; omega)
  | @loopT c bd σ σ₁ σ₂ E₁ E₂ hc0 _ _ ih₁ ih₂ =>
    intro hc N fp pos s W b hF hhi hwf hsub hcode ho hpc inv
    have hc' := hc
    simp only [CStmt.clean, Bool.and_eq_true] at hc'
    have hwf0 := hwf
    have hsub0 := hsub
    simp only [compCM, codeZ_append, codeZ_xs, codeZ_one, encZ_A, wfCM] at hsub hwf
    obtain ⟨hw1, hw2, hw3, hw4, hw5⟩ := hwf
    obtain ⟨h123, h4⟩ := hsub.split
    obtain ⟨h12, h3⟩ := h123.split
    obtain ⟨h1, h2⟩ := h12.split
    simp only [List.length_append, M.len_bz, len_compCM] at h3 h4
    refine M.runsTo_trans (M.genB_ok hF σ.env c 0 (by omega) hw2 (M.at_sub C.codeOK hcode h1 ho hpc) inv.rel.env)
      fun s₁ ⟨d₁, m₁, v₁, k₁⟩ => ?_
    rw [next_add] at d₁
    refine M.runsTo_trans (M.law_bz (rk_val (by omega)) hw3 (M.at_sub C.codeOK (M.codeAt_mem m₁ hcode) h2 d₁.ok d₁.hpc))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    rw [v₁, ite_neg hc0, M.len_bz, next_add] at d₂
    have inv₂ : M.InvM bv wb N fp R wbase σ s₂ W :=
      ⟨inv.wh, inv.hv, inv.below, RelB.same M.toMachineF inv.rel (by rw [m₂, m₁]) (M.keep_trans d₁.keep d₂.keep)
        fun i => by rw [st₂, k₁ _ (.inr (avar_ge i))]⟩
    refine M.runsTo_trans (ih₁ hc'.2 hF hhi hw5 (h3.cast (by omega)) (M.codeAt_mem (by rw [m₂, m₁]) hcode) d₂.ok
      (M.pcIs_cast d₂.hpc (by omega)) inv₂ (b := b)) fun s₃ h => ?_
    rcases h with ⟨pk₃, ok₃, kc₃, pc₃, hc₃, o₃, W₃, iu₃, inv₃⟩ | ⟨pk₃, ok₃, kc₃, pc₃, o₃⟩
    · refine M.runsTo_trans (M.law_jmp hw4 (M.at_sub C.codeOK hc₃ h4 ok₃ (M.pcIs_cast pc₃ (by omega))))
        fun s₄ ⟨d₄, st₄, m₄⟩ => ?_
      have pc₄ : M.pcIs s₄ (next cb pos) := M.pcIs_jmp d₄.hpc (by omega)
      refine M.runsTo_mono (ih₂ hc hF hhi hwf0 hsub0 (M.codeAt_mem m₄ hc₃) d₄.ok pc₄
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
  | @call res f args σ E σ₁ hf ha _ ih =>
    intro hc N fp pos s W b hF hhi hwf hsub hcode ho hpc inv
    simp only [CStmt.clean, Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨hres0, hargs⟩ := hc
    have hres := ne_hvar (not_unread hres0)
    obtain ⟨hbody, hret⟩ := fn_clean hP hf
    have enl := nlOf_eq hf
    simp only [compCM, MachineC.lenArgs, codeZ_append, codeZ_xs, codeZ_y, codeZ_one, encZ_C, wfCM, enl] at hsub hwf
    obtain ⟨-, hw2, hw3, hw4, hw5, hw6, hw7, hw8, hw9⟩ := hwf
    obtain ⟨hwN, hwr1, hwr2, hwb⟩ := C.wf f hf
    obtain ⟨h123, h4⟩ := hsub.split
    obtain ⟨h12, h3⟩ := h123.split
    obtain ⟨h1, h2⟩ := h12.split
    simp only [List.length_append, len_chkF, M.len_call] at h2 h3 h4
    have hfrm : P[f].frame = 8 * (P[f].nlocals + 1) := rfl
    have hstk := C.stk
    unfold Base.inRAM at hstk
    have hal := hF.al
    have hfr0 := MachineF.Frm.fr M.toMachineF hF inv.rel.env.fr
    have hlt := M.ramHi_lt
    have hsl := C.slotsLe
    have hwal := C.wal
    have hbel := inv.below
    have hfpR := hF.ram
    unfold Base.inRAM at hfpR
    have hpad : (padArgs P[f].nlocals args).length = P[f].nlocals := padArgs_length hw2
    have hU0 : M.get s regU = BitVec.ofNat 64 W.length := by
      rw [show regU = avar ⟨7, by decide⟩ from rfl, inv.rel.env.reg]; exact inv.hv
    have hW0 : M.get s (avar wb) = BitVec.ofNat 64 wbase := by
      rw [inv.rel.env.reg]; have := inv.rel.wbase 0 (by simp); simpa using this
    -- 1. the call check
    refine M.runsTo_trans (M.chkF_ok C.codeOK h1 hw8 hw9 hcode ho hpc hU0 hW0 inv.rel.env.fr (by omega)
      (by omega) (by omega)) fun s₁ h => ?_
    rcases h with ⟨hfit, d₁, k₁, m₁⟩ | ⟨hno, ok₁, kc₁, pc₁, m₁⟩
    rotate_left
    · refine M.runsTo_of (.inr ⟨?_, ok₁, kc₁, pc₁, Out.of_eq m₁⟩)
      rw [peak_call]
      have := peak_ge E (b + W.length + (P[f].nlocals + 1))
      omega
    have henv₁ : M.EnvB N fp σ.env s₁ :=
      EnvB.of M.toMachineF inv.rel.env m₁ d₁.keep fun i => k₁ _ (avar_ge i)
    have hc₁ := M.codeAt_mem m₁ hcode
    -- 2. the arguments
    refine M.runsTo_trans (M.args_ok C.codeOK hF σ.env P[f].nlocals hwN (by omega) (by unfold Base.inRAM; omega)
      (C.cd_in (by omega) (by omega)) (fun a h1 h2 => C.stw a (by omega) (by omega))
      (padArgs P[f].nlocals args) 0 (pos + M.lenChkF wb P[f].nlocals) (by omega) (pad_wf hw3) h2 hc₁ d₁.ok d₁.hpc
      henv₁) fun s₂ ⟨d₂, e₂, o₂, b₂⟩ => ?_
    rw [Nat.sub_zero] at o₂
    have hc₂ : M.codeAt s₂ cb Wc := M.codeAt_out hc₁ C.codeOK (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact C.cd_in (by omega) (by omega)) o₂
    -- 3. the call
    refine M.runsTo_trans (M.law_call hw7 (M.at_sub C.codeOK hc₂ (h3.cast (by omega)) d₂.ok d₂.hpc))
      fun s₃ ⟨ok₃, kc₃, pc₃, ra₃, fr₃, st₃, m₃⟩ => ?_
    rw [MachineC.next_call] at pc₃
    have hfr₃ : (M.fr s₃).toNat = fp := by rw [fr₃, M.keep_fr d₂.keep, M.keep_fr d₁.keep]; exact hfr0
    -- 4. the callee's prologue
    have hfn := C.fns f hf
    simp only [fnCM, codeZ_append, codeZ_xs, codeZ_one, codeZ_cons, codeZ_nil, List.append_nil, encZ_C, encZ_A]
      at hfn
    obtain ⟨g123, g4⟩ := hfn.split
    obtain ⟨g12, g3⟩ := g123.split
    obtain ⟨g1, g2⟩ := g12.split
    obtain ⟨g4a, g4b⟩ := g4.split
    simp only [List.length_append, len_compCM] at g3 g4a g4b
    refine M.runsTo_trans (M.law_enterC hwN (M.at_sub C.codeOK (M.codeAt_mem m₃ hc₂) g1 ok₃ pc₃)
      (by rw [hfr₃]; omega) (by rw [hfr₃]; unfold Base.inRAM; omega) (by rw [hfr₃]; exact hal)
      (fun i hi => by rw [hfr₃]; exact C.stw _ (by omega) (by omega) _ ok₃))
      fun s₄ ⟨ok₄, kc₄, pc₄, fr₄, st₄, m₄⟩ => ?_
    rw [hfr₃] at fr₄ m₄
    rw [next_add] at pc₄
    have hF' : M.Frm P[f].nlocals (fp - 8 * (P[f].nlocals + 1)) :=
      ⟨by unfold Base.inRAM; omega, by omega, hwN, fun a h1 h2 => C.stw a (by omega) (by omega)⟩
    have o₄ : Out [⟨fp - 8 * (P[f].nlocals + 1), 8 * (P[f].nlocals + 1)⟩] (M.mem s) (M.mem s₄) := by
      refine (Out.of_eq m₁).trans ((out1 o₂ (by omega) (by omega)).trans ?_)
      rw [m₄, m₃]
      exact Out.wr (List.mem_singleton_self _) (by dsimp only; omega) (by rw [length_le8]; dsimp only; omega)
    have byR : ∀ (a l : Nat), (a + l ≤ fp - 8 * (P[f].nlocals + 1) ∨ fp ≤ a) →
        bytes (M.mem s₄) a l = bytes (M.mem s) a l := fun a l h => bytes_out o₄ fun r' hr' => by
          rw [List.mem_singleton] at hr'; subst hr'; unfold disjoint; dsimp only; omega
    have hrel₄ : M.RelB P[f].nlocals (fp - 8 * (P[f].nlocals + 1)) bv [wb.val] R [⟨wbase, 8 * W.length⟩]
        ⟨callEnv σ.env (args.map (·.denote σ.env)), σ.heap, σ.wheap⟩ s₄ := by
      have r := inv.rel
      refine ⟨⟨fun i => ?_, fr₄, fun j hj => ?_⟩, r.hlen, r.bvlen, fun b' hb' => ?_, r.blen,
        fun b' hb' => ?_, r.whlen, r.wvlen, fun b' hb' => ?_, r.wblen, fun b' hb' => ?_⟩
      · rw [st₄, st₃, e₂, henv₁.reg]
        show _ = if i.val < 8 then _ else _
        rw [ite_pos i.2]
      · have hb := b₂ j (by rw [hpad]; exact hj)
        rw [pad_denote] at hb
        rw [m₄, bytes_wr_out (by rw [length_le8]; omega), m₃,
          show fp - 8 * (P[f].nlocals + 1) + 8 * (j + 1) = fp - 8 * (P[f].nlocals - (0 + j)) by omega, hb]
        show _ = (le8 (if 8 + j < 8 then _ else (args.map _).getD (8 + j - 8) 0)).map some
        rw [ite_neg (by omega), Nat.add_sub_cancel_left]
      · show (if bv.getD b' 0 < 8 then σ.env (bv.getD b' 0) else _) = _
        rw [ite_pos (C.bvlt _ (getD_memN (r.bvlen ▸ hb')))]; exact r.base b' hb'
      · have hd := C.rWrk (a := fp - 8 * (P[f].nlocals + 1)) (l := 8 * (P[f].nlocals + 1)) (by omega) (by omega)
          (List.getElem_mem hb')
        unfold disjoint at hd; dsimp only at hd
        rw [byR _ _ (by omega)]; exact r.rbytes b' hb'
      · have hb0 : b' = 0 := by simp at hb'; omega
        subst hb0
        show (if [wb.val].getD 0 0 < 8 then σ.env ([wb.val].getD 0 0) else _) = _
        rw [ite_pos (by simp)]
        exact r.wbase 0 hb'
      · have : b' = 0 := by simp at hb'; omega
        subst this
        rw [show ([⟨wbase, 8 * W.length⟩] : List Region)[0] = ⟨wbase, 8 * W.length⟩ from rfl, byR _ _ (by
          dsimp only; omega)]
        exact r.wbyts 0 hb'
    have inv₄ : M.InvM bv wb P[f].nlocals (fp - 8 * (P[f].nlocals + 1)) R wbase
        ⟨callEnv σ.env (args.map (·.denote σ.env)), σ.heap, σ.wheap⟩ s₄ W :=
      ⟨inv.wh, by simp only [callEnv, show hvar < 8 by decide, if_true]; exact inv.hv, by omega, hrel₄⟩
    have hc₄ : M.codeAt s₄ cb Wc := M.codeAt_out hcode C.codeOK (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact C.cd_in (by omega) (by omega)) o₄
    have kc₄ := M.keepC_trans (M.kC d₁) (M.keepC_trans (M.kC d₂) (M.keepC_trans kc₃ kc₄))
    have o₄W : Out (WrtM N fp R wbase) (M.mem s) (M.mem s₄) := out_wrtM o₄ (by omega) (by omega)
    have hA' : b + (P[f].nlocals + 1) + (fp - 8 * (P[f].nlocals + 1) - wbase) / 8 = b + (fp - wbase) / 8 := by omega
    -- 5. the body
    refine M.runsTo_trans (ih hbody hF' (by omega) hwb g2 hc₄ ok₄ pc₄ inv₄ (b := b + (P[f].nlocals + 1)))
      fun s₅ h => ?_
    rw [hA', show b + (P[f].nlocals + 1) + W.length = b + W.length + (P[f].nlocals + 1) by omega] at h
    rcases h with ⟨pk₅, ok₅, kc₅, pc₅, hc₅, o₅, W₅, iu₅, inv₅⟩ | ⟨pk₅, ok₅, kc₅, pc₅, o₅⟩
    rotate_left
    · refine M.runsTo_of (.inr ⟨?_, ok₅, M.keepC_trans kc₄ kc₅, pc₅, o₄W.trans (wrtM_callee o₅ (by omega) (by omega))⟩)
      rw [peak_call]; omega
    -- 6. the result
    refine M.runsTo_trans (M.genB_ok hF' σ₁.env P[f].ret 0 (by omega) hwr2
      (M.at_sub C.codeOK hc₅ g3 ok₅ (M.pcIs_cast pc₅ (by omega))) inv₅.rel.env) fun s₆ ⟨d₆, m₆, v₆, k₆⟩ => ?_
    rw [next_add] at d₆
    -- 7. the epilogue
    have hfr₆ : (M.fr s₆).toNat = fp - 8 * (P[f].nlocals + 1) :=
      MachineF.Frm.fr M.toMachineF hF' (by rw [M.keep_fr d₆.keep, inv₅.rel.env.fr])
    have hsv : bytes (M.mem s₆) (fp - 8 * (P[f].nlocals + 1)) 8 = (le8 (M.ra s₃)).map some := by
      rw [m₆, bytes_out o₅ (C.cell0M (by omega) (by omega)), m₄]
      have := bytes_wr_self (m := M.mem s₃) (a := fp - 8 * (P[f].nlocals + 1)) (l := le8 (M.ra s₃))
      rw [length_le8] at this; exact this
    refine M.runsTo_trans (M.law_leaveC (w := M.ra s₃) hwN
      (M.at_sub C.codeOK (M.codeAt_mem m₆ hc₅) g4a d₆.ok (M.pcIs_cast d₆.hpc (by omega)))
      (by rw [hfr₆]; exact hF'.ram) (by rw [hfr₆]; exact hF'.al) (by rw [hfr₆]; exact hsv))
      fun s₇ ⟨ok₇, kc₇, pc₇, ra₇, fr₇, st₇, m₇⟩ => ?_
    rw [next_add] at pc₇
    rw [hfr₆, Nat.sub_add_cancel (by omega)] at fr₇
    have hret : M.retOK (M.ra s₇) := by
      rw [ra₇, ra₃, next_add]
      apply M.retOK_al
      rw [M.pc_toNat C.codeOK (by have := h3.le; rw [M.len_call] at this; omega)]
      have := C.codeOK.1; omega
    refine M.runsTo_trans (M.law_ret hret (M.at_sub C.codeOK (M.codeAt_mem m₇ (M.codeAt_mem m₆ hc₅)) g4b ok₇
      (M.pcIs_cast pc₇ (by omega)))) fun s₈ ⟨d₈, st₈, m₈⟩ => ?_
    rw [ra₇, ra₃, next_add] at d₈
    -- 8. back in the caller
    have m₈₅ : M.mem s₈ = M.mem s₅ := by rw [m₈, m₇, m₆]
    have o₈ : Out (WrtM N fp R wbase) (M.mem s) (M.mem s₈) := by
      rw [m₈₅]; exact o₄W.trans (wrtM_callee o₅ (by omega) (by omega))
    have hrel₈ : M.RelB N fp bv [wb.val] R [⟨wbase, 8 * W₅.length⟩] ⟨retEnv σ.env σ₁.env, σ₁.heap, σ₁.wheap⟩ s₈ := by
      have r₅ := inv₅.rel
      refine ⟨⟨fun i => ?_, ?_, fun j hj => ?_⟩, r₅.hlen, r₅.bvlen, fun b' hb' => ?_, r₅.blen,
        fun b' hb' => by rw [m₈₅]; exact r₅.rbytes b' hb', r₅.whlen, r₅.wvlen, fun b' hb' => ?_, r₅.wblen,
        fun b' hb' => by rw [m₈₅]; exact r₅.wbyts b' hb'⟩
      · rw [st₈, st₇, k₆ _ (.inr (avar_ge i)), r₅.env.reg]
        show _ = if i.val < 8 then _ else _
        rw [ite_pos i.2]
      · rw [M.keep_fr d₈.keep, fr₇]
      · have hs := C.slotM (n := P[f].nlocals) (fp' := fp - 8 * (P[f].nlocals + 1)) (by omega) (by omega) hhi hj
        rw [m₈₅, bytes_out o₅ hs, bytes_out o₄ (fun r' hr' => by
          rw [List.mem_singleton] at hr'; subst hr'; unfold disjoint; dsimp only; omega), inv.rel.env.slot j hj]
        show _ = (le8 (if 8 + j < 8 then _ else _)).map some
        rw [ite_neg (by omega)]
      · show (if bv.getD b' 0 < 8 then σ₁.env (bv.getD b' 0) else _) = _
        rw [ite_pos (C.bvlt _ (getD_memN (r₅.bvlen ▸ hb')))]; exact r₅.base b' hb'
      · have hb0 : b' = 0 := by simp at hb'; omega
        subst hb0
        show (if [wb.val].getD 0 0 < 8 then σ₁.env ([wb.val].getD 0 0) else _) = _
        rw [ite_pos (by simp)]
        exact r₅.wbase 0 hb'
    -- 9. the result variable
    have hx : M.get s₈ (rk 0) = P[f].ret.denote σ₁.env := by rw [st₈, st₇, v₆]
    have hL := C.lay (N := N) (fp := fp) (u := W₅.length) (by have := inv₅.below; omega) hhi
    have hc₈ := C.codeAt_W (by omega) hhi hcode o₈
    refine M.runsTo_mono (M.setV_ok hF hL hw4 hw5 hw6
      (M.at_sub C.codeOK hc₈ h4 d₈.ok (M.pcIs_cast d₈.hpc (by omega))) hx hrel₈) fun s₉ ⟨d₉, o₉, r₉⟩ => ?_
    rw [next_add] at d₉
    refine .inl ⟨?_, d₉.ok, ?_, M.pcIs_cast d₉.hpc (by simp only [lenCM, MachineC.lenArgs, enl]; omega),
      C.codeAt_W (by omega) hhi hc₈ (allR_wrtM (by have := inv₅.below; omega) o₉ (B0_of_rel hrel₈ r₉ rfl)),
      o₈.trans (allR_wrtM (by have := inv₅.below; omega) o₉ (B0_of_rel hrel₈ r₉ rfl)), W₅, ?_,
      ⟨inv₅.wh, ?_, by have := inv₅.below; omega, r₉⟩⟩
    · rw [peak_call]
      have := inUse_le_peak (E ++ [.alloc (b + W.length + (P[f].nlocals + 1))])
      omega
    · exact M.keepC_trans kc₄ (M.keepC_trans kc₅ (M.keepC_trans (M.kC d₆) (M.keepC_trans kc₇
        (M.keepC_trans (M.kC d₈) (M.kC d₉)))))
    · rw [inUse_call, iu₅]; omega
    · show (BEnv.set (retEnv σ.env σ₁.env) res (P[f].ret.denote σ₁.env)) hvar = _
      simp only [BEnv.set, retEnv, show hvar < 8 by decide, if_true]
      rw [if_neg (Ne.symm hres)]; exact inv₅.hv

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF Proven.Top.Alloc

namespace MachineM
variable (M : MachineM) (P : Prog) (bv : List Nat) (wb : Fin 8)

/-! ## whole programs -/

/-- the word where function `f` of the table `Fs` (placed at `start`) begins -/
def offsM (start : Nat) : List Fn → Nat → Nat
  | [], _ => start
  | _ :: _, 0 => start
  | F :: Fs, f + 1 => offsM (start + M.lenFM P bv wb F) Fs f

def fnsCM (off : Nat → Nat) (hp : Nat) : Nat → List Fn → List ZOp
  | _, [] => []
  | pos, F :: Fs => M.fnCM P bv wb off hp pos F ++ fnsCM off hp (pos + M.lenFM P bv wb F) Fs

def lenFns (start : Nat) : List Fn → Nat
  | [] => 0
  | F :: Fs => M.lenFM P bv wb F + lenFns (start + M.lenFM P bv wb F) Fs

theorem len_fnsCM (off : Nat → Nat) (hp : Nat) : ∀ (Fs : List Fn) (start : Nat),
    (M.codeZ (M.fnsCM P bv wb off hp start Fs)).length = M.lenFns P bv wb start Fs
  | [], _ => rfl
  | F :: Fs, start => by
    simp only [fnsCM, lenFns, codeZ_append, List.length_append, len_fnCM, len_fnsCM off hp Fs]

theorem fnsM_sub (off : Nat → Nat) (hp : Nat) : ∀ (Fs : List Fn) (start : Nat) (pre post : List (BitVec 32)),
    pre.length = start → ∀ f (hf : f < Fs.length),
    Sub (pre ++ M.codeZ (M.fnsCM P bv wb off hp start Fs) ++ post) (M.offsM P bv wb start Fs f)
      (M.codeZ (M.fnCM P bv wb off hp (M.offsM P bv wb start Fs f) Fs[f]))
  | F :: Fs, start, pre, post, hp', 0, _ =>
    ⟨pre, M.codeZ (M.fnsCM P bv wb off hp (start + M.lenFM P bv wb F) Fs) ++ post, by
      show pre ++ M.codeZ (M.fnCM P bv wb off hp start F ++ _) ++ post = pre ++ M.codeZ (M.fnCM P bv wb off hp start F) ++ _
      rw [codeZ_append]; simp only [List.append_assoc], hp'⟩
  | F :: Fs, start, pre, post, hp', f + 1, hf => by
    have hf' : f < Fs.length := by simp only [List.length_cons] at hf; omega
    have := fnsM_sub off hp Fs (start + M.lenFM P bv wb F) (pre ++ M.codeZ (M.fnCM P bv wb off hp start F)) post
      (by rw [List.length_append, len_fnCM, hp']) f hf'
    show Sub (pre ++ M.codeZ (M.fnCM P bv wb off hp start F ++ M.fnsCM P bv wb off hp (start + M.lenFM P bv wb F) Fs) ++ post)
      (M.offsM P bv wb (start + M.lenFM P bv wb F) Fs f)
      (M.codeZ (M.fnCM P bv wb off hp (M.offsM P bv wb (start + M.lenFM P bv wb F) Fs f) Fs[f]))
    rw [codeZ_append, ← List.append_assoc]; exact this

/-- the stub's early check: the stub's two cells must fit above the heap base -/
def pre1 : List ZOp :=
  [opA (.li (rk 1) 8), opA (.bin .sub (rk 0) (rk 0) (rk 1)), opA (.mov (rk 1) (avar wb))]
/-- the early exit: status `-1`, return -/
def early : List ZOp := [opA (.li (rk 0) (BitVec.allOnes 64)), opA (.mov (avar 0) (rk 0)), opA .ret]
/-- the globals the program owns start at 0, global 7 (the heap length) too -/
def zeroG : List ZOp :=
  [opA (.li (avar 4) 0), opA (.li (avar 5) 0), opA (.li (avar 6) 0), opA (.li regU 0)]

def preLen : Nat := (M.encM (.getTop (rk 0))).length + (M.codeZ (pre1 wb)).length + M.lenBr + (M.codeZ early).length

/-- the word where the stub's call statement begins -/
def posSM : Nat := M.preLen wb + (M.encX (.enter 0)).length + (M.encC (.enterC 0)).length + (M.codeZ zeroG).length

def lenStubM (res main : Nat) : Nat :=
  M.posSM wb + M.lenCM P bv wb (.call res main []) +
    ((M.encC (.leaveC 0)).length + ((M.encX .leave).length + (M.enc .ret).length))

def stubM (off : Nat → Nat) (hp res main : Nat) : List ZOp :=
  [.m (.getTop (rk 0))] ++ pre1 wb ++ [.m (.bgeu (rk 0) (rk 1) (M.lenBr + (M.codeZ early).length))] ++ early ++
    [opF (.enter 0), opC (.enterC 0)] ++ zeroG ++ M.compCM P bv wb off hp (M.posSM wb) (.call res main []) ++
    [opC (.leaveC 0), opF .leave, opA .ret]

def progOffM (res main : Nat) : Nat → Nat := M.offsM P bv wb (M.lenStubM P bv wb res main) P

/-- the exit's word -/
def hpM (res main : Nat) : Nat := M.lenStubM P bv wb res main + M.lenFns P bv wb (M.lenStubM P bv wb res main) P

/-- **the compiler with run-time memory checks**: stub, functions, exit -/
def compPM (res main : Nat) : List ZOp :=
  M.stubM P bv wb (M.progOffM P bv wb res main) (M.hpM P bv wb res main) res main ++
    M.fnsCM P bv wb (M.progOffM P bv wb res main) (M.hpM P bv wb res main) (M.lenStubM P bv wb res main) P ++
    [.m .exit]

theorem len_stubM (off : Nat → Nat) (hp res main : Nat) :
    (M.codeZ (M.stubM P bv wb off hp res main)).length = M.lenStubM P bv wb res main := by
  simp only [stubM, lenStubM, posSM, preLen, codeZ_append, codeZ_one, codeZ_cons, codeZ_nil, List.append_nil, encZ_m,
    encZ_C, encZ_F, encZ_A, List.length_append, len_compCM, M.len_bgeu]
  omega

/-- the well-formedness of the whole program -/
def WfPM (res main : Nat) : Prop :=
  (∀ f (hf : f < P.length), M.wfFM P bv wb (M.progOffM P bv wb res main) (M.hpM P bv wb res main)
    (M.progOffM P bv wb res main f) P[f]) ∧
  M.wfCM P bv wb (M.progOffM P bv wb res main) (M.hpM P bv wb res main) 0 (M.posSM wb) (.call res main []) ∧
  M.bzOK (M.lenBr + (M.codeZ early).length)

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF Proven.Top.Alloc

/-- the globals after the stub: the program's own globals `4 .. 6` and the heap length `7` are `0` -/
def stubEnv (env : BEnv) : BEnv := (((env.set 4 0).set 5 0).set 6 0).set hvar 0

theorem stubEnv_lt4 (env : BEnv) {i : Nat} (h : i < 4) : stubEnv env i = env i := by
  simp only [stubEnv, BEnv.set, hvar]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

namespace MachineM
variable {M : MachineM} {P : Prog} {bv : List Nat} {wb : Fin 8}

theorem pre1_simple (wb : Fin 8) : ∀ o ∈ pre1 wb, simpleOK o := by
  intro o ho
  simp only [pre1, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  all_goals first
    | exact (show (rk 1).val < 11 from by decide)
    | exact ⟨by decide, rfl, rfl⟩
    | exact movOK_rk_avar (by decide) _

theorem zeroG_simple : ∀ o ∈ zeroG, simpleOK o := by
  intro o ho
  simp only [zeroG, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  all_goals show (Fin.val _) < 11
  all_goals decide

theorem pre1_eff (wb : Fin 8) (f t : BitVec 64) (g : Reg → BitVec 64) :
    sEffs f t (pre1 wb) g (rk 0) = g (rk 0) - 8 ∧ sEffs f t (pre1 wb) g (rk 1) = g (avar wb) ∧
    ∀ r : Reg, 7 ≤ r.val → sEffs f t (pre1 wb) g r = g r := by
  refine ⟨?_, ?_, fun r hr => ?_⟩
  · simp [sEffs, sEff, pre1, avar_ne_rk, Op.eval, rk01, rk02, rk12, rk10, rk20, rk21]
  · simp [sEffs, sEff, pre1, avar_ne_rk, Op.eval, rk01, rk02, rk12, rk10, rk20, rk21]
  · have h0 : r ≠ rk 0 := fun e => by subst e; simp [rk] at hr
    have h1 : r ≠ rk 1 := fun e => by subst e; simp [rk] at hr
    simp [sEffs, sEff, pre1, h0, h1]

theorem zeroG_eff (f t : BitVec 64) (g : Reg → BitVec 64) (i : Fin 8) :
    sEffs f t zeroG g (avar i) = if 4 ≤ i.val then 0 else g (avar i) := by
  match i with
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ =>
    simp (config := {decide := true}) [sEffs, sEff, zeroG, regU, avar, Fin.ext_iff]

end MachineM
end Proven.Mach

namespace Proven.Mach
open MachineF Proven.Top.Alloc

namespace MachineM
variable {M : MachineM} {P : Prog} {bv : List Nat} {wb : Fin 8}

/-- the layout of a run: the code at `cb`, the byte blocks `R`, the work area `[wbase, frameAt s 0 + 8)` -/
structure PLayM (cb : BitVec 64) (n : Nat) (R : List Region) (wbase top : Nat) : Prop where
  ram : ∀ r ∈ R, M.inRAM r.base r.len
  rp : R.Pairwise disjoint
  wal : wbase % 8 = 0
  lotop : wbase ≤ top
  stk : M.inRAM wbase (top - wbase)
  sR : ∀ r ∈ R, disjoint ⟨wbase, top - wbase⟩ r
  cd : ∀ r ∈ R ++ [⟨wbase, top - wbase⟩], disjoint ⟨cb.toNat, 4 * n⟩ r
  wr : ∀ r ∈ R, ∀ a, r.base ≤ a → a < r.base + r.len → ∀ s, M.ok s → M.writable s a
  stw : ∀ a, wbase ≤ a → a < top → ∀ s, M.ok s → M.writable s a
  slotsLe : 8 * (M.maxSlots + 1) ≤ wbase

/-- **Programs with run-time memory checks: compiler correctness from the `MachineM` laws.**  The run with
events of `res := main()` from the globals with `4 .. 7` zeroed and an empty heap ends in `σ'` with
events `E`.  If the entry stub's two cells and the events fit the cells of the work area (`peak ≤ cells`)
the code returns to the caller with `σ'`'s globals and blocks; else it returns with `-1` in global 0.
Either way it writes only the byte blocks and the work area. -/
theorem compPM_ok (hP : progClean P = true) {res main : Nat} (hres : (!unread.contains res) = true)
    {R : List Region} {wbase : Nat} {env : BEnv} {H : Heap} {σ' : BState} {E : List MemEvent} {s : M.S}
    {cb : BitVec 64}
    (hex : TExec P (.call res main []) ⟨stubEnv env, H, [[]]⟩ E σ')
    (hA : M.At s cb (M.codeZ (M.compPM P bv wb res main))) (hwf : M.WfPM P bv wb res main)
    (hbv4 : ∀ x ∈ bv, x < 4) (hwb4 : wb.val < 4) (hwbv : wb.val ∉ bv)
    (hen : wbase ≤ M.frameAt s 0 - 8 → M.enterOK s 0)
    (hL : M.PLayM cb (M.codeZ (M.compPM P bv wb res main)).length R wbase (M.frameAt s 0 + 8))
    (hreg : ∀ i : Fin 8, M.get s (avar i) = env i.val) (hwbase : env wb.val = BitVec.ofNat 64 wbase)
    (hlen : H.length = R.length) (hbvl : bv.length = R.length)
    (hbase : ∀ b (hb : b < R.length), env (bv.getD b 0) = BitVec.ofNat 64 R[b].base)
    (hblen : ∀ b (hb : b < R.length), (H[b]?.getD []).length = R[b].len)
    (hbytes : ∀ b (hb : b < R.length), bytes (M.mem s) R[b].base R[b].len = (H[b]?.getD []).map some)
    (hra : M.retOK (M.ra s)) (htop8 : 8 ≤ M.frameAt s 0) :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ M.ok s' ∧
      Out (R.drop 1 ++ [⟨wbase, M.frameAt s 0 + 8 - wbase⟩]) (M.mem s) (M.mem s') ∧
      ((peak (E ++ [.alloc 2]) ≤ (M.frameAt s 0 + 8 - wbase) / 8 ∧
          (∀ i : Fin 8, M.get s' (avar i) = σ'.env i.val) ∧
          ∃ W' : List (BitVec 64), M.HeapB bv [wb.val] R [⟨wbase, 8 * W'.length⟩] σ' s') ∨
        ((M.frameAt s 0 + 8 - wbase) / 8 < peak (E ++ [.alloc 2]) ∧ M.get s' (avar 0) = BitVec.allOnes 64)) := by
  obtain ⟨hwfF, hwfS, hbzE⟩ := hwf
  have hfns : ∀ f (hf : f < P.length), Sub (M.codeZ (M.compPM P bv wb res main)) (M.progOffM P bv wb res main f)
      (M.codeZ (M.fnCM P bv wb (M.progOffM P bv wb res main) (M.hpM P bv wb res main)
        (M.progOffM P bv wb res main f) P[f])) := fun f hf => by
    unfold compPM; rw [codeZ_append, codeZ_append]
    exact M.fnsM_sub P bv wb _ _ P _ _ _ (M.len_stubM P bv wb _ _ res main) f hf
  have hsubS : Sub (M.codeZ (M.compPM P bv wb res main)) 0
      (M.codeZ (M.stubM P bv wb (M.progOffM P bv wb res main) (M.hpM P bv wb res main) res main)) :=
    ⟨[], _, by unfold compPM; rw [codeZ_append, codeZ_append, List.append_assoc]; rfl, rfl⟩
  have hsubX : Sub (M.codeZ (M.compPM P bv wb res main)) (M.hpM P bv wb res main) (M.encM .exit) :=
    ⟨_, [], by unfold compPM; rw [codeZ_append, codeZ_append, codeZ_one, encZ_m, List.append_nil],
      by rw [List.length_append, len_stubM, len_fnsCM]; rfl⟩
  generalize M.codeZ (M.compPM P bv wb res main) = Wc at hA hL hsubS hfns hsubX
  generalize M.progOffM P bv wb res main = off at hwfF hwfS hsubS hfns
  generalize M.hpM P bv wb res main = hp at hwfF hwfS hsubS hfns hsubX
  generalize hfp : M.frameAt s 0 = fp₀ at *
  have hstk := hL.stk
  unfold Base.inRAM at hstk
  have hlt := M.ramHi_lt
  have hsl := hL.slotsLe
  simp only [stubM, codeZ_append, codeZ_cons, codeZ_nil, List.append_nil, encZ_m, encZ_C, encZ_F, encZ_A]
    at hsubS
  obtain ⟨q7, qend⟩ := hsubS.split
  obtain ⟨q6, qcall⟩ := q7.split
  obtain ⟨q5, qzero⟩ := q6.split
  obtain ⟨q4, qecs⟩ := q5.split
  obtain ⟨q3, qearly⟩ := q4.split
  obtain ⟨qGP, qbge⟩ := q3.split
  obtain ⟨qtop, qpre⟩ := qGP.split
  obtain ⟨qen, qec⟩ := qecs.split
  obtain ⟨qlc, qlvr⟩ := qend.split
  obtain ⟨qlv, qret⟩ := qlvr.split
  simp only [List.length_append, len_compCM, M.len_bgeu] at qbge qearly qen qec qzero qcall qlc qlv qret
  have hc := hA.code
  have hok := hA.codeOK
  have hpc0 : M.pcIs s (next cb 0) := by rw [next_zero]; exact hA.hpc
  have hcd := hL.cd
  have hcdS := hcd _ memLast
  unfold disjoint at hcdS; dsimp only at hcdS
  -- 1. `r0 := frameAt - 8`, `r1 := wbase`
  refine M.runsTo_trans (M.law_getTop (d := rk 0) (by decide) (by rw [hfp]; exact htop8)
    (M.at_sub hok hc qtop hA.ok hpc0))
    fun s₀ ⟨d₀, st₀, m₀⟩ => ?_
  rw [next_add] at d₀
  refine M.runsTo_trans (M.run_simple (pre1 wb) (pre1_simple wb) (M.at_sub hok (M.codeAt_mem m₀ hc) qpre d₀.ok
    (M.pcIs_cast d₀.hpc (by omega)))) fun s₁' ⟨d₁', g₁, m₁'⟩ => ?_
  rw [next_add] at d₁'
  have d₁ := Core.Done.trans _ d₀ d₁'
  have m₁ : M.mem s₁' = M.mem s := by rw [m₁', m₀]
  rename_i s₁ _
  clear d₁'
  obtain ⟨e10, e11, e17⟩ := pre1_eff wb (M.fr s₀) (BitVec.ofNat 64 (M.frameAt s₀ 0)) (M.get s₀)
  have v0 : (M.get s₁' (rk 0)).toNat = fp₀ - 8 := by
    rw [g₁, e10, Core.Set1.same _ st₀, hfp, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      bv_sub_toNat (by omega) (by omega)]
  have v1 : (M.get s₁' (rk 1)).toNat = wbase := by
    rw [g₁, e11, Core.Set1.other _ st₀ (avar_ne_rk _ (by decide)), hreg, hwbase, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hc₁ := M.codeAt_mem m₁ hc
  refine M.runsTo_trans (M.law_bgeu hbzE (M.at_sub hok hc₁ qbge d₁.ok (M.pcIs_cast d₁.hpc (by omega))))
    fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
  rw [v0, v1] at d₂
  by_cases hfit0 : wbase ≤ fp₀ - 8
  rotate_left
  · -- the early exit
    rw [if_neg hfit0, next_add] at d₂
    simp only [early, codeZ_cons, codeZ_nil, List.append_nil, encZ_A] at qearly
    obtain ⟨e1, e23⟩ := qearly.split
    obtain ⟨e2, e3⟩ := e23.split
    have hc₂ := M.codeAt_mem m₂ hc₁
    refine M.runsTo_trans (M.law_li (d := rk 0) (c := BitVec.allOnes 64) (by decide)
      (M.at_sub hok hc₂ e1 d₂.ok (M.pcIs_cast d₂.hpc (by omega)))) fun s₃ ⟨d₃, st₃, m₃⟩ => ?_
    rw [next_add] at d₃
    refine M.runsTo_trans (M.law_mov (movOK_avar_rk0 0) (M.at_sub hok (M.codeAt_mem m₃ hc₂) e2 d₃.ok d₃.hpc))
      fun s₄ ⟨d₄, st₄, m₄⟩ => ?_
    rw [next_add] at d₄
    have era : M.ra s₄ = M.ra s := by
      rw [M.keep_ra d₄.keep, M.keep_ra d₃.keep, M.keep_ra d₂.keep, M.keep_ra d₁.keep]
    refine M.runsTo_mono (M.law_ret (by rw [era]; exact hra) (M.at_sub hok (M.codeAt_mem (m₄.trans m₃) hc₂) e3 d₄.ok
      d₄.hpc)) fun s₅ ⟨d₅, st₅, m₅⟩ => ⟨by rw [← era]; exact d₅.hpc, d₅.ok,
        Out.of_eq (by rw [m₅, m₄, m₃, m₂, m₁]), .inr ⟨?_, ?_⟩⟩
    · have := peak_ge E 2; omega
    · rw [st₅, Core.Set1.same _ st₄, Core.Set1.same _ st₃]
  rw [if_pos hfit0, next_add] at d₂
  have hc₂ := M.codeAt_mem m₂ hc₁
  -- 2. enter
  have hpc₂ : M.pcIs s₂ (next cb (0 + ((M.encM (KOp.getTop (rk 0))).length + (M.codeZ (pre1 wb)).length + M.lenBr +
      (M.codeZ early).length))) :=
    M.pcIs_cast d₂.hpc (by omega)
  have hk₂ := M.keep_trans d₁.keep d₂.keep
  have hen' := hen hfit0
  obtain ⟨hns, hram0, hal0, -⟩ := M.enterOK_frame hen'
  rw [hfp] at hram0 hal0
  unfold Base.inRAM at hram0
  have hen₂ : M.enterOK s₂ 0 := M.enterOK_keep hk₂ hen'
  have hfp₂ : M.frameAt s₂ 0 = fp₀ := by rw [M.frameAt_keep hk₂, hfp]
  refine M.runsTo_trans (M.law_enter hen₂ (M.at_sub hok hc₂ qen d₂.ok hpc₂) (by
    rw [hfp₂]; have := qen.le; have e := M.pc_toNat hok (a := 0 + ((M.encM (KOp.getTop (rk 0))).length +
      (M.codeZ (pre1 wb)).length + M.lenBr + (M.codeZ early).length)) (by omega)
    rw [e]; unfold disjoint; dsimp only; omega))
    fun s₃ ⟨ok₃, kf₃, pc₃, fr₃, rg₃, o₃, sv₃, z₃⟩ => ?_
  rw [hfp₂] at fr₃ o₃ sv₃
  rw [next_add] at pc₃
  have hfr₃ : (M.fr s₃).toNat = fp₀ := by rw [fr₃, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have oS₃ : Out [⟨wbase, fp₀ + 8 - wbase⟩] (M.mem s₂) (M.mem s₃) := out1 o₃ (by omega) (by omega)
  have hcdW : ∀ r ∈ [(⟨wbase, fp₀ + 8 - wbase⟩ : Region)], disjoint ⟨cb.toNat, 4 * Wc.length⟩ r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hcd _ memLast
  have hc₃ := M.codeAt_out hc₂ hok hcdW oS₃
  -- 3. save the return address
  refine M.runsTo_trans (M.law_enterC (n := 0) (Nat.zero_le _)
    (M.at_sub hok hc₃ qec ok₃ (M.pcIs_cast pc₃ (by omega))) (by rw [hfr₃]; omega)
    (by rw [hfr₃]; unfold Base.inRAM; omega) (by rw [hfr₃]; exact hal0)
    (fun i hi => by rw [hfr₃]; exact hL.stw _ (by omega) (by omega) _ ok₃))
    fun s₄ ⟨ok₄, kc₄, pc₄, fr₄, st₄, m₄⟩ => ?_
  rw [hfr₃] at fr₄ m₄
  rw [next_add] at pc₄
  have o₄ : Out [⟨fp₀ - 8 * (0 + 1), 8⟩] (M.mem s₃) (M.mem s₄) := by
    rw [m₄]; exact Out.wr (List.mem_singleton_self _) (Nat.le_refl _) (by rw [length_le8]; exact Nat.le_refl _)
  have oS₄ : Out [⟨wbase, fp₀ + 8 - wbase⟩] (M.mem s₂) (M.mem s₄) := oS₃.trans (out1 o₄ (by omega) (by omega))
  have hc₄ := M.codeAt_out hc₂ hok hcdW oS₄
  -- 4. zero the program's globals
  refine M.runsTo_trans (M.run_simple zeroG zeroG_simple (M.at_sub hok hc₄ qzero ok₄ (M.pcIs_cast pc₄ (by omega))))
    fun s₅ ⟨d₅, g₅, m₅⟩ => ?_
  rw [next_add] at d₅
  have hc₅ := M.codeAt_mem m₅ hc₄
  have m₅₂ : M.mem s₅ = M.mem s₄ := m₅
  have hfr₅ : M.fr s₅ = BitVec.ofNat 64 (fp₀ - 8 * (0 + 1)) := by rw [M.keep_fr d₅.keep, fr₄]
  -- 5. the context of the run
  have C : M.CtxM P bv wb off hp cb Wc R wbase fp₀ :=
    { codeOK := hok, fns := hfns, wf := hwfF, bvlt := fun x hx => by have := hbv4 x hx; omega,
      wb7 := fun e => by rw [e] at hwb4; exact absurd hwb4 (by decide),
      wbv := hwbv, hbv := fun h => by have := hbv4 _ h; simp [hvar] at this,
      ram := hL.ram, rp := hL.rp, wr := hL.wr, wal := hL.wal, lohi := by omega,
      stk := by unfold Base.inRAM; omega,
      sR := fun r hr => by have := hL.sR r hr; unfold disjoint at this ⊢; dsimp only at this ⊢; omega,
      cd := fun r hr => by
        rcases List.mem_append.1 hr with hr | hr
        · exact hcd r (List.mem_append_left _ hr)
        · rw [List.mem_singleton] at hr; subst hr; unfold disjoint; dsimp only; omega,
      stw := fun a h1 h2 => hL.stw a h1 (by omega), slotsLe := hsl }
  have hF : M.Frm 0 (fp₀ - 8 * (0 + 1)) := ⟨by unfold Base.inRAM; omega, by omega, Nat.zero_le _,
    fun a h1 h2 => hL.stw a (by omega) (by omega)⟩
  have byR : ∀ r ∈ R, bytes (M.mem s₅) r.base r.len = bytes (M.mem s) r.base r.len := fun r hr => by
    rw [m₅₂, bytes_out oS₄ fun r' hr' => by
      rw [List.mem_singleton] at hr'; subst hr'; exact disj_symm (hL.sR r hr), m₂, m₁]
  have hreg₅ : ∀ i : Fin 8, M.get s₅ (avar i) = stubEnv env i.val := fun i => by
    rw [g₅, zeroG_eff, st₄, rg₃ _ (avar_ge i), st₂, g₁, e17 _ (avar_ge i), Core.Set1.other _ st₀ (avar_ne_rk _ (by decide)), hreg]
    simp only [stubEnv, BEnv.set, hvar]
    match i with
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ => simp
  have inv₅ : M.InvM bv wb 0 (fp₀ - 8 * (0 + 1)) R wbase ⟨stubEnv env, H, [[]]⟩ s₅ [] := by
    refine ⟨rfl, by simp [stubEnv, BEnv.set], by simp; omega, ⟨⟨hreg₅, hfr₅, fun j hj => absurd hj (by omega)⟩,
      hlen, hbvl, fun b hb => ?_, hblen, fun b hb => by rw [byR _ (List.getElem_mem hb)]; exact hbytes b hb, rfl, rfl,
      fun b hb => ?_, fun b hb => ?_, fun b hb => ?_⟩⟩
    · show stubEnv env (bv.getD b 0) = _
      rw [stubEnv_lt4 _ (hbv4 _ (getD_memN (hbvl ▸ hb)))]; exact hbase b hb
    · have hb0 : b = 0 := by simp at hb; omega
      subst hb0; show stubEnv env ([wb.val].getD 0 0) = _
      simp only [List.getD_cons_zero]; rw [stubEnv_lt4 _ hwb4, hwbase]; rfl
    · have hb0 : b = 0 := by simp at hb; omega
      subst hb0; rfl
    · have hb0 : b = 0 := by simp at hb; omega
      subst hb0; rfl
  have kc₅ : M.keepC s s₅ := M.keepC_trans (M.kC d₁) (M.keepC_trans (M.kC d₂) (M.keepC_trans
    (M.keepC_of_keepF kf₃) (M.keepC_trans kc₄ (M.kC d₅))))
  have hcl : (CStmt.call res main []).clean = true := by
    simp only [CStmt.clean, List.all_nil, Bool.and_true]; exact hres
  have hA2 : 2 + (fp₀ - 8 * (0 + 1) - wbase) / 8 = (fp₀ + 8 - wbase) / 8 := by omega
  -- 6. the call of `main`
  refine M.runsTo_trans (M.execCM_ok C hP hex hcl hF (by omega) hwfS (qcall.cast (by unfold posSM preLen; omega))
    hc₅ d₅.ok (M.pcIs_cast d₅.hpc (by unfold posSM preLen; omega)) inv₅ (b := 2)) fun s₆ h => ?_
  rw [hA2] at h
  simp only [List.length_nil, Nat.add_zero] at h
  have hmS : M.mem s₅ = M.mem s₄ := m₅₂
  have oT₅ : Out (R.drop 1 ++ [⟨wbase, fp₀ + 8 - wbase⟩]) (M.mem s) (M.mem s₅) := by
    rw [hmS]; exact (Out.of_eq (by rw [m₂, m₁])).trans (Out.mono oS₄ fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact ⟨_, memLast, Nat.le_refl _, Nat.le_refl _⟩)
  have hsvS : bytes (M.mem s₅) (fp₀ - 8 * (0 + 1)) 8 = (le8 (M.ra s)).map some := by
    rw [hmS, m₄]
    have := bytes_wr_self (m := M.mem s₃) (a := fp₀ - 8 * (0 + 1)) (l := le8 (M.ra s₃))
    rw [length_le8] at this; rw [this, M.keepF_ra kf₃, M.keep_ra d₂.keep, M.keep_ra d₁.keep]
  rcases h with ⟨pk₆, ok₆, kc₆, pc₆, hc₆, o₆, W₆, iu₆, inv₆⟩ | ⟨pk₆, ok₆, kc₆, pc₆, o₆⟩
  rotate_left
  · -- out of memory: the exit
    have kc : M.keepC s s₆ := M.keepC_trans kc₅ kc₆
    have hfa : M.frameAt s₆ 0 = fp₀ := by rw [M.frameAt_keepC kc, hfp]
    have hcd₆ : ∀ r ∈ WrtM 0 (fp₀ - 8 * (0 + 1)) R wbase, disjoint ⟨fp₀ - 8, 8⟩ r := C.cell0M (by omega) (by omega)
    refine M.runsTo_mono (M.law_exit (w := M.ra s) (M.at_sub hok (C.codeAt_W (by omega) (by omega) hc₅ o₆) hsubX
      ok₆ pc₆) (by rw [hfa]; omega) (by rw [hfa]; unfold Base.inRAM; omega) (by rw [hfa]; omega)
      (by rw [hfa, bytes_out o₆ hcd₆]; exact hsvS) hra) fun s₇ ⟨ok₇, pc₇, a₇, m₇⟩ =>
        ⟨pc₇, ok₇, ?_, .inr ⟨pk₆, a₇⟩⟩
    rw [m₇]
    exact oT₅.trans (Out.mono o₆ fun r hr => by
      unfold WrtM at hr
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with (hr | hr) | hr
      · exact ⟨r, List.mem_append_left _ hr, Nat.le_refl _, Nat.le_refl _⟩
      · obtain ⟨j, hj, -⟩ := mem_slots hr; exact absurd hj (by omega)
      · subst hr; exact ⟨_, memLast, Nat.le_refl _, by dsimp only; omega⟩)
  -- 7. restore the return address and the frame register, return
  have hcdC : ∀ r ∈ WrtM 0 (fp₀ - 8 * (0 + 1)) R wbase, disjoint ⟨fp₀ - 8 * (0 + 1), 8⟩ r :=
    C.cell0M (by omega) (by omega)
  have hfr₆ : (M.fr s₆).toNat = fp₀ - 8 * (0 + 1) := MachineF.Frm.fr M.toMachineF hF inv₆.rel.env.fr
  refine M.runsTo_trans (M.law_leaveC (n := 0) (w := M.ra s) (Nat.zero_le _)
    (M.at_sub hok hc₆ qlc ok₆ (M.pcIs_cast pc₆ (by unfold posSM preLen; omega))) (by rw [hfr₆]; exact hF.ram)
    (by rw [hfr₆]; exact hF.al) (by rw [hfr₆, bytes_out o₆ hcdC]; exact hsvS))
    fun s₇ ⟨ok₇, kc₇, pc₇, ra₇, fr₇, st₇, m₇⟩ => ?_
  rw [hfr₆, Nat.sub_add_cancel (by omega)] at fr₇
  rw [next_add] at pc₇
  have hfr₇ : (M.fr s₇).toNat = fp₀ := by rw [fr₇, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hsv₇ : bytes (M.mem s₇) fp₀ 8 = (le8 (M.fr s)).map some := by
    rw [m₇, bytes_out o₆ (fun r hr => by
      unfold WrtM at hr
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with (hr | hr) | hr
      · have := hL.sR r (List.mem_of_mem_drop hr); unfold disjoint at this ⊢; dsimp only at this ⊢; omega
      · obtain ⟨j, hj, -⟩ := mem_slots hr; exact absurd hj (by omega)
      · subst hr; unfold disjoint; dsimp only; omega), hmS,
      bytes_out o₄ (fun r hr => by rw [List.mem_singleton] at hr; subst hr; unfold disjoint; dsimp only; omega)]
    rw [sv₃, M.keep_fr d₂.keep, M.keep_fr d₁.keep]
  refine M.runsTo_trans (M.law_leave (w := M.fr s)
    (M.at_sub hok (M.codeAt_mem m₇ hc₆) qlv ok₇ (M.pcIs_cast pc₇ (by omega)))
    (by rw [hfr₇]; unfold Base.inRAM; omega) (by rw [hfr₇]; exact hal0) (by rw [hfr₇]; exact hsv₇))
    fun s₈ ⟨ok₈, kf₈, pc₈, fr₈, st₈, m₈⟩ => ?_
  rw [next_add] at pc₈
  have era : M.ra s₈ = M.ra s := by rw [M.keepF_ra kf₈, ra₇]
  refine M.runsTo_mono (M.law_ret (by rw [era]; exact hra)
    (M.at_sub hok (M.codeAt_mem m₈ (M.codeAt_mem m₇ hc₆)) qret ok₈ (M.pcIs_cast pc₈ (by omega))))
    fun s₉ ⟨d₉, st₉, m₉⟩ => ?_
  have m₉₆ : M.mem s₉ = M.mem s₆ := by rw [m₉, m₈, m₇]
  have r₆ := inv₆.rel
  refine ⟨by rw [← era]; exact d₉.hpc, d₉.ok, ?_, .inl ⟨pk₆, fun i => by rw [st₉, st₈, st₇, r₆.env.reg], W₆,
    ⟨r₆.hlen, r₆.bvlen, r₆.base, r₆.blen, fun b hb => by rw [m₉₆]; exact r₆.rbytes b hb, r₆.whlen, r₆.wvlen,
      r₆.wbase, r₆.wblen, fun b hb => by rw [m₉₆]; exact r₆.wbyts b hb⟩⟩⟩
  rw [m₉₆]
  exact oT₅.trans (Out.mono o₆ fun r hr => by
    unfold WrtM at hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with (hr | hr) | hr
    · exact ⟨r, List.mem_append_left _ hr, Nat.le_refl _, Nat.le_refl _⟩
    · obtain ⟨j, hj, -⟩ := mem_slots hr; exact absurd hj (by omega)
    · subst hr; exact ⟨_, memLast, Nat.le_refl _, by dsimp only; omega⟩)

end MachineM
end Proven.Mach
