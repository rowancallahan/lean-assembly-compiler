/- The machine adapter (the "few small adapters" design, Testing/notes/NANO_V2_ARM.md §0-adapter): everything from a J
run to the owner's `CompileCorrect`/`CompileRuns` is proved ONCE over a `JTarget`.  A target supplies only
* its machine (`M : Machine`, Spec/Top: states, step, observe, configured, calling convention, RAM window),
* its machine words (`blockLen` words per J instruction, `enc`),
* its register locations (`reg`: J register ↦ machine register number; `scratch`: registers its blocks may clobber),
* its layout side condition (`lay`) and two laws: one J step = a machine run (`step_ok`), and the return to the host
  (`ret_ok`).
`Rel` (the J ↔ machine relation) is defined here, through `M.observe` only. -/
import Spec.Top
import Nano.V2Self.Proof.Machine.JLay
import Nano.V2Self.Proof.Machine.NoW
namespace JT
open Proven.Top SimW CallProbe

/-- byte `k` (0..3) of a 32-bit word, little-endian -/
def wbyte (w : BitVec 32) (k : Nat) : UInt8 := UInt8.ofBitVec (w.extractLsb' (8 * k) 8)

/-- byte `k` (0..7) of a J memory cell, little-endian -/
def cbyte (v : UInt64) (k : Nat) : UInt8 := (v >>> (8 * k).toUInt64).toUInt8

structure JTarget where
  M : Machine
  /-- machine words per J instruction -/
  blockLen : Nat
  /-- the words of one J instruction -/
  enc : J → List (BitVec 32)
  /-- J register ↦ machine register number (in `M.observe`) -/
  reg : Nat → Nat
  /-- machine registers the blocks may clobber -/
  scratch : List Nat
  /-- the target's side condition on a layout and program (ranges, window, encodability) -/
  lay : LayW → List J → Prop
  /-- the entry memory as bytes (`LayW.m0` of the entry state) -/
  m0 : M.State → Nat → Option (BitVec 8)
  /-- a target-private invariant kept along `Rel` (RISC-V: Sail memory beyond 2^64 unchanged) -/
  inv : LayW → M.State → Prop
  /-- the code words the layout records (`LayW.W`; RISC-V: the RV64 words) -/
  words : List J → List Nat

namespace JTarget
variable (T : JTarget)

/-- the byte address of J instruction `pc` -/
def addr (base pc : Nat) : Nat := base + 4 * T.blockLen * pc

/-- **the J ↔ machine relation** (SimW's `RelW`, stated through `observe`): `s0` is the entry state -/
structure Rel (K : LayW) (C : List J) (s0 : T.M.State) (p : Nat × CallProbe.St) (s : T.M.State) : Prop where
  cfg : T.M.configured s
  pc : (T.M.observe s).programCounter = UInt64.ofNat (T.addr K.base p.1)
  code : ∀ i (h : i < C.length) k (hk : k < (T.enc C[i]).length) b, b < 4 →
    (T.M.observe s).memory (UInt64.ofNat (T.addr K.base i + 4 * k + b)) = some (wbyte (T.enc C[i])[k] b)
  x0 : p.2.x 0 = 0
  bb : p.2.b = K.base
  x : ∀ j, 0 < j → j < 32 → (T.M.observe s).register (T.reg j) = p.2.x j
  keep : ∀ r, (∀ j, 0 < j → j < 32 → T.reg j ≠ r) → r ∉ T.scratch →
    (T.M.observe s).register r = (T.M.observe s0).register r
  w : ∀ a, wok K a → ∀ k < 8, (T.M.observe s).memory (UInt64.ofNat (a + k)) = some (cbyte (p.2.m a) k)
  bw : ∀ a, io K a → (T.M.observe s).memory (UInt64.ofNat a) = some (cbyte (p.2.m (a - a % 8)) (a % 8))
  fr : ∀ a, a < 2 ^ 64 → ¬ wok K (a - a % 8) → ¬ outB K a →
    (T.M.observe s).memory (UInt64.ofNat a) = (K.m0 a).map UInt8.ofBitVec
  inv : T.inv K s

/-- the generic layout conditions (`LayW.Ok` with the machine's RAM window and `n` code bytes) -/
structure LayOK (M : Machine) (n : Nat) (K : LayW) : Prop where
  b4 : K.base % 4 = 0
  blo : M.ramStart ≤ K.base
  bhi : K.base + n ≤ M.ramEnd
  wlo : M.ramStart ≤ K.lo
  whi : K.hi ≤ M.ramEnd
  cw : K.base + n ≤ K.lo ∨ K.hi ≤ K.base
  ibl : M.ramStart ≤ K.ib
  ibh : K.ib + K.il ≤ M.ramEnd
  obl : M.ramStart ≤ K.ob
  obh : K.ob + K.ol ≤ M.ramEnd
  oc : K.ob + K.ol ≤ K.base ∨ K.base + n ≤ K.ob

/-- **the laws a target proves** (per instruction kind, against the generic `Rel`) -/
structure Laws : Prop where
  /-- the calling convention's registers, as J registers (a0..a3 = x10..x13, ra = x1, sp = x2) -/
  reg_map : T.reg 1 = T.M.mapping.returnAddress ∧ T.reg 2 = T.M.mapping.workTop ∧
    T.reg 10 = T.M.mapping.inputAddress ∧ T.reg 11 = T.M.mapping.inputLength ∧
    T.reg 12 = T.M.mapping.workAddress ∧ T.reg 13 = T.M.mapping.outputAddress ∧
    T.M.mapping.status = T.reg 10 ∧ T.M.mapping.outputLength = T.reg 11
  /-- every kept register is a J register Gen keeps (`keepR`, or s0 = x8), or one no block touches -/
  kept_map : ∀ r ∈ T.M.mapping.kept, (∃ j, 0 < j ∧ j < 32 ∧ T.reg j = r ∧ (Templates.keepR j = true ∨ j = 8)) ∨
    ((∀ j, 0 < j → j < 32 → T.reg j ≠ r) ∧ r ∉ T.scratch)
  /-- the RAM window lies in [2048, 2^32) -/
  ram : 2048 ≤ T.M.ramStart ∧ T.M.ramEnd ≤ 2 ^ 32
  /-- the generic layout conditions give the target's -/
  lay_init : ∀ (K : LayW) (C : List J), LayOK T.M (4 * T.blockLen * C.length) K → K.W = T.words C → T.lay K C
  /-- `m0` is what `observe` shows -/
  m0_obs : ∀ (s : T.M.State) a, a < 2 ^ 64 → (T.M.observe s).memory (UInt64.ofNat a) = (T.m0 s a).map UInt8.ofBitVec
  /-- the invariant holds at entry, for the entry memory -/
  inv_init : ∀ (K : LayW) (s : T.M.State), K.m0 = T.m0 s → T.inv K s
  /-- one safe J step is a machine run -/
  step_ok : ∀ {K : LayW} {C : List J} {s0 : T.M.State} {a b : Nat × CallProbe.St} {s : T.M.State},
    T.lay K C → T.Rel K C s0 a s → SafeX K C a → CallProbe.step C a = some b →
    ∃ s', Runs T.M s s' ∧ T.Rel K C s0 b s'
  /-- the return to the host: `jalr x0, 0(x1)` with any 4-aligned `x1` runs to pc = `x1`, keeping registers, memory
  and the configuration -/
  ret_ok : ∀ {K : LayW} {C : List J} {s0 : T.M.State} {pc : Nat} {st : CallProbe.St} {s : T.M.State},
    T.lay K C → T.Rel K C s0 (pc, st) s → C[pc]? = some (.jalr 0 1) → (st.x 1).toNat % 4 = 0 →
    ∃ s', Runs T.M s s' ∧ (T.M.observe s').programCounter = st.x 1 ∧
      (∀ r, (T.M.observe s').register r = (T.M.observe s).register r) ∧
      (T.M.observe s').memory = (T.M.observe s).memory ∧ T.M.configured s'

end JTarget

theorem Runs.trans {M : Machine} {a b c : M.State} (h1 : Runs M a b) (h2 : Runs M b c) : Runs M a c := by
  induction h1 with
  | stop => exact h2
  | step hs _ ih => exact .step hs (ih h2)

/-- **a safe J run is a machine run**, keeping `Rel` (proved once, for every target) -/
theorem sim_star {T : JTarget} (L : T.Laws) {K : LayW} {C : List J} (hl : T.lay K C) {s0 : T.M.State}
    {a b : Nat × CallProbe.St} (h : SStarX K C a b) : ∀ {s : T.M.State}, T.Rel K C s0 a s →
    ∃ s', Runs T.M s s' ∧ T.Rel K C s0 b s' := by
  induction h with
  | refl => exact fun hR => ⟨_, .stop, hR⟩
  | head hS hs _ ih =>
    intro s hR
    obtain ⟨s1, r1, R1⟩ := L.step_ok hl hR hS hs
    obtain ⟨s2, r2, R2⟩ := ih R1
    exact ⟨s2, Runs.trans r1 r2, R2⟩

end JT
