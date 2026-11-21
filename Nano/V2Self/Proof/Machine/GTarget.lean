/- The GENERAL machine adapter: `JTarget` (Target.lean) without the uniform-block assumptions, for targets whose code
is not one fixed-size block per J instruction (the native AArch64 generator `C/GenArm.lean`; later x86-64).
* `Img`: a program image, supplied per program by the target's `valid`: the machine code BYTES (no word size), the
  byte offset `off pc` of each J instruction (no `blockLen`), and the ANCHOR pcs `vis` (the J pcs at which the machine
  state is related to the J state; a fused template, e.g. `subs; b.cond` for `bgeu; jal`, has J pcs with no machine
  state of their own).
* `GTarget.Rel`: `JTarget.Rel` with the pc through `off`, the code as bytes, and the J link layout = the image's (`lk`).
* `GTarget.Laws.seg`: the SEGMENT law, replacing the one-step `step_ok`: from an anchor, along a safe J run that ends
  at an anchor, the machine runs to a later anchor of that run.  Instruction width and branch reach are the
  target's business (`lay` / `valid`); nothing here mentions them.
* `gsim`: a safe J run between anchors is a machine run (proved once).
* `JTarget.toG`, `rel_toG`, `laws_toG` (GUniform.lean): every uniform target is a general one (RISC-V and rv2arm need
  nothing new).  The host lift (`Host*.lean`) and the top theorems (Main/TopOn.lean) are proved over `GTarget` only. -/
import Nano.V2Self.Proof.Machine.Target
namespace JT
open Proven.Top SimW CallProbe

/-! ## safe J runs with their length -/

/-- a safe J run of exactly `n` steps -/
inductive SRunN (K : LayW) (C : List J) : Nat → Nat × CallProbe.St → Nat × CallProbe.St → Prop
  | refl (a) : SRunN K C 0 a a
  | head {n a b c} : SafeX K C a → CallProbe.step C a = some b → SRunN K C n b c → SRunN K C (n + 1) a c

theorem sstar_toN {K : LayW} {C : List J} {a b : Nat × CallProbe.St} (h : SStarX K C a b) : ∃ n, SRunN K C n a b := by
  induction h with
  | refl => exact ⟨0, .refl _⟩
  | head hS hs _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .head hS hs hn⟩

theorem SRunN.toStar {K : LayW} {C : List J} {n : Nat} {a b : Nat × CallProbe.St} (h : SRunN K C n a b) :
    SStarX K C a b := by
  induction h with
  | refl => exact .refl _
  | head hS hs _ ih => exact .head hS hs ih

/-! ## the general target -/

/-- a program image: code bytes, the layout (`ly.off pc` = byte offset of J instruction `pc`; it is also the J state's
link layout, so a return address is the byte address of its J index), anchor pcs -/
structure Img where
  code : List UInt8
  ly : CallProbe.LinkLay
  vis : Nat → Prop

/-- the byte offset of J instruction `pc` -/
def Img.off (I : Img) (pc : Nat) : Nat := I.ly.off pc

structure GTarget where
  M : Machine
  /-- J register ↦ machine register number (in `M.observe`) -/
  reg : Nat → Nat
  /-- machine registers the code may clobber -/
  scratch : List Nat
  /-- the target's side condition on a layout, program and image (ranges, window, branch reach) -/
  lay : LayW → List J → Img → Prop
  /-- the entry memory as bytes -/
  m0 : M.State → Nat → Option (BitVec 8)
  /-- a target-private invariant kept along `Rel` -/
  inv : LayW → List J → Img → M.State → Prop
  /-- `I` is a faithful image of the J program (the target's code generator / translator relation) -/
  valid : List J → Img → Prop
  /-- the loader contract on a start state beyond `StartCorrect` -/
  loader : M.State → Call → List UInt8 → List UInt8 → Prop

namespace GTarget
variable (T : GTarget)

/-- **the J ↔ machine relation**, required at anchor pcs only -/
structure Rel (K : LayW) (C : List J) (I : Img) (s0 : T.M.State) (p : Nat × CallProbe.St) (s : T.M.State) : Prop where
  cfg : T.M.configured s
  pc : (T.M.observe s).programCounter = UInt64.ofNat (K.base + I.off p.1)
  code : ∀ a (h : a < I.code.length), (T.M.observe s).memory (UInt64.ofNat (K.base + a)) = some I.code[a]
  x0 : p.2.x 0 = 0
  bb : p.2.b = K.base
  lk : p.2.ly = I.ly
  x : ∀ j, 0 < j → j < 32 → (T.M.observe s).register (T.reg j) = p.2.x j
  keep : ∀ r, (∀ j, 0 < j → j < 32 → T.reg j ≠ r) → r ∉ T.scratch →
    (T.M.observe s).register r = (T.M.observe s0).register r
  w : ∀ a, wok K a → ∀ k < 8, (T.M.observe s).memory (UInt64.ofNat (a + k)) = some (cbyte (p.2.m a) k)
  bw : ∀ a, io K a → (T.M.observe s).memory (UInt64.ofNat a) = some (cbyte (p.2.m (a - a % 8)) (a % 8))
  fr : ∀ a, a < 2 ^ 64 → ¬ wok K (a - a % 8) → ¬ outB K a →
    (T.M.observe s).memory (UInt64.ofNat a) = (K.m0 a).map UInt8.ofBitVec
  inv : T.inv K C I s

/-- **the laws a general target proves** -/
structure Laws : Prop where
  reg_map : T.reg 1 = T.M.mapping.returnAddress ∧ T.reg 2 = T.M.mapping.workTop ∧
    T.reg 10 = T.M.mapping.inputAddress ∧ T.reg 11 = T.M.mapping.inputLength ∧
    T.reg 12 = T.M.mapping.workAddress ∧ T.reg 13 = T.M.mapping.outputAddress ∧
    T.M.mapping.status = T.reg 10 ∧ T.M.mapping.outputLength = T.reg 11
  kept_map : ∀ r ∈ T.M.mapping.kept, (∃ j, 0 < j ∧ j < 32 ∧ T.reg j = r ∧ (Templates.keepR j = true ∨ j = 8)) ∨
    ((∀ j, 0 < j → j < 32 → T.reg j ≠ r) ∧ r ∉ T.scratch)
  ram : 2048 ≤ T.M.ramStart ∧ T.M.ramEnd ≤ 2 ^ 32
  /-- the generic layout conditions (with the image's code size) give the target's -/
  lay_init : ∀ (K : LayW) (C : List J) (I : Img), JTarget.LayOK T.M I.code.length K → T.valid C I → T.lay K C I
  m0_obs : ∀ (s : T.M.State) a, a < 2 ^ 64 → (T.M.observe s).memory (UInt64.ofNat a) = (T.m0 s a).map UInt8.ofBitVec
  inv_init : ∀ (K : LayW) (C : List J) (I : Img) (s : T.M.State) (call : Call) (x : List UInt8),
    StartCorrect T.M s call I.code x → T.loader s call I.code x → T.valid C I →
    K.base = (T.M.observe s).programCounter.toNat → K.m0 = T.m0 s →
    K.lo = call.workAddress.toNat → K.hi ≤ call.workAddress.toNat + call.workLength →
    K.ib = call.inputAddress.toNat → K.il = x.length → K.ob = call.outputAddress.toNat → K.ol ≤ call.outputLength →
    T.inv K C I s
  /-- the entry is an anchor at offset 0 -/
  entry : ∀ (C : List J) (I : Img), T.valid C I → I.vis 0 ∧ I.off 0 = 0
  /-- every J instruction's offset lies in the code (return addresses do not wrap: gives `LinkOK`) -/
  off_le : ∀ (C : List J) (I : Img), T.valid C I → ∀ n, n ≤ C.length → I.off n ≤ I.code.length
  /-- every `jalr x0, 0(x1)` (return to the host, function return) is an anchor -/
  vis_ret : ∀ (C : List J) (I : Img) (pc : Nat), T.valid C I → C[pc]? = some (.jalr 0 1) → I.vis pc
  /-- the error-status pair `addi a0, x0, imm; addi a1, x0, 0` and its successor are anchors (stubs, start check) -/
  vis_err : ∀ (C : List J) (I : Img) (pc : Nat) (imm : Int), T.valid C I → C[pc]? = some (.addi 10 0 imm) →
    C[pc + 1]? = some (.addi 11 0 0) → I.vis pc ∧ I.vis (pc + 1) ∧ I.vis (pc + 2)
  /-- **the segment law**: from an anchor `a`, along a safe J run of `n + 1` steps that ends at an anchor `z`, the
  machine runs to an anchor `c` of that run, `m + 1` steps in -/
  seg : ∀ {K : LayW} {C : List J} {I : Img} {s0 : T.M.State} {a z : Nat × CallProbe.St} {s : T.M.State} {n : Nat},
    T.lay K C I → T.Rel K C I s0 a s → I.vis a.1 → SRunN K C (n + 1) a z → I.vis z.1 →
    ∃ m c s', m ≤ n ∧ SRunN K C (n - m) c z ∧ I.vis c.1 ∧ Runs T.M s s' ∧ T.Rel K C I s0 c s'
  /-- addi with the machine's (wrapping) sum, between anchors (the stubs' a0 = −1 / −2) -/
  addi_ok : ∀ {K : LayW} {C : List J} {I : Img} {s0 : T.M.State} {pc : Nat} {st : CallProbe.St} {s : T.M.State}
    {rd rs : Nat} {imm : Int}, T.lay K C I → T.Rel K C I s0 (pc, st) s → I.vis pc → I.vis (pc + 1) →
    C[pc]? = some (.addi rd rs imm) → rd < 32 → rs < 32 → -2048 ≤ imm → imm < 2048 →
    ∃ s', Runs T.M s s' ∧ T.Rel K C I s0 (pc + 1, CallProbe.wr st rd (st.x rs + UInt64.ofInt imm)) s'
  /-- the return to the host, from an anchor -/
  ret_ok : ∀ {K : LayW} {C : List J} {I : Img} {s0 : T.M.State} {pc : Nat} {st : CallProbe.St} {s : T.M.State},
    T.lay K C I → T.Rel K C I s0 (pc, st) s → I.vis pc → C[pc]? = some (.jalr 0 1) → (st.x 1).toNat % 4 = 0 →
    ∃ s', Runs T.M s s' ∧ (T.M.observe s').programCounter = st.x 1 ∧
      (∀ r, (T.M.observe s').register r = (T.M.observe s).register r) ∧
      (T.M.observe s').memory = (T.M.observe s).memory ∧ T.M.configured s'

end GTarget

/-- **a safe J run between anchors is a machine run**, keeping `Rel` (proved once, for every general target) -/
theorem gsimN {T : GTarget} (L : T.Laws) {K : LayW} {C : List J} {I : Img} (hl : T.lay K C I) {s0 : T.M.State}
    {z : Nat × CallProbe.St} (hz : I.vis z.1) : ∀ (N n : Nat) {a : Nat × CallProbe.St} {s : T.M.State}, n ≤ N →
    SRunN K C n a z → I.vis a.1 → T.Rel K C I s0 a s → ∃ s', Runs T.M s s' ∧ T.Rel K C I s0 z s'
  | _, 0, _, _, _, h, _, hR => by cases h; exact ⟨_, .stop, hR⟩
  | 0, n + 1, _, _, hn, _, _, _ => absurd hn (by omega)
  | N + 1, n + 1, _, _, hn, h, ha, hR => by
    obtain ⟨m, c, s1, hm, hc, vc, r1, R1⟩ := L.seg hl hR ha h hz
    obtain ⟨s2, r2, R2⟩ := gsimN L hl hz N (n - m) (by omega) hc vc R1
    exact ⟨s2, Runs.trans r1 r2, R2⟩

theorem gsim {T : GTarget} (L : T.Laws) {K : LayW} {C : List J} {I : Img} (hl : T.lay K C I) {s0 : T.M.State}
    {a z : Nat × CallProbe.St} (h : SStarX K C a z) (ha : I.vis a.1) (hz : I.vis z.1) {s : T.M.State}
    (hR : T.Rel K C I s0 a s) : ∃ s', Runs T.M s s' ∧ T.Rel K C I s0 z s' := by
  obtain ⟨n, hn⟩ := sstar_toN h
  exact gsimN L hl hz n n (Nat.le_refl _) hn ha hR

end JT
