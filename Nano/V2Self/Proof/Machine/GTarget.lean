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
* `JTarget.toG`, `rel_toG`, `laws_toG`: every uniform target is a general one (RISC-V and rv2arm need nothing new). -/
import Nano.V2Self.Proof.Machine.HostGen
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

/-! ## every uniform target is a general one -/

/-- the image of a uniform target: its blocks' bytes, the uniform layout, every pc an anchor -/
def JTarget.uimg (T : JTarget) (C : List J) : Img := ⟨tbytes T C, CallProbe.LinkLay.lin (T.blockLen - 1), fun _ => True⟩

def JTarget.toG (T : JTarget) : GTarget where
  M := T.M
  reg := T.reg
  scratch := T.scratch
  lay K C I := I = T.uimg C ∧ T.lay K C
  m0 := T.m0
  inv K C _ s := T.inv K C s
  valid C I := I = T.uimg C ∧ T.valid C
  loader := T.loader

variable {T : JTarget}

/-- the uniform code relation (words of blocks) from the bytes -/
theorem ucode_of (L : T.Laws) {K : LayW} {C : List J} {o : MachineState}
    (h : ∀ a (h : a < (tbytes T C).length), o.memory (UInt64.ofNat (K.base + a)) = some (tbytes T C)[a]) :
    ∀ i (h : i < C.length) k (hk : k < (T.enc C[i]).length) b, b < 4 →
      o.memory (UInt64.ofNat (T.addr K.base i + 4 * k + b)) = some (wbyte (T.enc C[i])[k] b) := by
  intro i hi k hk b hb
  rw [L.enc_len] at hk
  have hlt : 4 * T.blockLen * i + 4 * k + b < (tbytes T C).length := by
    rw [tbytes_len L C]
    have := Nat.mul_le_mul_left (4 * T.blockLen) (show i + 1 ≤ C.length by omega)
    rw [Nat.mul_succ] at this; omega
  have e := tbytes_get L C i hi k hk b hb
  rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem (by rw [L.enc_len]; exact hk)] at e
  rw [JTarget.addr, show K.base + 4 * T.blockLen * i + 4 * k + b = K.base + (4 * T.blockLen * i + 4 * k + b) by omega,
    h _ hlt]
  exact e

/-- the bytes from the uniform code relation -/
theorem bytes_of (L : T.Laws) {K : LayW} {C : List J} {o : MachineState}
    (h : ∀ i (h : i < C.length) k (hk : k < (T.enc C[i]).length) b, b < 4 →
      o.memory (UInt64.ofNat (T.addr K.base i + 4 * k + b)) = some (wbyte (T.enc C[i])[k] b)) :
    ∀ a (h : a < (tbytes T C).length), o.memory (UInt64.ofNat (K.base + a)) = some (tbytes T C)[a] := by
  intro a ha
  have hp := L.blk_pos
  have hn := tbytes_len L C
  have hq : 0 < 4 * T.blockLen := by omega
  have hi : a / (4 * T.blockLen) < C.length := by
    rw [Nat.div_lt_iff_lt_mul hq, Nat.mul_comm]; omega
  have hr := Nat.mod_lt a hq
  have hk : a % (4 * T.blockLen) / 4 < T.blockLen := by rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
  have hb := Nat.mod_lt (a % (4 * T.blockLen)) (show 0 < 4 by decide)
  have ea : 4 * T.blockLen * (a / (4 * T.blockLen)) + 4 * (a % (4 * T.blockLen) / 4) + a % (4 * T.blockLen) % 4 = a := by
    have := Nat.div_add_mod a (4 * T.blockLen); have := Nat.div_add_mod (a % (4 * T.blockLen)) 4; omega
  have e := tbytes_get L C _ hi _ hk _ hb
  rw [ea, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem (by rw [L.enc_len]; exact hk)] at e
  have := h _ hi _ (by rw [L.enc_len]; exact hk) _ hb
  rw [JTarget.addr, show K.base + 4 * T.blockLen * (a / (4 * T.blockLen)) + 4 * (a % (4 * T.blockLen) / 4) +
    a % (4 * T.blockLen) % 4 = K.base + a by omega] at this
  rw [this]; exact e.symm

theorem uoff (L : T.Laws) (C : List J) (pc : Nat) : (T.uimg C).off pc = 4 * T.blockLen * pc := by
  have := L.blk_pos
  show 4 * (T.blockLen - 1 + 1) * pc = _; rw [show T.blockLen - 1 + 1 = T.blockLen by omega]

theorem rel_toG (L : T.Laws) {K : LayW} {C : List J} {s0 : T.M.State} {p : Nat × CallProbe.St} {s : T.M.State}
    (h : T.Rel K C s0 p s) : T.toG.Rel K C (T.uimg C) s0 p s where
  cfg := h.cfg
  pc := (h.pc : _ = UInt64.ofNat (T.addr K.base p.1)).trans (by rw [uoff L]; rfl)
  code := bytes_of L h.code
  x0 := h.x0
  bb := h.bb
  lk := h.ww
  x := h.x
  keep := h.keep
  w := h.w
  bw := h.bw
  fr := h.fr
  inv := h.inv

theorem rel_ofG (L : T.Laws) {K : LayW} {C : List J} {s0 : T.M.State} {p : Nat × CallProbe.St} {s : T.M.State}
    (h : T.toG.Rel K C (T.uimg C) s0 p s) : T.Rel K C s0 p s where
  cfg := h.cfg
  pc := (h.pc : (T.M.observe s).programCounter = _).trans (by rw [uoff L]; rfl)
  code := ucode_of L h.code
  x0 := h.x0
  bb := h.bb
  ww := h.lk
  x := h.x
  keep := h.keep
  w := h.w
  bw := h.bw
  fr := h.fr
  inv := h.inv

/-- **a uniform target's laws give the general laws** -/
theorem laws_toG (L : T.Laws) : T.toG.Laws where
  reg_map := L.reg_map
  kept_map := L.kept_map
  ram := L.ram
  lay_init K C I hK hv := by
    obtain ⟨rfl, hv⟩ := hv
    exact ⟨rfl, L.lay_init K C (by rw [← tbytes_len L C]; exact hK) hv⟩
  m0_obs := L.m0_obs
  inv_init K C I s call x sc hld hv hb hm0 hlo hhi hib hil hob hol := by
    obtain ⟨rfl, hv⟩ := hv
    exact L.inv_init K C s call _ x sc hld (tbytes_len L C) hb hm0 hlo hhi hib hil hob hol
  entry C I hv := by obtain ⟨rfl, -⟩ := hv; exact ⟨trivial, by rw [uoff L]; rfl⟩
  seg := by
    intro K C I s0 a z s n hl hR _ hrun _
    obtain ⟨rfl, hl⟩ := hl
    cases hrun with
    | head hS hs hrest =>
      obtain ⟨s', r, R⟩ := L.step_ok hl (rel_ofG L hR) hS hs
      exact ⟨0, _, s', Nat.zero_le _, hrest, trivial, r, rel_toG L R⟩
  addi_ok := by
    intro K C I s0 pc st s rd rs imm hl hR _ _ hc h1 h2 h3 h4
    obtain ⟨rfl, hl⟩ := hl
    obtain ⟨s', r, R⟩ := L.addi_ok hl (rel_ofG L hR) hc h1 h2 h3 h4
    exact ⟨s', r, rel_toG L R⟩
  ret_ok := by
    intro K C I s0 pc st s hl hR _ hc h4
    obtain ⟨rfl, hl⟩ := hl
    exact L.ret_ok hl (rel_ofG L hR) hc h4

end JT
