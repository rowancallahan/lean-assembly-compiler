-- Nano v2 proof templates, Astra round 6 (E: compiled loop with label/layout layer; F: multi-buffer ownership + append;
-- G: non-tail recursion -> explicit work stack). VERIFIED on Lean 4.29.0 by the main session 2026-11-17: no errors,
-- axioms ⊆ {propext, Classical.choice, Quot.sound}. Standalone (import Lean); redeclares the round-5 NanoProofs names,
-- so do NOT import it together with NANO_V2_SKELETONS.lean. Explanations: Testing/notes/NANO_V2_ROUND6.md.
import Lean

namespace NanoProofs

-- A. Abstract machine loop.
namespace Loops

inductive Star {M : Type} (Step : M → M → Prop) : M → M → Prop where
  | refl (m : M) : Star Step m m
  | tail {a b c : M} : Step a b → Star Step b c → Star Step a c

namespace Star

theorem trans {M : Type} {Step : M → M → Prop} {a b c : M}
    (hab : Star Step a b) (hbc : Star Step b c) : Star Step a c := by
  induction hab with
  | refl => exact hbc
  | tail h _ ih => exact .tail h (ih hbc)

end Star

inductive Action (S R : Type) where
  | continue (s : S)
  | exit (r : R)

def loopSpec {S R : Type} (zeroResult : S → R) (body : Nat → S → Action S R)
    (fuel : Nat) (s : S) : R :=
  match fuel with
  | 0 => zeroResult s
  | n + 1 =>
    match body n s with
    | .continue s' => loopSpec zeroResult body n s'
    | .exit r => r
termination_by structural fuel

theorem loop_correct {S R M : Type}
    (Step : M → M → Prop)
    (zeroResult : S → R) (body : Nat → S → Action S R)
    (H BodyEntry : Nat → S → M → Prop)
    (ContinueAt : Nat → S → M → Prop)
    (Exit : R → M → Prop)
    (header_zero : ∀ s m, H 0 s m →
      ∃ m', Star Step m m' ∧ Exit (zeroResult s) m')
    (header_nonzero : ∀ n s m, H (n+1) s m →
      ∃ m', Star Step m m' ∧ BodyEntry n s m')
    (body_correct : ∀ n s m, BodyEntry n s m →
      ∃ m', Star Step m m' ∧
        match body n s with
        | .continue s' => ContinueAt n s' m'
        | .exit r => Exit r m')
    (update_backedge : ∀ n s m, ContinueAt n s m →
      ∃ m', Star Step m m' ∧ H n s m') :
    ∀ n s m, H n s m →
      ∃ m', Star Step m m' ∧ Exit (loopSpec zeroResult body n s) m' := by
  intro n
  induction n with
  | zero =>
    intro s m hm
    exact header_zero s m hm
  | succ n ih =>
    intro s m hm
    obtain ⟨m1, h01, hentry⟩ := header_nonzero n s m hm
    obtain ⟨m2, h12, hbody⟩ := body_correct n s m1 hentry
    cases hb : body n s with
    | exit r =>
      have hexit : Exit r m2 := by simpa only [hb] using hbody
      refine ⟨m2, Star.trans h01 h12, ?_⟩
      simpa only [loopSpec, hb] using hexit
    | «continue» s' =>
      have hcont : ContinueAt n s' m2 := by simpa only [hb] using hbody
      obtain ⟨m3, h23, hhead⟩ := update_backedge n s' m2 hcont
      obtain ⟨m4, h34, hresult⟩ := ih s' m3 hhead
      refine ⟨m4, Star.trans h01 (Star.trans h12 (Star.trans h23 h34)), ?_⟩
      simpa only [loopSpec, hb] using hresult

end Loops

-- B. Word-cell memory; Nat addresses are byte offsets.
namespace Buffers

abbrev Mem := Nat → UInt64
abbrev Footprint := Nat → Prop

structure Desc where
  base : Nat  -- address of the len header
  cap : Nat
  len : Nat

def dataBase (d : Desc) : Nat := d.base + 16

def footprint (d : Desc) : Footprint :=
  fun p => d.base ≤ p ∧ p < dataBase d + 8 * d.cap

def Disjoint (F G : Footprint) : Prop :=
  ∀ p, F p → G p → False

def SameOutside (F : Footprint) (m m' : Mem) : Prop :=
  ∀ p, ¬ F p → m' p = m p

def update (m : Mem) (p : Nat) (v : UInt64) : Mem :=
  fun q => if q = p then v else m q

structure BufferRep (a : Array UInt64) (d : Desc) (m : Mem) : Prop where
  size_eq : a.size = d.len
  len_le_cap : d.len ≤ d.cap
  cap_lt : d.cap < 2^64
  aligned : d.base % 8 = 0
  header_len : m d.base = UInt64.ofNat d.len
  header_cap : m (d.base + 8) = UInt64.ofNat d.cap
  elems : ∀ i (hi : i < a.size), m (dataBase d + 8*i) = a[i]

theorem update_sameOutside (m : Mem) (F : Footprint) (p : Nat) (v : UInt64)
    (hp : F p) : SameOutside F m (update m p v) := by
  intro q hq
  have hne : q ≠ p := by
    intro h; subst q; exact hq hp
  simp [update, hne]

theorem buffer_set (a : Array UInt64) (d : Desc) (m : Mem)
    (i : Nat) (v : UInt64) (hr : BufferRep a d m) (hi : i < a.size) :
    BufferRep (a.set i v hi) d (update m (dataBase d + 8*i) v) ∧
    SameOutside (footprint d) m (update m (dataBase d + 8*i) v) := by
  have hicap : i < d.cap := by have := hr.size_eq; have := hr.len_le_cap; omega
  have hp : footprint d (dataBase d + 8*i) := by
    simp only [footprint, dataBase]
    constructor <;> omega
  constructor
  · refine ⟨?_, hr.len_le_cap, hr.cap_lt, hr.aligned, ?_, ?_, ?_⟩
    · simpa only [Array.size_set] using hr.size_eq
    · have hne : d.base ≠ dataBase d + 8*i := by simp only [dataBase]; omega
      simpa only [update, if_neg hne] using hr.header_len
    · have hne : d.base + 8 ≠ dataBase d + 8*i := by simp only [dataBase]; omega
      simpa only [update, if_neg hne] using hr.header_cap
    · intro j hj
      have hjold : j < a.size := by simpa only [Array.size_set] using hj
      by_cases hij : i = j
      · subst j
        simp [update, Array.getElem_set]
      · have haddr : dataBase d + 8*j ≠ dataBase d + 8*i := by omega
        simp only [update, if_neg haddr, Array.getElem_set, if_neg hij]
        exact hr.elems j hjold
  · exact update_sameOutside m (footprint d) _ v hp

theorem buffer_frame (b : Array UInt64) (d' : Desc) (m m' : Mem)
    (F : Footprint) (hr : BufferRep b d' m)
    (hd : Disjoint F (footprint d')) (hs : SameOutside F m m') :
    BufferRep b d' m' := by
  have preserve : ∀ p, footprint d' p → m' p = m p := by
    intro p hp
    exact hs p (fun hf => hd p hf hp)
  refine ⟨hr.size_eq, hr.len_le_cap, hr.cap_lt, hr.aligned, ?_, ?_, ?_⟩
  · rw [preserve d'.base (by simp only [footprint, dataBase]; constructor <;> omega)]
    exact hr.header_len
  · rw [preserve (d'.base + 8) (by simp only [footprint, dataBase]; constructor <;> omega)]
    exact hr.header_cap
  · intro i hi
    have hicap : i < d'.cap := by have := hr.size_eq; have := hr.len_le_cap; omega
    rw [preserve (dataBase d' + 8*i) (by simp only [footprint, dataBase]; constructor <;> omega)]
    exact hr.elems i hi

end Buffers


end NanoProofs

namespace Round6
namespace Machine
open NanoProofs.Loops

abbrev Reg := Fin 32
structure State where
  pc : Nat
  regs : Reg → UInt64
  mem : Nat → UInt64

def read (m : State) (r : Reg) : UInt64 := if r = 0 then 0 else m.regs r

def write (m : State) (r : Reg) (v : UInt64) : State :=
  { m with regs := fun q => if q = 0 then 0 else if q = r then v else m.regs q }

@[simp] theorem read_zero (m : State) : read m 0 = 0 := by simp [read]
@[simp] theorem read_write_same (m : State) (r : Reg) (v : UInt64) (hr : r ≠ 0) :
    read (write m r v) r = v := by simp [read, write, hr]

def addImm (v : UInt64) (imm : Int) : UInt64 :=
  if 0 ≤ imm then v + UInt64.ofNat imm.toNat else v - UInt64.ofNat (-imm).toNat
@[simp] theorem addImm_neg_one (v : UInt64) : addImm v (-1) = v - 1 := rfl

inductive Instr where
  | addi (rd rs : Reg) (imm : Int)
  | beq (r1 r2 : Reg) (off : Int)
  | bne (r1 r2 : Reg) (off : Int)
  | jal (off : Int) -- only jal x0

def jump (lo hi : Int) (off : Int) (m : State) : Option State :=
  if off % 4 = 0 ∧ lo ≤ off ∧ off ≤ hi ∧ 0 ≤ (m.pc : Int) + off then
    some {m with pc := ((m.pc : Int) + off).toNat}
  else none

def exec : Instr → State → Option State
  | .addi rd rs imm, m => some {write m rd (addImm (read m rs) imm) with pc := m.pc + 4}
  | .beq r1 r2 off, m => if read m r1 = read m r2 then jump (-4096) 4094 off m
      else some {m with pc := m.pc + 4}
  | .bne r1 r2 off, m => if read m r1 ≠ read m r2 then jump (-4096) 4094 off m
      else some {m with pc := m.pc + 4}
  | .jal off, m => jump (-1048576) 1048574 off m

def step (code : Array Instr) (m : State) : Option State :=
  if m.pc % 4 = 0 then
    match code[m.pc / 4]? with
    | none => none
    | some i => exec i m
  else none

def Step (code : Array Instr) (m m' : State) : Prop := step code m = some m'

theorem step_deterministic (code : Array Instr) (m a b : State)
    (ha : Step code m a) (hb : Step code m b) : a = b := by
  exact Option.some.inj (ha.symm.trans hb)

structure CodeAt (code : Array Instr) (pc : Nat) (i : Instr) : Prop where
  aligned : pc % 4 = 0
  fetch : code[pc / 4]? = some i

structure JumpCert (lo hi : Int) (src dst : Nat) (off : Int) : Prop where
  off_aligned : off % 4 = 0
  lower : lo ≤ off
  upper : off ≤ hi
  target : (src : Int) + off = (dst : Int)
  dst_aligned : dst % 4 = 0

theorem cert_of_labels (lo hi : Int) (src dst : Nat)
    (hs : src % 4 = 0) (hd : dst % 4 = 0)
    (hl : lo ≤ (dst : Int) - (src : Int))
    (hu : (dst : Int) - (src : Int) ≤ hi) :
    JumpCert lo hi src dst ((dst : Int) - (src : Int)) := by
  exact ⟨by omega, hl, hu, by omega, hd⟩

theorem step_at (code : Array Instr) (m m' : State) (pc : Nat) (i : Instr)
    (atCode : CodeAt code pc i) (hpc : m.pc = pc) (he : exec i m = some m') :
    Step code m m' := by
  simpa [Step, step, hpc, atCode.aligned, atCode.fetch] using he

theorem jump_target (lo hi off : Int) (m : State) (src dst : Nat)
    (cert : JumpCert lo hi src dst off) (hpc : m.pc = src) :
    jump lo hi off m = some {m with pc := dst} := by
  have ht : (m.pc : Int) + off = (dst : Int) := by rw [hpc]; exact cert.target
  have hn : 0 ≤ (m.pc : Int) + off := by rw [ht]; omega
  unfold jump
  rw [if_pos ⟨cert.off_aligned, cert.lower, cert.upper, hn⟩, ht]
  rfl

theorem beq_to_label (code : Array Instr) (m : State) (src dst : Nat)
    (r1 r2 : Reg) (off : Int)
    (atCode : CodeAt code src (.beq r1 r2 off))
    (cert : JumpCert (-4096) 4094 src dst off)
    (hpc : m.pc = src) (heq : read m r1 = read m r2) :
    Step code m {m with pc := dst} := by
  apply step_at code m _ src _ atCode hpc
  simp only [exec, if_pos heq]
  exact jump_target _ _ _ _ _ _ cert hpc

theorem beq_fallthrough (code : Array Instr) (m : State) (src : Nat)
    (r1 r2 : Reg) (off : Int) (atCode : CodeAt code src (.beq r1 r2 off))
    (hpc : m.pc = src) (hne : read m r1 ≠ read m r2) :
    Step code m {m with pc := src + 4} := by
  apply step_at code m _ src _ atCode hpc
  simp [exec, hne, hpc]

theorem jal_to_label (code : Array Instr) (m : State) (src dst : Nat) (off : Int)
    (atCode : CodeAt code src (.jal off))
    (cert : JumpCert (-1048576) 1048574 src dst off) (hpc : m.pc = src) :
    Step code m {m with pc := dst} := by
  apply step_at code m _ src _ atCode hpc
  exact jump_target _ _ _ _ _ _ cert hpc

theorem addi_step (code : Array Instr) (m : State) (src : Nat)
    (rd rs : Reg) (imm : Int) (atCode : CodeAt code src (.addi rd rs imm))
    (hpc : m.pc = src) :
    Step code m {write m rd (addImm (read m rs) imm) with pc := src + 4} := by
  apply step_at code m _ src _ atCode hpc
  simp only [exec, hpc]

def word (n : Nat) : UInt64 := UInt64.ofNat n

theorem word_toNat (n : Nat) (hn : n < 2^64) : (word n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' hn

theorem word_ne_zero (n : Nat) (hp : 0 < n) (hn : n < 2^64) : word n ≠ 0 := by
  intro he
  have h := congrArg UInt64.toNat he
  rw [word_toNat n hn] at h
  change n = 0 at h
  omega

theorem word_pred (n : Nat) (hp : 0 < n) (hn : n < 2^64) : word n - 1 = word (n-1) := by
  apply UInt64.toNat.inj
  have hle : (1 : UInt64) ≤ word n := by
    rw [UInt64.le_iff_toNat_le, word_toNat n hn]
    change 1 ≤ n
    omega
  rw [UInt64.toNat_sub_of_le _ _ hle, word_toNat n hn,
      word_toNat (n-1) (by omega)]
  rfl

structure Layout (code : Array Instr) where
  header : Nat
  bodyPC : Nat
  updatePC : Nat
  backedge : Nat
  exitPC : Nat
  fuelReg : Reg
  fuel_nonzero : fuelReg ≠ 0
  exitOff : Int
  backOff : Int
  body_next : bodyPC = header + 4
  back_next : backedge = updatePC + 4
  headerCode : CodeAt code header (.beq fuelReg 0 exitOff)
  updateCode : CodeAt code updatePC (.addi fuelReg fuelReg (-1))
  backCode : CodeAt code backedge (.jal backOff)
  exitCert : JumpCert (-4096) 4094 header exitPC exitOff
  backCert : JumpCert (-1048576) 1048574 backedge header backOff

-- P abstracts payload ownership/data; it ignores pc and the fuel register.
structure PayloadLaws {S : Type} (P : S → State → Prop) (fr : Reg) : Prop where
  pc : ∀ s m p, P s m → P s {m with pc := p}
  fuel : ∀ s m v, P s m → P s (write m fr v)

def H {S : Type} {code : Array Instr} (L : Layout code) (P : S → State → Prop)
    (n : Nat) (s : S) (m : State) : Prop :=
  m.pc = L.header ∧ read m L.fuelReg = word n ∧ n < 2^64 ∧ P s m

def BodyEntry {S : Type} {code : Array Instr} (L : Layout code) (P : S → State → Prop)
    (n : Nat) (s : S) (m : State) : Prop :=
  m.pc = L.bodyPC ∧ read m L.fuelReg = word (n+1) ∧ n+1 < 2^64 ∧ P s m

def ContinueAt {S : Type} {code : Array Instr} (L : Layout code) (P : S → State → Prop)
    (n : Nat) (s : S) (m : State) : Prop :=
  m.pc = L.updatePC ∧ read m L.fuelReg = word (n+1) ∧ n+1 < 2^64 ∧ P s m

theorem header_zero {S R : Type} {code : Array Instr} (L : Layout code)
    (P : S → State → Prop) (Exit : R → State → Prop) (zeroResult : S → R)
    (zero_exit : ∀ s m, P s m → Exit (zeroResult s) {m with pc := L.exitPC})
    (s : S) (m : State) (hm : H L P 0 s m) :
    ∃ m', Star (Step code) m m' ∧ Exit (zeroResult s) m' := by
  obtain ⟨hpc, hf, _, hp⟩ := hm
  refine ⟨{m with pc := L.exitPC}, ?_, zero_exit s m hp⟩
  exact .tail (beq_to_label code m _ _ _ _ _ L.headerCode L.exitCert hpc
    (by simpa [word] using hf)) (.refl _)

theorem header_nonzero {S : Type} {code : Array Instr} (L : Layout code)
    (P : S → State → Prop) (laws : PayloadLaws P L.fuelReg)
    (n : Nat) (s : S) (m : State) (hm : H L P (n+1) s m) :
    ∃ m', Star (Step code) m m' ∧ BodyEntry L P n s m' := by
  obtain ⟨hpc, hf, hn, hp⟩ := hm
  have hne : read m L.fuelReg ≠ read m 0 := by
    rw [read_zero, hf]
    exact word_ne_zero (n+1) (by omega) hn
  refine ⟨{m with pc := L.header+4}, .tail
    (beq_fallthrough code m _ _ _ _ L.headerCode hpc hne) (.refl _), ?_⟩
  exact ⟨L.body_next.symm, hf, hn, laws.pc s m _ hp⟩

theorem update_backedge {S : Type} {code : Array Instr} (L : Layout code)
    (P : S → State → Prop) (laws : PayloadLaws P L.fuelReg)
    (n : Nat) (s : S) (m : State) (hm : ContinueAt L P n s m) :
    ∃ m', Star (Step code) m m' ∧ H L P n s m' := by
  obtain ⟨hpc, hf, hn, hp⟩ := hm
  have hpred : word (n+1) - 1 = word n := by
    simpa using word_pred (n+1) (by omega) hn
  let m1 : State := {write m L.fuelReg (word n) with pc := L.backedge}
  have hs1 : Step code m m1 := by
    have hs := addi_step code m _ _ _ _ L.updateCode hpc
    simpa [m1, addImm_neg_one, hf, hpred, L.back_next] using hs
  have hs2 : Step code m1 {m1 with pc := L.header} :=
    jal_to_label code m1 _ _ _ L.backCode L.backCert rfl
  refine ⟨{m1 with pc := L.header}, .tail hs1 (.tail hs2 (.refl _)), rfl, ?_, ?_, ?_⟩
  · change read (write m L.fuelReg (word n)) L.fuelReg = word n
    exact read_write_same _ _ _ L.fuel_nonzero
  · omega
  · exact laws.pc s m1 _ (laws.pc s (write m L.fuelReg (word n)) _ (laws.fuel s m _ hp))

theorem compiled_loop_correct {S R : Type} {code : Array Instr} (L : Layout code)
    (P : S → State → Prop) (laws : PayloadLaws P L.fuelReg)
    (zeroResult : S → R) (body : Nat → S → Action S R) (Exit : R → State → Prop)
    (zero_exit : ∀ s m, P s m → Exit (zeroResult s) {m with pc := L.exitPC})
    (body_correct : ∀ n s m, BodyEntry L P n s m →
      ∃ m', Star (Step code) m m' ∧
        match body n s with
        | .continue s' => ContinueAt L P n s' m'
        | .exit r => Exit r m')
    (n : Nat) (s : S) (m : State) (hm : H L P n s m) :
    ∃ m', Star (Step code) m m' ∧ Exit (loopSpec zeroResult body n s) m' := by
  exact loop_correct (Step code) zeroResult body (H L P) (BodyEntry L P)
    (ContinueAt L P) Exit (header_zero L P Exit zeroResult zero_exit)
    (header_nonzero L P laws) body_correct (update_backedge L P laws) n s m hm

end Machine
end Round6

namespace Round6
-- Local replacement: Function.update is not exported by import Lean on 4.35.
namespace Function

def update {α β : Type} [DecidableEq α] (f : α → β) (i : α) (v : β) : α → β :=
  fun j => if j = i then v else f j
@[simp] theorem update_same {α β : Type} [DecidableEq α] (f : α → β) (i : α) (v : β) :
    update f i v i = v := by simp [update]
@[simp] theorem update_other {α β : Type} [DecidableEq α] (f : α → β) (i j : α) (v : β)
    (h : j ≠ i) : update f i v j = f j := by simp [update, h]
end Function

namespace MultiBuffer
open NanoProofs.Buffers

theorem sameOutside_trans (F : Footprint) (m m1 m2 : Mem)
    (h1 : SameOutside F m m1) (h2 : SameOutside F m1 m2) : SameOutside F m m2 := by
  intro p hp
  exact (h2 p hp).trans (h1 p hp)

def appendMem (a : Array UInt64) (d : Desc) (m : Mem) (v : UInt64) : Mem :=
  update (update m (dataBase d + 8*a.size) v) d.base (UInt64.ofNat (d.len+1))

theorem buffer_push (a : Array UInt64) (d : Desc) (m : Mem) (v : UInt64)
    (hr : BufferRep a d m) (hcap : a.size < d.cap) :
    BufferRep (a.push v) {d with len := d.len+1} (appendMem a d m v) ∧
    SameOutside (footprint d) m (appendMem a d m v) := by
  have hheader : footprint d d.base := by
    simp only [footprint, dataBase]
    constructor <;> omega
  have hdata : footprint d (dataBase d + 8*a.size) := by
    simp only [footprint, dataBase]
    constructor <;> omega
  constructor
  · refine ⟨?_, ?_, hr.cap_lt, hr.aligned, ?_, ?_, ?_⟩
    · simpa only [Array.size_push] using congrArg (fun n => n+1) hr.size_eq
    · change d.len + 1 ≤ d.cap
      have := hr.size_eq; omega
    · simp [appendMem, update]
    · have h1 : d.base + 8 ≠ d.base := by omega
      have h2 : d.base + 8 ≠ dataBase d + 8*a.size := by simp only [dataBase]; omega
      simpa only [appendMem, update, if_neg h1, if_neg h2] using hr.header_cap
    · intro j hj
      have hjbound : j < a.size+1 := by simpa only [Array.size_push] using hj
      have hhead : dataBase d + 8*j ≠ d.base := by simp only [dataBase]; omega
      change (appendMem a d m v) (dataBase d + 8*j) = (a.push v)[j]
      by_cases hold : j < a.size
      · have hne : dataBase d + 8*j ≠ dataBase d + 8*a.size := by omega
        rw [Array.getElem_push_lt hold]
        simp only [appendMem, update, if_neg hhead, if_neg hne]
        exact hr.elems j hold
      · have heq : j = a.size := by omega
        subst j
        simp [appendMem, update, hhead]
  · exact sameOutside_trans (footprint d) m _ _
      (update_sameOutside m (footprint d) _ v hdata)
      (update_sameOutside _ (footprint d) d.base _ hheader)

def Owned {k : Nat} (own : Fin k → Desc) : Prop :=
  ∀ i j, i ≠ j → Disjoint (footprint (own i)) (footprint (own j))

def EnvRep {k : Nat} (env : Fin k → Array UInt64) (own : Fin k → Desc) (m : Mem) : Prop :=
  ∀ j, BufferRep (env j) (own j) m

theorem env_update {k : Nat} (env : Fin k → Array UInt64) (own : Fin k → Desc)
    (m m' : Mem) (i : Fin k) (a' : Array UInt64) (d' : Desc)
    (ho : Owned own) (hr : EnvRep env own m)
    (localRep : BufferRep a' d' m')
    (frame : SameOutside (footprint (own i)) m m')
    (sameFootprint : footprint d' = footprint (own i)) :
    EnvRep (Function.update env i a') (Function.update own i d') m' ∧
    Owned (Function.update own i d') := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j
      simpa only [Function.update_same] using localRep
    · simp only [Function.update_other _ _ _ _ h]
      exact buffer_frame (env j) (own j) m m' (footprint (own i)) (hr j)
        (ho i j (Ne.symm h)) frame
  · have hf : ∀ j, footprint (Function.update own i d' j) = footprint (own j) := by
      intro j
      by_cases h : j = i
      · subst j; simpa only [Function.update_same] using sameFootprint
      · rw [Function.update_other own i j d' h]
    intro j l hjl
    change Disjoint (footprint (Function.update own i d' j))
      (footprint (Function.update own i d' l))
    rw [hf j, hf l]
    exact ho j l hjl

theorem env_set {k : Nat} (env : Fin k → Array UInt64) (own : Fin k → Desc)
    (m : Mem) (i : Fin k) (j : Nat) (v : UInt64)
    (ho : Owned own) (hr : EnvRep env own m) (hj : j < (env i).size) :
    EnvRep (Function.update env i ((env i).set j v hj)) own
      (update m (dataBase (own i) + 8*j) v) := by
  obtain ⟨hl, hf⟩ := buffer_set (env i) (own i) m j v (hr i) hj
  have heq : Function.update own i (own i) = own := by
    funext q
    by_cases hq : q = i <;> simp [Function.update, hq]
  have h := (env_update env own m _ i _ (own i) ho hr hl hf rfl).1
  simpa only [heq] using h

theorem env_push {k : Nat} (env : Fin k → Array UInt64) (own : Fin k → Desc)
    (m : Mem) (i : Fin k) (v : UInt64)
    (ho : Owned own) (hr : EnvRep env own m) (hcap : (env i).size < (own i).cap) :
    EnvRep (Function.update env i ((env i).push v))
      (Function.update own i {own i with len := (own i).len+1})
      (appendMem (env i) (own i) m v) ∧
    Owned (Function.update own i {own i with len := (own i).len+1}) := by
  obtain ⟨hl, hf⟩ := buffer_push (env i) (own i) m v (hr i) hcap
  exact env_update env own m _ i _ _ ho hr hl hf rfl

end MultiBuffer
end Round6

namespace Round6.WorkStack

inductive Item where
  | emit (v : UInt64)
  | fork (left right : Item)

def expandItem : Item → List UInt64
  | .emit v => [v]
  | .fork l r => expandItem l ++ expandItem r

def expand : List Item → List UInt64
  | [] => []
  | x :: xs => expandItem x ++ expand xs

def nodes : Item → Nat
  | .emit _ => 1
  | .fork l r => 1 + nodes l + nodes r

def weight : List Item → Nat
  | [] => 0
  | x :: xs => nodes x + weight xs

theorem nodes_pos (x : Item) : 0 < nodes x := by
  cases x <;> simp only [nodes] <;> omega

structure WorkState where
  stack : List Item
  outRev : List UInt64

def advance : WorkState → WorkState
  | ⟨[], out⟩ => ⟨[], out⟩
  | ⟨.emit v :: xs, out⟩ => ⟨xs, v :: out⟩
  | ⟨.fork l r :: xs, out⟩ => ⟨l :: r :: xs, out⟩

def run (fuel : Nat) (st : WorkState) : List UInt64 :=
  match fuel with
  | 0 => st.outRev.reverse
  | fuel+1 =>
    match st.stack with
    | [] => st.outRev.reverse
    | _ :: _ => run fuel (advance st)
termination_by structural fuel

theorem run_correct (fuel : Nat) : ∀ stack out,
    weight stack ≤ fuel → run fuel ⟨stack, out⟩ = out.reverse ++ expand stack := by
  induction fuel with
  | zero =>
    intro stack out hb
    cases stack with
    | nil => simp [run, expand]
    | cons x xs =>
      have hp := nodes_pos x
      simp only [weight] at hb
      omega
  | succ fuel ih =>
    intro stack out hb
    cases stack with
    | nil => simp [run, expand]
    | cons x xs =>
      cases x with
      | emit v =>
        have hb' : weight xs ≤ fuel := by simp only [weight, nodes] at hb; omega
        change run fuel ⟨xs, v :: out⟩ = _
        rw [ih xs (v::out) hb']
        simp [expand, expandItem, List.reverse_cons, List.append_assoc]
      | fork l r =>
        have hb' : weight (l :: r :: xs) ≤ fuel := by
          simp only [weight, nodes] at hb ⊢
          omega
        change run fuel ⟨l :: r :: xs, out⟩ = _
        rw [ih (l::r::xs) out hb']
        simp [expand, expandItem, List.append_assoc]

def tailVersion (fuel : Nat) (xs : List Item) : List UInt64 := run fuel ⟨xs, []⟩

theorem tailVersion_eq (fuel : Nat) (xs : List Item) (h : weight xs ≤ fuel) :
    tailVersion fuel xs = expand xs := by
  simpa only [tailVersion, List.reverse_nil, List.nil_append] using run_correct fuel xs [] h

-- The general worklist equation need not itself be structurally recursive.
-- Its measure must strictly decrease when replacing x by h x.
def runWork {I W : Type} (g : I → List W) (h : I → List I) :
    Nat → List I → List W → List W
  | 0, _, out => out.reverse
  | _+1, [], out => out.reverse
  | fuel+1, x::xs, out => runWork g h fuel (h x ++ xs) ((g x).reverse ++ out)

theorem runWork_correct {I W : Type} (g : I → List W) (h : I → List I)
    (f : List I → List W) (measure : List I → Nat)
    (f_nil : f [] = [])
    (f_cons : ∀ x xs, f (x::xs) = g x ++ f (h x ++ xs))
    (decreases : ∀ x xs, measure (h x ++ xs) < measure (x::xs)) :
    ∀ fuel xs out, measure xs ≤ fuel →
      runWork g h fuel xs out = out.reverse ++ f xs := by
  intro fuel
  induction fuel with
  | zero =>
    intro xs out hb
    cases xs with
    | nil => simp [runWork, f_nil]
    | cons x xs => have hd := decreases x xs; omega
  | succ fuel ih =>
    intro xs out hb
    cases xs with
    | nil => simp [runWork, f_nil]
    | cons x xs =>
      have hb' : measure (h x ++ xs) ≤ fuel := by have hd := decreases x xs; omega
      change runWork g h fuel (h x ++ xs) ((g x).reverse ++ out) = _
      rw [ih _ _ hb', f_cons]
      simp [List.reverse_append, List.reverse_reverse, List.append_assoc]

def sample : List Item := [.fork (.emit 10) (.fork (.emit 20) (.emit 30))]
example : tailVersion 5 sample = [10,20,30] := by decide +kernel

end Round6.WorkStack

namespace Round6.Machine.CountExample
open NanoProofs.Loops

def code : Array Instr := #[.beq 1 0 16, .addi 2 2 1, .addi 1 1 (-1), .jal (-12)]

def layout : Layout code where
  header := 0
  bodyPC := 4
  updatePC := 8
  backedge := 12
  exitPC := 16
  fuelReg := 1
  fuel_nonzero := by decide
  exitOff := 16
  backOff := -12
  body_next := rfl
  back_next := rfl
  headerCode := ⟨rfl, rfl⟩
  updateCode := ⟨rfl, rfl⟩
  backCode := ⟨rfl, rfl⟩
  exitCert := cert_of_labels _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  backCert := cert_of_labels _ _ _ _ (by decide) (by decide) (by decide) (by decide)

def Payload (acc : UInt64) (m : State) : Prop := read m 2 = acc

def laws : PayloadLaws Payload layout.fuelReg where
  pc := by intro s m p h; exact h
  fuel := by
    intro s m v h
    simpa [Payload, layout, read, write] using h

def body (_ : Nat) (acc : UInt64) : Action UInt64 UInt64 := .continue (acc+1)
def Exit (acc : UInt64) (m : State) : Prop := m.pc = 16 ∧ read m 2 = acc

theorem body_correct (n : Nat) (acc : UInt64) (m : State)
    (hm : BodyEntry layout Payload n acc m) :
    ∃ m', Star (Step code) m m' ∧
      match body n acc with
      | .continue acc' => ContinueAt layout Payload n acc' m'
      | .exit r => Exit r m' := by
  obtain ⟨hpc, hf, hn, hp⟩ := hm
  let m' : State := {write m 2 (acc+1) with pc := 8}
  have hs : Step code m m' := by
    have hc : CodeAt code 4 (.addi 2 2 1) := ⟨rfl, rfl⟩
    have hs := addi_step code m 4 2 2 1 hc hpc
    change read m 2 = acc at hp
    simpa [m', addImm, hp] using hs
  refine ⟨m', .tail hs (.refl _), rfl, ?_, hn, ?_⟩
  · simpa [m', layout, read, write] using hf
  · change read m' 2 = acc+1
    exact read_write_same m 2 (acc+1) (by decide)

theorem count_compiled (n : Nat) (acc : UInt64) (m : State)
    (hm : H layout Payload n acc m) :
    ∃ m', Star (Step code) m m' ∧ Exit (loopSpec id body n acc) m' := by
  apply compiled_loop_correct layout Payload laws id body Exit
    (fun s m hp => ⟨rfl, hp⟩) body_correct n acc m hm

-- A finite trace can return at pc=16; fetch there is outside this code array.
example : step code ⟨16, fun _ => 0, fun _ => 0⟩ = none := rfl

end Round6.Machine.CountExample

-- Reproducible axiom audit (ordinary logical axioms are permitted).
#print axioms Round6.Machine.cert_of_labels
#print axioms Round6.Machine.beq_to_label
#print axioms Round6.Machine.jal_to_label
#print axioms Round6.Machine.header_zero
#print axioms Round6.Machine.header_nonzero
#print axioms Round6.Machine.update_backedge
#print axioms Round6.Machine.compiled_loop_correct
#print axioms Round6.Machine.CountExample.count_compiled
#print axioms Round6.MultiBuffer.buffer_push
#print axioms Round6.MultiBuffer.env_update
#print axioms Round6.MultiBuffer.env_set
#print axioms Round6.MultiBuffer.env_push
#print axioms Round6.WorkStack.tailVersion_eq
#print axioms Round6.WorkStack.runWork_correct

