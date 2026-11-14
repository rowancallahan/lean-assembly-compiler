/- Machinery for register-generic step lemmas: an instruction word is `c ||| f` with `c` the concrete
fields (opcode, funct3, funct7) and `f` the symbolic fields (registers, immediates), zero elsewhere.
As in `Riscv/Steps/Branch.lean`, the decoder's bit-range tests are decided by `*_known` / `*_mismatch`
/ `*_ne` (a range inside the concrete fields) and `*_imm` (a range inside the symbolic fields); a mask
`K` says which bits are concrete, and a hypothesis `f &&& K = 0` in context lets `simp` discharge them.
Registers are read and written through `rX_bits_ok` / `wX_bits_ok` (`GenRegs.lean`). -/
import Riscv.Steps.GenRegs
import Riscv.Steps.Branch
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Proven
namespace G

/-! ## Masks of the concrete fields -/

/-- R-type: funct7, funct3, opcode -/
def KR : BitVec 32 := 0xFE00707F#32
/-- I/S/B-type: funct3, opcode -/
def KI : BitVec 32 := 0x0000707F#32
/-- RV64 shift-immediate: funct6, funct3, opcode -/
def KS : BitVec 32 := 0xFC00707F#32
/-- U/J-type: opcode -/
def KU : BitVec 32 := 0x0000007F#32

/-- a range with no concrete bit set: a slice of the symbolic fields -/
@[simp] theorem F_imm {c m : BitVec 32} {lo n} (hk : ∀ i < n, c.getLsbD (lo + i) = false) :
    (c ||| m).extractLsb' lo n = m.extractLsb' lo n := ext_imm hk

theorem field_ne {c m : BitVec 32} {lo n p : Nat} {d : BitVec n} {v : BitVec 5}
    (hv : m.extractLsb' p 5 = v) (hv0 : v ≠ 0)
    (hk : lo ≤ p ∧ p + 5 ≤ lo + n ∧ (∀ i < 5, c.getLsbD (p + i) = false) ∧ (∀ i < 5, d.getLsbD (p - lo + i) = false)) :
    ((c ||| m).extractLsb' lo n = d) = False := by
  obtain ⟨h1, h2, hc, hd⟩ := hk
  simp only [eq_iff_iff, iff_false]; intro he; apply hv0; rw [← hv]; ext i hi
  have := congrArg (·.getLsbD (p - lo + i)) he
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, hd i hi] at this
  rw [show lo + (p - lo + i) = p + i by omega, hc i hi] at this
  simp at this; simp [this (by omega)]
theorem ofFin_ne {r : Fin 32} (h : r ≠ 0) : (BitVec.ofFin r : BitVec 5) ≠ 0 := by
  intro he; apply h; have := congrArg BitVec.toFin he; exact this

/-! ## Symbolic fields (generated block, see the comment at the top) -/

/-- symbolic fields, zero elsewhere -/
def fR (rd rs1 rs2 : Fin 32) : BitVec 32 :=
  (0#7 : BitVec 7) +++ (BitVec.ofFin rs2 : BitVec 5) +++ (BitVec.ofFin rs1 : BitVec 5) +++ (0#3 : BitVec 3) +++
    (BitVec.ofFin rd : BitVec 5) +++ (0#7 : BitVec 7)
theorem fR_K (rd rs1 rs2 : Fin 32) : fR rd rs1 rs2 &&& KR = 0 := by simp only [fR, KR]; bits
theorem fR_low2 (rd rs1 rs2 : Fin 32) : (fR rd rs1 rs2).extractLsb' 0 2 = 0#2 := by simp only [fR]; bits
@[simp] theorem fR_rd (rd rs1 rs2 : Fin 32) : (fR rd rs1 rs2).extractLsb' 7 5 = BitVec.ofFin rd := by simp only [fR]; bits
@[simp] theorem fR_rs1 (rd rs1 rs2 : Fin 32) : (fR rd rs1 rs2).extractLsb' 15 5 = BitVec.ofFin rs1 := by simp only [fR]; bits
@[simp] theorem fR_rs2 (rd rs1 rs2 : Fin 32) : (fR rd rs1 rs2).extractLsb' 20 5 = BitVec.ofFin rs2 := by simp only [fR]; bits
@[simp] theorem fR_known {c : BitVec 32} (rd rs1 rs2 : Fin 32) {lo n} (hk : ∀ i < n, KR.getLsbD (lo + i) = true) :
    (c ||| fR rd rs1 rs2).extractLsb' lo n = c.extractLsb' lo n := ext_known (fR_K ..) hk
@[simp] theorem fR_mismatch {c : BitVec 32} (rd rs1 rs2 : Fin 32) {lo n} {d : BitVec n}
    (hk : ∃ i < n, KR.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| fR rd rs1 rs2).extractLsb' lo n = d) = False := ext_mismatch (fR_K ..) hk
@[simp] theorem fR_ne {c d : BitVec 32} (rd rs1 rs2 : Fin 32)
    (hk : ∃ i < 32, KR.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) : ((c ||| fR rd rs1 rs2) = d) = False :=
  word_ne (fR_K ..) hk
@[simp] theorem fR_zero (rd rs1 rs2 : Fin 32) {lo n} (hk : ∀ i < n, KR.getLsbD (lo + i) = true) :
    (fR rd rs1 rs2).extractLsb' lo n = 0#n := by
  have := ext_known (c := 0) (fR_K rd rs1 rs2) hk; simpa using this
@[simp] theorem fR_rdne {c : BitVec 32} (rd rs1 rs2 : Fin 32) (hrd : rd ≠ 0) {lo n} {d : BitVec n}
    (hk : lo ≤ 7 ∧ 12 ≤ lo + n ∧ (∀ i < 5, c.getLsbD (7 + i) = false) ∧ (∀ i < 5, d.getLsbD (7 - lo + i) = false)) :
    ((c ||| fR rd rs1 rs2).extractLsb' lo n = d) = False := field_ne (fR_rd ..) (ofFin_ne hrd) hk
/-- symbolic fields, zero elsewhere -/
def fI (rd rs1 : Fin 32) (imm : BitVec 12) : BitVec 32 :=
  imm +++ (BitVec.ofFin rs1 : BitVec 5) +++ (0#3 : BitVec 3) +++ (BitVec.ofFin rd : BitVec 5) +++ (0#7 : BitVec 7)
theorem fI_K (rd rs1 : Fin 32) (imm : BitVec 12) : fI rd rs1 imm &&& KI = 0 := by simp only [fI, KI]; bits
theorem fI_low2 (rd rs1 : Fin 32) (imm : BitVec 12) : (fI rd rs1 imm).extractLsb' 0 2 = 0#2 := by simp only [fI]; bits
@[simp] theorem fI_rd (rd rs1 : Fin 32) (imm : BitVec 12) : (fI rd rs1 imm).extractLsb' 7 5 = BitVec.ofFin rd := by simp only [fI]; bits
@[simp] theorem fI_rs1 (rd rs1 : Fin 32) (imm : BitVec 12) : (fI rd rs1 imm).extractLsb' 15 5 = BitVec.ofFin rs1 := by simp only [fI]; bits
@[simp] theorem fI_imm (rd rs1 : Fin 32) (imm : BitVec 12) : (fI rd rs1 imm).extractLsb' 20 12 = imm := by simp only [fI]; bits
@[simp] theorem fI_known {c : BitVec 32} (rd rs1 : Fin 32) (imm : BitVec 12) {lo n} (hk : ∀ i < n, KI.getLsbD (lo + i) = true) :
    (c ||| fI rd rs1 imm).extractLsb' lo n = c.extractLsb' lo n := ext_known (fI_K ..) hk
@[simp] theorem fI_mismatch {c : BitVec 32} (rd rs1 : Fin 32) (imm : BitVec 12) {lo n} {d : BitVec n}
    (hk : ∃ i < n, KI.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| fI rd rs1 imm).extractLsb' lo n = d) = False := ext_mismatch (fI_K ..) hk
@[simp] theorem fI_ne {c d : BitVec 32} (rd rs1 : Fin 32) (imm : BitVec 12)
    (hk : ∃ i < 32, KI.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) : ((c ||| fI rd rs1 imm) = d) = False :=
  word_ne (fI_K ..) hk
@[simp] theorem fI_zero (rd rs1 : Fin 32) (imm : BitVec 12) {lo n} (hk : ∀ i < n, KI.getLsbD (lo + i) = true) :
    (fI rd rs1 imm).extractLsb' lo n = 0#n := by
  have := ext_known (c := 0) (fI_K rd rs1 imm) hk; simpa using this
@[simp] theorem fI_rdne {c : BitVec 32} (rd rs1 : Fin 32) (imm : BitVec 12) (hrd : rd ≠ 0) {lo n} {d : BitVec n}
    (hk : lo ≤ 7 ∧ 12 ≤ lo + n ∧ (∀ i < 5, c.getLsbD (7 + i) = false) ∧ (∀ i < 5, d.getLsbD (7 - lo + i) = false)) :
    ((c ||| fI rd rs1 imm).extractLsb' lo n = d) = False := field_ne (fI_rd ..) (ofFin_ne hrd) hk
/-- symbolic fields, zero elsewhere -/
def fSh (rd rs1 : Fin 32) (sh : BitVec 6) : BitVec 32 :=
  (0#6 : BitVec 6) +++ sh +++ (BitVec.ofFin rs1 : BitVec 5) +++ (0#3 : BitVec 3) +++ (BitVec.ofFin rd : BitVec 5) +++
    (0#7 : BitVec 7)
theorem fSh_K (rd rs1 : Fin 32) (sh : BitVec 6) : fSh rd rs1 sh &&& KS = 0 := by simp only [fSh, KS]; bits
theorem fSh_low2 (rd rs1 : Fin 32) (sh : BitVec 6) : (fSh rd rs1 sh).extractLsb' 0 2 = 0#2 := by simp only [fSh]; bits
@[simp] theorem fSh_rd (rd rs1 : Fin 32) (sh : BitVec 6) : (fSh rd rs1 sh).extractLsb' 7 5 = BitVec.ofFin rd := by simp only [fSh]; bits
@[simp] theorem fSh_rs1 (rd rs1 : Fin 32) (sh : BitVec 6) : (fSh rd rs1 sh).extractLsb' 15 5 = BitVec.ofFin rs1 := by simp only [fSh]; bits
@[simp] theorem fSh_sh (rd rs1 : Fin 32) (sh : BitVec 6) : (fSh rd rs1 sh).extractLsb' 20 6 = sh := by simp only [fSh]; bits
@[simp] theorem fSh_known {c : BitVec 32} (rd rs1 : Fin 32) (sh : BitVec 6) {lo n} (hk : ∀ i < n, KS.getLsbD (lo + i) = true) :
    (c ||| fSh rd rs1 sh).extractLsb' lo n = c.extractLsb' lo n := ext_known (fSh_K ..) hk
@[simp] theorem fSh_mismatch {c : BitVec 32} (rd rs1 : Fin 32) (sh : BitVec 6) {lo n} {d : BitVec n}
    (hk : ∃ i < n, KS.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| fSh rd rs1 sh).extractLsb' lo n = d) = False := ext_mismatch (fSh_K ..) hk
@[simp] theorem fSh_ne {c d : BitVec 32} (rd rs1 : Fin 32) (sh : BitVec 6)
    (hk : ∃ i < 32, KS.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) : ((c ||| fSh rd rs1 sh) = d) = False :=
  word_ne (fSh_K ..) hk
@[simp] theorem fSh_zero (rd rs1 : Fin 32) (sh : BitVec 6) {lo n} (hk : ∀ i < n, KS.getLsbD (lo + i) = true) :
    (fSh rd rs1 sh).extractLsb' lo n = 0#n := by
  have := ext_known (c := 0) (fSh_K rd rs1 sh) hk; simpa using this
@[simp] theorem fSh_rdne {c : BitVec 32} (rd rs1 : Fin 32) (sh : BitVec 6) (hrd : rd ≠ 0) {lo n} {d : BitVec n}
    (hk : lo ≤ 7 ∧ 12 ≤ lo + n ∧ (∀ i < 5, c.getLsbD (7 + i) = false) ∧ (∀ i < 5, d.getLsbD (7 - lo + i) = false)) :
    ((c ||| fSh rd rs1 sh).extractLsb' lo n = d) = False := field_ne (fSh_rd ..) (ofFin_ne hrd) hk
/-- symbolic fields, zero elsewhere -/
def fU (rd : Fin 32) (imm : BitVec 20) : BitVec 32 :=
  imm +++ (BitVec.ofFin rd : BitVec 5) +++ (0#7 : BitVec 7)
theorem fU_K (rd : Fin 32) (imm : BitVec 20) : fU rd imm &&& KU = 0 := by simp only [fU, KU]; bits
theorem fU_low2 (rd : Fin 32) (imm : BitVec 20) : (fU rd imm).extractLsb' 0 2 = 0#2 := by simp only [fU]; bits
@[simp] theorem fU_rd (rd : Fin 32) (imm : BitVec 20) : (fU rd imm).extractLsb' 7 5 = BitVec.ofFin rd := by simp only [fU]; bits
@[simp] theorem fU_imm (rd : Fin 32) (imm : BitVec 20) : (fU rd imm).extractLsb' 12 20 = imm := by simp only [fU]; bits
@[simp] theorem fU_known {c : BitVec 32} (rd : Fin 32) (imm : BitVec 20) {lo n} (hk : ∀ i < n, KU.getLsbD (lo + i) = true) :
    (c ||| fU rd imm).extractLsb' lo n = c.extractLsb' lo n := ext_known (fU_K ..) hk
@[simp] theorem fU_mismatch {c : BitVec 32} (rd : Fin 32) (imm : BitVec 20) {lo n} {d : BitVec n}
    (hk : ∃ i < n, KU.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| fU rd imm).extractLsb' lo n = d) = False := ext_mismatch (fU_K ..) hk
@[simp] theorem fU_ne {c d : BitVec 32} (rd : Fin 32) (imm : BitVec 20)
    (hk : ∃ i < 32, KU.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) : ((c ||| fU rd imm) = d) = False :=
  word_ne (fU_K ..) hk
@[simp] theorem fU_zero (rd : Fin 32) (imm : BitVec 20) {lo n} (hk : ∀ i < n, KU.getLsbD (lo + i) = true) :
    (fU rd imm).extractLsb' lo n = 0#n := by
  have := ext_known (c := 0) (fU_K rd imm) hk; simpa using this
@[simp] theorem fU_rdne {c : BitVec 32} (rd : Fin 32) (imm : BitVec 20) (hrd : rd ≠ 0) {lo n} {d : BitVec n}
    (hk : lo ≤ 7 ∧ 12 ≤ lo + n ∧ (∀ i < 5, c.getLsbD (7 + i) = false) ∧ (∀ i < 5, d.getLsbD (7 - lo + i) = false)) :
    ((c ||| fU rd imm).extractLsb' lo n = d) = False := field_ne (fU_rd ..) (ofFin_ne hrd) hk
/-- symbolic fields, zero elsewhere -/
def fS (rs1 rs2 : Fin 32) (imm : BitVec 12) : BitVec 32 :=
  imm.extractLsb' 5 7 +++ (BitVec.ofFin rs2 : BitVec 5) +++ (BitVec.ofFin rs1 : BitVec 5) +++ (0#3 : BitVec 3) +++
    imm.extractLsb' 0 5 +++ (0#7 : BitVec 7)
theorem fS_K (rs1 rs2 : Fin 32) (imm : BitVec 12) : fS rs1 rs2 imm &&& KI = 0 := by simp only [fS, KI]; bits
theorem fS_low2 (rs1 rs2 : Fin 32) (imm : BitVec 12) : (fS rs1 rs2 imm).extractLsb' 0 2 = 0#2 := by simp only [fS]; bits
@[simp] theorem fS_rs1 (rs1 rs2 : Fin 32) (imm : BitVec 12) : (fS rs1 rs2 imm).extractLsb' 15 5 = BitVec.ofFin rs1 := by simp only [fS]; bits
@[simp] theorem fS_rs2 (rs1 rs2 : Fin 32) (imm : BitVec 12) : (fS rs1 rs2 imm).extractLsb' 20 5 = BitVec.ofFin rs2 := by simp only [fS]; bits
@[simp] theorem fS_hi (rs1 rs2 : Fin 32) (imm : BitVec 12) : (fS rs1 rs2 imm).extractLsb' 25 7 = imm.extractLsb' 5 7 := by simp only [fS]; bits
@[simp] theorem fS_lo (rs1 rs2 : Fin 32) (imm : BitVec 12) : (fS rs1 rs2 imm).extractLsb' 7 5 = imm.extractLsb' 0 5 := by simp only [fS]; bits
@[simp] theorem fS_known {c : BitVec 32} (rs1 rs2 : Fin 32) (imm : BitVec 12) {lo n} (hk : ∀ i < n, KI.getLsbD (lo + i) = true) :
    (c ||| fS rs1 rs2 imm).extractLsb' lo n = c.extractLsb' lo n := ext_known (fS_K ..) hk
@[simp] theorem fS_mismatch {c : BitVec 32} (rs1 rs2 : Fin 32) (imm : BitVec 12) {lo n} {d : BitVec n}
    (hk : ∃ i < n, KI.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| fS rs1 rs2 imm).extractLsb' lo n = d) = False := ext_mismatch (fS_K ..) hk
@[simp] theorem fS_ne {c d : BitVec 32} (rs1 rs2 : Fin 32) (imm : BitVec 12)
    (hk : ∃ i < 32, KI.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) : ((c ||| fS rs1 rs2 imm) = d) = False :=
  word_ne (fS_K ..) hk
@[simp] theorem fS_zero (rs1 rs2 : Fin 32) (imm : BitVec 12) {lo n} (hk : ∀ i < n, KI.getLsbD (lo + i) = true) :
    (fS rs1 rs2 imm).extractLsb' lo n = 0#n := by
  have := ext_known (c := 0) (fS_K rs1 rs2 imm) hk; simpa using this
/-- symbolic fields, zero elsewhere -/
def fB (rs1 rs2 : Fin 32) (o : BitVec 12) : BitVec 32 :=
  o.extractLsb' 11 1 +++ o.extractLsb' 4 6 +++ (BitVec.ofFin rs2 : BitVec 5) +++ (BitVec.ofFin rs1 : BitVec 5) +++
    (0#3 : BitVec 3) +++ o.extractLsb' 0 4 +++ o.extractLsb' 10 1 +++ (0#7 : BitVec 7)
theorem fB_K (rs1 rs2 : Fin 32) (o : BitVec 12) : fB rs1 rs2 o &&& KI = 0 := by simp only [fB, KI]; bits
theorem fB_low2 (rs1 rs2 : Fin 32) (o : BitVec 12) : (fB rs1 rs2 o).extractLsb' 0 2 = 0#2 := by simp only [fB]; bits
@[simp] theorem fB_rs1 (rs1 rs2 : Fin 32) (o : BitVec 12) : (fB rs1 rs2 o).extractLsb' 15 5 = BitVec.ofFin rs1 := by simp only [fB]; bits
@[simp] theorem fB_rs2 (rs1 rs2 : Fin 32) (o : BitVec 12) : (fB rs1 rs2 o).extractLsb' 20 5 = BitVec.ofFin rs2 := by simp only [fB]; bits
@[simp] theorem fB_known {c : BitVec 32} (rs1 rs2 : Fin 32) (o : BitVec 12) {lo n} (hk : ∀ i < n, KI.getLsbD (lo + i) = true) :
    (c ||| fB rs1 rs2 o).extractLsb' lo n = c.extractLsb' lo n := ext_known (fB_K ..) hk
@[simp] theorem fB_mismatch {c : BitVec 32} (rs1 rs2 : Fin 32) (o : BitVec 12) {lo n} {d : BitVec n}
    (hk : ∃ i < n, KI.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| fB rs1 rs2 o).extractLsb' lo n = d) = False := ext_mismatch (fB_K ..) hk
@[simp] theorem fB_ne {c d : BitVec 32} (rs1 rs2 : Fin 32) (o : BitVec 12)
    (hk : ∃ i < 32, KI.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) : ((c ||| fB rs1 rs2 o) = d) = False :=
  word_ne (fB_K ..) hk
@[simp] theorem fB_zero (rs1 rs2 : Fin 32) (o : BitVec 12) {lo n} (hk : ∀ i < n, KI.getLsbD (lo + i) = true) :
    (fB rs1 rs2 o).extractLsb' lo n = 0#n := by
  have := ext_known (c := 0) (fB_K rs1 rs2 o) hk; simpa using this
/-- symbolic fields, zero elsewhere -/
def fJ (rd : Fin 32) (o : BitVec 20) : BitVec 32 :=
  o.extractLsb' 19 1 +++ o.extractLsb' 0 10 +++ o.extractLsb' 10 1 +++ o.extractLsb' 11 8 +++
    (BitVec.ofFin rd : BitVec 5) +++ (0#7 : BitVec 7)
theorem fJ_K (rd : Fin 32) (o : BitVec 20) : fJ rd o &&& KU = 0 := by simp only [fJ, KU]; bits
theorem fJ_low2 (rd : Fin 32) (o : BitVec 20) : (fJ rd o).extractLsb' 0 2 = 0#2 := by simp only [fJ]; bits
@[simp] theorem fJ_rd (rd : Fin 32) (o : BitVec 20) : (fJ rd o).extractLsb' 7 5 = BitVec.ofFin rd := by simp only [fJ]; bits
@[simp] theorem fJ_known {c : BitVec 32} (rd : Fin 32) (o : BitVec 20) {lo n} (hk : ∀ i < n, KU.getLsbD (lo + i) = true) :
    (c ||| fJ rd o).extractLsb' lo n = c.extractLsb' lo n := ext_known (fJ_K ..) hk
@[simp] theorem fJ_mismatch {c : BitVec 32} (rd : Fin 32) (o : BitVec 20) {lo n} {d : BitVec n}
    (hk : ∃ i < n, KU.getLsbD (lo + i) = true ∧ c.getLsbD (lo + i) ≠ d.getLsbD i) :
    ((c ||| fJ rd o).extractLsb' lo n = d) = False := ext_mismatch (fJ_K ..) hk
@[simp] theorem fJ_ne {c d : BitVec 32} (rd : Fin 32) (o : BitVec 20)
    (hk : ∃ i < 32, KU.getLsbD (0 + i) = true ∧ c.getLsbD (0 + i) ≠ d.getLsbD i) : ((c ||| fJ rd o) = d) = False :=
  word_ne (fJ_K ..) hk
@[simp] theorem fJ_zero (rd : Fin 32) (o : BitVec 20) {lo n} (hk : ∀ i < n, KU.getLsbD (lo + i) = true) :
    (fJ rd o).extractLsb' lo n = 0#n := by
  have := ext_known (c := 0) (fJ_K rd o) hk; simpa using this
@[simp] theorem fJ_rdne {c : BitVec 32} (rd : Fin 32) (o : BitVec 20) (hrd : rd ≠ 0) {lo n} {d : BitVec n}
    (hk : lo ≤ 7 ∧ 12 ≤ lo + n ∧ (∀ i < 5, c.getLsbD (7 + i) = false) ∧ (∀ i < 5, d.getLsbD (7 - lo + i) = false)) :
    ((c ||| fJ rd o).extractLsb' lo n = d) = False := field_ne (fJ_rd ..) (ofFin_ne hrd) hk

theorem low2_or {c m : BitVec 32} (hc : c.extractLsb' 0 2 = 3#2) (hm : m.extractLsb' 0 2 = 0#2) :
    (c ||| m).extractLsb' 0 2 = 3#2 := by
  rw [← hc]; ext i hi
  have := congrArg (·.getLsbD i) hm; simp at this; simp [this hi]
theorem rvc_or {c m : BitVec 32} (hc : c.extractLsb' 0 2 = 3#2) (hm : m.extractLsb' 0 2 = 0#2) :
    isRVC (BitVec.setWidth 16 ((c ||| m).extractLsb' 24 8 ++ (c ||| m).extractLsb' 16 8 ++
      (c ||| m).extractLsb' 8 8 ++ (c ||| m).extractLsb' 0 8)) = false := rvc_of (low2_or hc hm)

/-- an R-type word: `c` concrete (opcode `0x33`, funct3, funct7) -/
def wR (c : BitVec 32) (rd rs1 rs2 : Fin 32) : BitVec 32 := c ||| fR rd rs1 rs2

@[simp] theorem sign_extend_eq {n : Nat} (x : BitVec n) : sign_extend (m := 64) x = x.signExtend 64 := by
  simp [sign_extend, Sail.BitVec.signExtend]

/-! ## Branch / jump offsets -/

theorem fB_dec (rs1 rs2 : Fin 32) (o : BitVec 12) :
    (BitVec.extractLsb' 31 1 (fB rs1 rs2 o) +++ BitVec.extractLsb' 7 1 (fB rs1 rs2 o) +++
      BitVec.extractLsb' 25 6 (fB rs1 rs2 o) +++ BitVec.extractLsb' 8 4 (fB rs1 rs2 o) +++ (0#1 : BitVec 1) :
      BitVec 13) = o +++ (0#1 : BitVec 1) := by
  simp only [fB]; bits
theorem fJ_dec (rd : Fin 32) (o : BitVec 20) :
    (BitVec.extractLsb' 31 1 (fJ rd o) +++ BitVec.extractLsb' 12 8 (fJ rd o) +++ BitVec.extractLsb' 20 1 (fJ rd o) +++
      BitVec.extractLsb' 21 10 (fJ rd o) +++ (0#1 : BitVec 1) : BitVec 21) = o +++ (0#1 : BitVec 1) := by
  simp only [fJ]; bits
theorem add_boff_even' (a : Nat) (o : BitVec 12) :
    (a + ((o +++ (0#1 : BitVec 1)).signExtend 64).toNat) % 2 = a % 2 := by
  have := add_boff_even a o; simpa [sign_extend, Sail.BitVec.signExtend] using this
theorem add_joff_even' (a : Nat) (o : BitVec 20) :
    (a + ((o +++ (0#1 : BitVec 1)).signExtend 64).toNat) % 2 = a % 2 := by
  have := add_joff_even a o; simpa [sign_extend, Sail.BitVec.signExtend] using this

/-! ## Register-field decoding -/

@[simp] theorem reg_matches (x : BitVec 5) : encdec_reg_backwards_matches x = true := by
  revert x; decide
@[simp] theorem reg_back (x : BitVec 5) (s : St) : encdec_reg_backwards x s = .ok (regidx.Regidx x) s := by
  sail_eval [encdec_reg_backwards]
  all_goals first | rfl | (have := reg_matches x; simp_all [encdec_reg_backwards_matches, Functions.regidx_bit_width])

/-! ## Finishing: the model's final register map as `xset` of `stepF` -/

/-- an even address (a def, so `simp` leaves a side condition `evenB x` alone) -/
def evenB (x : BitVec 64) : Prop := x.toNat % 2 = 0
theorem update0_evenB {x : BitVec 64} (h : evenB x) : Sail.BitVec.update x 0 0#1 = x := update0_even x h

@[simp] theorem xset_zero (m : Regs) (v : BitVec 64) : xset m 0 v = m := rfl

theorem xval_ins {m : Regs} {r : Register} {v} (hr : r ∉ xregs := by decide) (j : Fin 32) :
    xval (m.insert r v) j = xval m j := xval_insert_other hr j

/-! ## The tactic -/

set_option hygiene false in
/-- `step_word_core` for a word `c ||| f` with symbolic fields; `hm : f &&& K = 0` and
`hlow : f.extractLsb' 0 2 = 0` must be provable by `gfield` -/
macro "gstep_core" : tactic => `(tactic| (
  · intro s h hpc hi hQ
    simp only [Proven.getX_eq] at hQ
    have hok' := hok; obtain ⟨_, _, _⟩ := hok'
    have hf := Proven.fetch_cfg h hpc hok hi (Proven.G.rvc_or (by decide) (by first | with_reducible exact Proven.G.fR_low2 .. | with_reducible exact Proven.G.fI_low2 .. | with_reducible exact Proven.G.fSh_low2 .. | with_reducible exact Proven.G.fU_low2 .. | with_reducible exact Proven.G.fS_low2 .. | with_reducible exact Proven.G.fB_low2 .. | with_reducible exact Proven.G.fJ_low2 ..))
    rw [Proven.bytes_eq] at hf
    have hd := Proven.dispatch_cfg h
    have hxp := h.xpresent
    cfg_facts h
    obtain ⟨_, _, _, _, _, _⟩ := h.pma
    have := h.present .pmpaddr_n (by simp)
    sail_eval frozen[LeanRV64D.Functions.fetch, LeanRV64D.Functions.dispatchInterrupt, LeanRV64D.Functions.pmpCheck,
        LeanRV64D.Functions.rX_bits, LeanRV64D.Functions.wX_bits]
      [*, Proven.pmp_none, Std.ExtDHashMap.contains_insert, BitVec.add_sub_cancel, LeanRV64D.Functions.matching_pma_region,
      LeanRV64D.Functions.matching_pma_region_bits_range, LeanRV64D.Functions.override_PMA, LeanRV64D.Functions.hartSupports, LeanRV64D.Functions.range_subset, LeanRV64D.Functions.zopz0zIzJ_u,
      LeanRV64D.Functions.zopz0zI_u, LeanRV64D.Functions.zopz0zKzJ_u, LeanRV64D.Functions.zopz0zK_u, LeanRV64D.Functions.zopz0zI_s, LeanRV64D.Functions.zopz0zKzJ_s,
      BitVec.toNat_sub, BitVec.toNat_add, Proven.G.F_imm, Proven.G.fB_dec, Proven.G.fJ_dec,
      Proven.G.add_boff_even', Proven.G.add_joff_even', Proven.add_boff_even, Proven.add_joff_even,
      Proven.G.fR_rd, Proven.G.fR_rs1, Proven.G.fR_rs2, Proven.G.fR_zero, Proven.G.fR_rdne, Proven.G.fR_known, Proven.G.fR_mismatch, Proven.G.fR_ne, Proven.G.fI_rd, Proven.G.fI_rs1, Proven.G.fI_imm, Proven.G.fI_zero, Proven.G.fI_rdne, Proven.G.fI_known, Proven.G.fI_mismatch, Proven.G.fI_ne, Proven.G.fSh_rd, Proven.G.fSh_rs1, Proven.G.fSh_sh, Proven.G.fSh_zero, Proven.G.fSh_rdne, Proven.G.fSh_known, Proven.G.fSh_mismatch, Proven.G.fSh_ne, Proven.G.fU_rd, Proven.G.fU_imm, Proven.G.fU_zero, Proven.G.fU_rdne, Proven.G.fU_known, Proven.G.fU_mismatch, Proven.G.fU_ne, Proven.G.fS_rs1, Proven.G.fS_rs2, Proven.G.fS_hi, Proven.G.fS_lo, Proven.G.fS_zero, Proven.G.fS_known, Proven.G.fS_mismatch, Proven.G.fS_ne, Proven.G.fB_rs1, Proven.G.fB_rs2, Proven.G.fB_zero, Proven.G.fB_known, Proven.G.fB_mismatch, Proven.G.fB_ne, Proven.G.fJ_rd, Proven.G.fJ_zero, Proven.G.fJ_rdne, Proven.G.fJ_known, Proven.G.fJ_mismatch, Proven.G.fJ_ne,
      Proven.sail_ext, Proven.setw_ext,
      Proven.rX_bits_ok, Proven.wX_bits_ok, Proven.G.reg_matches, Proven.G.reg_back, Proven.xpresent_insert]
    all_goals simp [Proven.stepF, Proven.update0_even, Proven.ze32, Proven.boff, Proven.joff, Proven.G.update0_evenB, *]
  all_goals simp))

open Lean Meta Elab Tactic in
/-- `step_word` for words with symbolic fields (same interface) -/
elab "gstep" : tactic => withMainContext do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  let .app _ (.lam _ _ body _) := ty | throwError "gstep: expected ∃ s', Next s s' .."
  let args := body.getAppArgs
  unless body.isAppOfArity ``Next 6 do throwError "gstep: expected ∃ s', Next s s' .."
  let s := args[0]!
  let fn (e : Expr) : TacticM Term := do
    if e.hasLooseBVars then throwError "gstep: {e} mentions s'"
    Term.exprToSyntax (← mkLambdaFVars #[s] e)
  let (npc, v, mem) := (← fn args[2]!, ← fn args[4]!, ← fn args[5]!)
  let mut side : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || [`h, `hpc, `hi].contains d.userName then continue
    let t ← instantiateMVars d.type
    if (← isProp t) && t.containsFVar s.fvarId! then side := side.push d.toExpr
  let qBody ← side.foldrM (fun p acc => do mkAppM ``And #[← inferType p, acc]) (mkConst ``True)
  let qPf ← side.foldrM (fun p acc => mkAppM ``And.intro #[p, acc]) (mkConst ``True.intro)
  let q ← Term.exprToSyntax (← mkLambdaFVars #[s] qBody)
  let hq ← Term.exprToSyntax qPf
  let sT ← Term.exprToSyntax s
  evalTactic (← `(tactic| refine Proven.next_of (s := $sT) (npc := $npc) (v := $v) (mem := $mem)
    (Q := $q) ?_ $(mkIdent `h) $(mkIdent `hpc) $(mkIdent `hi) $hq
    (by set_option linter.unnecessarySimpa false in simpa using $hq) ?_ ?_ ?_))
  evalTactic (← `(tactic| gstep_core))

end G
end Proven
