/- **The S3 compiler in `Implements1` form** (`Spec/Implements1.lean`): the code of every compiled S3 program
implements the program's function with the strong per-function specification `Implements1With`
(`retLen = true`: `a1` holds the result length), for the identity encoding of the result.

The proof composes the lowering's run (`Compiler/S3/LowerMain.lean`: `lower_result`, `main` returns the number of
bytes written) with the IR back end's `emit_ok` (`Compiler/Ir/EmitTop.lean`), whose final predicate `Ctx.Fin` gives
`Cfg`, the return, the preserved registers (`keepC` and the frame register `gp`), `main`'s result in `a1` (the stub
moves it there) and the output bytes.  The memory frame comes from `Ctx.Unch` with the context's output length set
to the RESULT length (`emit_ok` holds for any context). -/
import Riscv.Back.S3Top
import Spec.Implements1
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.S3
open Proven Proven.Mach Proven.Mach.Riscv Proven.Top Proven.Top.Alloc

/-- **the emitted words** of an S3 program (empty when the compiler rejects it) -/
noncomputable def words (P : Prog) : List (BitVec 32) :=
  match Ir.compileW (lowerP P) with
  | some (ws, _) => ws
  | none => []

theorem compile_words {P : Prog} {c : CompiledA} (hc : compile P = some c) :
    ∃ Q code L, Accepted P ∧ Ir.alloc (lowerP P) = some Q ∧ rvT.emitP Q L = some code ∧
      words P = rvT.words code ∧ c = ⟨wordBytes (words P), 8, Ir.events Q⟩ := by
  obtain ⟨hG, hc'⟩ := compile_inv hc
  unfold Ir.compile at hc'
  cases hw : Ir.compileW (lowerP P) with
  | none => rw [hw] at hc'; exact nomatch hc'
  | some p =>
    obtain ⟨ws, Q⟩ := p
    rw [hw] at hc'; cases hc'
    have hwP : words P = ws := by unfold words; rw [hw]
    unfold Ir.compileW at hw
    split at hw
    · rename_i Q' ha
      unfold Ir.Target.lin at hw
      cases he : rvT.emitP Q' (rvT.layout Q' (Ir.Target.rounds Q') ⟨[], [], 0⟩) with
      | none => rw [he] at hw; exact nomatch hw
      | some code =>
        rw [he] at hw; cases hw
        exact ⟨_, code, _, hG, ha, he, hwP, by rw [hwP]⟩
    · exact nomatch hw

/-- the code bytes of a compiled program are the bytes of its words -/
theorem code_eq {P : Prog} {c : CompiledA} (hc : compile P = some c) : c.code = wordBytes (words P) := by
  obtain ⟨Q, code, L, -, -, -, -, rfl⟩ := compile_words hc; rfl

theorem code_length {P : Prog} {c : CompiledA} (hc : compile P = some c) : c.code.length = 4 * (words P).length := by
  rw [code_eq hc, wordBytes_length]

/-! ## The work space as a function of the input length -/

/-- every byte list of length `n` -/
def allBytes : Nat → List (List UInt8)
  | 0 => [[]]
  | n + 1 => (allBytes n).flatMap fun l => (List.range 256).map fun b => b.toUInt8 :: l

theorem mem_allBytes : ∀ x : List UInt8, x ∈ allBytes x.length
  | [] => by simp [allBytes]
  | b :: x => by
    simp only [allBytes, List.length_cons, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨x, mem_allBytes x, b.toNat, b.toNat_lt, by simp⟩

theorem le_foldr_max : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ≤ l.foldr max 0
  | b :: l, a, h => by
    simp only [List.mem_cons] at h
    simp only [List.foldr_cons]
    rcases h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

/-- **the work space** a compiled program needs for an input of `n` bytes: the most memory any input of `n` bytes
needs -/
noncomputable def spaceOf (c : CompiledA) (n : Nat) : Nat := ((allBytes n).map (memoryNeeded c)).foldr max 0

theorem memoryNeeded_le_spaceOf (c : CompiledA) (x : List UInt8) : memoryNeeded c x ≤ spaceOf c x.length :=
  le_foldr_max (List.mem_map.2 ⟨x, mem_allBytes x, rfl⟩)

/-! ## The adapter -/

/-- `KC` and `gp` kept give the ABI-preserved registers -/
theorem abi_of_KC {s s' : St} (h : Cfg s) (h₃ : Cfg s') (f : KC s s') (h3 : getX s' 3 = getX s 3) :
    abiSavedKept s s' := by
  have k : ∀ j ∈ ([2, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 32)), getX s' j = getX s j :=
    fun j hj => f j (by revert j; decide) (by revert j; decide) (by revert j; decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₃.x2, h.x2, k 2 (by decide)]
  · rw [h₃.x3, h.x3, h3]
  · rw [h₃.x4, h.x4, k 4 (by decide)]
  · rw [h₃.x8, h.x8, k 8 (by decide)]
  · rw [h₃.x9, h.x9, k 9 (by decide)]
  · rw [h₃.x18, h.x18, k 18 (by decide)]
  · rw [h₃.x19, h.x19, k 19 (by decide)]
  · rw [h₃.x20, h.x20, k 20 (by decide)]
  · rw [h₃.x21, h.x21, k 21 (by decide)]
  · rw [h₃.x22, h.x22, k 22 (by decide)]
  · rw [h₃.x23, h.x23, k 23 (by decide)]
  · rw [h₃.x24, h.x24, k 24 (by decide)]
  · rw [h₃.x25, h.x25, k 25 (by decide)]
  · rw [h₃.x26, h.x26, k 26 (by decide)]
  · rw [h₃.x27, h.x27, k 27 (by decide)]

set_option maxHeartbeats 1000000 in
/-- **The S3 compiler meets `Implements1`**: the words of a compiled S3 program implement the function `f` the
program computes (on the encoded arguments), with the work space bound `space` (any bound on `memoryNeeded`), and
`a1` holds the result length. -/
theorem implements1 {P : Prog} {c : CompiledA} (hc : compile P = some c) {α : Type}
    (encA : α → List UInt8) (f : α → List UInt8) (hf : ∀ a, P.run (encA a) = some (f a))
    (space : Nat → Nat)
    (hsp : ∀ a, (encA a).length ≤ 2 ^ 20 → memoryNeeded c (encA a) ≤ space (encA a).length) :
    Implements1With encA (fun l => l) (words P) f space (2 ^ 20) true := by
  obtain ⟨Q, code, L, hG, ha, he, hwords, rfl⟩ := compile_words hc
  intro a s entry ra input output work x y codeR hmax h hpc hal hcode h10 h11 h12 h13 h2 h1 hra hrad hx
    hil hol hws hwal hram hdis hmapO hmapW
  have hin : ∀ r ∈ [input, output, work, codeR], r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  obtain ⟨⟨ri1, ri2⟩, ⟨ro1, ro2⟩, ⟨rw1, rw2⟩, ⟨rc1, rc2⟩⟩ := hin
  unfold Proven.disjoint at d12 d13 d14 d23 d24 d34
  simp only [codeR] at d14 d24 d34 rc1 rc2
  have hil' : input.len = x.length := hil
  have hol' : y.length ≤ output.len := hol
  have hyx : y = f a := rfl
  -- the run of the program
  obtain ⟨v, hD, ho⟩ := Prog.run_some (hf a)
  obtain ⟨r0, hres, hout0, hvs0⟩ := lower_result P hG (encA a) (f a) v hD ho
    (by have : (encA a).length ≤ 2 ^ 20 := hmax; omega) (by have : (f a).length ≤ output.len := hol; omega)
  obtain ⟨r, hrun, hvs, hmem⟩ := Ir.alloc_runs ha (Ir.Prog.result_some hres)
  rw [← hmem] at hout0
  obtain ⟨hol2, hob⟩ := Ir.output_bytes hout0
  have hmn : memoryNeeded ⟨wordBytes (words P), 8, Ir.events Q⟩ (encA a) =
      8 * peak (r.ev ++ [Ir.Ctx.base Q]) := by
    show 8 * peak (Ir.events Q (encA a)) = _
    simp [Ir.events, Ir.Prog.result_eq hrun]
  have hpk : peak (r.ev ++ [Ir.Ctx.base Q]) ≤ work.len / 8 := by
    have := hsp a hmax; have hws' : space x.length ≤ work.len := hws
    rw [hmn] at this
    have : 8 * peak (r.ev ++ [Ir.Ctx.base Q]) ≤ work.len := Nat.le_trans this hws'
    omega
  -- the start state
  have hsp2 : getX s 2 = BitVec.ofNat 64 (work.base + work.len) := getX_of (h.x2.symm.trans h2) rfl
  have hspn : (getX s 2).toNat = work.base + work.len := by rw [hsp2]; exact toNat_ofNat' (by omega)
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  have hcodeOK : rvT.codeOK entry (words P).length := ⟨hal, rc1, by show _ ≤ 0x100000000; omega⟩
  let C : Ir.Ctx rvT := {
    W := words P
    pc0 := entry
    s0 := s
    input := x
    inA := input.base
    outA := output.base
    outL := y.length
    wb := work.base
    wl := work.len
    nS := 0
    F0 := 0
    sv := 0
    hm := fun _ => none
    code0 := codeAt_of_codeBytes hcodeOK hcode
    codeOK := hcodeOK
    lo := by decide
    inR := ⟨ri1, by show _ ≤ 0x100000000; omega⟩
    outR := ⟨ro1, by show _ ≤ 0x100000000; omega⟩
    wR := ⟨rw1, rw2⟩
    wal := hwal
    dCO := by unfold Mach.disjoint; dsimp only; omega
    dCW := by unfold Mach.disjoint; dsimp only; omega
    dIO := by unfold Mach.disjoint; dsimp only; omega
    dIW := by unfold Mach.disjoint; dsimp only; omega
    dOW := by unfold Mach.disjoint; dsimp only; omega
    inb := fun i hi => by
      have h' : bytesAt s input.base x.length = (x.map (·.toBitVec)).map some := by
        rw [hx, List.map_map]; rfl
      have := mem_of_bytesAt h' (i := i) (by simpa using hi)
      simpa using this
    wr := fun s a h => by show 0x80000000 ≤ a ∧ a + 1 ≤ 0x100000000; omega
    retOK := by show (getX s 1).toNat % 2 = 0; rw [hra']; omega
    htop := by
      show (getX s 2).toNat / 8 * 8 = work.base + work.len / 8 * 8
      rw [hspn]; omega }
  have hW : C.W = rvT.words code := hwords
  have hout : r.mem.out.length ≤ C.outL := by show r.mem.out.length ≤ (f a).length; omega
  have := C.emit_ok he hW h hpc
    (by show getX s 10 = _; rw [getX_of (h.x10.symm.trans h10) rfl])
    (by show getX s 11 = _; rw [getX_of (h.x11.symm.trans h11) rfl])
    (by show getX s 12 = _; rw [getX_of (h.x12.symm.trans h12) rfl])
    (by show getX s 13 = _; rw [getX_of (h.x13.symm.trans h13) rfl])
    (by show 16 ≤ (getX s 2).toNat / 8 * 8; rw [hspn]; omega)
    hrun hout
  obtain ⟨n, s', hsteps, hok, hpcF, hU, hcase⟩ := this
  refine ⟨n, s', hsteps, ?_⟩
  rcases hcase with ⟨-, -, bo, hkc, hfr, hlen⟩ | ⟨pk, -⟩
  rotate_left
  · exact absurd hpk (Nat.not_le.2 pk)
  change Cfg s' at hok
  refine ⟨?_, ?_, ?_, abi_of_KC h hok hkc hfr, hok, fun _ => ?_⟩
  · have : s'.regs.get? .PC = some (getX s 1) := hpcF
    rw [this, hra']
  · apply List.ext_getElem (by simp [bytesAt])
    intro i h1 h2
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    have hi : i < y.length := by simpa [bytesAt] using h1
    exact bo i _ (hob i (by rw [hyx] at hi; exact hi))
  · intro q hq
    have a2 := hq ⟨output.base, y.length⟩ (by simp); have a3 := hq work (by simp)
    dsimp only at a2 a3
    exact hU q a2 a3
  · have e := hlen (BitVec.ofNat 64 y.length) (by rw [hvs, hvs0]; rfl)
    change getX s' 11 = _ at e
    rw [hok.x11, e]

/-- **The S3 compiler meets `Implements1`**, with the work space `spaceOf c` (no space hypothesis). -/
theorem implements1_spaceOf {P : Prog} {c : CompiledA} (hc : compile P = some c) {α : Type}
    (encA : α → List UInt8) (f : α → List UInt8) (hf : ∀ a, P.run (encA a) = some (f a)) :
    Implements1With encA (fun l => l) (words P) f (spaceOf c) (2 ^ 20) true :=
  implements1 hc encA f hf (spaceOf c) fun a _ => memoryNeeded_le_spaceOf c (encA a)

end Proven.S3
