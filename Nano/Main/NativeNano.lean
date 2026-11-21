/- **The native AArch64 compiler in nano**: `genNano x = C.e71 x (AST of x)` (Nano/Codegen/JArmTop.lean: Gen's word
buffer `e70`, the word-size check `e72`, the J → AArch64 translator `e64` of Nano/Codegen/JArm.lean, bytes `e49`),
`compileNano = compileGen genNano`, and its correctness on any machine with the A64 steps:
`C_correct_nano` / `C_runs_nano`, from `StepOK` (Run/JArmStep.lean: the 21 per-atom facts of the translator) and the
proved parts: the translator's core theorem `e64_natEncJ` (Run/JArmCore.lean), `jArmBits`, Gen's buffer
(`g42_e70`, `e70_len`, Run/JArmGen.lean), `cjUnique`, `natLawsOK`, the host lift (`C_correct_g`).
KNOWN WART: `genNano` guards `C.e71` by "the AST list is shorter than 2^31".  The nano code's own test
(`2147483647 < bsize x` in `e70`) reads the length modulo 2^64, and `GenOKG` quantifies over all source texts, so the
list bound (needed for `e70_len`) is put in the Lean wrapper, as `compileGen` does for the text length (≤ 2^20).  For a
source the front end accepts the guard holds (`ParSerLen.ser_lt`); removing it needs `GenOKG` to pass that fact. -/
import Nano.Main.NativeEnc
import Nano.Run.JArmCore
import Nano.Run.JArmInst
import Nano.Run.JArmGen
import Nano.Codegen.JArmTop
namespace NanoMain
open Proven.Top Proven.Top.Alloc JT CallProbe

/-- the native code generator in nano, from source text (see KNOWN WART above for the guard) -/
def genNano (x : List UInt8) : List UInt8 :=
  if (C.o41 (C.y16 (C.s10 x))).length < 2 ^ 31 then C.e71 x (C.o41 (C.y16 (C.s10 x))) else []

/-- **the native AArch64 compiler** -/
noncomputable def compileNano : SrcC → Option CompiledA := compileGen genNano

/-- the word-size check: every word from `i` on is below 2^32 -/
theorem e72_all : ∀ (k : Nat) (w : Buf) (i : Nat), w.length < 2 ^ 64 → C.e72 k w i.toUInt64 ≠ 0 →
    ∀ p, i ≤ p → p < w.length → (w.getD p 0).toNat < 2 ^ 32
  | 0, _, _, _, h, _, _, _ => absurd rfl h
  | k + 1, w, i, hw, h, p, hip, hp => by
    have hi : i.toUInt64 < bsize w := by rw [bsize_tU]; exact (tU_lt (by omega) (by omega)).2 (by omega)
    simp only [C.e72] at h
    rw [if_pos hi] at h
    by_cases hb : 4294967295 < bget w i.toUInt64
    · rw [if_pos hb] at h; exact absurd rfl h
    · rw [if_neg hb, tU_succ (by omega)] at h
      rcases Nat.eq_or_lt_of_le hip with rfl | hlt
      · have : ¬ (4294967295 : UInt64).toNat < (bget w i.toUInt64).toNat := fun h' => hb (UInt64.lt_iff_toNat_lt.2 h')
        have e : bget w i.toUInt64 = w.getD i 0 := by unfold bget; rw [ArmRA.toU_toNat (by omega)]
        rw [e] at this
        have h32 : (4294967295 : UInt64).toNat = 4294967295 := by decide
        omega
      · exact e72_all k w (i + 1) hw h p (by omega) hp

theorem wordBytes_tU (A : List Nat) : wordBytes ((A.map Nat.toUInt64).map UInt64.toNat) = wordBytes A := by
  have e : ∀ x : Nat, BitVec.ofNat 32 (x.toUInt64.toNat) = BitVec.ofNat 32 x := fun x => by
    apply BitVec.eq_of_toNat_eq
    simp [Nat.toUInt64_eq] <;> omega
  induction A with
  | nil => rfl
  | cons x A ih =>
    simp only [List.map_cons, wordBytes, List.flatMap_cons] at ih ⊢
    rw [ih, e x]

variable {M : Machine} {X W : M.State → Nat → Prop}

/-- **the nano native generator meets the general generator interface** -/
theorem genOKG_nano (S : StepOK) : GenOKG (natTarget M X W NatV) genNano := fun x hx => by
  -- the output as an opaque list (no unfolding of the generator in definitional checks)
  obtain ⟨Bx, hBx⟩ : ∃ Bx, Bx = genNano x := ⟨_, rfl⟩
  rw [← hBx]
  by_cases ha : (C.o41 (C.y16 (C.s10 x))).length < 2 ^ 31
  case neg => exact absurd (by unfold genNano; rw [if_neg ha]) hx
  have hgn : genNano x = C.e71 x (C.o41 (C.y16 (C.s10 x))) := by unfold genNano; rw [if_pos ha]
  have hx' : C.e71 x (C.o41 (C.y16 (C.s10 x))) ≠ [] := by rw [← hgn]; exact hx
  obtain ⟨g, hg⟩ : ∃ g, g = C.e70 (C.o41 (C.y16 (C.s10 x))) C.g_999 := ⟨_, rfl⟩
  have gl : g.length < 2 ^ 64 := by
    have := e70_len (C.o41 (C.y16 (C.s10 x))) C.g_999 ha
    rw [hg]; omega
  have gb : mC x = C.g40 16777216 x g 0 [] := by
    have e0 : mC x = C.g42 x (C.o41 (C.y16 (C.s10 x))) C.g_999 := by unfold mC C.g41; rfl
    rw [e0, hg, g42_e70]
  have he71 : C.e71 x (C.o41 (C.y16 (C.s10 x))) =
      if (C.e72 16777216 g 0 == 0) = true then [] else
      if (bsize (C.e64 g) == 0) = true then [] else C.e49 16777216 x (C.e64 g) 0 [] := by
    rw [hg]; simp only [C.e71]
  rw [he71] at hx'
  by_cases c1 : (C.e72 16777216 g 0 == 0) = true
  · rw [if_pos c1] at hx'; exact absurd rfl hx'
  rw [if_neg c1] at hx' he71
  by_cases c2 : (bsize (C.e64 g) == 0) = true
  · rw [if_pos c2] at hx'; exact absurd rfl hx'
  rw [if_neg c2] at hx' he71
  have h64 : C.e64 g ≠ [] := fun e => c2 (by rw [e]; rfl)
  have h72 : C.e72 16777216 g (0 : Nat).toUInt64 ≠ 0 := fun e => c1 (by
    have e' : C.e72 16777216 g 0 = 0 := e
    rw [e']; rfl)
  -- the size of Gen's buffer, from e64's own tests
  have h64' := h64
  rw [e64_eq] at h64'
  by_cases d1 : (bsize g == 0) = true
  · rw [if_pos d1] at h64'; exact absurd rfl h64'
  rw [if_neg d1] at h64'
  by_cases d2 : 262144 < bsize g
  · rw [if_pos d2] at h64'; exact absurd rfl h64'
  have hne0 : g ≠ [] := fun e => d1 (by rw [e]; rfl)
  have hd2 : ¬ 262144 < g.length := fun h => d2 (by
    rw [bsize_tU]
    apply UInt64.lt_iff_toNat_lt.2
    rw [ArmRA.toU_toNat gl]
    exact h)
  have hw32 : ∀ w ∈ g, w.toNat < 2 ^ 32 := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hw
    have := e72_all 16777216 g 0 gl h72 p (Nat.zero_le _) hp
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp] using this
  have hm : mC x = g.flatMap ArmRA.le4 := by
    rw [gb]
    have := g40_le4 x g gl 16777216 0 [] (by omega) (by omega)
    simpa using this
  have hmne : mC x ≠ [] := by
    rw [hm]
    cases g with
    | nil => exact absurd rfl hne0
    | cons w r => simp [ArmRA.le4]
  by_cases hex : ∃ (c : List UInt8) (Cj : List CallProbe.J), Cj.length < 2 ^ 18 ∧ (∀ j ∈ Cj, SimW.JOK j) ∧
      mC x = C.g40 16777216 c (Cj.map CallProbe.encG) 0 []
  · obtain ⟨c, Cj, hl, hj, e⟩ := hex
    have e2 : C.g40 16777216 c (Cj.map encG) 0 [] = (Cj.map encG).flatMap ArmRA.le4 := by
      have := g40_le4 c (Cj.map encG) (by rw [List.length_map]; omega) 16777216 0 []
        (by rw [List.length_map]; omega) (by omega)
      simpa using this
    have hg' : g = Cj.map encG := CjU.flat_inj g _ hw32
      (fun w hw => by
        obtain ⟨j, hj', rfl⟩ := List.mem_map.1 hw
        exact jArmBits.l2_lt j (hj j hj'))
      (hm.symm.trans (e.trans e2))
    rw [hg'] at h64 he71
    obtain ⟨A, hA, hwA, hAl⟩ := e64_natEncJ jArmBits S hj hl h64
    obtain ⟨I, hI, hV⟩ := natEncJ_img hA
    have hcode : genNano x = wordBytes A := by
      rw [hgn]
      have hwA' : C.e64 (Cj.map encG) = A.map Nat.toUInt64 := hwA
      rw [he71, hwA', e49_wordBytes x _ 16777216 (by rw [List.length_map]; omega) (by rw [List.length_map]; omega),
        wordBytes_tU]
    refine ⟨hmne, I, by rw [hI, hBx, hcode], fun c' Cj' h1 h2 h3 => ?_⟩
    have : Cj' = Cj := cjUnique c' c Cj' Cj h1 hl h2 hj (h3.symm.trans e)
    rw [this]; exact hV
  · exact ⟨hmne, ⟨Bx, CallProbe.LinkLay.lin 0, fun _ => True, fun _ _ => False⟩, rfl,
      fun c Cj h1 h2 h3 => absurd ⟨c, Cj, h1, h2, h3⟩ hex⟩

/-- **the nano native compiler is correct on AArch64** (any machine with the A64 steps) -/
theorem C_correct_nano (A : A64SemN M X W) (S : StepOK) (hwin : 2 ^ 31 ≤ M.ramStart) :
    CompileCorrectP M (ArmLoader X W) compileNano :=
  C_correct_g (natLaws A (natLawsOK A)) genNano (genOKG_nano S) hwin

/-- **the nano native compiler runs correctly on AArch64, with any work block** -/
theorem C_runs_nano (A : A64SemN M X W) (S : StepOK) (hwin : 2 ^ 31 ≤ M.ramStart) :
    CompileRunsP M (ArmLoader X W) compileNano :=
  C_runs_g (natLaws A (natLawsOK A)) genNano (genOKG_nano S) hwin

end NanoMain
