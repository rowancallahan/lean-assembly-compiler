/- Non-vacuity of `boot_correct_with` (`Riscv/Back/Boot.lean`): an explicit memory image (stub, code,
length word, input, loaded with `loadBytes`) meets `Image` for any code and input that fit, and for the
`compile%` example `revinc5` on input `[3, 1, 2]` the theorem gives the run to the halt address with
`[3, 2, 4]` in the output block, from the bare-metal start with the reservation hook a no-op. -/
import Legacy.Riscv.Back.Boot
import Legacy.Riscv.Examples.PipeExamples
import Nano.Base.Riscv.Examples.Implements1Ex
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option maxRecDepth 100000

namespace Proven.Boot
open Proven.Top Proven.Vacuity

/-- the image: stub, code, length word, input -/
def bootImage (code input : List UInt8) : Mem :=
  loadBytes (loadBytes (loadBytes (loadBytes ∅ 0x80000000 (codeBytes8 stub)) codeBase (code.map (·.toBitVec)))
    lenAddr (le8 (BitVec.ofNat 64 input.length))) inputBase (input.map (·.toBitVec))

theorem holds_load (m : Mem) (base : Nat) (bytes : List UInt8) :
    Holds (loadBytes m base (bytes.map (·.toBitVec))) base bytes := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [load_get_in _ _ _ _ (by simpa using h1)]; simp

theorem holds_other {m : Mem} {base : Nat} {bytes : List UInt8} (h : Holds m base bytes) (b : Nat)
    (bs : List (BitVec 8)) (hd : base + bytes.length ≤ b ∨ b + bs.length ≤ base) :
    Holds (loadBytes m b bs) base bytes := by
  rw [Holds, ← h]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  rw [load_get_other _ _ _ _ (by omega)]

theorem le8_length (x : BitVec 64) : (le8 x).length = 8 := by simp [le8]

/-- **`Image` is satisfiable**: the explicit image for any code and input that fit -/
theorem bootImage_ok {code input : List UInt8} (hcode : code.length ≤ 0xFF000) :
    Image (bootImage code input) code input where
  stub i hi := by
    have hs : (codeBytes8 stub).length = 84 := by rw [codeBytes8_length]; rfl
    have : stub.length = 21 := rfl
    rw [bootImage, load_get_other _ _ _ _ (by simp [inputBase]; omega),
      load_get_other _ _ _ _ (by simp [lenAddr, le8_length]; omega),
      load_get_other _ _ _ _ (by simp [codeBase]; omega), loadBytes_get, if_pos (by omega)]
    simp
  code := by
    refine holds_other (holds_other (holds_load _ _ _) _ _ ?_) _ _ ?_ <;>
      simp [codeBase, lenAddr, inputBase, le8_length] <;> omega
  length := by
    refine holds_other ?_ _ _ (by simp [lenAddr, inputBase, encLen, le8_length])
    have := holds_load (loadBytes (loadBytes ∅ 0x80000000 (codeBytes8 stub)) codeBase (code.map (·.toBitVec)))
      lenAddr (encLen input.length)
    simp [encLen, List.map_map] at this ⊢; exact this
  input := holds_load _ _ _

/-- the example's compiled program -/
def exCompiled : Top.Compiled := ⟨wordBytes PipeEx.revinc5.code1, XPipe.space1 PipeEx.revinc5.pipe⟩

theorem ex_compiles : Top.compile PipeEx.revinc5.pipe = some exCompiled := by
  unfold Top.compile; rw [PipeEx.revinc5.compiles1]; rfl

theorem ex_computes : Computes PipeEx.revinc5.pipe (fun xs : List UInt8 => ((xs.take 5).map (· + 1)).reverse)
    id id := fun xs => by
  show some (XPipe.denote _ xs) = some _
  rw [← PipeEx.revinc5.denote]; rfl

/-- `boot_correct_with` for the `compile%` example `revinc5` on `[3, 1, 2]`: every hypothesis but the code size
is discharged here.  (The code is 62 words by `#eval`, but the kernel cannot evaluate the optimiser's
`List.mergeSort`, so `decide +kernel` cannot check its length.) -/
theorem boot_revinc5 (codeFits : exCompiled.code.length ≤ 0xFF000) :
    ∃ finishState, Runs riscv (bootStart (pure ()) (bootImage exCompiled.code [3, 1, 2])) finishState ∧
      (riscv.observe finishState).programCounter = 0x80000050 ∧
      readMemory (riscv.observe finishState) 0x80300000 3 = some [3, 2, 4] :=
  boot_correct_with (fun _ => rfl) ex_compiles ex_computes (argument := [3, 1, 2])
    (bootImage_ok codeFits) codeFits (by decide) (by decide)

/-- **fully concrete**: the `Implements1` example `incCode1` (add 1 to each byte) on `[3, 1, 2]`, from the
bare-metal start, reaches the halt address with `[4, 2, 3]` in the output block; no hypotheses -/
theorem boot_example :
    ∃ finishState, Runs riscv (bootStart (pure ()) (bootImage (wordBytes Mach.Riscv.incCode1) [3, 1, 2]))
      finishState ∧ (riscv.observe finishState).programCounter = 0x80000050 ∧
      readMemory (riscv.observe finishState) 0x80300000 3 = some [4, 2, 3] := by
  have hc : (wordBytes Mach.Riscv.incCode1).length ≤ 0xFF000 := by rw [wordBytes_length]; decide +kernel
  exact boot_implements1_with (fun _ => rfl) Mach.Riscv.inc_implements1 (argument := [3, 1, 2])
    (bootImage_ok hc) hc (by decide) (by decide) (by decide)

end Proven.Boot
