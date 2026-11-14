/- Non-vacuity, part 1: an explicit machine state satisfying `Cfg` (`Spec/Riscv.lean`), and a loader that
places byte blocks in memory, with lookup lemmas proved by `simp` / induction (no `decide` on hash maps).

`witness pc ra sp a0 a1 a2 a3 mem` is the state the later files instantiate: Sail reset values for the control
registers, `x1 = ra`, `x2 = sp`, `x10..x13 = a0..a3`, every other `x` register `0`, memory `mem`. -/
import Riscv.Direct.Arr
import Riscv.Direct.Loop
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.Vacuity

/-! ## Memory: loading byte blocks -/

abbrev Mem := Std.ExtHashMap Nat (BitVec 8)

/-- write `bs` at `a, a+1, ...` -/
def loadBytes : Mem → Nat → List (BitVec 8) → Mem
  | m, _, [] => m
  | m, a, b :: bs => loadBytes (m.insert a b) (a + 1) bs

theorem loadBytes_get : ∀ (bs : List (BitVec 8)) (m : Mem) (a k : Nat),
    (loadBytes m a bs)[k]? = if a ≤ k ∧ k < a + bs.length then bs[k - a]? else m[k]?
  | [], m, a, k => by simp [loadBytes]; omega
  | b :: bs, m, a, k => by
    rw [loadBytes, loadBytes_get bs, Std.ExtHashMap.getElem?_insert]
    by_cases h1 : a + 1 ≤ k ∧ k < a + 1 + bs.length
    · rw [if_pos h1, if_pos (by simp; omega)]
      obtain ⟨j, rfl⟩ : ∃ j, k = a + 1 + j := ⟨k - (a + 1), by omega⟩
      simp [show a + 1 + j - a = j + 1 by omega]
    · rw [if_neg h1]
      by_cases h2 : a = k
      · subst h2; simp
      · rw [if_neg (by simpa using h2)]
        rw [if_neg (by simp; omega)]

/-- bytes `[a, a+n)` of a memory map -/
def memAt (m : Mem) (a n : Nat) : List (Option (BitVec 8)) := (List.range n).map (m[a + ·]?)

theorem bytesAt_eq (s : St) (a n : Nat) : bytesAt s a n = memAt s.mem a n := rfl

theorem memAt_load_self (m : Mem) (a : Nat) (bs : List (BitVec 8)) :
    memAt (loadBytes m a bs) a bs.length = bs.map some := by
  apply List.ext_getElem (by simp [memAt])
  intro i h1 h2
  simp only [memAt, List.getElem_map, List.getElem_range, loadBytes_get]
  simp [memAt] at h1; rw [if_pos (by omega)]; simp

theorem memAt_load_other (m : Mem) (a n b : Nat) (bs : List (BitVec 8))
    (hd : a + n ≤ b ∨ b + bs.length ≤ a) : memAt (loadBytes m b bs) a n = memAt m a n := by
  apply List.ext_getElem (by simp [memAt])
  intro i h1 h2
  simp only [memAt, List.getElem_map, List.getElem_range, loadBytes_get]
  simp [memAt] at h1; rw [if_neg (by omega)]

theorem load_get_other (m : Mem) (b k : Nat) (bs : List (BitVec 8)) (hk : k < b ∨ b + bs.length ≤ k) :
    (loadBytes m b bs)[k]? = m[k]? := by
  rw [loadBytes_get, if_neg (by omega)]

theorem load_get_in (m : Mem) (b i : Nat) (bs : List (BitVec 8)) (hi : i < bs.length) :
    (loadBytes m b bs)[b + i]? = some bs[i] := by
  rw [loadBytes_get, if_pos (by omega)]; simp [hi]

/-- the bytes of a code list (little endian), without `some` -/
def codeBytes8 (code : List (BitVec 32)) : List (BitVec 8) :=
  code.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

theorem codeBytes_eq (code : List (BitVec 32)) : codeBytes code = (codeBytes8 code).map some := by
  simp [codeBytes, codeBytes8, List.map_flatMap]

theorem codeBytes8_length (code : List (BitVec 32)) : (codeBytes8 code).length = 4 * code.length := by
  induction code with
  | nil => rfl
  | cons w ws ih => simp [codeBytes8] at ih ⊢; omega

/-! ## Registers -/

/-- PMA attributes of the single RAM region (rwx; everything else Sail's `default`) -/
def ramPMA : PMA := { (default : PMA) with executable := true, readable := true, writable := true }

/-- the register map of the witness -/
def wRegs (pc ra sp a0 a1 a2 a3 : BitVec 64) : Regs :=
  ((∅ : Regs)
  |>.insert .cur_privilege .Machine
  |>.insert .hart_state (.HART_ACTIVE ())
  |>.insert .misa 0x800000000014112F#64
  |>.insert .mstatus 0x0000000A00000000#64
  |>.insert .mcountinhibit 0#32
  |>.insert .minstretcfg 0#64
  |>.insert .pmpcfg_n (Vector.replicate 64 0#8)
  |>.insert .htif_tohost_base none
  |>.insert .elp 0#1
  |>.insert .mseccfg 0#64
  |>.insert .pma_regions [⟨0x80000000#64, 0x80000000#64, ramPMA, false⟩]
  |>.insert .mideleg 0#64
  |>.insert .mip 0#64
  |>.insert .mie 0#64
  |>.insert .sig_meip 0#1
  |>.insert .sig_seip 0#1
  |>.insert .pmpaddr_n (Vector.replicate 64 0#64)
  |>.insert .minstret 0#64
  |>.insert .PC pc
  |>.insert .x1 ra |>.insert .x2 sp |>.insert .x3 0#64 |>.insert .x4 0#64 |>.insert .x5 0#64
  |>.insert .x6 0#64 |>.insert .x7 0#64 |>.insert .x8 0#64 |>.insert .x9 0#64 |>.insert .x10 a0
  |>.insert .x11 a1 |>.insert .x12 a2 |>.insert .x13 a3 |>.insert .x14 0#64 |>.insert .x15 0#64
  |>.insert .x16 0#64 |>.insert .x17 0#64 |>.insert .x18 0#64 |>.insert .x19 0#64 |>.insert .x20 0#64
  |>.insert .x21 0#64 |>.insert .x22 0#64 |>.insert .x23 0#64 |>.insert .x24 0#64 |>.insert .x25 0#64
  |>.insert .x26 0#64 |>.insert .x27 0#64 |>.insert .x28 0#64 |>.insert .x29 0#64 |>.insert .x30 0#64
  |>.insert .x31 0#64)

/-- **the witness state** -/
def witness (pc ra sp a0 a1 a2 a3 : BitVec 64) (mem : Mem) : St :=
  { regs := wRegs pc ra sp a0 a1 a2 a3, choiceState := (), mem := mem, tags := (), cycleCount := 0,
    sailOutput := #[] }

/-- **Every clause of `Cfg` is met** by the witness (any register values, any memory). -/
theorem witness_cfg (pc ra sp a0 a1 a2 a3 : BitVec 64) (mem : Mem) : Cfg (witness pc ra sp a0 a1 a2 a3 mem) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨ramPMA, false, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [witness, wRegs, ramPMA, Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.contains_insert] <;> rfl

/-- **Non-vacuity of `Cfg`.** -/
theorem cfg_nonvacuous : ∃ s, Cfg s := ⟨_, witness_cfg 0x80000000#64 0 0 0 0 0 0 ∅⟩

theorem witness_pc (pc ra sp a0 a1 a2 a3 mem) : (witness pc ra sp a0 a1 a2 a3 mem).regs.get? .PC = some pc := by
  simp [witness, wRegs, Std.ExtDHashMap.get?_insert]
theorem witness_x1 (pc ra sp a0 a1 a2 a3 mem) : (witness pc ra sp a0 a1 a2 a3 mem).regs.get? .x1 = some ra := by
  simp [witness, wRegs, Std.ExtDHashMap.get?_insert]
theorem witness_x2 (pc ra sp a0 a1 a2 a3 mem) : (witness pc ra sp a0 a1 a2 a3 mem).regs.get? .x2 = some sp := by
  simp [witness, wRegs, Std.ExtDHashMap.get?_insert]
theorem witness_x10 (pc ra sp a0 a1 a2 a3 mem) : (witness pc ra sp a0 a1 a2 a3 mem).regs.get? .x10 = some a0 := by
  simp [witness, wRegs, Std.ExtDHashMap.get?_insert]
theorem witness_x11 (pc ra sp a0 a1 a2 a3 mem) : (witness pc ra sp a0 a1 a2 a3 mem).regs.get? .x11 = some a1 := by
  simp [witness, wRegs, Std.ExtDHashMap.get?_insert]
theorem witness_x12 (pc ra sp a0 a1 a2 a3 mem) : (witness pc ra sp a0 a1 a2 a3 mem).regs.get? .x12 = some a2 := by
  simp [witness, wRegs, Std.ExtDHashMap.get?_insert]
theorem witness_x13 (pc ra sp a0 a1 a2 a3 mem) : (witness pc ra sp a0 a1 a2 a3 mem).regs.get? .x13 = some a3 := by
  simp [witness, wRegs, Std.ExtDHashMap.get?_insert]

/-- all `x` registers of the witness, as `getX` -/
theorem witness_getX (pc ra sp a0 a1 a2 a3 mem) (i : Fin 32) :
    getX (witness pc ra sp a0 a1 a2 a3 mem) i =
      if i = 1 then ra else if i = 2 then sp else if i = 10 then a0 else if i = 11 then a1 else
      if i = 12 then a2 else if i = 13 then a3 else 0 := by
  rw [getX_eq]
  obtain ⟨n, hn⟩ := i
  rcases n with _|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|_|n
  all_goals first | omega | simp [xval, witness, wRegs, Std.ExtDHashMap.get?_insert]

/-! ## Code placement -/

theorem codeAt_of_mem {s : St} : ∀ {code : List (BitVec 32)} {pc : BitVec 64}, codeOK pc code.length →
    (∀ i < 4 * code.length, s.mem[pc.toNat + i]? = (codeBytes8 code)[i]?) → codeAt s pc code
  | [], _, _, _ => fun i hi => absurd hi (by simp)
  | w :: ws, pc, hok, hb => by
    have g := fun i (hi : i < 4) => hb i (by simp; omega)
    have hi : instrAt s pc w :=
      ⟨by simpa [codeBytes8] using g 0 (by omega), by simpa [codeBytes8] using g 1 (by omega),
        by simpa [codeBytes8] using g 2 (by omega), by simpa [codeBytes8] using g 3 (by omega)⟩
    have hok' := (codeOK_append (a := 1) (b := ws.length) (by simpa [Nat.add_comm] using hok)).2
    have e := pc_toNat hok (a := 1) (by simp)
    have ih := codeAt_of_mem hok' (fun i hi' => by
      rw [e]; have := hb (4 + i) (by simp; omega)
      simp only [codeBytes8, List.flatMap_cons] at this
      rw [Nat.add_assoc, this, List.getElem?_append_right (by simp)]; simp [codeBytes8])
    exact (codeAt_append (l₁ := [w])).2 ⟨fun k hk => by simp at hk; subst hk; simpa using hi, ih⟩

theorem codeAt_load (m : Mem) (code : List (BitVec 32)) {pc : BitVec 64} (hok : codeOK pc code.length)
    {s : St} (hm : s.mem = loadBytes m pc.toNat (codeBytes8 code)) : codeAt s pc code :=
  codeAt_of_mem hok fun i hi => by
    rw [hm, loadBytes_get, if_pos (by rw [codeBytes8_length]; omega)]; simp

end Proven.Vacuity
