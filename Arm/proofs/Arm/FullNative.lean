/- The Sail full steps for the native back end's extra A64 forms (`A64SemN`, Nano/Run/A64SemN.lean), beyond rv2arm's:
`movn`, `add xd, xn, xm, lsl #3`, `lsl xd, xn, #sh` (UBFM), `ldp xt, xu, [xn]`, `ldrb wt, [xn, xm]`, and `ldur` from
`ArmFullB` (FullBrLdur's `full_ldur` is stated from `ArmFull`). `movz` with a shift, `cbnz`, `stur` exist already
(`full_movz`, `full_cbnz`, `full_stur`). Same recipe as FullBrLdur / FullAluAdd: decode prune (`sprune`/`sfin`),
execute under `Pins`, full step via `full_x` / `full_ld` / `full_gen`. The model is not edited. -/
import Arm.FullBrLdur
import Arm.FullAluAdd
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.all false

namespace ArmProof

/-! ## decode prune -/

theorem dec_movnsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFF800000#32 = 0x92800000#32) :
    __DecodeA64 pc w s = decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 16) (Sail.BitVec.slice w 21 2) 0#2 1#1
      { s with regs := s.regs.insert .SEE (697 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcImm
  sfin hK h hs see
  all_goals rfl

theorem dec_ubfmsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFC00000#32 = 0xD3400000#32) :
    __DecodeA64 pc w s = decode_ubfm_aarch64_instrs_integer_bitfield (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) (Sail.BitVec.slice w 10 6) (Sail.BitVec.slice w 16 6) 1#1 2#2 1#1
      { s with regs := s.regs.insert .SEE (78 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcImm
  sfin hK h hs see
  all_goals rfl

theorem dec_add3sym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC00#32 = 0x8B000C00#32) :
    __DecodeA64 pc w s = decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg
      (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) 3#6 (Sail.BitVec.slice w 16 5) 0#2 0#1 0#1 1#1
      { s with regs := s.regs.insert .SEE (14 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl

theorem dec_ldpsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFC00000#32 = 0xA9400000#32) :
    __DecodeA64 pc w s = decode_ldp_gen_aarch64_instrs_memory_pair_general_offset (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) (Sail.BitVec.slice w 10 5) (Sail.BitVec.slice w 15 7) 1#1 2#2
      { s with regs := s.regs.insert .SEE (611 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_LoadStore
  sfin hK h hs see
  all_goals rfl

theorem dec_ldrbRsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC00#32 = 0x38606800#32) :
    __DecodeA64 pc w s = decode_ldrb_reg_aarch64_instrs_memory_single_general_register (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) 0#1 3#3 (Sail.BitVec.slice w 16 5) 1#2 0#2
      { s with regs := s.regs.insert .SEE (656 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_LoadStore
  sfin hK h hs see
  all_goals rfl

/-! ## execute -/

section
variable {s : St} {d n m : Nat} {a b : BitVec 64}

theorem movn_exec' (hd : d < 31) (imm : BitVec 16) (hw : BitVec 2) :
    decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide (BitVec.ofNat 5 d) imm hw 0#2 1#1 s =
      .ok () { s with regs := xset s.regs d (~~~(imm.setWidth 64 <<< (hw.toNat * 16))) } := by
  idx d
  have := hw.isLt
  dsimp only [decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide]; dsimp
  exec_simp
  rw [hw4] at *
  simp only [show ((hw.toNat * 16 : Nat) : Int) + 15 < 64 by omega, ite_true, EStateM.pure]
  rw [sw2 _ _ (by rw [wid]; decide)]

theorem add3_exec (hd : d < 31) (hn : n < 31) (hm : m < 31) (ha : xget s.regs n = some a) (hb : xget s.regs m = some b) :
    decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) 3#6
      (BitVec.ofNat 5 m) 0#2 0#1 0#1 1#1 s = .ok () { s with regs := xset s.regs d (a + (b <<< 3)) } := by
  idx d; idx n; idx m
  dsimp only [decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg]; dsimp
  exec_simp
  rfl

end

/-! ## `lsl xd, xn, #sh` = UBFM: `HighestSetBit` (well-founded loop, first step), the masks per shift, the value -/

theorem hsb (x : BitVec 6) : HighestSetBit (1#1 +++ x) = 6 := by
  simp only [HighestSetBit, ExceptM.run, forIn, ForIn.forIn, ForIn'.forIn', IntRange.forIn']
  rw [IntRange.forIn'.loop.eq_1]
  simp (config := {decide := true}) [Membership.mem, BitVec.access, BitVec.join1, Sail.BitVec.length]
  have h6 : (1#1 +++ x)[6]! = true := by
    rw [getElem!_pos (1#1 +++ x) 6 (by decide), BitVec.getElem_append]; simp
  rw [h6]
  rfl
theorem dbm_gen (sh : Nat) (h1 : 0 < sh) (h2 : sh < 64) (s : St) :
    DecodeBitMasks (1#1) (BitVec.ofNat 6 (63 - sh)) (BitVec.ofNat 6 ((64 - sh) % 64)) false 64 s =
      .ok (BitVec.allOnes 64 <<< sh, BitVec.allOnes 64) s := by
  simp only [DecodeBitMasks]
  generalize hL : HighestSetBit (1#1 +++ ~~~(BitVec.ofNat 6 (63 - sh))) = L
  rw [hsb] at hL; subst hL
  rcases (show sh = 1 ∨ sh = 2 ∨ sh = 3 ∨ sh = 4 ∨ sh = 5 ∨ sh = 6 ∨ sh = 7 ∨ sh = 8 ∨ sh = 9 ∨ sh = 10 ∨ sh = 11 ∨ sh = 12 ∨ sh = 13 ∨ sh = 14 ∨ sh = 15 ∨ sh = 16 ∨ sh = 17 ∨ sh = 18 ∨ sh = 19 ∨ sh = 20 ∨ sh = 21 ∨ sh = 22 ∨ sh = 23 ∨ sh = 24 ∨ sh = 25 ∨ sh = 26 ∨ sh = 27 ∨ sh = 28 ∨ sh = 29 ∨ sh = 30 ∨ sh = 31 ∨ sh = 32 ∨ sh = 33 ∨ sh = 34 ∨ sh = 35 ∨ sh = 36 ∨ sh = 37 ∨ sh = 38 ∨ sh = 39 ∨ sh = 40 ∨ sh = 41 ∨ sh = 42 ∨ sh = 43 ∨ sh = 44 ∨ sh = 45 ∨ sh = 46 ∨ sh = 47 ∨ sh = 48 ∨ sh = 49 ∨ sh = 50 ∨ sh = 51 ∨ sh = 52 ∨ sh = 53 ∨ sh = 54 ∨ sh = 55 ∨ sh = 56 ∨ sh = 57 ∨ sh = 58 ∨ sh = 59 ∨ sh = 60 ∨ sh = 61 ∨ sh = 62 ∨ sh = 63 by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  simp (config := {decide := true}) [PreSail.sail_assert, bind, pure, EStateM.bind, EStateM.pure, integer_subrange, ROR, Ones, Sail.BitVec.zeroExtend, Sail.BitVec.length]
theorem ror_mask (a : BitVec 64) (sh : Nat) (h1 : 0 < sh) (h2 : sh < 64) :
    (a >>> (64 - sh) ||| a <<< sh) &&& (BitVec.allOnes 64 <<< sh) = a <<< sh := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes]
  by_cases hs : i < sh
  · simp [hs]
  · have : 64 - sh + i ≥ 64 := by omega
    simp [hs, hi, BitVec.getLsbD_of_ge a (64 - sh + i) this]; intro; omega
section
variable {s : St} {d n : Nat} {a : BitVec 64}
theorem ubfm_exec (hd : d < 31) (hn : n < 31) (ha : xget s.regs n = some a) (sh : Nat) (h1 : 0 < sh) (h2 : sh < 64) :
    decode_ubfm_aarch64_instrs_integer_bitfield (BitVec.ofNat 5 d) (BitVec.ofNat 5 n) (BitVec.ofNat 6 (63 - sh))
      (BitVec.ofNat 6 ((64 - sh) % 64)) 1#1 2#2 1#1 s = .ok () { s with regs := xset s.regs d (a <<< sh) } := by
  idx d; idx n
  dsimp only [decode_ubfm_aarch64_instrs_integer_bitfield]; dsimp
  exec_simp
  rw [dbm_gen sh h1 h2]
  simp (config := {decide := true}) [execute_aarch64_instrs_integer_bitfield, X_read, X_set, get_R, set_R, *, PreSail.sail_assert, bind, pure, EStateM.bind, EStateM.pure, ROR, Zeros, read_gpr_get, write_gpr_ok]
  have e1 : (64 - sh) % 64 = 64 - sh := by omega
  have e2 : (64 - sh).mod 64 = 64 - sh := e1
  have e3 : (64 : Int) - ((64 - sh : Nat) : Int) = (sh : Int) := by omega
  have ex : Sail.BitVec.extractLsb a 63 0 = a := by
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb]
  congr 2
  simp only [e1, ex, show (64 - sh = 0) = False by simp; omega, ite_false, BitVec.length, e2, e3, shl_int_nat]
  have hA : (18446744073709551615#64) = BitVec.allOnes 64 := by decide
  rw [hA, BitVec.and_allOnes, ror_mask a sh h1 h2]
  simp [Sail.BitVec.zeroExtend]
end

section
variable {s : St} (hc : Pins s.regs)
include hc
theorem ldrbR_exec {t n m : Nat} (ht : t < 31) (hn : n < 31) (hm : m < 31) {a c : BitVec 64} (ha : xget s.regs n = some a)
    (hcm : xget s.regs m = some c)
    {b : BitVec 8} (hlt : VaOK (a + c).toNat) (hb : s.mem.get? (a + c).toNat = some b) :
    decode_ldrb_reg_aarch64_instrs_memory_single_general_register (BitVec.ofNat 5 t) (BitVec.ofNat 5 n) 0#1 3#3 (BitVec.ofNat 5 m) 1#2 0#2 s =
      .ok () { s with regs := xset (s.regs.insert .InGuardedPage false) t (b.setWidth 64) } := by
  idx t; idx n; idx m
  have hg := gpr_ok hc .MemOp_LOAD (.inl rfl)
  have hmr := memreadG1 hc (a + c) b hlt hb
  simp only [decode_ldrb_reg_aarch64_instrs_memory_single_general_register,
    execute_aarch64_instrs_memory_single_general_register]
  have := u_MemOp; have := u_Constraint; have := read_gpr_ok ha; have := read_gpr_ok hcm
  have hn31 : (n == 31) = false := by simp; omega
  have hspe : (xset (s.regs.insert .InGuardedPage false) t (b.setWidth 64)).get? .SPESampleInFlight = some false := by
    rw [xset_get_ne _ _ _ _ (xreg_ne' (by decide))]; simp [Std.ExtDHashMap.get?_insert]; exact hc.spe
  have hdr : DecodeRegExtend (3#3) s = .ok .ExtendType_UXTX s := rfl
  have her : ExtendReg (m : Int) .ExtendType_UXTX 0 64 s = .ok c s := by
    simp (config := {decide := true}) [ExtendReg, Extend, X_read, get_R, PreSail.sail_assert, bind, pure, EStateM.bind, EStateM.pure,
      PreSail.undefined_bool, PreSail.undefined_int, choose_ok, read_gpr_get, *, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', BitVec.length]
  pins
  exec_simp
  have hb31 : (n != 31) = true := by simp; omega
  simp only [choice_unit] at hmr
  have hel0 : (3#2 != EL0) = true := by decide
  have hpf : (MemOp.MemOp_LOAD != MemOp.MemOp_PREFETCH) = true := by decide
  simp only [sz1, sz1', w8, hb31, hel0, hpf, Bool.and_true, BitVec.setWidth_eq]
  esimp
  simp only [sz1', hmr, BitVec.setWidth_eq]
  esimp
  done
theorem ldp_exec {t u n : Nat} (ht : t < 31) (hu : u < 31) (hn : n < 31) (htu : t ≠ u) {a : BitVec 64}
    (ha : xget s.regs n = some a) {v1 v2 : BitVec 64}
    (hlt : VaOK a.toNat) (hal : a.toNat % 8 = 0) (hv1 : MemD s.mem a.toNat v1)
    (hlt2 : VaOK (a + 8#64).toNat) (hal2 : (a + 8#64).toNat % 8 = 0) (hv2 : MemD s.mem (a + 8#64).toNat v2) :
    decode_ldp_gen_aarch64_instrs_memory_pair_general_offset (BitVec.ofNat 5 t) (BitVec.ofNat 5 n) (BitVec.ofNat 5 u) 0#7 1#1 2#2 s =
      .ok () { s with regs := xset (xset (s.regs.insert .InGuardedPage false) t v1) u v2 } := by
  idx t; idx u; idx n
  have hg := gpr_ok hc .MemOp_LOAD (.inl rfl)
  have hm1 := memreadG8 hc a v1 hlt hal hv1
  have := u_MemOp; have := u_Constraint; have := read_gpr_ok ha
  have hn31 : (n == 31) = false := by simp; omega
  have htu' : (t == u) = false := by simp; omega
  simp only [decode_ldp_gen_aarch64_instrs_memory_pair_general_offset,
    execute_aarch64_instrs_memory_pair_general_post_idx]
  pins
  exec_simp
  have hb31 : (n != 31) = true := by simp; omega
  have hel0 : (3#2 != EL0) = true := by decide
  simp only [choice_unit] at hm1
  simp only [hb31, hel0]
  esimp
  generalize hD : Int.shiftl 8 (2 + ↑(BitVec.join1 [BitVec.access (2#2) 1]).toNat) = D
  have hD' : D = 64 := by rw [← hD]; decide
  subst hD'
  have kz : sign_extend (0#7) 64 = 0#64 := by decide
  have k1 : (2 + ↑(BitVec.join1 [BitVec.access (2#2) 1]).toNat : Int) = 3 := by decide
  have ko : BitVec.ofInt 64 ((max (64 : Int) 0).ediv 8) = 8#64 := by decide
  simp only [kz, k1, ko]
  generalize hS : ((↑(Int.toNat 64) : Int).ediv 8).toNat = S
  have hS' : S = 8 := by rw [← hS]; decide
  subst hS'
  have kz2 : (0#64 <<< (3 : Int)) = 0#64 := by decide
  simp only [kz2, BitVec.add_zero, hm1]
  have hc1 : Pins (s.regs.insert .InGuardedPage false) := (pins_insert _ rfl).2 hc
  have hm2 := memreadG8 (s := { s with regs := s.regs.insert .InGuardedPage false, choiceState := () }) hc1 (a + 8#64) v2 hlt2 hal2 hv2
  simp only [choice_unit] at hm2
  have hspe : (xset (xset (s.regs.insert .InGuardedPage false) t v1) u v2).get? .SPESampleInFlight = some false := by
    rw [xset_get_ne _ _ _ _ (xreg_ne' (by decide)), xset_get_ne _ _ _ _ (xreg_ne' (by decide))]
    simp [Std.ExtDHashMap.get?_insert]; exact hc.spe
  simp only [hm2, insert_insert, BitVec.setWidth_eq]
  esimp
  done
end

/-! ## full steps -/

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
  (heret : BitVec.ofNat 20 (w.toNat >>> 12) ≠ 879088#20)
include hf ha hpc hlt hal hm heret

/-- full step for a pair load: `X[t] := v1`, then `X[u] := v2` -/
theorem full_ld2 {k : Int} {t u : Nat} (ht : t < 31) (hu : u < 31) {v1 v2 : BitVec 64}
    (hdec : __DecodeA64 pc.toNat w (s0of s w) = .ok () { s0of s w with regs := xset (xset (((s0of s w).regs.insert .SEE k).insert .InGuardedPage false) t v1) u v2 }) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' ((a.setX t v1).setX u v2) ∧ ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧
      s'.mem = s.mem := by
  obtain ⟨b0, hb0, hbr0⟩ := hf.bt
  have hx : ∀ r : Register, (∀ i < 31, xreg i ≠ r) → r ≠ .SEE →
      (xset (xset (((s0of s w).regs.insert .SEE k).insert .InGuardedPage false) t v1) u v2).get? r = (s0of s w).regs.get? r := fun r h1 h2 => by
    rw [xset_get_ne _ _ _ _ h1, xset_get_ne _ _ _ _ h1]
    by_cases e : r = .InGuardedPage
    · subst e; simp [Std.ExtDHashMap.get?_insert]; exact (s0_igp hf ha hpc hlt hal hm heret).symm
    · simp [Std.ExtDHashMap.get?_insert, Ne.symm h2, Ne.symm e]
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_gen hf hpc hlt hal hm heret hdec (bt := false) (pc1 := pc) (b := b0)
    (fun r h1 h2 h3 _ _ _ _ => hx r h1 h3)
    (fun p hp => ⟨p, by rw [hx _ (xreg_ne' (by decide)) (by decide)]; exact s0_ps hf ha hpc hlt hal hm heret p hp, pkeep_refl p⟩)
    (by rw [hx _ (xreg_ne' (by decide)) (by decide)]; simp [s0of, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [hx _ (xreg_ne' (by decide)) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hpc)
    (by rw [hx _ (xreg_ne' (by decide)) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hb0) hbr0
    (by rw [hx _ (xreg_ne' (by decide)) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hf.btn)
    (Abs.xset (Abs.xset (abs_ins (abs_ins (s0_abs ha w) .SEE (by decide) (by decide) k) .InGuardedPage (by decide) (by decide) false) ht v1) hu v2)
  exact ⟨s', h1, h2, h3, by simpa using h4, h5⟩

end

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`movn xd, #imm16, lsl #16hw`** -/
theorem full_movn (hK : w &&& 0xFF800000#32 = 0x92800000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat
        (~~~((Sail.BitVec.slice w 5 16).setWidth 64 <<< ((Sail.BitVec.slice w 21 2).toNat * 16)))) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_movnsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), movn_exec' hd31] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 26 (by decide) (by decide) (by decide)) hd31 hd

/-- **`add xd, xn, xm, lsl #3`** (`d n m < 31`) -/
theorem full_add3 (hK : w &&& 0xFFE0FC00#32 = 0x8B000C00#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat + (a.x (Sail.BitVec.slice w 16 5).toNat <<< 3))) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_add3sym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    add3_exec hd31 hn31 hm31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31)] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 30 (by decide) (by decide) (by decide)) hd31 hd

/-- **`lsl xd, xn, #sh`** (UBFM, `0 < sh < 64`, `d n < 31`) -/
theorem full_ubfm (hK : w &&& 0xFFC00000#32 = 0xD3400000#32) (hd31 : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31) (sh : Nat) (h1 : 0 < sh) (h2 : sh < 64)
    (hs : Sail.BitVec.slice w 10 6 = BitVec.ofNat 6 (63 - sh)) (hr : Sail.BitVec.slice w 16 6 = BitVec.ofNat 6 ((64 - sh) % 64)) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (a.x (Sail.BitVec.slice w 5 5).toNat <<< sh)) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_ubfmsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5), hs, hr,
    ubfm_exec hd31 hn31 (s0_xk ha w _ hn31) sh h1 h2] at hd
  exact full_x hf ha hpc hlt hal hm (noteret hK 24 (by decide) (by decide) (by decide)) hd31 hd

/-- **`ldrb wt, [xn, xm]`** (`t n m < 31`) -/
theorem full_ldrbR (hK : w &&& 0xFFE0FC00#32 = 0x38606800#32) (ht : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn : (Sail.BitVec.slice w 5 5).toNat < 31) (hm' : (Sail.BitVec.slice w 16 5).toNat < 31) {b : BitVec 8}
    (hA : VaOK (a.x (Sail.BitVec.slice w 5 5).toNat + a.x (Sail.BitVec.slice w 16 5).toNat).toNat)
    (hb : s.mem.get? (a.x (Sail.BitVec.slice w 5 5).toNat + a.x (Sail.BitVec.slice w 16 5).toNat).toNat = some b) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat (b.setWidth 64)) ∧ ArmFullB s' nb ∧
      s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_ldrbRsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5), ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    ldrbR_exec (s := { s0of s w with regs := (s0of s w).regs.insert .SEE (656 : Int) }) (s0_pins' hf w _) ht hn hm'
      (s0_xk ha w _ hn) (s0_xk ha w _ hm') hA hb] at hd
  exact full_ld hf ha hpc hlt hal hm (noteret hK 31 (by decide) (by decide) (by decide)) ht hd

/-- **`ldp xt, xu, [xn]`** (`t u n < 31`, `t ≠ u`, 8-aligned) -/
theorem full_ldp (hK : w &&& 0xFFC00000#32 = 0xA9400000#32) (ht : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hu : (Sail.BitVec.slice w 10 5).toNat < 31) (hn : (Sail.BitVec.slice w 5 5).toNat < 31)
    (htu : (Sail.BitVec.slice w 0 5).toNat ≠ (Sail.BitVec.slice w 10 5).toNat) (hi : Sail.BitVec.slice w 15 7 = 0#7)
    {v1 v2 : BitVec 64}
    (hA : VaOK (a.x (Sail.BitVec.slice w 5 5).toNat).toNat) (hA8 : (a.x (Sail.BitVec.slice w 5 5).toNat).toNat % 8 = 0)
    (hv1 : MemD s.mem (a.x (Sail.BitVec.slice w 5 5).toNat).toNat v1)
    (hB : VaOK (a.x (Sail.BitVec.slice w 5 5).toNat + 8#64).toNat) (hB8 : (a.x (Sail.BitVec.slice w 5 5).toNat + 8#64).toNat % 8 = 0)
    (hv2 : MemD s.mem (a.x (Sail.BitVec.slice w 5 5).toNat + 8#64).toNat v2) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' ((a.setX (Sail.BitVec.slice w 0 5).toNat v1).setX (Sail.BitVec.slice w 10 5).toNat v2) ∧ ArmFullB s' nb ∧
      s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_ldpsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5), ← ofNat_toNat5 (Sail.BitVec.slice w 10 5), hi,
    ldp_exec (s := { s0of s w with regs := (s0of s w).regs.insert .SEE (611 : Int) }) (s0_pins' hf w _) ht hu hn htu
      (s0_xk ha w _ hn) hA hA8 hv1 hB hB8 hv2] at hd
  exact full_ld2 hf ha hpc hlt hal hm (noteret hK 30 (by decide) (by decide) (by decide)) ht hu hd

/-- **`ldur xt, [xn, #simm9]`** from `ArmFullB` (8-aligned) -/
theorem full_ldurB (hK : w &&& 0xFFE00C00#32 = 0xF8400000#32) (ht : (Sail.BitVec.slice w 0 5).toNat < 31)
    (hn : (Sail.BitVec.slice w 5 5).toNat < 31) {v : BitVec 64}
    (hA : VaOK (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 12 9).signExtend 64).toNat)
    (hA8 : (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 12 9).signExtend 64).toNat % 8 = 0)
    (hv : MemD s.mem (a.x (Sail.BitVec.slice w 5 5).toNat + (Sail.BitVec.slice w 12 9).signExtend 64).toNat v) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' (a.setX (Sail.BitVec.slice w 0 5).toNat v) ∧ ArmFullB s' nb ∧
      s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  have hd := dec_ldursym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 0 5), ← ofNat_toNat5 (Sail.BitVec.slice w 5 5),
    ldur_exec (s := { s0of s w with regs := (s0of s w).regs.insert .SEE (680 : Int) }) (s0_pins' hf w _) ht hn _ (s0_xk ha w _ hn) hA hA8 hv] at hd
  exact full_ld hf ha hpc hlt hal hm (noteret hK 29 (by decide) (by decide) (by decide)) ht hd

end

end ArmProof

#print axioms ArmProof.full_movn
#print axioms ArmProof.full_add3
#print axioms ArmProof.full_ubfm
#print axioms ArmProof.full_ldrbR
#print axioms ArmProof.full_ldp
#print axioms ArmProof.full_ldurB
