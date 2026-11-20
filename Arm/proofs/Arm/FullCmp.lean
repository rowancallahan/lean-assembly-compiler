/- DRAFT (not yet compiled against the model; statements fuzz-confirmed on qemu-aarch64, 200k+ cases).
Proof notes:
* `dec_cmpsym`/`dec_csetsym`: same recipe as `dec_movsym` (sprune/sfin). cmp = 0xEB00001F | m<<16 | n<<5 (SEE 17),
  cset = csinc xd,xzr,xzr,c = 0x9A9F07E0 | c<<12 | d (SEE 188); only the fields outside the mask stay symbolic.
* `cmp_exec` (Exec.lean) already gives PSTATE := setFlags p (AddWithCarry a (~~~b) 1).2; `sub_flags` (Flags.lean) turns
  that into N/Z/C/V; `full_pst` = `full_nt` plus a PSTATE insert (PKeep holds since only NZCV changes).
* `cset_exec` keeps the condition symbolic via `cond_ok` (BrFull) instead of unfolding `ConditionHolds` on literals;
  `condP_abs` relates `condP` to `AState.cond` by `decide` over the 16 conditions x 16 flag states.
* cset with d = 31 (xzr destination) is not covered (needs d < 31).
Open risks: `exec_simp` after `cond_ok` rewriting in `cset_exec`; defeq of the nested `{ { s with .. } with regs := .. }`
in `full_pst`'s `hdec`; `decide` size in `condP_abs`. -/
/- Symbolic-register full machine steps for `cmp xn, xm` (`subs xzr, xn, xm`) and `cset xd, cond`
(`csinc xd, xzr, xzr, !cond`, any of the 16 conditions in the encoded field). -/
import Arm.BrFull
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.all false

namespace ArmProof

/-! ## decode prune -/

theorem dec_cmpsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE0FC1F#32 = 0xEB00001F#32) :
    __DecodeA64 pc w s = decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg 31#5
      (Sail.BitVec.slice w 5 5) 0#6 (Sail.BitVec.slice w 16 5) 0#2 1#1 1#1 1#1
      { s with regs := s.regs.insert .SEE (17 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcReg
  sfin hK h hs see
  all_goals rfl

/-! ## execute -/

section
variable {s : St} {d : Nat} {p : ProcState}

end

/-! ## full steps -/

/-- inserting PSTATE with the flags of `a'` keeps `Abs` (X registers unchanged) -/
theorem abs_pst {s : St} {a a' : AState} (h : Abs s a) (hx : a'.x = a.x) (v : ProcState)
    (hN : v.N = .ofBool a'.n) (hZ : v.Z = .ofBool a'.z) (hC : v.C = .ofBool a'.c) (hV : v.V = .ofBool a'.v) :
    Abs { s with regs := s.regs.insert .PSTATE v } a' :=
  ⟨fun i hi => by
    show xget (s.regs.insert .PSTATE v) i = _
    rw [xget_insert _ _ _ (xreg_ne' (by decide)), h.x i hi, hx],
   ⟨v, by simp [Std.ExtDHashMap.get?_insert], hN, hZ, hC, hV⟩⟩

theorem condP_abs (c : BitVec 4) {p : ProcState} {a : AState} (hN : p.N = .ofBool a.n) (hZ : p.Z = .ofBool a.z)
    (hC : p.C = .ofBool a.c) (hV : p.V = .ofBool a.v) : condP c p = a.cond c := by
  unfold condP AState.cond; rw [hN, hZ, hC, hV]
  generalize a.n = n; generalize a.z = z; generalize a.c = k; generalize a.v = v
  revert c n z k v; decide

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
  (heret : BitVec.ofNat 20 (w.toNat >>> 12) ≠ 879088#20)
include hf ha hpc hlt hal hm heret

/-- full step for a decode+execute that writes only SEE and PSTATE.NZCV -/
theorem full_pst {k : Int} {v : ProcState} {a' : AState}
    (hdec : __DecodeA64 pc.toNat w (s0of s w) = .ok ()
      { s0of s w with regs := ((s0of s w).regs.insert .SEE k).insert .PSTATE v })
    (hv : ∀ p, s.regs.get? .PSTATE = some p → PKeep p v) (hx : a'.x = a.x)
    (hN : v.N = .ofBool a'.n) (hZ : v.Z = .ofBool a'.z) (hC : v.C = .ofBool a'.c) (hV : v.V = .ofBool a'.v) :
    ∃ s', stepModel s = .ok () s' ∧ Abs s' a' ∧ ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  obtain ⟨b0, hb0, hbr0⟩ := hf.bt
  have hx' : ∀ r : Register, r ≠ .SEE → r ≠ .PSTATE →
      (((s0of s w).regs.insert .SEE k).insert .PSTATE v).get? r = (s0of s w).regs.get? r :=
    fun r h1 h2 => by simp [Std.ExtDHashMap.get?_insert, Ne.symm h1, Ne.symm h2]
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_gen hf hpc hlt hal hm heret hdec (bt := false) (pc1 := pc) (b := b0)
    (fun r _ h2 h3 _ _ _ _ => hx' r h3 h2)
    (fun p hp => ⟨v, by simp [Std.ExtDHashMap.get?_insert], hv p hp⟩)
    (by rw [hx' _ (by decide) (by decide)]; simp [s0of, preRegs, Std.ExtDHashMap.get?_insert])
    (by rw [hx' _ (by decide) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hpc)
    (by rw [hx' _ (by decide) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hb0) hbr0
    (by rw [hx' _ (by decide) (by decide), s0_get _ _ _ (by decide) (by decide)]; exact hf.btn)
    (abs_pst (abs_ins (s0_abs ha w) .SEE (by decide) (by decide) k) hx v hN hZ hC hV)
  exact ⟨s', h1, h2, h3, by simpa using h4, h5⟩
end

section
variable {w : BitVec 32} {s : St} {a : AState} {nb : BitVec 2} (hf : ArmFullB s nb) (ha : Abs s a) {pc : BitVec 64}
  (hpc : s.regs.get? ._PC = some pc) (hlt : VaOK pc.toNat) (hal : pc.toNat % 4 = 0) (hm : MemWord s.mem pc.toNat w)
include hf ha hpc hlt hal hm

/-- **`cmp xn, xm`** (`subs xzr, xn, xm`; `n m < 31`): NZCV as by `AddWithCarry x (~~~y) 1`, i.e. `sub_flags`
(N = msb (x-y), Z = (x-y = 0), C = y ≤ x unsigned, V = signed overflow); nothing else changes -/
theorem full_cmp (hK : w &&& 0xFFE0FC1F#32 = 0xEB00001F#32) (hn31 : (Sail.BitVec.slice w 5 5).toNat < 31)
    (hm31 : (Sail.BitVec.slice w 16 5).toNat < 31) :
    ∃ s', stepModel s = .ok () s' ∧
      Abs s' (a.setSub (a.x (Sail.BitVec.slice w 5 5).toNat) (a.x (Sail.BitVec.slice w 16 5).toNat)) ∧
      ArmFullB s' nb ∧ s'.regs.get? ._PC = some (pc + 4) ∧ s'.mem = s.mem := by
  obtain ⟨p, hp, hN, hZ, hC, hV⟩ := ha.p
  have hd := dec_cmpsym (s0of s w) pc.toNat (-1) (by decide) (s0_see s w) hK
  have hp0 : ((s0of s w).regs.insert .SEE (17 : Int)).get? .PSTATE = some p := by
    simp only [Std.ExtDHashMap.get?_insert]; simp; exact (s0_get _ _ _ (by decide) (by decide)).trans hp
  rw [← ofNat_toNat5 (Sail.BitVec.slice w 5 5), ← ofNat_toNat5 (Sail.BitVec.slice w 16 5),
    cmp_exec hn31 hm31 (s0_xk ha w _ hn31) (s0_xk ha w _ hm31) hp0, sub_flags] at hd
  exact full_pst hf ha hpc hlt hal hm (noteret hK 29 (by decide) (by decide) (by decide)) hd
    (fun p' hp' => by rw [hp] at hp'; cases hp'; rfl) rfl rfl rfl rfl rfl

end

end ArmProof
