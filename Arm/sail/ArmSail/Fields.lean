/- The `A64Sem` fields on `armSail`, one per instruction form, from the Sail `full_*` lemmas (Arm/proofs/Arm:
BrFull, Mem, FullSubs, FullAluAdd, FullAluLogic, FullAluShift, FullMul, FullBrLdur).
Proof notes (each field): `pre` gives `ArmFullB s n`, `Abs s a`, the pc facts (`VaOK` from the RAM window) and the
fetched `MemWord`; the encoding facts (`mask32`, `fldt`, `immt`, offsets `off19`/`off26` after `sx2`) turn the
lemma's slices into the field's numbers; `goes_set` / `goes_jump` / `goes1` compare observations through `obsA`.
`cmpbr` runs `full_subsr` then `full_bc` (flags via `condP_abs` and `cond_sub`). Stores compare Sail's `wrD` /
`insert` with `store8` / `store1` byte by byte. -/
import ArmSail.Machine
import ArmSail.Enc
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open Sail
namespace ArmSail
open Proven.Top ArmProof

/-! ## observation helpers -/

theorem regS {s : St} {w : Nat} {n : BitVec 2} {a : AState} {pc : BitVec 64} (P : Pre s w n a pc) {r : Nat}
    (hr : r < 31) : (obsS s).register r = UInt64.ofBitVec (a.x r) := by
  rw [P.obs]; simp [obsA, hr]

theorem pcS {s : St} {w : Nat} {n : BitVec 2} {a : AState} {pc : BitVec 64} (P : Pre s w n a pc) :
    (obsS s).programCounter = UInt64.ofBitVec pc := by rw [P.obs]; rfl

theorem goes_set {s : St} {a : AState} {pc : BitVec 64} {n : BitVec 2} {d : Nat} {v : BitVec 64} {u : UInt64}
    (hd : d < 31) (hobs : obsS s = obsA pc a s.mem)
    (h : ∃ s', stepModel s = .ok () s' ∧ Abs s' (a.setX d v) ∧ ArmFullB s' n ∧ s'.regs.get? ._PC = some (pc + 4) ∧
      s'.mem = s.mem) (hu : UInt64.ofBitVec v = u) : JT.GoesK armSail TT TT s (JT.setReg (obsS s) d u) := by
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := h
  exact goes1 h1 h3 h4 (by rw [obs_eq h2 h4, h5, hobs, set_obsA hd, hu])

theorem goes_jump {s : St} {a : AState} {pc : BitVec 64} {n : BitVec 2} {t : BitVec 64} {u : UInt64}
    (hobs : obsS s = obsA pc a s.mem)
    (h : ∃ s', stepModel s = .ok () s' ∧ Abs s' a ∧ ArmFullB s' n ∧ s'.regs.get? ._PC = some t ∧ s'.mem = s.mem)
    (hu : UInt64.ofBitVec t = u) : JT.GoesK armSail TT TT s (JT.jumpTo (obsS s) u) := by
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := h
  exact goes1 h1 h3 h4 (by rw [obs_eq h2 h4, h5, hobs, ← hu]; rfl)

/-- observation after writing `x[d] := v` (any flags) with the pc at `p` -/
theorem gen_obsA {p q : BitVec 64} {a : AState} {m : Mem} {d : Nat} (hd : d < 31) (v : BitVec 64) :
    obsA p (a.setX d v) m = ⟨UInt64.ofBitVec p, fun r => if r = d then UInt64.ofBitVec v else (obsA q a m).register r,
      (obsA q a m).memory⟩ := by
  simp only [obsA]
  congr 1
  funext r
  by_cases e : r = d
  · subst e; simp [hd, AState.setX, show r ≠ 31 by omega]
  · simp only [e, ite_false, AState.setX, show d ≠ 31 by omega]

/-! ## moves and immediates -/

theorem F_movz (s : St) (d i : Nat) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hd : d < 31) (hi : i < 2 ^ 16)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.movz d i)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) d (UInt64.ofNat i)) := by
  obtain ⟨n, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.movz] at hm
  have := full_movz P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt)
  rw [show (Sail.BitVec.slice (wd (0xD2800000 + i * 2 ^ 5 + d)) 0 5).toNat = d by fldt,
    show (Sail.BitVec.slice (wd (0xD2800000 + i * 2 ^ 5 + d)) 21 2).toNat = 0 by fldt,
    show (Sail.BitVec.slice (wd (0xD2800000 + i * 2 ^ 5 + d)) 5 16).setWidth 64 = BitVec.ofNat 64 i by immt] at this
  exact goes_set hd P.obs this (by simp; rfl)

/-- `movk`'s value, as `A64Sem` writes it -/
theorem movk_val (x : BitVec 64) (i h : Nat) (hh : h < 4) :
    UInt64.ofBitVec (~~~(0xFFFF#64 <<< (h * 16)) &&& x ||| BitVec.ofNat 64 i <<< (h * 16)) = JT.movkV (UInt64.ofBitVec x) i h := by
  apply UInt64.toBitVec_inj.mp
  simp [JT.movkV, UInt64.toBitVec_shiftLeft, Nat.mul_comm, BitVec.and_comm, show h * 16 % 64 = h * 16 by omega]
  rw [show (UInt64.ofNat i).toBitVec = BitVec.ofNat 64 i from rfl]

theorem F_movk (s : St) (d i h : Nat) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hd : d < 31) (hi : i < 2 ^ 16) (hh : h < 4)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.movk d i h)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) d (JT.movkV ((armSail.observe s).register d) i h)) := by
  obtain ⟨n, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.movk] at hm
  have := full_movk P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt)
  rw [show (Sail.BitVec.slice (wd (0xF2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)) 0 5).toNat = d by fldt,
    show (Sail.BitVec.slice (wd (0xF2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)) 21 2).toNat = h by fldt,
    show (Sail.BitVec.slice (wd (0xF2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)) 5 16).setWidth 64 = BitVec.ofNat 64 i by immt]
    at this
  refine goes_set hd P.obs this ?_
  show _ = JT.movkV ((obsS s).register d) i h
  rw [regS P hd]; exact movk_val _ _ _ hh

theorem F_addi (s : St) (d n i : Nat) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hd : d < 31) (hn : n < 31) (hi : i < 4096)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.addi d n i)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) d ((armSail.observe s).register n + UInt64.ofNat i)) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.addi] at hm
  have := full_addi P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt) (by fldt)
  rw [show (Sail.BitVec.slice (wd (0x91000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)) 0 5).toNat = d by fldt,
    show (Sail.BitVec.slice (wd (0x91000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)) 5 5).toNat = n by fldt,
    show (Sail.BitVec.slice (wd (0x91000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)) 10 12).setWidth 64 = BitVec.ofNat 64 i by immt]
    at this
  refine goes_set hd P.obs this ?_
  show _ = (obsS s).register n + _
  rw [regS P hn]; rfl

theorem F_subi (s : St) (d n i : Nat) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hd : d < 31) (hn : n < 31) (hi : i < 4096)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.subi d n i)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) d ((armSail.observe s).register n - UInt64.ofNat i)) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.subi] at hm
  have := full_subi P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt) (by fldt)
  rw [show (Sail.BitVec.slice (wd (0xD1000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)) 0 5).toNat = d by fldt,
    show (Sail.BitVec.slice (wd (0xD1000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)) 5 5).toNat = n by fldt,
    show (Sail.BitVec.slice (wd (0xD1000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)) 10 12).setWidth 64 = BitVec.ofNat 64 i by immt]
    at this
  refine goes_set hd P.obs this ?_
  show _ = (obsS s).register n - _
  rw [regS P hn]; rfl

/-! ## register ALU -/

/-- the three register fields of an `rr` word -/
theorem rr_f {c d n m : Nat} (hc : c < 2 ^ 32) (h0 : c % 32 = 0) (h1 : c / 32 % 32 = 0) (h2 : c / 65536 % 32 = 0)
    (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    (Sail.BitVec.slice (wd (c + m * 2 ^ 16 + n * 2 ^ 5 + d)) 0 5).toNat = d ∧
    (Sail.BitVec.slice (wd (c + m * 2 ^ 16 + n * 2 ^ 5 + d)) 5 5).toNat = n ∧
    (Sail.BitVec.slice (wd (c + m * 2 ^ 16 + n * 2 ^ 5 + d)) 16 5).toNat = m :=
  ⟨by fldt, by fldt, by fldt⟩

theorem F_alu (s : St) (op d n m : Nat) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (h1 : 1 ≤ op) (h2 : op ≤ 8) (hd : d < 31) (hn : n < 31) (hm : m < 31)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.rr (ArmEnc.aluC op) d n m)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) d (JT.aluV op ((armSail.observe s).register n)
      ((armSail.observe s).register m) ((armSail.observe s).register 17))) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  show JT.GoesK armSail TT TT s (JT.setReg (obsS s) d (JT.aluV op ((obsS s).register n) ((obsS s).register m)
    ((obsS s).register 17)))
  rw [regS P hn, regS P hm, regS P (by decide : 17 < 31)]
  have hW := P.hm
  rcases (show op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [ArmEnc.aluC, ArmEnc.rr] at hW
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x8B000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by omega)
    have := full_addr P.hf P.ha P.hpc P.va P.al hW (by mask32) (by rw [ed]; omega) (by rw [en]; omega) (by rw [em]; omega)
    rw [ed, en, em] at this
    refine goes_set hd P.obs this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0xCB000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by omega)
    have := full_subr P.hf P.ha P.hpc P.va P.al hW (by mask32) (by rw [ed]; omega) (by rw [en]; omega) (by rw [em]; omega)
    rw [ed, en, em] at this
    refine goes_set hd P.obs this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x9B004400) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by omega)
    have ea : (Sail.BitVec.slice (wd (0x9B004400 + m * 2 ^ 16 + n * 2 ^ 5 + d)) 10 5).toNat = 17 := by fldt
    have := full_madd P.hf P.ha P.hpc P.va P.al hW (by mask32) (by rw [ed]; omega) (by rw [en]; omega) (by rw [em]; omega) (by rw [ea]; omega)
    rw [ed, en, em, ea] at this
    refine goes_set hd P.obs this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x8A000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by omega)
    have := full_andr P.hf P.ha P.hpc P.va P.al hW (by mask32) (by rw [ed]; omega) (by rw [en]; omega) (by rw [em]; omega)
    rw [ed, en, em] at this
    refine goes_set hd P.obs this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0xAA000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by omega)
    have := full_orrr P.hf P.ha P.hpc P.va P.al hW (by mask32) (by rw [ed]; omega) (by rw [en]; omega) (by rw [em]; omega)
    rw [ed, en, em] at this
    refine goes_set hd P.obs this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x9AC02000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by omega)
    have := full_lslv P.hf P.ha P.hpc P.va P.al hW (by mask32) (by rw [ed]; omega) (by rw [en]; omega) (by rw [em]; omega)
    rw [ed, en, em] at this
    refine goes_set hd P.obs this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV, UInt64.toBitVec_shiftLeft]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x9AC02400) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by omega)
    have := full_lsrv P.hf P.ha P.hpc P.va P.al hW (by mask32) (by rw [ed]; omega) (by rw [en]; omega) (by rw [em]; omega)
    rw [ed, en, em] at this
    refine goes_set hd P.obs this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV, UInt64.toBitVec_shiftRight]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0xCA000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide)
      (by decide) (by omega) (by omega) (by omega)
    have := full_eorr P.hf P.ha P.hpc P.va P.al hW (by mask32) (by rw [ed]; omega) (by rw [en]; omega) (by rw [em]; omega)
    rw [ed, en, em] at this
    refine goes_set hd P.obs this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV]

/-! ## branches -/

theorem sl26 (f : Int) : Sail.BitVec.slice (wd (0x14000000 + ArmEnc.mo f 26)) 0 26 = BitVec.ofNat 26 (ArmEnc.mo f 26) := by
  have := mo_lt f 26
  apply BitVec.eq_of_toNat_eq; simp [sl, Nat.shiftRight_eq_div_pow]; omega
theorem sl26l (f : Int) : Sail.BitVec.slice (wd (0x94000000 + ArmEnc.mo f 26)) 0 26 = BitVec.ofNat 26 (ArmEnc.mo f 26) := by
  have := mo_lt f 26
  apply BitVec.eq_of_toNat_eq; simp [sl, Nat.shiftRight_eq_div_pow]; omega

theorem F_b (s : St) (f : Int) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hf1 : -2 ^ 25 ≤ f) (hf2 : f < 2 ^ 25)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.bB f)) :
    JT.GoesK armSail TT TT s (JT.jumpTo (armSail.observe s) ((armSail.observe s).programCounter + 4 * UInt64.ofInt f)) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.bB] at hm
  have := full_b P.hf P.ha P.hpc P.va P.al hm (by have := mo_lt f 26; mask32)
  rw [sl26, sx2 _ (by decide), off26 f hf1 hf2] at this
  refine goes_jump P.obs this ?_
  show _ = (obsS s).programCounter + _
  rw [pcS P]; rfl

theorem F_bl (s : St) (f : Int) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hf1 : -2 ^ 25 ≤ f) (hf2 : f < 2 ^ 25)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.blB f)) :
    JT.GoesK armSail TT TT s ⟨(armSail.observe s).programCounter + 4 * UInt64.ofInt f,
      fun r => if r = 30 then (armSail.observe s).programCounter + 4 else (armSail.observe s).register r,
      (armSail.observe s).memory⟩ := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.blB] at hm
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_bl P.hf P.ha P.hpc P.va P.al hm (by have := mo_lt f 26; mask32)
  rw [sl26l, sx2 _ (by decide), off26 f hf1 hf2] at h4
  refine goes1 h1 h3 h4 ?_
  rw [obs_eq h2 h4, h5, gen_obsA (q := pc) (by decide)]
  show _ = (⟨(obsS s).programCounter + _, fun r => if r = 30 then (obsS s).programCounter + 4 else (obsS s).register r,
    (obsS s).memory⟩ : MachineState)
  rw [pcS P, P.obs]; rfl

theorem F_cbz (s : St) (r : Nat) (f : Int) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hr : r < 31) (hf1 : -2 ^ 18 ≤ f) (hf2 : f < 2 ^ 18)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.cbz r f)) :
    JT.GoesK armSail TT TT s (JT.jumpTo (armSail.observe s) (if (armSail.observe s).register r = 0
      then (armSail.observe s).programCounter + 4 * UInt64.ofInt f else (armSail.observe s).programCounter + 4)) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.cbz] at hm
  have hmo := mo_lt f 19
  have := full_cbz P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt)
  rw [show Sail.BitVec.slice (wd (0xB4000000 + ArmEnc.mo f 19 * 2 ^ 5 + r)) 5 19 = BitVec.ofNat 19 (ArmEnc.mo f 19) by
      apply BitVec.eq_of_toNat_eq; simp [sl, Nat.shiftRight_eq_div_pow]; omega,
    show (Sail.BitVec.slice (wd (0xB4000000 + ArmEnc.mo f 19 * 2 ^ 5 + r)) 0 5).toNat = r by fldt,
    sx2 _ (by decide), off19 f hf1 hf2] at this
  refine goes_jump P.obs this ?_
  show _ = if (obsS s).register r = 0 then (obsS s).programCounter + _ else (obsS s).programCounter + 4
  rw [regS P hr, pcS P]
  by_cases hz : a.x r = 0
  · rw [if_pos hz, if_pos (by rw [hz]; rfl)]; rfl
  · rw [if_neg hz, if_neg (fun h => hz (by have := congrArg UInt64.toBitVec h; simpa using this))]; rfl

theorem F_br (s : St) (n : Nat) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hn : n < 31)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.brR n)) :
    JT.GoesK armSail TT TT s (JT.jumpTo (armSail.observe s) ((armSail.observe s).register n)) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.brR] at hm
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_brB P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt)
  rw [show (Sail.BitVec.slice (wd (0xD61F0000 + n * 2 ^ 5)) 5 5).toNat = n by fldt] at h4
  exact goes1 h1 h3 h4 (by rw [obs_eq h2 h4, h5]; show _ = JT.jumpTo (obsS s) ((obsS s).register n); rw [regS P hn, P.obs]; rfl)

theorem F_cmpbr (s : St) (c n m : Nat) (f : Int) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 8) (hc4 : c < 4) (hn : n < 31) (hm : m < 31)
    (hf1 : -2 ^ 18 ≤ f) (hf2 : f < 2 ^ 18) (h8 : (armSail.observe s).programCounter.toNat + 8 ≤ armSail.ramEnd)
    (hw0 : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.subsR n m))
    (hw1 : JT.WordAt (armSail.observe s) ((armSail.observe s).programCounter.toNat + 4) (ArmEnc.bc c f)) :
    JT.GoesK armSail TT TT s ⟨if JT.condV c ((armSail.observe s).register n) ((armSail.observe s).register m)
        then (armSail.observe s).programCounter + 4 + 4 * UInt64.ofInt f else (armSail.observe s).programCounter + 8,
      fun r => if r = 16 then (armSail.observe s).register n - (armSail.observe s).register m
        else (armSail.observe s).register r, (armSail.observe s).memory⟩ := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw0
  have hW0 := P.hm; simp only [ArmEnc.subsR] at hW0
  obtain ⟨ed, en, em⟩ := rr_f (c := 0xEB000000) (d := 16) (n := n) (m := m) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  obtain ⟨s1, h1, a1, f1, p1, m1⟩ := full_subsr P.hf P.ha P.hpc P.va P.al hW0 (by mask32) (by rw [ed]; omega) (by rw [en]; omega) (by rw [em]; omega)
  rw [ed, en, em] at a1
  -- the second word, at pc + 4, read from the same memory
  have e0 : (obsS s).programCounter.toNat = pc.toNat := by rw [pcS P]; rfl
  have h8' : pc.toNat + 8 ≤ 3 * 2 ^ 30 := by have := h8; simp only [armSail] at this; show _ ≤ _; rw [← e0]; exact this
  have e4 : (pc + 4).toNat = pc.toNat + 4 := by simp [BitVec.toNat_add]; omega
  have hW1 : MemWord s1.mem (pc + 4).toNat (wd (ArmEnc.bc c f)) := by
    have hw1' : JT.WordAt (obsS s) (pc.toNat + 4) (ArmEnc.bc c f) := by
      have := hw1; rw [show (armSail.observe s).programCounter.toNat = pc.toNat from e0] at this; exact this
    rw [m1, e4]; exact memword (by omega) hw1'
  simp only [ArmEnc.bc] at hW1
  have hmo := mo_lt f 19
  obtain ⟨p, hpp, hN, hZ, hC, hV⟩ := a1.p
  obtain ⟨s2, h2, a2, f2, p2, m2⟩ := full_bc f1 a1 p1 (vaRam (by rw [e4]; have := P.lo; omega) (by rw [e4]; omega)) (by rw [e4]; have := P.al; omega)
    hW1 (by mask32) hpp
  rw [condP_abs _ hN hZ hC hV,
    show Sail.BitVec.slice (wd (0x54000000 + ArmEnc.mo f 19 * 2 ^ 5 + c)) 0 4 = BitVec.ofNat 4 c by
      apply BitVec.eq_of_toNat_eq; simp [sl, Nat.shiftRight_eq_div_pow]; omega,
    show Sail.BitVec.slice (wd (0x54000000 + ArmEnc.mo f 19 * 2 ^ 5 + c)) 5 19 = BitVec.ofNat 19 (ArmEnc.mo f 19) by
      apply BitVec.eq_of_toNat_eq; simp [sl, Nat.shiftRight_eq_div_pow]; omega,
    sx2 _ (by decide), off19 f hf1 hf2] at p2
  have hcs := cond_sub a c hc4 (UInt64.ofBitVec (a.x n)) (UInt64.ofBitVec (a.x m)) (a.x n - a.x m)
  simp only [UInt64.toBitVec_ofBitVec] at hcs
  rw [hcs] at p2
  refine goes2 h1 h2 f2 p2 ?_
  rw [obs_eq a2 p2, m2, m1, gen_obsA (q := pc) (by decide)]
  show _ = (⟨if JT.condV c ((obsS s).register n) ((obsS s).register m) then (obsS s).programCounter + 4 + _
      else (obsS s).programCounter + 8,
    fun r => if r = 16 then (obsS s).register n - (obsS s).register m else (obsS s).register r, (obsS s).memory⟩ :
      MachineState)
  rw [regS P hn, regS P hm, pcS P, P.obs]
  congr 1
  by_cases hcv : JT.condV c (UInt64.ofBitVec (a.x n)) (UInt64.ofBitVec (a.x m)) = true
  · simp only [hcv, ite_true]; apply UInt64.toBitVec_inj.mp; simp [BitVec.add_assoc]
  · simp only [hcv, ite_false, Bool.false_eq_true]; apply UInt64.toBitVec_inj.mp; simp [BitVec.add_assoc]

/-! ## loads and stores -/

theorem mget_insert (m : Mem) (k : Nat) (v : BitVec 8) (a : Nat) :
    (m.insert k v).get? a = if k == a then some v else m.get? a := Std.ExtHashMap.getElem?_insert

theorem cbyte_bv (v : UInt64) (k : Nat) (hk : k < 8) : (JT.cbyte v k).toBitVec = v.toBitVec.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [JT.cbyte, UInt64.toBitVec_shiftRight, BitVec.getLsbD_extractLsb', show 8 * k % 64 = 8 * k by omega, hi]

/-- the effective address `x + imm·2^k` of an unsigned-offset word, as a number -/
theorem ea_toNat (x : BitVec 64) (q k : Nat) (hk : k ≤ 3) (hq : q < 4096) (hl : x.toNat + q * 2 ^ k < 2 ^ 64) :
    (x + BitVec.ofNat 64 q <<< k).toNat = x.toNat + q * 2 ^ k := by
  have : q * 2 ^ k < 2 ^ 64 := by omega
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt this]
  omega

theorem F_ldr (s : St) (r n f : Nat) (v : UInt64) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hr : r < 31) (hn : n < 31) (hf8 : f % 8 = 0) (hf : f < 32768)
    (hl : ((armSail.observe s).register n).toNat + f < 2 ^ 64)
    (hal : (((armSail.observe s).register n).toNat + f) % 8 = 0)
    (hlo : armSail.ramStart ≤ ((armSail.observe s).register n).toNat + f)
    (hhi : ((armSail.observe s).register n).toNat + f + 8 ≤ armSail.ramEnd)
    (hW : ∀ k < 8, TT s (((armSail.observe s).register n).toNat + f + k))
    (hv : ∀ k < 8, (armSail.observe s).memory (UInt64.ofNat (((armSail.observe s).register n).toNat + f + k)) =
      some (JT.cbyte v k))
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.ldr r n f)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) r v) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have er : ((obsS s).register n).toNat = (a.x n).toNat := by rw [regS P hn]; rfl
  change ((obsS s).register n).toNat + f < 2 ^ 64 at hl
  change (((obsS s).register n).toNat + f) % 8 = 0 at hal
  change 2 ^ 31 ≤ ((obsS s).register n).toNat + f at hlo
  change ((obsS s).register n).toNat + f + 8 ≤ 3 * 2 ^ 30 at hhi
  change ∀ k < 8, (obsS s).memory (UInt64.ofNat (((obsS s).register n).toNat + f + k)) = some (JT.cbyte v k) at hv
  rw [er] at hl hal hlo hhi hv
  have hm := P.hm; simp only [ArmEnc.ldr] at hm
  have ee : (a.x n + (Sail.BitVec.slice (wd (0xF9400000 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + r)) 10 12).setWidth 64 <<< 3).toNat =
      (a.x n).toNat + f := by
    rw [show (Sail.BitVec.slice (wd (0xF9400000 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + r)) 10 12).setWidth 64 =
      BitVec.ofNat 64 (f / 8) by immt, ea_toNat _ _ 3 (by decide) (by omega) (by omega)]
    omega
  have := full_ldr P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt) (by fldt) (v := v.toBitVec)
    (by rw [show (Sail.BitVec.slice (wd (0xF9400000 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + r)) 5 5).toNat = n by fldt, ee]
        exact vaRam hlo (by omega))
    (by rw [show (Sail.BitVec.slice (wd (0xF9400000 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + r)) 5 5).toNat = n by fldt, ee]
        exact hal)
    (by rw [show (Sail.BitVec.slice (wd (0xF9400000 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + r)) 5 5).toNat = n by fldt, ee]
        intro k hk; rw [byte_obs (by omega) (hv k hk), cbyte_bv _ _ hk])
  rw [show (Sail.BitVec.slice (wd (0xF9400000 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + r)) 0 5).toNat = r by fldt] at this
  exact goes_set hr P.obs this rfl

theorem F_ldrb (s : St) (r n f : Nat) (b : UInt8) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hr : r < 31) (hn : n < 31) (hf : f < 4096)
    (hl : ((armSail.observe s).register n).toNat + f < 2 ^ 64)
    (hlo : armSail.ramStart ≤ ((armSail.observe s).register n).toNat + f)
    (hhi : ((armSail.observe s).register n).toNat + f < armSail.ramEnd)
    (hW : TT s (((armSail.observe s).register n).toNat + f))
    (hv : (armSail.observe s).memory (UInt64.ofNat (((armSail.observe s).register n).toNat + f)) = some b)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.ldrb r n f)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) r b.toUInt64) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have er : ((obsS s).register n).toNat = (a.x n).toNat := by rw [regS P hn]; rfl
  change ((obsS s).register n).toNat + f < 2 ^ 64 at hl
  change 2 ^ 31 ≤ ((obsS s).register n).toNat + f at hlo
  change ((obsS s).register n).toNat + f < 3 * 2 ^ 30 at hhi
  change (obsS s).memory (UInt64.ofNat (((obsS s).register n).toNat + f)) = some b at hv
  rw [er] at hl hlo hhi hv
  have hm := P.hm; simp only [ArmEnc.ldrb] at hm
  have ee : (a.x n + (Sail.BitVec.slice (wd (0x39400000 + f * 2 ^ 10 + n * 2 ^ 5 + r)) 10 12).setWidth 64).toNat =
      (a.x n).toNat + f := by
    rw [show (Sail.BitVec.slice (wd (0x39400000 + f * 2 ^ 10 + n * 2 ^ 5 + r)) 10 12).setWidth 64 =
      BitVec.ofNat 64 f by immt]
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt (show f < 2 ^ 64 by omega)]; omega
  have en : (Sail.BitVec.slice (wd (0x39400000 + f * 2 ^ 10 + n * 2 ^ 5 + r)) 5 5).toNat = n := by fldt
  have := full_ldrb P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt) (by fldt) (b := b.toBitVec)
    (by rw [en, ee]; exact vaRam hlo (by omega)) (by rw [en, ee]; exact byte_obs (by omega) hv)
  rw [show (Sail.BitVec.slice (wd (0x39400000 + f * 2 ^ 10 + n * 2 ^ 5 + r)) 0 5).toNat = r by fldt] at this
  exact goes_set hr P.obs this (by apply UInt64.toBitVec_inj.mp; simp)

theorem wrD_get (m : Mem) (e : Nat) (v : BitVec 64) (i : Nat) :
    (wrD m e v).get? i = if e ≤ i ∧ i < e + 8 then some (v.extractLsb' (8 * (i - e)) 8) else m.get? i := by
  have hw : wrD m e v = ((((((((m.insert (e + 0) (v.extractLsb' (8 * 0) 8)).insert (e + 1) (v.extractLsb' (8 * 1) 8)).insert
      (e + 2) (v.extractLsb' (8 * 2) 8)).insert (e + 3) (v.extractLsb' (8 * 3) 8)).insert (e + 4) (v.extractLsb' (8 * 4) 8)).insert
      (e + 5) (v.extractLsb' (8 * 5) 8)).insert (e + 6) (v.extractLsb' (8 * 6) 8)).insert (e + 7) (v.extractLsb' (8 * 7) 8)) := rfl
  rw [hw]; simp only [mget_insert]
  by_cases hi : e ≤ i ∧ i < e + 8
  · rw [if_pos hi]
    obtain ⟨k, rfl⟩ : ∃ k, i = e + k := ⟨i - e, by omega⟩
    have hk : k < 8 := by omega
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · rw [if_neg hi]
    have : ∀ k < 8, (e + k == i) = false := fun k hk => by simp; omega
    simp only [this 0 (by decide), this 1 (by decide), this 2 (by decide), this 3 (by decide), this 4 (by decide),
      this 5 (by decide), this 6 (by decide), this 7 (by decide), Bool.false_eq_true, ite_false]

theorem F_str (s : St) (r n f : Nat) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hr : r < 31) (hn : n < 31) (hf8 : f % 8 = 0) (hf : f < 32768)
    (hl : ((armSail.observe s).register n).toNat + f < 2 ^ 64)
    (hal : (((armSail.observe s).register n).toNat + f) % 8 = 0)
    (hlo : armSail.ramStart ≤ ((armSail.observe s).register n).toNat + f)
    (hhi : ((armSail.observe s).register n).toNat + f + 8 ≤ armSail.ramEnd)
    (hW : ∀ k < 8, TT s (((armSail.observe s).register n).toNat + f + k))
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.str r n f)) :
    JT.GoesK armSail TT TT s (JT.store8 (armSail.observe s) (((armSail.observe s).register n).toNat + f)
      ((armSail.observe s).register r)) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have er : ((obsS s).register n).toNat = (a.x n).toNat := by rw [regS P hn]; rfl
  change ((obsS s).register n).toNat + f < 2 ^ 64 at hl
  change (((obsS s).register n).toNat + f) % 8 = 0 at hal
  change 2 ^ 31 ≤ ((obsS s).register n).toNat + f at hlo
  change ((obsS s).register n).toNat + f + 8 ≤ 3 * 2 ^ 30 at hhi
  show JT.GoesK armSail TT TT s (JT.store8 (obsS s) (((obsS s).register n).toNat + f) ((obsS s).register r))
  rw [er] at hl hal hlo hhi ⊢
  rw [regS P hr]
  have hm := P.hm; simp only [ArmEnc.str] at hm
  have ee : (a.x n + (Sail.BitVec.slice (wd (0xF9000000 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + r)) 10 12).setWidth 64 <<< 3).toNat =
      (a.x n).toNat + f := by
    rw [show (Sail.BitVec.slice (wd (0xF9000000 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + r)) 10 12).setWidth 64 =
      BitVec.ofNat 64 (f / 8) by immt, ea_toNat _ _ 3 (by decide) (by omega) (by omega)]
    omega
  have en : (Sail.BitVec.slice (wd (0xF9000000 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + r)) 5 5).toNat = n := by fldt
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_str P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt) (by fldt)
    (by rw [en, ee]; exact vaRam hlo (by omega)) (by rw [en, ee]; exact hal)
  rw [en, ee, show (Sail.BitVec.slice (wd (0xF9000000 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + r)) 0 5).toNat = r by fldt] at h5
  refine goes1 h1 h3 h4 ?_
  rw [obs_eq h2 h4, h5, P.obs]
  simp only [obsA, JT.store8]
  congr 1
  funext u
  rw [wrD_get]
  split
  · rename_i hu
    simp only [Option.map_some, Option.some.injEq]
    apply UInt8.toBitVec_inj.mp
    rw [cbyte_bv _ _ (by omega)]
  · rfl

theorem F_strb (s : St) (r n f : Nat) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hr : r < 31) (hn : n < 31) (hf : f < 4096)
    (hl : ((armSail.observe s).register n).toNat + f < 2 ^ 64)
    (hlo : armSail.ramStart ≤ ((armSail.observe s).register n).toNat + f)
    (hhi : ((armSail.observe s).register n).toNat + f < armSail.ramEnd)
    (hW : TT s (((armSail.observe s).register n).toNat + f))
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.strb r n f)) :
    JT.GoesK armSail TT TT s (JT.store1 (armSail.observe s) (((armSail.observe s).register n).toNat + f)
      ((armSail.observe s).register r)) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have er : ((obsS s).register n).toNat = (a.x n).toNat := by rw [regS P hn]; rfl
  change ((obsS s).register n).toNat + f < 2 ^ 64 at hl
  change 2 ^ 31 ≤ ((obsS s).register n).toNat + f at hlo
  change ((obsS s).register n).toNat + f < 3 * 2 ^ 30 at hhi
  show JT.GoesK armSail TT TT s (JT.store1 (obsS s) (((obsS s).register n).toNat + f) ((obsS s).register r))
  rw [er] at hl hlo hhi ⊢
  rw [regS P hr]
  have hm := P.hm; simp only [ArmEnc.strb] at hm
  have ee : (a.x n + (Sail.BitVec.slice (wd (0x39000000 + f * 2 ^ 10 + n * 2 ^ 5 + r)) 10 12).setWidth 64).toNat =
      (a.x n).toNat + f := by
    rw [show (Sail.BitVec.slice (wd (0x39000000 + f * 2 ^ 10 + n * 2 ^ 5 + r)) 10 12).setWidth 64 =
      BitVec.ofNat 64 f by immt]
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt (show f < 2 ^ 64 by omega)]; omega
  have en : (Sail.BitVec.slice (wd (0x39000000 + f * 2 ^ 10 + n * 2 ^ 5 + r)) 5 5).toNat = n := by fldt
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_strb P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt) (by fldt)
    (by rw [en, ee]; exact vaRam hlo (by omega))
  rw [en, ee, show (Sail.BitVec.slice (wd (0x39000000 + f * 2 ^ 10 + n * 2 ^ 5 + r)) 0 5).toNat = r by fldt] at h5
  refine goes1 h1 h3 h4 ?_
  rw [obs_eq h2 h4, h5, P.obs]
  simp only [obsA, JT.store1]
  congr 1
  funext u
  rw [mget_insert]
  by_cases hu : u.toNat = (a.x n).toNat + f
  · rw [if_pos (by simp [hu]), if_pos hu]
    simp only [Option.map_some, Option.some.injEq]
    apply UInt8.toBitVec_inj.mp; simp
  · rw [if_neg (by simp; omega), if_neg hu]

end ArmSail
