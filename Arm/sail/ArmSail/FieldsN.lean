/- The nine `A64SemN` fields beyond `A64Sem` (Nano/Run/A64SemN.lean: the native back end's extra forms) on
`armSail`, from the Sail full steps of Arm/proofs/Arm/FullNative.lean (`full_movn`, `full_add3`, `full_ubfm`,
`full_ldrbR`, `full_ldp`, `full_ldurB`) and the existing `full_movz`, `full_cbnz`, `full_stur`. Same recipe as
Fields.lean: `pre`, encoding facts (`mask32`, `fldt`, `immt`, offsets), `goes_set` / `goes_jump` / `goes1`. -/
import ArmSail.Fields
import Arm.FullNative
import Nano.Run.A64SemN
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open Sail
namespace ArmSail
open Proven.Top ArmProof

/-! ## moves, shifted add, lsl -/

theorem F_movzH (s : St) (d i h : Nat) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hd : d < 31) (hi : i < 2 ^ 16) (hh : h < 4)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.movzH d i h)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) d ((UInt64.ofNat i) <<< (16 * h).toUInt64)) := by
  obtain ⟨n, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.movzH] at hm
  have := full_movz P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt)
  rw [show (Sail.BitVec.slice (wd (0xD2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)) 0 5).toNat = d by fldt,
    show (Sail.BitVec.slice (wd (0xD2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)) 21 2).toNat = h by fldt,
    show (Sail.BitVec.slice (wd (0xD2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)) 5 16).setWidth 64 = BitVec.ofNat 64 i by immt] at this
  refine goes_set hd P.obs this ?_
  apply UInt64.toBitVec_inj.mp
  simp [UInt64.toBitVec_shiftLeft, Nat.mul_comm, show 16 * h % 64 = 16 * h by omega, show h * 16 % 64 = h * 16 by omega]
  rfl

/-- `movn`'s value, as `A64SemN` writes it -/
theorem movn_val (i h : Nat) (hh : h < 4) :
    UInt64.ofBitVec (~~~(BitVec.ofNat 64 i <<< (h * 16))) = JT.movnV i h := by
  apply UInt64.toBitVec_inj.mp
  simp [JT.movnV, UInt64.toBitVec_shiftLeft, Nat.mul_comm, show 16 * h % 64 = 16 * h by omega, show h * 16 % 64 = h * 16 by omega]
  rfl

theorem F_movn (s : St) (d i h : Nat) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hd : d < 31) (hi : i < 2 ^ 16) (hh : h < 4)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.movn d i h)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) d (JT.movnV i h)) := by
  obtain ⟨n, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.movn] at hm
  have := full_movn P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt)
  rw [show (Sail.BitVec.slice (wd (0x92800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)) 0 5).toNat = d by fldt,
    show (Sail.BitVec.slice (wd (0x92800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)) 21 2).toNat = h by fldt,
    show (Sail.BitVec.slice (wd (0x92800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)) 5 16).setWidth 64 = BitVec.ofNat 64 i by immt] at this
  exact goes_set hd P.obs this (movn_val i h hh)

theorem F_addLsl3 (s : St) (d n m : Nat) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hd : d < 31) (hn : n < 31) (hm' : m < 31)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.addLsl3 d n m)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) d
      ((armSail.observe s).register n + ((armSail.observe s).register m <<< 3))) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.addLsl3] at hm
  have := full_add3 P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt) (by fldt) (by fldt)
  rw [show (Sail.BitVec.slice (wd (0x8B000C00 + m * 2 ^ 16 + n * 2 ^ 5 + d)) 0 5).toNat = d by fldt,
    show (Sail.BitVec.slice (wd (0x8B000C00 + m * 2 ^ 16 + n * 2 ^ 5 + d)) 5 5).toNat = n by fldt,
    show (Sail.BitVec.slice (wd (0x8B000C00 + m * 2 ^ 16 + n * 2 ^ 5 + d)) 16 5).toNat = m by fldt] at this
  refine goes_set hd P.obs this ?_
  show _ = (obsS s).register n + ((obsS s).register m <<< 3)
  rw [regS P hn, regS P hm']
  apply UInt64.toBitVec_inj.mp
  simp [UInt64.toBitVec_shiftLeft]

theorem F_lslI (s : St) (d n sh : Nat) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hd : d < 31) (hn : n < 31) (h1 : 0 < sh) (h2 : sh < 64)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.lslI d n sh)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) d ((armSail.observe s).register n <<< sh.toUInt64)) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.lslI] at hm
  have : (64 - sh) % 64 < 64 := Nat.mod_lt _ (by decide)
  have : 63 - sh < 64 := by omega
  have := full_ubfm P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt) (by fldt) sh h1 h2
    (by apply BitVec.eq_of_toNat_eq; rw [fld, BitVec.toNat_ofNat]; omega)
    (by apply BitVec.eq_of_toNat_eq; rw [fld, BitVec.toNat_ofNat]; omega)
  rw [show (Sail.BitVec.slice (wd (0xD3400000 + (64 - sh) % 64 * 2 ^ 16 + (63 - sh) * 2 ^ 10 + n * 2 ^ 5 + d)) 0 5).toNat = d by fldt,
    show (Sail.BitVec.slice (wd (0xD3400000 + (64 - sh) % 64 * 2 ^ 16 + (63 - sh) * 2 ^ 10 + n * 2 ^ 5 + d)) 5 5).toNat = n by fldt] at this
  refine goes_set hd P.obs this ?_
  show _ = (obsS s).register n <<< sh.toUInt64
  rw [regS P hn]
  apply UInt64.toBitVec_inj.mp
  simp [UInt64.toBitVec_shiftLeft, Nat.mod_eq_of_lt h2]

/-! ## cbnz -/

theorem F_cbnz (s : St) (r : Nat) (f : Int) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hr : r < 31) (hf1 : -2 ^ 18 ≤ f) (hf2 : f < 2 ^ 18)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.cbnz r f)) :
    JT.GoesK armSail TT TT s (JT.jumpTo (armSail.observe s) (if (armSail.observe s).register r = 0
      then (armSail.observe s).programCounter + 4 else (armSail.observe s).programCounter + 4 * UInt64.ofInt f)) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have hm := P.hm; simp only [ArmEnc.cbnz] at hm
  have hmo := mo_lt f 19
  have := full_cbnz P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt)
  rw [show Sail.BitVec.slice (wd (0xB5000000 + ArmEnc.mo f 19 * 2 ^ 5 + r)) 5 19 = BitVec.ofNat 19 (ArmEnc.mo f 19) by
      apply BitVec.eq_of_toNat_eq; simp [sl, Nat.shiftRight_eq_div_pow]; omega,
    show (Sail.BitVec.slice (wd (0xB5000000 + ArmEnc.mo f 19 * 2 ^ 5 + r)) 0 5).toNat = r by fldt,
    sx2 _ (by decide), off19 f hf1 hf2] at this
  refine goes_jump P.obs this ?_
  show _ = if (obsS s).register r = 0 then (obsS s).programCounter + 4 else (obsS s).programCounter + _
  rw [regS P hr, pcS P]
  by_cases hz : a.x r = 0
  · rw [if_pos hz, if_pos (by rw [hz]; rfl)]; rfl
  · rw [if_neg hz, if_neg (fun h => hz (by have := congrArg UInt64.toBitVec h; simpa using this))]; rfl


/-! ## unscaled, pair and register-offset loads; unscaled store -/

/-- the 9-bit signed offset field -/
theorem mo9 (f : Int) (h1 : -256 ≤ f) (h2 : f < 256) : ArmEnc.mo f 9 = if 0 ≤ f then f.toNat else 512 - f.natAbs := by
  unfold ArmEnc.mo; split <;> simp only [Nat.reducePow] <;> omega

/-- the effective address `x + simm9` of an unscaled word -/
theorem eauS {c d n a : Nat} {f : Int} (x : BitVec 64) (hc : c < 2 ^ 32) (hc0 : c % 2 ^ 21 = 0) (hn : n < 32)
    (hd : d < 32) (h1 : -256 ≤ f) (h2 : f < 256) (ha : (a : Int) = x.toNat + f) (hl : a < 2 ^ 64) :
    (x + (Sail.BitVec.slice (wd (c + ArmEnc.mo f 9 * 2 ^ 12 + n * 2 ^ 5 + d)) 12 9).signExtend 64).toNat = a := by
  have hm : ArmEnc.mo f 9 < 2 ^ 9 := mo_lt f 9
  rw [show Sail.BitVec.slice (wd (c + ArmEnc.mo f 9 * 2 ^ 12 + n * 2 ^ 5 + d)) 12 9 = BitVec.ofNat 9 (ArmEnc.mo f 9) by
      apply BitVec.eq_of_toNat_eq; simp [sl, Nat.shiftRight_eq_div_pow]; omega]
  have hx := x.isLt
  rw [BitVec.toNat_add, BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [mo9 f h1 h2] at hm ⊢
  by_cases h0 : 0 ≤ f
  · simp only [h0, ite_true] at hm ⊢
    simp only [show ¬ 2 ^ (9 - 1) ≤ f.toNat % 2 ^ 9 by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
    omega
  · simp only [h0, ite_false] at hm ⊢
    simp only [show 2 ^ (9 - 1) ≤ (512 - f.natAbs) % 2 ^ 9 by omega, decide_true, ↓reduceIte]
    omega

theorem F_ldur (s : St) (r n a : Nat) (f : Int) (v : UInt64) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hr : r < 31) (hn : n < 31) (hf1 : -256 ≤ f) (hf2 : f < 256)
    (ha : (a : Int) = ((armSail.observe s).register n).toNat + f) (hal : a % 8 = 0)
    (hlo : armSail.ramStart ≤ a) (hhi : a + 8 ≤ armSail.ramEnd) (hW : ∀ k < 8, TT s (a + k))
    (hv : ∀ k < 8, (armSail.observe s).memory (UInt64.ofNat (a + k)) = some (JT.cbyte v k))
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.ldur r n f)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) r v) := by
  obtain ⟨nb, a', pc, P⟩ := pre hc hp hw
  have er : ((obsS s).register n).toNat = (a'.x n).toNat := by rw [regS P hn]; rfl
  change (a : Int) = ((obsS s).register n).toNat + f at ha
  change 2 ^ 31 ≤ a at hlo
  change a + 8 ≤ 3 * 2 ^ 30 at hhi
  change ∀ k < 8, (obsS s).memory (UInt64.ofNat (a + k)) = some (JT.cbyte v k) at hv
  rw [er] at ha
  have hm := P.hm; simp only [ArmEnc.ldur] at hm
  have hmo9 := mo_lt f 9
  have ee := eauS (c := 0xF8400000) (d := r) (n := n) (a := a) (f := f) (a'.x n) (by decide) (by decide) (by omega) (by omega)
    hf1 hf2 ha (by omega)
  have en : (Sail.BitVec.slice (wd (0xF8400000 + ArmEnc.mo f 9 * 2 ^ 12 + n * 2 ^ 5 + r)) 5 5).toNat = n := by
    have := mo_lt f 9; fldt
  have := full_ldurB P.hf P.ha P.hpc P.va P.al hm (by mask32) (by have := mo_lt f 9; fldt) (by rw [en]; omega)
    (v := v.toBitVec) (by rw [en, ee]; exact vaRam hlo (by omega)) (by rw [en, ee]; exact hal)
    (by rw [en, ee]; intro k hk; rw [byte_obs (by omega) (hv k hk), cbyte_bv _ _ hk])
  rw [show (Sail.BitVec.slice (wd (0xF8400000 + ArmEnc.mo f 9 * 2 ^ 12 + n * 2 ^ 5 + r)) 0 5).toNat = r by
    have := mo_lt f 9; fldt] at this
  exact goes_set hr P.obs this rfl

theorem F_stur (s : St) (r n e : Nat) (f : Int) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (hr : r < 31) (hn : n < 31) (hf1 : -256 ≤ f) (hf2 : f < 256)
    (ha : (e : Int) = ((armSail.observe s).register n).toNat + f) (hal : e % 8 = 0)
    (hlo : armSail.ramStart ≤ e) (hhi : e + 8 ≤ armSail.ramEnd) (hW : ∀ k < 8, TT s (e + k))
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.stur r n f)) :
    JT.GoesK armSail TT TT s (JT.store8 (armSail.observe s) e ((armSail.observe s).register r)) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have er : ((obsS s).register n).toNat = (a.x n).toNat := by rw [regS P hn]; rfl
  change (e : Int) = ((obsS s).register n).toNat + f at ha
  change 2 ^ 31 ≤ e at hlo
  change e + 8 ≤ 3 * 2 ^ 30 at hhi
  show JT.GoesK armSail TT TT s (JT.store8 (obsS s) e ((obsS s).register r))
  rw [er] at ha
  rw [regS P hr]
  have hm := P.hm; simp only [ArmEnc.stur] at hm
  have hmo9 := mo_lt f 9
  have ee := eauS (c := 0xF8000000) (d := r) (n := n) (a := e) (f := f) (a.x n) (by decide) (by decide) (by omega) (by omega)
    hf1 hf2 ha (by omega)
  have en : (Sail.BitVec.slice (wd (0xF8000000 + ArmEnc.mo f 9 * 2 ^ 12 + n * 2 ^ 5 + r)) 5 5).toNat = n := by
    have := mo_lt f 9; fldt
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_stur P.hf P.ha P.hpc P.va P.al hm (by mask32) (by have := mo_lt f 9; fldt)
    (by rw [en]; omega) (by rw [en, ee]; exact vaRam hlo (by omega)) (by rw [en, ee]; exact hal)
  rw [en, ee, show (Sail.BitVec.slice (wd (0xF8000000 + ArmEnc.mo f 9 * 2 ^ 12 + n * 2 ^ 5 + r)) 0 5).toNat = r by
    have := mo_lt f 9; fldt] at h5
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

theorem F_ldrbR (s : St) (t n m : Nat) (b : UInt8) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (ht : t < 31) (hn : n < 31) (hm' : m < 31)
    (hlo : armSail.ramStart ≤ ((armSail.observe s).register n + (armSail.observe s).register m).toNat)
    (hhi : ((armSail.observe s).register n + (armSail.observe s).register m).toNat < armSail.ramEnd)
    (hW : TT s (((armSail.observe s).register n + (armSail.observe s).register m).toNat))
    (hv : (armSail.observe s).memory (UInt64.ofNat (((armSail.observe s).register n + (armSail.observe s).register m).toNat)) = some b)
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.ldrbR t n m)) :
    JT.GoesK armSail TT TT s (JT.setReg (armSail.observe s) t b.toUInt64) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have er : ((obsS s).register n + (obsS s).register m).toNat = (a.x n + a.x m).toNat := by
    rw [regS P hn, regS P hm']; rfl
  change 2 ^ 31 ≤ ((obsS s).register n + (obsS s).register m).toNat at hlo
  change ((obsS s).register n + (obsS s).register m).toNat < 3 * 2 ^ 30 at hhi
  change (obsS s).memory (UInt64.ofNat (((obsS s).register n + (obsS s).register m).toNat)) = some b at hv
  rw [er] at hlo hhi hv
  have hm := P.hm; simp only [ArmEnc.ldrbR] at hm
  have en : (Sail.BitVec.slice (wd (0x38606800 + m * 2 ^ 16 + n * 2 ^ 5 + t)) 5 5).toNat = n := by fldt
  have em : (Sail.BitVec.slice (wd (0x38606800 + m * 2 ^ 16 + n * 2 ^ 5 + t)) 16 5).toNat = m := by fldt
  have := full_ldrbR P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt) (by fldt) (by fldt) (b := b.toBitVec)
    (by rw [en, em]; exact vaRam hlo (by omega)) (by rw [en, em]; exact byte_obs (by omega) hv)
  rw [show (Sail.BitVec.slice (wd (0x38606800 + m * 2 ^ 16 + n * 2 ^ 5 + t)) 0 5).toNat = t by fldt] at this
  exact goes_set ht P.obs this (by apply UInt64.toBitVec_inj.mp; simp)

theorem F_ldp (s : St) (t u n : Nat) (v1 v2 : UInt64) (hc : armSail.configured s) (hp : JT.PcOK armSail (armSail.observe s))
    (hx : JT.FetchX armSail TT s 4) (ht : t < 31) (hu : u < 31) (hn : n < 31) (htu : t ≠ u)
    (hal : ((armSail.observe s).register n).toNat % 8 = 0)
    (hlo : armSail.ramStart ≤ ((armSail.observe s).register n).toNat)
    (hhi : ((armSail.observe s).register n).toNat + 16 ≤ armSail.ramEnd)
    (hW : ∀ k < 16, TT s (((armSail.observe s).register n).toNat + k))
    (hv1 : ∀ k < 8, (armSail.observe s).memory (UInt64.ofNat (((armSail.observe s).register n).toNat + k)) = some (JT.cbyte v1 k))
    (hv2 : ∀ k < 8, (armSail.observe s).memory (UInt64.ofNat (((armSail.observe s).register n).toNat + 8 + k)) = some (JT.cbyte v2 k))
    (hw : JT.WordAt (armSail.observe s) (armSail.observe s).programCounter.toNat (ArmEnc.ldp t u n)) :
    JT.GoesK armSail TT TT s (JT.setReg2 (armSail.observe s) t u v1 v2) := by
  obtain ⟨nb, a, pc, P⟩ := pre hc hp hw
  have er : ((obsS s).register n).toNat = (a.x n).toNat := by rw [regS P hn]; rfl
  change ((obsS s).register n).toNat % 8 = 0 at hal
  change 2 ^ 31 ≤ ((obsS s).register n).toNat at hlo
  change ((obsS s).register n).toNat + 16 ≤ 3 * 2 ^ 30 at hhi
  change ∀ k < 8, (obsS s).memory (UInt64.ofNat (((obsS s).register n).toNat + k)) = some (JT.cbyte v1 k) at hv1
  change ∀ k < 8, (obsS s).memory (UInt64.ofNat (((obsS s).register n).toNat + 8 + k)) = some (JT.cbyte v2 k) at hv2
  rw [er] at hal hlo hhi hv1 hv2
  have e8 : (a.x n + 8#64).toNat = (a.x n).toNat + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  have hm := P.hm; simp only [ArmEnc.ldp] at hm
  have en : (Sail.BitVec.slice (wd (0xA9400000 + u * 2 ^ 10 + n * 2 ^ 5 + t)) 5 5).toNat = n := by fldt
  have := full_ldp P.hf P.ha P.hpc P.va P.al hm (by mask32) (by fldt) (by fldt) (by fldt)
    (by rw [show (Sail.BitVec.slice (wd (0xA9400000 + u * 2 ^ 10 + n * 2 ^ 5 + t)) 0 5).toNat = t by fldt,
          show (Sail.BitVec.slice (wd (0xA9400000 + u * 2 ^ 10 + n * 2 ^ 5 + t)) 10 5).toNat = u by fldt]; exact htu)
    (by apply BitVec.eq_of_toNat_eq; rw [fld]; simp; omega)
    (v1 := v1.toBitVec) (v2 := v2.toBitVec)
    (by rw [en]; exact vaRam hlo (by omega)) (by rw [en]; exact hal)
    (by rw [en]; intro k hk; rw [byte_obs (by omega) (hv1 k hk), cbyte_bv _ _ hk])
    (by rw [en, e8]; exact vaRam (by omega) (by omega)) (by rw [en, e8]; omega)
    (by rw [en, e8]; intro k hk; rw [show (a.x n).toNat + 8 + k = (a.x n).toNat + 8 + k from rfl,
          byte_obs (by omega) (hv2 k hk), cbyte_bv _ _ hk])
  rw [show (Sail.BitVec.slice (wd (0xA9400000 + u * 2 ^ 10 + n * 2 ^ 5 + t)) 0 5).toNat = t by fldt,
    show (Sail.BitVec.slice (wd (0xA9400000 + u * 2 ^ 10 + n * 2 ^ 5 + t)) 10 5).toNat = u by fldt] at this
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := this
  refine goes1 h1 h3 h4 ?_
  rw [obs_eq h2 h4, h5]
  change _ = JT.setReg2 (obsS s) t u v1 v2
  rw [P.obs]
  simp only [obsA, JT.setReg2]
  congr 1
  · funext r
    by_cases eu : r = u
    · subst eu; simp [hu, AState.setX, show r ≠ 31 by omega]
    · by_cases et : r = t
      · subst et; simp [ht, eu, AState.setX, show r ≠ 31 by omega, show u ≠ 31 by omega]
      · simp only [eu, et, ite_false, AState.setX, show u ≠ 31 by omega, show t ≠ 31 by omega]

end ArmSail
