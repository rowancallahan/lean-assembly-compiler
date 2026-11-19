/- Opus box E: the host lift, assembled (`gen_host`): Gen's bytes, called per `ImplementsCW`'s convention, run `Sem κC p x`
to its `.ok` outcome whenever `semAt main` succeeds in the work area. -/
import Nano.V2Self.Proof.Machine.HostLift
namespace SimW
open Proven Templates CallProbe C GenRef ParSpec

theorem lbm_wordAt (t : Proven.St) (a : Nat) : lbm (wordAt t) a = UInt64.ofNat (gb t a).toNat := by
  have hk : a % 8 < 8 := Nat.mod_lt _ (by decide)
  have h := congrArg BitVec.toNat (wordAt_byte t (a - a % 8) (a % 8) hk)
  rw [show a - a % 8 + a % 8 = a by omega] at h
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at h
  apply UInt64.toNat_inj.1
  simp only [lbm, UInt64.toNat_and, UInt64.toNat_shiftRight]
  have e : (8 * (a % 8)).toUInt64.toNat % 64 = 8 * (a % 8) := by simp; omega
  rw [e, Nat.shiftRight_eq_div_pow, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := (gb t a).isLt
  rw [show (UInt64.ofNat (gb t a).toNat).toNat = (gb t a).toNat from by simp; omega]; exact h

theorem steps_snoc : ∀ {n : Nat} {a b c : Proven.St}, Steps n a b → Retires b c → Steps (n + 1) a c
  | 0, a, b, c, h, r => by cases h; exact ⟨c, r, rfl⟩
  | n + 1, a, b, c, ⟨a1, r1, h⟩, r => ⟨a1, r1, steps_snoc h r⟩

theorem bv_toNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by simp; omega

/-- **the host lift, success**: Gen's bytes `B` for a parsed, linear program, called per `ImplementsCW` with input `x`
and at least 16 bytes of work: if `semAt main` succeeds (for Gen's code positions `T`, whatever they are) in the
8-aligned work area, the run ends with `Sem κC p x`'s result as the spec's `.ok` outcome. -/
theorem gen_host (c : List UInt8) {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p)
    (Ks : List (List Nat)) (hO : OwnSpec.progOk [] [] Ks p = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hXl : (serialize p).length < 2 ^ 31) (h : g41 c (serialize p) ≠ []) (hdb : ∀ d ∈ p, DB d)
    (x : List UInt8) (s : Proven.St) (entry ra : BitVec 64) (input output work : Region) (oomOK : Prop)
    (hxl : x.length ≤ 2 ^ 20) (hc : Cfg s) (hpc : s.regs.get? .PC = some entry) (he4 : entry.toNat % 4 = 0)
    (hB : bytesAt s entry.toNat (g41 c (serialize p)).length = (g41 c (serialize p)).map (some ·.toBitVec))
    (h10 : s.regs.get? .x10 = some (BitVec.ofNat 64 input.base))
    (h11 : s.regs.get? .x11 = some (BitVec.ofNat 64 x.length))
    (h12 : s.regs.get? .x12 = some (BitVec.ofNat 64 work.base))
    (h13 : s.regs.get? .x13 = some (BitVec.ofNat 64 output.base))
    (h2 : s.regs.get? .x2 = some (BitVec.ofNat 64 (work.base + work.len)))
    (h1 : s.regs.get? .x1 = some ra) (hra4 : ra.toNat % 4 = 0)
    (hin : bytesAt s input.base x.length = x.map (some ·.toBitVec)) (hil : input.len = x.length)
    (hout : ∀ y, NanoMain.Sem NanoMain.κC p x = .ok y → y.length ≤ output.len) (hw8 : work.base % 8 = 0)
    (hram : ∀ r ∈ [input, output, work, ⟨entry.toNat, (g41 c (serialize p)).length⟩], Region.inRAM r)
    (hdis : [input, output, work, ⟨entry.toNat, (g41 c (serialize p)).length⟩].Pairwise disjoint)
    (hMo : Mapped s output) (hMw : Mapped s work) (h16 : 16 ≤ work.len)
    (hS : ∀ T, ∃ vs H', semAt (pcOf 524288 (work.base + 16) (UInt64.ofNat x.length) (NanoMain.inpW x) T) p
      (p.length - 1) [] ((work.base + work.len) / 8 * 8) ⟨work.base + 16, fun _ => none⟩ = some (vs, H')) :
    runsTo s (NanoMain.Outcome s ra output work (NanoMain.Sem NanoMain.κC p x) oomOK) := by
  -- the regions
  have rI := hram input (by simp); have rO := hram output (by simp); have rW := hram work (by simp)
  have rC := hram ⟨entry.toNat, (g41 c (serialize p)).length⟩ (by simp)
  simp only [Region.inRAM] at rI rO rW rC
  simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq, List.not_mem_nil,
    List.Pairwise.nil, and_true, disjoint] at hdis
  obtain ⟨⟨dIO, dIW, dIC⟩, ⟨dOW, dOC⟩, dWC⟩ := hdis
  -- the registers
  have g10 : getX s 10 = BitVec.ofNat 64 input.base := Option.some.inj (hc.x10.symm.trans h10)
  have g11 : getX s 11 = BitVec.ofNat 64 x.length := Option.some.inj (hc.x11.symm.trans h11)
  have g12 : getX s 12 = BitVec.ofNat 64 work.base := Option.some.inj (hc.x12.symm.trans h12)
  have g13 : getX s 13 = BitVec.ofNat 64 output.base := Option.some.inj (hc.x13.symm.trans h13)
  have g2 : getX s 2 = BitVec.ofNat 64 (work.base + work.len) := Option.some.inj (hc.x2.symm.trans h2)
  have g1 : getX s 1 = ra := Option.some.inj (hc.x1.symm.trans h1)
  let s0 := jOf s entry.toNat
  have sx : ∀ j (hj : j < 32), s0.x j = UInt64.ofBitVec (getX s ⟨j, hj⟩) := fun j hj => by simp [s0, jOf, hj]
  have x10 : (s0.x 10).toNat = input.base := by rw [sx 10 (by omega)]; show (getX s 10).toNat = _; rw [g10, bv_toNat (by omega)]
  have x11 : s0.x 11 = UInt64.ofNat x.length := by rw [sx 11 (by omega)]; show UInt64.ofBitVec (getX s 11) = _; rw [g11]; rfl
  have x12 : (s0.x 12).toNat = work.base := by rw [sx 12 (by omega)]; show (getX s 12).toNat = _; rw [g12, bv_toNat (by omega)]
  have x13 : (s0.x 13).toNat = output.base := by rw [sx 13 (by omega)]; show (getX s 13).toNat = _; rw [g13, bv_toNat (by omega)]
  have x1 : s0.x 1 = UInt64.ofBitVec ra := by rw [sx 1 (by omega)]; show UInt64.ofBitVec (getX s 1) = _; rw [g1]
  have hxb : ∀ i, i < x.length → s.mem[input.base + i]? = some (x.getD i 0).toBitVec := by
    intro i hi
    have := congrArg (·[i]?) hin
    simp only [bytesAt, List.getElem?_map, List.getElem?_range hi, Option.map_some] at this
    rw [List.getElem?_eq_getElem hi] at this
    simp only [Option.map_some, Option.some.injEq] at this
    rw [this]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hxm : ∀ i, i < x.length → lbm s0.m ((s0.x 10).toNat + i) = (x.getD i 0).toUInt64 := by
    intro i hi
    rw [x10]; show lbm (wordAt s) _ = _; rw [lbm_wordAt]
    unfold gb; rw [hxb i hi]
    apply UInt64.toNat_inj.1; simp
  obtain ⟨C, pr, S0, T, hg, hc18, hst, hss, h32, hwd, hrun⟩ := gen_main c hP Ks hO hK2 hXl h hdb s0 x x11 (by omega) hxm
  have hgB : g41 c (serialize p) = (C.map encG).flatMap le4 := by
    have e0 : (0 : UInt64) = UInt64.ofNat 0 := rfl
    rw [hg, e0, g40_bytes c _ (by rw [List.length_map]; omega) 16777216 0 [] (by rw [List.length_map]; omega) (by omega)]
    simp
  have hBl : (g41 c (serialize p)).length = 4 * C.length := by rw [hgB, len_le4]; simp
  rw [hBl] at rC dIC dOC dWC
  have xl : x.length < 2 ^ 64 := by omega
  have x11' : (s0.x 11).toNat = x.length := by rw [x11]; simp; omega
  let E0 := (work.base + work.len) / 8 * 8
  have hE0v : E0 = (work.base + work.len) / 8 * 8 := rfl
  have hE0 : ((s0.x 2 >>> 3) <<< 3).toNat = E0 := by
    rw [sx 2 (by omega)]; show ((UInt64.ofBitVec (getX s 2) >>> 3) <<< 3).toNat = _; rw [g2]
    simp only [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.toNat_ofBitVec, bv_toNat (show work.base + work.len < 2 ^ 64 by omega)]
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, E0]; omega
  let olen : Nat := match NanoMain.Sem NanoMain.κC p x with
    | .ok y => y.length
    | .error _ => 0
  let KL : LayW := ⟨entry.toNat, (C.map encG).map UInt64.toNat, work.base, E0, input.base, x.length, output.base,
    olen, fun a => s.mem[a]?⟩
  obtain ⟨vs, H', hSd⟩ := hS T
  have z0 : s0.x 0 = 0 := by rw [sx 0 (by omega)]; simp [getX, xval]
  obtain ⟨y, hSem, hcont⟩ := (hrun KL E0 hE0 z0 (by rw [x12]; exact hw8) (by rw [x12]; omega) (by rw [x12]; omega) (by omega)
    (by show entry.toNat + 4 * C.length < 2 ^ 64; omega) (by rw [x10, x11']; omega)
    (by rw [x10, x11', x12]; rcases dIW with d | d <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)) (by rw [x12]; exact Nat.le_refl _)
    (Nat.le_refl _) rfl (fun i hi => by rw [x11'] at hi; rw [x10]; exact Or.inr (Or.inl ⟨by simp [KL], by simp [KL]; omega⟩))).1
    vs H' (by rw [x12, x11]; exact hSd)
  have hol : KL.ol = y.length := by simp [KL, olen, hSem]
  have hyo := hout y hSem
  obtain ⟨s3, h3, c31, kp, b3, e1, e8, e10, e11, hby⟩ := hcont (by rw [x13]; omega)
    (by rw [x13, x12]; rcases dOW with d | d <;> first | exact Or.inl (by omega) | exact Or.inr (by omega))
    (fun i hi => by rw [x13]; exact Or.inr ⟨by simp [KL], by simp [KL, olen, hSem]; omega⟩)
  have hK : KL.Ok := {
    b4 := he4
    blo := by simp [KL]; omega
    bhi := by simp [KL]; omega
    wlo := by simp [KL]; omega
    whi := by simp [KL, E0]; omega
    cw := by simp [KL, E0]; rcases dWC with d | d <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)
    ibl := by simp [KL]; omega
    ibh := by simp [KL]; omega
    obl := by simp [KL]; omega
    obh := by simp [KL, olen, hSem]; omega
    oc := by simp [KL, olen, hSem]; rcases dOC with d | d <;> first | exact Or.inl (by omega) | exact Or.inr (by omega) }
  have hR0 : RelW KL (0, s0) s := by
    refine rel_init hc (by rw [hpc]; congr 1; apply BitVec.eq_of_toNat_eq; simp [KL]) ?_ ?_ ?_ rfl
    · intro i hi
      have hi' : i < (C.map encG).length := by simpa [KL] using hi
      have := code_at (t := s) (e := entry.toNat) (ws := C.map encG) (by simp; omega) (by rw [← hgB]; exact hB) i hi'
      simpa [KL] using this
    · intro a ha k hk
      simp only [wok, KL] at ha
      have := hMw (a + k - work.base) (by omega)
      rwa [show work.base + (a + k - work.base) = a + k by omega] at this
    · intro a ha
      rcases ha with ⟨a1, a2⟩ | ⟨a1, a2⟩
      · simp only [KL] at a1 a2
        rw [show a = input.base + (a - input.base) by omega, hxb _ (by omega)]; rfl
      · simp only [KL, olen, hSem] at a1 a2
        have := hMo (a - output.base) (by omega)
        rwa [show output.base + (a - output.base) = a by omega] at this
  obtain ⟨n, t', hSt, hR'⟩ := sim_starX hK (hwd : KL.W = _) h3 hR0
  have hC : KL.W[pr]? = some (_root_.C.g2 _root_.C.g_103 0 0 (UInt64.ofNat 1) 0).toNat := by
    simp [KL, c31, encG]
  have r1 : (s3.x 1).toBitVec = ra := by rw [e1, x1]
  obtain ⟨t4, ret, pc4, abi, cfg4, a0, a1, bytes, unch⟩ := fin_out hK hR' hC
    (by rw [e1, x1]; show ra.toNat % 2 = 0; omega) hc (fun j => by rw [sx j j.isLt]) kp e8 rfl work
    (Nat.le_refl _) (by simp [KL, E0]; omega) y hol (fun i hi => by show lbm s3.m (output.base + i) = _; rw [← x13]; exact hby i hi)
  refine ⟨n + 1, t4, steps_snoc hSt ret, ?_⟩
  unfold NanoMain.Outcome
  rw [hSem]
  refine ⟨by rw [pc4, r1], abi, cfg4, Or.inl ⟨by rw [a0, e10]; unfold NanoMain.a0Ok; split <;> rfl,
    by rw [a1, e11]; rfl, bytes, unch⟩⟩

end SimW
