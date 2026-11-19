/- Opus box E: the host lift when the work block is too small for the start code (fewer than 16 usable bytes): the
start code's own check returns the spec's out-of-memory outcome. -/
import Nano.V2Self.Proof.CapHost
namespace SimW
open Proven Nano.V2B Templates CallProbe C GenRef ParSpec

/-- **the host lift, tiny work block**: fewer than 16 usable bytes of work: the start code itself returns the spec's
out-of-memory outcome (a0 = −1, a1 = 0), for any result `r`. -/
theorem gen_host_tinyX (c : List UInt8) {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p)
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
    (hMo : Mapped s output) (hMw : Mapped s work) (hsmall : (work.base + work.len) / 8 * 8 < work.base + 16)
    (hoom : oomOK)
    (r : Except NanoMain.Stop (List UInt8)) :
    runsTo s (OomOut s ra output work) := by
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
  let olen : Nat := 0
  let KL : LayW := ⟨entry.toNat, (C.map encG).map UInt64.toNat, work.base, E0, input.base, x.length, output.base,
    olen, fun a => s.mem[a]?⟩
  have z0 : s0.x 0 = 0 := by rw [sx 0 (by omega)]; simp [getX, xval]
  have ol0 : olen = 0 := rfl
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
    obh := by simp [KL, ol0]; omega
    oc := by simp [KL, ol0]; rcases dOC with d | d <;> first | exact Or.inl (by omega) | exact Or.inr (by omega) }
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
      · simp only [KL, ol0] at a1 a2; omega
  have z0 : s0.x 0 = 0 := by rw [sx 0 (by omega)]; simp [getX, xval]
  obtain ⟨w, hsw⟩ := hss
  have j0 : C[0]? = some (.jal 0 (S0 : Int)) := by have := hst 0 (by simp [stubJ]); simpa [stubJ] using this
  have c0 := At.get hsw 0 (by simp [startJ]); have c1 := At.get hsw 1 (by simp [startJ])
  have c2 := At.get hsw 2 (by simp [startJ]); have c3 := At.get hsw 3 (by simp [startJ])
  have c4 := At.get hsw 4 (by simp [startJ]); have c5 := At.get hsw 5 (by simp [startJ])
  have c6 := At.get hsw 6 (by simp [startJ])
  simp only [startJ, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at c0 c1 c2 c3 c4 c5 c6
  have hl32 := h32
  have l12 : (s0.x 12).toNat + 16 < 2 ^ 64 := by rw [x12]; omega
  have e12 : CallProbe.ea (s0.x 12) 16 = (s0.x 12).toNat + 16 := by simp [CallProbe.ea]; omega
  let sa : CallProbe.St := CallProbe.wr s0 30 (UInt64.ofNat ((s0.x 12).toNat + 16))
  let sb : CallProbe.St := CallProbe.wr sa 31 (sa.x 2 >>> (3 : Nat).toUInt64)
  let sc : CallProbe.St := CallProbe.wr sb 31 (sb.x 31 <<< (3 : Nat).toUInt64)
  have scx : ∀ j, j ≠ 30 → j ≠ 31 → sc.x j = s0.x j := by
    intro j h1 h2; simp [sc, sb, sa, CallProbe.wr, CallProbe.upd, h1, h2]
  have sc30 : (sc.x 30).toNat = work.base + 16 := by
    simp [sc, sb, sa, CallProbe.wr, CallProbe.upd]; rw [x12]; omega
  have sc31 : (sc.x 31).toNat = E0 := by
    rw [← hE0]; simp [sc, sb, sa, CallProbe.wr, CallProbe.upd]
  have hrun : CallProbe.run C 5 (0, s0) = some (S0 + 4, sc) := by
    have : ¬ (sc.x 30).toNat ≤ (sc.x 31).toNat := by rw [sc30, sc31]; omega
    simp [CallProbe.run, CallProbe.step, j0, c0, c1, c2, c3, e12, sa, sb, sc, CallProbe.wr, CallProbe.upd] at this ⊢
    exact fun hh => absurd hh (Nat.not_le.mpr this)
  have hsx : SStarX KL C (0, s0) (S0 + 4, sc) := sstarX_of_run hrun (fun j hj c hc => by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
    · simp [CallProbe.run] at hc; subst hc; simp [SafeX, j0]; omega
    all_goals simp [CallProbe.run, CallProbe.step, j0, c0, c1, c2, e12, CallProbe.wr, CallProbe.upd] at hc
    all_goals subst hc
    all_goals simp [SafeX, c0, c1, c2, c3, CallProbe.wr, CallProbe.upd]
    all_goals omega)
  have hW : KL.W = C.map SimW.encJX := by simp only [KL]; exact hwd
  obtain ⟨n, t', hSt, hR'⟩ := SimW.sim_starX hK hW hsx hR0
  have hWi : ∀ (i : Nat) (j : J), C[i]? = some j → KL.W[i]? = some (SimW.encJX j) := by
    intro i j h; rw [hW]; simp [h]
  obtain ⟨t1, r1, R1⟩ := sim_addiN hK hR' (hWi _ _ c4) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨t2, r2, R2⟩ := sim_addiN hK R1 (hWi _ _ c5) (by decide) (by decide) (by decide) (by decide)
  generalize hs2 : CallProbe.wr (CallProbe.wr sc 10 (sc.x 0 + UInt64.ofInt (-1))) 11
    ((CallProbe.wr sc 10 (sc.x 0 + UInt64.ofInt (-1))).x 0 + UInt64.ofInt 0) = s2 at R2
  have x2 : ∀ j, j ≠ 10 → j ≠ 11 → j ≠ 30 → j ≠ 31 → s2.x j = s0.x j := by
    intro j a b c d; rw [← hs2]; simp [CallProbe.wr, CallProbe.upd, a, b]; exact scx j c d
  have z00 : sc.x 0 = 0 := by rw [scx 0 (by decide) (by decide), z0]
  have x210 : s2.x 10 = UInt64.ofInt (-1) := by rw [← hs2]; simp [CallProbe.wr, CallProbe.upd, z00]
  have x211 : s2.x 11 = 0 := by rw [← hs2]; simp [CallProbe.wr, CallProbe.upd, z00]; rfl
  have r21 : s2.x 1 = s0.x 1 := x2 1 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨t3, v, hN⟩ := sim_ret hK R2 (by decide) (hWi _ _ c6) (by rw [r21, x1]; show ra.toNat % 2 = 0; omega)
  have gx : ∀ j : Fin 32, getX t3 j = (s2.x j.val).toBitVec := fun j => by
    rw [hN.x j]; simp only [show ¬ (j = 0 ∧ j ≠ 0) from fun h => h.2 h.1, if_false]; exact R2.x j
  have gk : ∀ j : Fin 32, j.val ≠ 10 → j.val ≠ 11 → j.val ≠ 30 → j.val ≠ 31 → getX t3 j = getX s j := by
    intro j a b c d; rw [gx j, x2 _ a b c d, sx j j.isLt]
  refine ⟨n + 3, t3, steps_app hSt ⟨t1, r1, t2, r2, steps_one hN.ret⟩, ?_⟩
  unfold OomOut
  refine ⟨by rw [hN.pc, r21, x1], ?_, hN.cfg,
    by rw [hN.cfg.x10, gx 10]; exact congrArg some (by show (s2.x 10).toBitVec = _; rw [x210, ofInt_bv]; rfl),
    by rw [hN.cfg.x11, gx 11]; exact congrArg some (by show (s2.x 11).toBitVec = _; rw [x211]; rfl), ?_⟩
  · intro reg hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hN.cfg.x2, hc.x2, gk 2 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x3, hc.x3, gk 3 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x4, hc.x4, gk 4 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x8, hc.x8, gk 8 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x9, hc.x9, gk 9 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x18, hc.x18, gk 18 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x19, hc.x19, gk 19 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x20, hc.x20, gk 20 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x21, hc.x21, gk 21 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x22, hc.x22, gk 22 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x23, hc.x23, gk 23 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x24, hc.x24, gk 24 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x25, hc.x25, gk 25 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x26, hc.x26, gk 26 (by decide) (by decide) (by decide) (by decide)]
    · rw [hN.cfg.x27, hc.x27, gk 27 (by decide) (by decide) (by decide) (by decide)]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at ha
    have h1 : ¬ wok KL (a - a % 8) := fun hw => by simp only [wok, KL, E0] at hw; omega
    have h2 : ¬ outB KL a := fun ho => by simp only [outB, KL, ol0] at ho; omega
    rw [hN.mem, R2.fr a h1 h2]


theorem gen_host_tiny (c : List UInt8) {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p)
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
    (hMo : Mapped s output) (hMw : Mapped s work) (hsmall : (work.base + work.len) / 8 * 8 < work.base + 16)
    (hoom : oomOK)
    (r : Except NanoMain.Stop (List UInt8)) :
    runsTo s (NanoMain.Outcome s ra output work r oomOK) := by
  obtain ⟨n, s', hs, ho⟩ := gen_host_tinyX c hP Ks hO hK2 hXl h hdb x s entry ra input output work oomOK hxl hc hpc he4 hB h10 h11 h12 h13 h2 h1 hra4 hin hil hout hw8 hram hdis hMo hMw hsmall hoom r
  exact ⟨n, s', hs, ho.outcome hoom⟩

end SimW
