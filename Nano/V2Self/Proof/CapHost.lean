/- Opus box E: the capacity stub on Sail.  `sim_addiN`: addi with the hardware's (wrapping) sum; `stub_sail`: from
the cap stub (word 6) with ra / s0 saved at a2, five Sail steps return to ra with a0 = −2, a1 = 0, s0 restored. -/
import Nano.V2Self.Proof.HostMain
namespace SimW
open Proven Nano.V2B Templates CallProbe C GenRef ParSpec

/-- **addi**, any sum: the J register gets the hardware's value `x[a] + imm` -/
theorem sim_addiN {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {rd a : Nat} {imm : Int} (hC : K.W[pc]? = some (I.i .addi rd a imm).enc) (hrd : rd < 32) (ha : a < 32)
    (hi1 : -2048 ≤ imm) (hi2 : imm < 2048) :
    ∃ t', Retires t t' ∧ RelW K (pc + 1, CallProbe.wr s rd (s.x a + UInt64.ofInt imm)) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 0 (BitVec.ofNat 12 (bits imm 12)).toNat RD A) := by
    rw [imm12_toNat]; exact hi
  obtain ⟨t', hN⟩ := G.step_addi hR.cfg hR.pc hok RD A _ hi'
  have hv : getX t A + (BitVec.ofNat 12 (bits imm 12)).signExtend 64 = (s.x a + UInt64.ofInt imm).toBitVec := by
    rw [hR.x A, sext_bits imm hi1 hi2, UInt64.toBitVec_add, ofInt_bv]
  rw [hv] at hN
  exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩

theorem steps_one {a b : Proven.St} (h : Retires a b) : Steps 1 a b := ⟨b, h, rfl⟩

/-- **the cap stub on Sail** -/
theorem stub_sail {K : LayW} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (6, s) t)
    (hW6 : K.W[6]? = some (I.i .addi 10 0 (-2)).enc) (hW7 : K.W[7]? = some (I.i .addi 11 0 0).enc)
    (hW8 : K.W[8]? = some (I.ld 1 12 0).enc) (hW9 : K.W[9]? = some (I.ld 8 12 8).enc)
    (hW10 : K.W[10]? = some (C.g2 C.g_103 0 0 (UInt64.ofNat 1) 0).toNat)
    (hz : s.x 0 = 0) (w0 : wok K (s.x 12).toNat) (w8 : wok K ((s.x 12).toNat + 8))
    (hra : (s.m (s.x 12).toNat).toNat % 2 = 0) :
    ∃ n t', Steps n t t' ∧ t'.regs.get? .PC = some (s.m (s.x 12).toNat).toBitVec ∧ Cfg t' ∧
      getX t' 10 = (UInt64.ofInt (-2)).toBitVec ∧ getX t' 11 = 0 ∧ getX t' 8 = (s.m ((s.x 12).toNat + 8)).toBitVec ∧
      (∀ j : Fin 32, j.val ≠ 1 → j.val ≠ 8 → j.val ≠ 10 → j.val ≠ 11 → getX t' j = (s.x j.val).toBitVec) ∧
      (∀ a, ¬ wok K (a - a % 8) → ¬ outB K a → t'.mem[a]? = K.m0 a) := by
  have wx : ∀ (u : CallProbe.St) (r j : Nat) (v : UInt64), j ≠ r → (CallProbe.wr u r v).x j = u.x j := by
    intro u r j v h; unfold CallProbe.wr; split
    · rfl
    · simp [CallProbe.upd, h]
  have wxs : ∀ (u : CallProbe.St) (r : Nat) (v : UInt64), r ≠ 0 → (CallProbe.wr u r v).x r = v := by
    intro u r v h; simp [CallProbe.wr, h, CallProbe.upd]
  have wm : ∀ (u : CallProbe.St) (r : Nat) (v : UInt64), (CallProbe.wr u r v).m = u.m := by
    intro u r v; unfold CallProbe.wr; split <;> rfl
  have lt12 := (s.x 12).toNat_lt
  have h8 : (s.x 12).toNat + 8 < 2 ^ 64 := by unfold wok at w8; have := hK.whi; omega
  obtain ⟨t1, r1, R1⟩ := sim_addiN hK hR hW6 (by decide) (by decide) (by decide) (by decide)
  generalize hs1 : CallProbe.wr s 10 (s.x 0 + UInt64.ofInt (-2)) = s1 at R1
  have a1 : s1.x 12 = s.x 12 := by rw [← hs1, wx _ _ _ _ (by decide)]
  have m1 : s1.m = s.m := by rw [← hs1, wm]
  have z1 : s1.x 0 = 0 := by rw [← hs1, wx _ _ _ _ (by decide), hz]
  obtain ⟨t2, r2, R2⟩ := sim_addiN hK R1 hW7 (by decide) (by decide) (by decide) (by decide)
  generalize hs2 : CallProbe.wr s1 11 (s1.x 0 + UInt64.ofInt 0) = s2 at R2
  have a2 : s2.x 12 = s.x 12 := by rw [← hs2, wx _ _ _ _ (by decide), a1]
  have m2 : s2.m = s.m := by rw [← hs2, wm, m1]
  have e0 : CallProbe.ea (s2.x 12) 0 = (s.x 12).toNat := by rw [a2]; simp [CallProbe.ea]
  obtain ⟨t3, r3, R3⟩ := sim_ld hK R2 hW8 (by decide) (by decide) (by decide) (by decide)
    (by rw [a2]; omega) (by rw [e0]; exact w0)
  generalize hs3 : CallProbe.wr s2 1 (s2.m (CallProbe.ea (s2.x 12) 0)) = s3 at R3
  have a3 : s3.x 12 = s.x 12 := by rw [← hs3, wx _ _ _ _ (by decide), a2]
  have m3 : s3.m = s.m := by rw [← hs3, wm, m2]
  have e8 : CallProbe.ea (s3.x 12) 8 = (s.x 12).toNat + 8 := by rw [a3]; simp [CallProbe.ea]; omega
  obtain ⟨t4, r4, R4⟩ := sim_ld hK R3 hW9 (by decide) (by decide) (by decide) (by decide)
    (by rw [a3]; omega) (by rw [e8]; exact w8)
  generalize hs4 : CallProbe.wr s3 8 (s3.m (CallProbe.ea (s3.x 12) 8)) = s4 at R4
  have x1 : s4.x 1 = s.m (s.x 12).toNat := by
    rw [← hs4, wx _ _ _ _ (by decide), ← hs3, wxs _ _ _ (by decide), m2, e0]
  have x8 : s4.x 8 = s.m ((s.x 12).toNat + 8) := by rw [← hs4, wxs _ _ _ (by decide), m3, e8]
  have x10 : s4.x 10 = UInt64.ofInt (-2) := by
    rw [← hs4, wx _ _ _ _ (by decide), ← hs3, wx _ _ _ _ (by decide), ← hs2, wx _ _ _ _ (by decide), ← hs1,
      wxs _ _ _ (by decide), hz]; rfl
  have x11 : s4.x 11 = 0 := by
    rw [← hs4, wx _ _ _ _ (by decide), ← hs3, wx _ _ _ _ (by decide), ← hs2, wxs _ _ _ (by decide), z1]; rfl
  have xo : ∀ j, j ≠ 1 → j ≠ 8 → j ≠ 10 → j ≠ 11 → s4.x j = s.x j := by
    intro j j1 j8 j10 j11
    rw [← hs4, wx _ _ _ _ j8, ← hs3, wx _ _ _ _ j1, ← hs2, wx _ _ _ _ j11, ← hs1, wx _ _ _ _ j10]
  obtain ⟨t5, v, hN⟩ := sim_ret hK R4 (by decide) hW10 (by rw [x1]; exact hra)
  have gx : ∀ j : Fin 32, getX t5 j = (s4.x j.val).toBitVec := fun j => by
    rw [hN.x j]; simp only [show ¬ (j = 0 ∧ j ≠ 0) from fun h => h.2 h.1, if_false]; exact R4.x j
  refine ⟨5, t5, ⟨t1, r1, t2, r2, t3, r3, t4, r4, steps_one hN.ret⟩, by rw [hN.pc, x1], hN.cfg,
    by rw [gx 10]; show (s4.x 10).toBitVec = _; rw [x10], by rw [gx 11]; show (s4.x 11).toBitVec = _; rw [x11]; rfl,
    by rw [gx 8]; show (s4.x 8).toBitVec = _; rw [x8], fun j j1 j8 j10 j11 => by
      rw [gx j, xo j j1 j8 j10 j11], fun a h1 h2 => by rw [hN.mem]; exact R4.fr a h1 h2⟩

theorem steps_app : ∀ {n m : Nat} {a b c : Proven.St}, Steps n a b → Steps m b c → Steps (n + m) a c
  | 0, m, a, b, c, h, h2 => by cases h; simpa using h2
  | n + 1, m, a, b, c, ⟨a1, r1, h⟩, h2 => by
    rw [show n + 1 + m = (n + m) + 1 by omega]; exact ⟨a1, r1, steps_app h h2⟩

/-- **the host lift, capacity exit**: as `gen_host`, when `Sem` reports the capacity trap and E's kinded semantics of
main fails with `cap`: the run returns to ra with the spec's `.error .cap` outcome (a0 = −2, a1 = 0). -/
theorem gen_host_cap (c : List UInt8) {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p)
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
    (hSem : NanoMain.Sem NanoMain.κC p x = .error .cap)
    (hS : ∀ T, semAtF (pcOf 524288 (work.base + 16) (UInt64.ofNat x.length) (NanoMain.inpW x) T) p
      (p.length - 1) [] ((work.base + work.len) / 8 * 8) ⟨work.base + 16, fun _ => none⟩ = .error .cap) :
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
  obtain ⟨C, pr, S0, T, hg, hc18, hst, hrun⟩ := gen_main c hP Ks hO hK2 hXl h hdb s0 x x11 (by omega) hxm
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
  have z0 : s0.x 0 = 0 := by rw [sx 0 (by omega)]; simp [getX, xval]
  have ol0 : olen = 0 := by simp [olen, hSem]
  obtain ⟨s2, h2, m12, m8, z2, k2, b2, lift⟩ := (hrun KL E0 hE0 z0 (by rw [x12]; exact hw8) (by rw [x12]; omega) (by rw [x12]; omega) (by omega)
    (by show entry.toNat + 4 * C.length < 2 ^ 64; omega) (by rw [x10, x11']; omega)
    (by rw [x10, x11', x12]; rcases dIW with d | d <;> first | exact Or.inl (by omega) | exact Or.inr (by omega)) (by rw [x12]; exact Nat.le_refl _)
    (Nat.le_refl _) rfl (fun i hi => by rw [x11'] at hi; rw [x10]; exact Or.inr (Or.inl ⟨by simp [KL], by simp [KL]; omega⟩))).2
    (by rw [x12, x11]; exact hS T)
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
  obtain ⟨n, t', hSt, hR'⟩ := lift hK rfl s hR0
  have hWi : ∀ (i : Nat) (j : J), C[i]? = some j → CallProbe.GoodX j → KL.W[i]? = some (SimW.encJX j) := by
    intro i j h g; simp [KL, h, CallProbe.encG_encJX j g]
  have cs : ∀ i, i < 11 → C[i]? = (stubJ S0)[i]? := fun i hi => by
    have := hst i (by simp [stubJ]; omega); rwa [Nat.zero_add] at this
  have g6 := hWi 6 _ (by rw [cs 6 (by omega)]; rfl) (by simp [CallProbe.GoodX, CallProbe.GoodW])
  have g7 := hWi 7 _ (by rw [cs 7 (by omega)]; rfl) (by simp [CallProbe.GoodX, CallProbe.GoodW])
  have g8 := hWi 8 _ (by rw [cs 8 (by omega)]; rfl) (by simp [CallProbe.GoodX, CallProbe.GoodW])
  have g9 := hWi 9 _ (by rw [cs 9 (by omega)]; rfl) (by simp [CallProbe.GoodX, CallProbe.GoodW])
  have g10 := hWi 10 _ (by rw [cs 10 (by omega)]; rfl) (by simp [CallProbe.GoodX, CallProbe.GoodW])
  have k12 : s2.x 12 = s0.x 12 := k2 12 (by decide)
  have wk0 : wok KL (s2.x 12).toNat := by rw [k12, x12]; simp only [wok, KL, E0]; omega
  have wk8 : wok KL ((s2.x 12).toNat + 8) := by rw [k12, x12]; simp only [wok, KL, E0]; omega
  have mra : s2.m (s2.x 12).toNat = s0.x 1 := by rw [k12]; exact m12
  have ms0 : s2.m ((s2.x 12).toNat + 8) = s0.x 8 := by rw [k12]; exact m8
  obtain ⟨m, t5, hS5, pc5, cfg5, a05, a15, x85, xo5, fr5⟩ := stub_sail hK hR' g6 g7 g8 g9 g10 z2 wk0 wk8
    (by rw [mra, x1]; show ra.toNat % 2 = 0; omega)
  rw [mra, x1] at pc5
  rw [ms0] at x85
  have gk : ∀ j : Fin 32, Templates.keepR j.val = true ∨ j.val = 8 → getX t5 j = getX s j := by
    intro j hj
    rcases hj with hj | hj
    · have : j.val ≠ 1 ∧ j.val ≠ 8 ∧ j.val ≠ 10 ∧ j.val ≠ 11 := by
        simp [Templates.keepR] at hj; omega
      rw [xo5 j this.1 this.2.1 this.2.2.1 this.2.2.2, k2 _ hj, sx j j.isLt]
    · have : j = 8 := Fin.ext hj
      subst this; rw [x85, sx 8 (by omega)]; rfl
  refine ⟨n + m, t5, steps_app hSt hS5, ?_⟩
  unfold NanoMain.Outcome
  rw [hSem]
  refine ⟨by rw [pc5], ?_, cfg5, Or.inl ⟨by rw [cfg5.x10, a05, ofInt_bv]; rfl, by rw [cfg5.x11, a15], ?_⟩⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [cfg5.x2, hc.x2, gk 2 (by decide)]
    · rw [cfg5.x3, hc.x3, gk 3 (by decide)]
    · rw [cfg5.x4, hc.x4, gk 4 (by decide)]
    · rw [cfg5.x8, hc.x8, gk 8 (by decide)]
    · rw [cfg5.x9, hc.x9, gk 9 (by decide)]
    · rw [cfg5.x18, hc.x18, gk 18 (by decide)]
    · rw [cfg5.x19, hc.x19, gk 19 (by decide)]
    · rw [cfg5.x20, hc.x20, gk 20 (by decide)]
    · rw [cfg5.x21, hc.x21, gk 21 (by decide)]
    · rw [cfg5.x22, hc.x22, gk 22 (by decide)]
    · rw [cfg5.x23, hc.x23, gk 23 (by decide)]
    · rw [cfg5.x24, hc.x24, gk 24 (by decide)]
    · rw [cfg5.x25, hc.x25, gk 25 (by decide)]
    · rw [cfg5.x26, hc.x26, gk 26 (by decide)]
    · rw [cfg5.x27, hc.x27, gk 27 (by decide)]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ha
    have h1 : ¬ wok KL (a - a % 8) := fun hw => by simp only [wok, KL, E0] at hw; omega
    have h2 : ¬ outB KL a := fun ho => by simp only [outB, KL, ol0] at ho; omega
    rw [fr5 a h1 h2]

end SimW
