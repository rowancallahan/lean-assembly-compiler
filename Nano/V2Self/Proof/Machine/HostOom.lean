/- The generic host lift, part 4 (over any `JTarget`): the out-of-memory returns.  `stub_run`: the stub
`addi a0, x0, imm; addi a1, x0, 0; ld ra, 0(a2); ld s0, 8(a2)` as a machine run; `host_room`: main runs out of
room, the run reaches the room stub and returns with status = −1, memory changed only in the work block. -/
import Nano.V2Self.Proof.Machine.HostOk
namespace JT
open Proven.Top Proven.Top.Alloc SimW CallProbe ParSpec Templates

variable {T : JTarget}

/-- the stub tail before its `jalr`: a0 := imm (wrapping), a1 := 0, ra and s0 reloaded from the work base -/
theorem stub_run (L : T.Laws) {K : LayW} {Cj : List J} {s0 s : T.M.State} {b : Nat} {st : CallProbe.St}
    (hl : T.lay K Cj) (hR : T.Rel K Cj s0 (b, st) s) {imm : Int} (hi1 : -2048 ≤ imm) (hi2 : imm < 2048)
    (c0 : Cj[b]? = some (.addi 10 0 imm)) (c1 : Cj[b + 1]? = some (.addi 11 0 0))
    (c2 : Cj[b + 2]? = some (.ld 1 12 0)) (c3 : Cj[b + 3]? = some (.ld 8 12 8))
    (z : st.x 0 = 0) (w0 : wok K (st.x 12).toNat) (w8 : wok K ((st.x 12).toNat + 8)) :
    ∃ s' st', Runs T.M s s' ∧ T.Rel K Cj s0 (b + 4, st') s' ∧ st'.x 1 = st.m (st.x 12).toNat ∧
      st'.x 8 = st.m ((st.x 12).toNat + 8) ∧ st'.x 10 = UInt64.ofInt imm ∧ st'.x 11 = 0 ∧
      ∀ j, j ≠ 1 → j ≠ 8 → j ≠ 10 → j ≠ 11 → st'.x j = st.x j := by
  obtain ⟨s1, r1, R1⟩ := L.addi_ok hl hR c0 (by omega) (by omega) hi1 hi2
  obtain ⟨s2, r2, R2⟩ := L.addi_ok hl R1 c1 (by omega) (by omega) (by omega) (by omega)
  generalize e2 : CallProbe.wr (CallProbe.wr st 10 (st.x 0 + UInt64.ofInt imm)) 11
    ((CallProbe.wr st 10 (st.x 0 + UInt64.ofInt imm)).x 0 + UInt64.ofInt 0) = st2 at R2
  have q12 : st2.x 12 = st.x 12 := by rw [← e2]; simp [CallProbe.wr, CallProbe.upd]
  have qm : st2.m = st.m := by rw [← e2]; simp [CallProbe.wr]
  have ea0 : CallProbe.ea (st.x 12) 0 = (st.x 12).toNat := by simp [CallProbe.ea]
  have ea8 : CallProbe.ea (st.x 12) 8 = (st.x 12).toNat + 8 := by simp [CallProbe.ea]; omega
  obtain ⟨s3, r3, R3⟩ := L.step_ok hl R2
    (by simp only [SafeX, show b + 1 + 1 = b + 2 by omega, c2, q12, ea0]; exact ⟨by omega, by omega, by omega, by omega, by omega, w0⟩)
    (CallProbe.s_ld (by rw [show b + 1 + 1 = b + 2 by omega]; exact c2))
  generalize e3 : CallProbe.wr st2 1 (st2.m (CallProbe.ea (st2.x 12) 0)) = st3 at R3
  have q12' : st3.x 12 = st.x 12 := by rw [← e3]; simp [CallProbe.wr, CallProbe.upd, q12]
  have qm' : st3.m = st.m := by rw [← e3, ← qm]; simp [CallProbe.wr]
  obtain ⟨s4, r4, R4⟩ := L.step_ok hl R3
    (by simp only [SafeX, show b + 2 + 1 = b + 3 by omega, c3, q12', ea8]; exact ⟨by omega, by omega, by omega, by omega, by omega, w8⟩)
    (CallProbe.s_ld (by rw [show b + 2 + 1 = b + 3 by omega]; exact c3))
  refine ⟨s4, _, Runs.trans r1 (Runs.trans r2 (Runs.trans r3 r4)), by rw [show b + 2 + 1 + 1 = b + 4 by omega] at R4; exact R4, ?_⟩
  rw [← e3, ← e2]
  simp [CallProbe.wr, CallProbe.upd, ea0, ea8, z]
  exact ⟨rfl, fun j a b c d => by simp [a, b, c, d]⟩

theorem oomFlag_eq : UInt64.ofInt (-1) = oomFlag := by decide

/-- **out of room, on any target**: if main's kinded semantics fails with `room` in the work block, the run returns to
the caller with status = −1, memory changed only in the work block, the kept registers, configured -/
theorem host_room (L : T.Laws) (c : List UInt8) {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p)
    (Ks : List (List Nat)) (hO : OwnSpec.progOk [] [] Ks p = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hXl : (serialize p).length < 2 ^ 31) (h : C.g41 c (serialize p) ≠ []) (hdb : ∀ d ∈ p, DB d)
    (B : List UInt8) (hB : ∀ Cj : List J, Cj.length < 2 ^ 18 →
      C.g41 c (serialize p) = C.g40 16777216 c (Cj.map encG) 0 [] →
      (Cj.map encG).map UInt64.toNat = Cj.map SimW.encJX → B = tbytes T Cj ∧ T.valid Cj)
    {s : T.M.State} {call : Call} {x : List UInt8} (sc : StartCorrect T.M s call B x)
    (h16 : call.workAddress.toNat + 16 ≤ (call.workAddress.toNat + call.workLength) / 8 * 8)
    (hS : ∀ Tb, semAtF (pcOf 524288 (call.workAddress.toNat + 16) (UInt64.ofNat x.length)
      (NanoMain.inpW x) Tb) p (p.length - 1) [] ((call.workAddress.toNat + call.workLength) / 8 * 8)
      ⟨call.workAddress.toNat + 16, fun _ => none⟩ = .error .room) :
    ∃ s', Runs T.M s s' ∧ (T.M.observe s').programCounter = call.returnAddress ∧
      (T.M.observe s').register T.M.mapping.status = oomFlag ∧
      (∀ a, Outside a (call.workAddress, call.workLength) → (T.M.observe s').memory a = (T.M.observe s).memory a) ∧
      KeptRegisters T.M s s' ∧ T.M.configured s' := by
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, e3, f1, f2, g1, r32⟩ := blocks_of L sc
  have r0 := L.ram.1
  have ilen := sc.inputLength
  have xs := sc.inputSmall
  let base := (T.M.observe s).programCounter.toNat
  let s0 := jOfT T s base
  obtain ⟨j1, j2, j10, j11, j12, j13, j0, jb⟩ := jregs L sc base
  have hx11 : s0.x 11 = UInt64.ofNat x.length := j11
  have hxm : ∀ i, i < x.length → lbm s0.m ((s0.x 10).toNat + i) = (x.getD i 0).toUInt64 := by
    intro i hi
    obtain ⟨-, hr⟩ := read_some sc.inputLoaded
    show lbm (wordT T s) _ = _
    rw [lbm_wordT, j10]; unfold gbT; rw [hr i hi, List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  obtain ⟨Cj, pr, S0, Tb, hg, hc18, hst, -, -, hwd, hrun⟩ :=
    gen_main c hP Ks hO hK2 hXl h hdb s0 x hx11 (by omega) hxm
  obtain ⟨hBe, hv⟩ := hB Cj hc18 hg hwd
  subst hBe
  have hn := tbytes_len L Cj
  rw [hn] at d2 e3 f2 g1
  let wb := call.workAddress.toNat
  let E0 := (wb + call.workLength) / 8 * 8
  have x12 : (s0.x 12).toNat = wb := by rw [j12]
  have x10 : (s0.x 10).toNat = call.inputAddress.toNat := by rw [j10]
  have x11' : (s0.x 11).toNat = x.length := by rw [j11]; simp; omega
  have hE0 : ((s0.x 2 >>> 3) <<< 3).toNat = E0 := by
    rw [j2]
    have : (call.workAddress + call.workLength.toUInt64).toNat = wb + call.workLength := by
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.toUInt64]
      rw [Nat.mod_eq_of_lt (show call.workLength < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, this]
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, E0]; omega
  let KL : LayW := ⟨base, T.words Cj, wb, E0, call.inputAddress.toNat, x.length, call.outputAddress.toNat,
    0, T.m0 s⟩
  have hb4 : 4 * Cj.length ≤ 2 ^ 20 := by omega
  obtain ⟨s2, h2, m12, m8, z2, k2, -⟩ := (hrun KL E0 hE0 j0 (by rw [x12]; exact sc.workAligned) (by rw [x12]; omega)
    (by rw [x12]; omega) (by omega) (by rw [jb, jOfT_w L]; omega) (by rw [x10, x11']; omega)
    (by rw [x10, x11', x12]; omega) (by rw [x12]; exact Nat.le_refl _) (Nat.le_refl _) jb
    (fun i hi => by rw [x11'] at hi; rw [x10]; exact Or.inr (Or.inl ⟨by simp [KL], by simp [KL]; omega⟩))).2
    .room (by decide) (by rw [x12, hx11]; exact hS Tb)
  obtain ⟨hl, hR0⟩ := enter L sc KL rfl rfl rfl rfl (by simp [KL, E0]; omega) rfl rfl rfl (Nat.zero_le _) hv
  obtain ⟨s', r1, R1⟩ := sim_star L hl h2 hR0
  have cs : ∀ i, i < 11 → Cj[i]? = (stubJ S0)[i]? := fun i hi => by
    have := hst i (by simp [stubJ]; omega); rwa [Nat.zero_add] at this
  have k12 : s2.x 12 = s0.x 12 := k2 12 (by decide)
  have wa : wb % 8 = 0 := sc.workAligned
  obtain ⟨s5, st5, r5, R5, f1, f8, f10, -, fo⟩ := stub_run L hl (b := 1) R1 (imm := -1) (by decide) (by decide)
    (cs 1 (by omega)) (cs 2 (by omega)) (cs 3 (by omega)) (cs 4 (by omega)) z2
    (by rw [k12, x12]; simp only [wok, KL, E0]; omega) (by rw [k12, x12]; simp only [wok, KL, E0]; omega)
  have hra : (st5.x 1).toNat % 4 = 0 := by rw [f1, k12, m12, j1]; exact sc.returnAligned
  obtain ⟨s6, r6, pc6, q10, -, kept, -, frame, cfg⟩ := fin_on L hl R5 (cs 5 (by omega)) hra
    (fun j hj => by
      have : j ≠ 1 ∧ j ≠ 8 ∧ j ≠ 10 ∧ j ≠ 11 := by simp [keepR] at hj; omega
      rw [fo j this.1 this.2.1 this.2.2.1 this.2.2.2]; exact k2 j hj)
    (by rw [f8, k12]; exact m8) rfl wb (wb + call.workLength) (Nat.le_refl _) (by simp [KL, E0]; omega)
    [] rfl (fun i hi => absurd hi (by simp))
  obtain ⟨-, -, -, -, -, -, hst', -⟩ := L.reg_map
  refine ⟨s6, Runs.trans r1 (Runs.trans r5 r6), by rw [pc6, f1, k12, m12, j1], by rw [hst', q10, f10]; exact oomFlag_eq,
    fun a hw => ?_, kept, cfg⟩
  have := frame a.toNat a.toNat_lt (by simp [KL]; omega) hw
  rwa [UInt64.ofNat_toNat] at this

/-- **tiny work block, on any target**: fewer than 16 usable bytes: the start code's own check returns to the caller
with status = −1, memory changed only in the work block, the kept registers, configured -/
theorem host_tiny (L : T.Laws) (c : List UInt8) {ts : List UInt64} {p : List DefA} (hP : ParsesProgram ts p)
    (Ks : List (List Nat)) (hO : OwnSpec.progOk [] [] Ks p = true) (hK2 : ∀ K ∈ Ks, ∀ k ∈ K, k ≤ 2)
    (hXl : (serialize p).length < 2 ^ 31) (h : C.g41 c (serialize p) ≠ []) (hdb : ∀ d ∈ p, DB d)
    (B : List UInt8) (hB : ∀ Cj : List J, Cj.length < 2 ^ 18 →
      C.g41 c (serialize p) = C.g40 16777216 c (Cj.map encG) 0 [] →
      (Cj.map encG).map UInt64.toNat = Cj.map SimW.encJX → B = tbytes T Cj ∧ T.valid Cj)
    {s : T.M.State} {call : Call} {x : List UInt8} (sc : StartCorrect T.M s call B x)
    (hsm : (call.workAddress.toNat + call.workLength) / 8 * 8 < call.workAddress.toNat + 16) :
    ∃ s', Runs T.M s s' ∧ (T.M.observe s').programCounter = call.returnAddress ∧
      (T.M.observe s').register T.M.mapping.status = oomFlag ∧
      (∀ a, Outside a (call.workAddress, call.workLength) → (T.M.observe s').memory a = (T.M.observe s).memory a) ∧
      KeptRegisters T.M s s' ∧ T.M.configured s' := by
  obtain ⟨a1, a2, b1, b2, c1, c2, d1, d2, e1, e2, e3, f1, f2, g1, r32⟩ := blocks_of L sc
  have r0 := L.ram.1
  have ilen := sc.inputLength
  have xs := sc.inputSmall
  let base := (T.M.observe s).programCounter.toNat
  let s0 := jOfT T s base
  obtain ⟨j1, j2, j10, j11, j12, j13, j0, jb⟩ := jregs L sc base
  have hx11 : s0.x 11 = UInt64.ofNat x.length := j11
  have hxm : ∀ i, i < x.length → lbm s0.m ((s0.x 10).toNat + i) = (x.getD i 0).toUInt64 := by
    intro i hi
    obtain ⟨-, hr⟩ := read_some sc.inputLoaded
    show lbm (wordT T s) _ = _
    rw [lbm_wordT, j10]; unfold gbT; rw [hr i hi, List.getElem?_eq_getElem hi]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  obtain ⟨Cj, pr, S0, Tb, hg, hc18, hst, hss, h32, hwd, -⟩ :=
    gen_main c hP Ks hO hK2 hXl h hdb s0 x hx11 (by omega) hxm
  obtain ⟨hBe, hv⟩ := hB Cj hc18 hg hwd
  subst hBe
  have hn := tbytes_len L Cj
  rw [hn] at d2 e3 f2 g1
  let wb := call.workAddress.toNat
  have wa : wb % 8 = 0 := sc.workAligned
  let E0 := (wb + call.workLength) / 8 * 8
  have x12 : (s0.x 12).toNat = wb := by rw [j12]
  have hE0 : ((s0.x 2 >>> 3) <<< 3).toNat = E0 := by
    rw [j2]
    have : (call.workAddress + call.workLength.toUInt64).toNat = wb + call.workLength := by
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.toUInt64]
      rw [Nat.mod_eq_of_lt (show call.workLength < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, this]
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, E0]; omega
  let KL : LayW := ⟨base, T.words Cj, wb, E0, call.inputAddress.toNat, x.length, call.outputAddress.toNat,
    0, T.m0 s⟩
  obtain ⟨hl, hR0⟩ := enter L sc KL rfl rfl rfl rfl (by simp [KL, E0]; omega) rfl rfl rfl (Nat.zero_le _) hv
  -- the start code's size check
  obtain ⟨w, hsw⟩ := hss
  have q0 : Cj[0]? = some (.jal 0 (S0 : Int)) := by have := hst 0 (by simp [stubJ]); simpa [stubJ] using this
  have c0 := At.get hsw 0 (by simp [startJ]); have c1 := At.get hsw 1 (by simp [startJ])
  have c2 := At.get hsw 2 (by simp [startJ]); have c3 := At.get hsw 3 (by simp [startJ])
  have c4 := At.get hsw 4 (by simp [startJ]); have c5 := At.get hsw 5 (by simp [startJ])
  have c6 := At.get hsw 6 (by simp [startJ])
  simp only [startJ, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at c0 c1 c2 c3 c4 c5 c6
  have l12 : (s0.x 12).toNat + 16 < 2 ^ 64 := by rw [x12]; omega
  have e12 : CallProbe.ea (s0.x 12) 16 = (s0.x 12).toNat + 16 := by simp [CallProbe.ea]; omega
  let sa : CallProbe.St := CallProbe.wr s0 30 (UInt64.ofNat ((s0.x 12).toNat + 16))
  let sb : CallProbe.St := CallProbe.wr sa 31 (sa.x 2 >>> (3 : Nat).toUInt64)
  let sc' : CallProbe.St := CallProbe.wr sb 31 (sb.x 31 <<< (3 : Nat).toUInt64)
  have scx : ∀ j, j ≠ 30 → j ≠ 31 → sc'.x j = s0.x j := by
    intro j h1 h2; simp [sc', sb, sa, CallProbe.wr, CallProbe.upd, h1, h2]
  have sc30 : (sc'.x 30).toNat = wb + 16 := by
    simp [sc', sb, sa, CallProbe.wr, CallProbe.upd]; rw [x12]; omega
  have sc31 : (sc'.x 31).toNat = E0 := by
    rw [← hE0]; simp [sc', sb, sa, CallProbe.wr, CallProbe.upd]
  have hrun : CallProbe.run Cj 5 (0, s0) = some (S0 + 4, sc') := by
    have : ¬ (sc'.x 30).toNat ≤ (sc'.x 31).toNat := by rw [sc30, sc31]; omega
    simp [CallProbe.run, CallProbe.step, q0, c0, c1, c2, c3, e12, sa, sb, sc', CallProbe.wr, CallProbe.upd] at this ⊢
    exact fun hh => absurd hh (Nat.not_le.mpr this)
  have hsx : SStarX KL Cj (0, s0) (S0 + 4, sc') := sstarX_of_run hrun (fun j hj c hc => by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
    · simp [CallProbe.run] at hc; subst hc; simp [SafeX, q0]; omega
    all_goals simp [CallProbe.run, CallProbe.step, q0, c0, c1, c2, e12, CallProbe.wr, CallProbe.upd] at hc
    all_goals subst hc
    all_goals simp [SafeX, c0, c1, c2, c3, CallProbe.wr, CallProbe.upd]
    all_goals omega)
  obtain ⟨s1, r1, R1⟩ := sim_star L hl hsx hR0
  obtain ⟨s2, r2, R2⟩ := L.addi_ok hl R1 c4 (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s3, r3, R3⟩ := L.addi_ok hl R2 c5 (by omega) (by omega) (by omega) (by omega)
  generalize hs2 : CallProbe.wr (CallProbe.wr sc' 10 (sc'.x 0 + UInt64.ofInt (-1))) 11
    ((CallProbe.wr sc' 10 (sc'.x 0 + UInt64.ofInt (-1))).x 0 + UInt64.ofInt 0) = st2 at R3
  have x2 : ∀ j, j ≠ 10 → j ≠ 11 → j ≠ 30 → j ≠ 31 → st2.x j = s0.x j := by
    intro j a b c d; rw [← hs2]; simp [CallProbe.wr, CallProbe.upd, a, b]; exact scx j c d
  have z00 : sc'.x 0 = 0 := by rw [scx 0 (by decide) (by decide), j0]
  have x210 : st2.x 10 = UInt64.ofInt (-1) := by rw [← hs2]; simp [CallProbe.wr, CallProbe.upd, z00]
  have r21 : st2.x 1 = s0.x 1 := x2 1 (by decide) (by decide) (by decide) (by decide)
  have hra : (st2.x 1).toNat % 4 = 0 := by rw [r21, j1]; exact sc.returnAligned
  obtain ⟨s4, r4, pc4, q10, -, kept, -, frame, cfg⟩ := fin_on L hl R3 (pr := S0 + 4 + 1 + 1)
    (by rw [show S0 + 4 + 1 + 1 = S0 + 6 by omega]; exact c6) hra
    (fun j hj => by
      have : j ≠ 10 ∧ j ≠ 11 ∧ j ≠ 30 ∧ j ≠ 31 := by simp [keepR] at hj; omega
      exact x2 j this.1 this.2.1 this.2.2.1 this.2.2.2)
    (x2 8 (by decide) (by decide) (by decide) (by decide)) rfl wb (wb + call.workLength) (Nat.le_refl _)
    (by simp [KL, E0]; omega) [] rfl (fun i hi => absurd hi (by simp))
  obtain ⟨-, -, -, -, -, -, hst', -⟩ := L.reg_map
  refine ⟨s4, Runs.trans r1 (Runs.trans r2 (Runs.trans r3 r4)), by rw [pc4, r21, j1],
    by rw [hst', q10, x210]; exact oomFlag_eq, fun a hw => ?_, kept, cfg⟩
  have := frame a.toNat a.toNat_lt (by simp [KL]; omega) hw
  rwa [UInt64.ofNat_toNat] at this

end JT
