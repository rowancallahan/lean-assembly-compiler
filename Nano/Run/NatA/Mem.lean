/- T02 (M3 round 2): the atoms `ld` and `sd` (GenArm's `a9`, three forms, any mapped base register).
`NTm.memW`: `ldr`/`str` (uimm), `ldur`/`stur`, or `sub x16, xn, #k; ldr/str [x16]`; `sd 0` stores x17 after `movz x17, #0`. -/
import Nano.Run.NatA.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop} {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St}

/-! ## for ArmNat -/

/-- `sub x16, xn, #k` (scratch base of the far slot forms); the other registers are kept -/
theorem n_subi16 (S : A64SemN M X W) {h n k : Nat} (hM : NMid X W K A s0 st h s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hA : A[h]? = some (ArmEnc.subi 16 (armReg n) k)) (hn : mapped n = true)
    (hn0 : n ≠ 0) (hk : k < 4096) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (h + 1) s' ∧ (M.observe s').register 16 = st.x n - UInt64.ofNat k ∧
      ∀ r, r ≠ 16 → (M.observe s').register r = (M.observe s).register r := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.subi s 16 (armReg n) k hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (by decide) (armReg_lt hn hn0) hk (nmid_word hM hA hB)
  rw [hM.x n (by omega) (mapped_lt hn)] at this
  obtain ⟨s', r, N, o⟩ := nmid_scr hM (Or.inl rfl) this
  exact ⟨s', r, N, by rw [o]; simp [setReg], fun r' hr => by rw [o]; simp [setReg, hr]⟩

/-! ## the machine side: the words of `NTm.memW` -/

theorem n_memLd (S : A64SemN M X W) {h d n a : Nat} {off : Int} (hM : NMid X W K A s0 st h s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hA : ∀ i, i < (NTm.memW false (armReg d) (armReg n) off).length →
      A[h + i]? = (NTm.memW false (armReg d) (armReg n) off)[i]?)
    (hd : mapped d = true) (hd0 : d ≠ 0) (hn : mapped n = true) (hn0 : n ≠ 0)
    (hoff : -4096 < off ∧ off < 32768 ∧ (0 ≤ off → off % 8 = 0))
    (ha : (a : Int) = (st.x n).toNat + off) (hw : wok K a) :
    ∃ s', Runs M s s' ∧
      NMid X W K A s0 (CallProbe.wr st d (st.m a)) (h + (NTm.memW false (armReg d) (armReg n) off).length) s' := by
  have hn8 := hM.x n (by omega) (mapped_lt hn)
  by_cases c1 : off % 8 = 0 ∧ 0 ≤ off ∧ off < 32768
  · have e : NTm.memW false (armReg d) (armReg n) off = [ArmEnc.ldr (armReg d) (armReg n) off.toNat] := by
      unfold NTm.memW; rw [if_pos c1]; simp
    rw [e] at hA ⊢
    have a0 : A[h]? = some (ArmEnc.ldr (armReg d) (armReg n) off.toNat) := by simpa using hA 0 (by simp)
    exact n_ldr S hM hB a0 hd hd0 (armReg_lt hn hn0) hn8 (by omega) (by omega) (by omega) hw
  by_cases c2 : -256 ≤ off ∧ off < 0
  · have e : NTm.memW false (armReg d) (armReg n) off = [ArmEnc.ldur (armReg d) (armReg n) off] := by
      unfold NTm.memW; rw [if_neg c1, if_pos c2]; simp
    rw [e] at hA ⊢
    have a0 : A[h]? = some (ArmEnc.ldur (armReg d) (armReg n) off) := by simpa using hA 0 (by simp)
    exact n_ldur S hM hB a0 hd hd0 (armReg_lt hn hn0) hn8 (by omega) (by omega) ha hw
  · have e : NTm.memW false (armReg d) (armReg n) off =
        [ArmEnc.subi 16 (armReg n) (-off).toNat, ArmEnc.ldr (armReg d) 16 0] := by
      unfold NTm.memW; rw [if_neg c1, if_neg c2]; simp
    rw [e] at hA ⊢
    have a0 : A[h]? = some (ArmEnc.subi 16 (armReg n) (-off).toNat) := by simpa using hA 0 (by simp)
    have a1 : A[h + 1]? = some (ArmEnc.ldr (armReg d) 16 0) := by simpa using hA 1 (by simp)
    obtain ⟨s1, r1, N1, o16, -⟩ := n_subi16 S hM hB a0 hn hn0 (by omega)
    have e2 : (st.x n - UInt64.ofNat (-off).toNat).toNat = (st.x n).toNat - (-off).toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_ofNat_lt (by omega)]; omega),
        toNat_ofNat_lt (by omega)]
    obtain ⟨s2, r2, N2⟩ := n_ldr S N1 hB a1 hd hd0 (by decide) o16 (by decide) (by decide) (by rw [e2]; omega) hw
    exact ⟨s2, Runs.trans r1 r2, N2⟩

theorem n_memSt (S : A64SemN M X W) {h t n a : Nat} {v : UInt64} {off : Int} (hM : NMid X W K A s0 st h s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hA : ∀ i, i < (NTm.memW true t (armReg n) off).length → A[h + i]? = (NTm.memW true t (armReg n) off)[i]?)
    (ht : t < 31) (ht16 : t ≠ 16) (hv : (M.observe s).register t = v) (hn : mapped n = true) (hn0 : n ≠ 0)
    (hoff : -4096 < off ∧ off < 32768 ∧ (0 ≤ off → off % 8 = 0))
    (ha : (a : Int) = (st.x n).toNat + off) (hw : wok K a) :
    ∃ s', Runs M s s' ∧
      NMid X W K A s0 { st with m := CallProbe.upd st.m a v } (h + (NTm.memW true t (armReg n) off).length) s' := by
  have hn8 := hM.x n (by omega) (mapped_lt hn)
  by_cases c1 : off % 8 = 0 ∧ 0 ≤ off ∧ off < 32768
  · have e : NTm.memW true t (armReg n) off = [ArmEnc.str t (armReg n) off.toNat] := by
      unfold NTm.memW; rw [if_pos c1]; simp
    rw [e] at hA ⊢
    have a0 : A[h]? = some (ArmEnc.str t (armReg n) off.toNat) := by simpa using hA 0 (by simp)
    exact n_str S hM hB a0 ht hv (armReg_lt hn hn0) hn8 (by omega) (by omega) (by omega) hw
  by_cases c2 : -256 ≤ off ∧ off < 0
  · have e : NTm.memW true t (armReg n) off = [ArmEnc.stur t (armReg n) off] := by
      unfold NTm.memW; rw [if_neg c1, if_pos c2]; simp
    rw [e] at hA ⊢
    have a0 : A[h]? = some (ArmEnc.stur t (armReg n) off) := by simpa using hA 0 (by simp)
    exact n_stur S hM hB a0 ht hv (armReg_lt hn hn0) hn8 (by omega) (by omega) ha hw
  · have e : NTm.memW true t (armReg n) off = [ArmEnc.subi 16 (armReg n) (-off).toNat, ArmEnc.str t 16 0] := by
      unfold NTm.memW; rw [if_neg c1, if_neg c2]; simp
    rw [e] at hA ⊢
    have a0 : A[h]? = some (ArmEnc.subi 16 (armReg n) (-off).toNat) := by simpa using hA 0 (by simp)
    have a1 : A[h + 1]? = some (ArmEnc.str t 16 0) := by simpa using hA 1 (by simp)
    obtain ⟨s1, r1, N1, o16, ok16⟩ := n_subi16 S hM hB a0 hn hn0 (by omega)
    have e2 : (st.x n - UInt64.ofNat (-off).toNat).toNat = (st.x n).toNat - (-off).toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_ofNat_lt (by omega)]; omega),
        toNat_ofNat_lt (by omega)]
    obtain ⟨s2, r2, N2⟩ := n_str S N1 hB a1 ht ((ok16 t ht16).trans hv) (by decide) o16 (by decide) (by decide)
      (by rw [e2]; omega) hw
    exact ⟨s2, Runs.trans r1 r2, N2⟩

/-! ## the atoms -/

theorem asim_ld (S : A64SemN M X W) {d r : Nat} {off : Int} (hok : (NTm.ld d r off).ok = true) :
    ASim M X W (NTm.ld d r off) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hd, hd0⟩, hr, hr0⟩, hoff⟩ := hok
  have c0 : C[q]? = some (.ld d r off) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  obtain ⟨-, -, h1, h2, h3, hw⟩ := hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  have vr : v.x r = st.x r := hag.x r (by omega) (mapped_lt hr) (fun hD => by simpa [NTm.reads] using hrd r hD)
  have hA' : ∀ i, i < (NTm.memW false (armReg d) (armReg r) off).length →
      A[h + i]? = (NTm.memW false (armReg d) (armReg r) off)[i]? := fun i hi => hA i hi
  obtain ⟨s', rn, N⟩ := n_memLd S hM hB hA' hd hd0 hr hr0 hoff (a := CallProbe.ea (st.x r) off)
    (by rw [vr]; unfold CallProbe.ea; omega) hw
  have e : v.m (CallProbe.ea (st.x r) off) = st.m (CallProbe.ea (st.x r) off) := by rw [hag.m]
  rw [e] at N
  exact ⟨0, _, _, s', Nat.zero_le _, hrest, rn, by rw [show π (q + 1) = _ from hft]; exact N,
    (agree_wr hag d _).mono (fun r' hr' => Or.inl ⟨hr'.1, by
      simp only [NTm.writes, beq_eq_false_iff_ne]; exact fun e => hr'.2 e.symm⟩),
    CallProbe.wr_b _ _ _, CallProbe.wr_w _ _ _, Or.inl rfl⟩

theorem asim_sd (S : A64SemN M X W) {u r : Nat} {off : Int} (hok : (NTm.sd u r off).ok = true) :
    ASim M X W (NTm.sd u r off) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff, decide_eq_true_eq] at hok
  obtain ⟨⟨hu, hr, hr0⟩, hoff⟩ := hok
  have c0 : C[q]? = some (.sd u r off) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  obtain ⟨-, -, h1, h2, h3, hw⟩ := hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  have vr : v.x r = st.x r := hag.x r (by omega) (mapped_lt hr) (fun hD => by simpa [NTm.reads] using hrd r hD)
  have ha : ((CallProbe.ea (st.x r) off : Nat) : Int) = (v.x r).toNat + off := by
    rw [vr]; unfold CallProbe.ea; omega
  by_cases hu0 : u = 0
  · subst hu0
    have ea0 : NTm.a π q h (NTm.sd 0 r off) = ArmEnc.movz 17 0 :: NTm.memW true 17 (armReg r) off := by
      simp [NTm.a]
    have hlen : (NTm.sd 0 r off).alen = (NTm.memW true 17 (armReg r) off).length + 1 := by
      simp [NTm.alen, NTm.a]
    have a0 : A[h]? = some (ArmEnc.movz 17 0) := by
      have := hA 0 (by rw [hlen]; omega); rw [ea0] at this; simpa using this
    have hq := (List.getElem?_eq_some_iff.1 a0).1
    obtain ⟨s1, r1, N1, o1⟩ := nmid_scr hM (Or.inr rfl) (S.movz s 17 0 hM.cfg (nmid_pcok hM hB hq)
      (nmid_fx hM hB (by omega) (by omega)) (by decide) (by decide) (nmid_word hM a0 hB))
    have z17 : (M.observe s1).register 17 = 0 := by rw [o1]; simp [setReg]
    have hA' : ∀ i, i < (NTm.memW true 17 (armReg r) off).length →
        A[h + 1 + i]? = (NTm.memW true 17 (armReg r) off)[i]? := fun i hi => by
      have := hA (i + 1) (by rw [hlen]; omega)
      rw [ea0, show h + (i + 1) = h + 1 + i by omega] at this
      exact this
    obtain ⟨s2, r2, N⟩ := n_memSt S N1 hB hA' (by decide) (by decide) z17 hr hr0 hoff ha hw
    have hs0 : st.x 0 = 0 := hag.x0
    have hagS : Agree D { v with m := CallProbe.upd v.m (CallProbe.ea (st.x r) off) 0 }
        { st with m := CallProbe.upd st.m (CallProbe.ea (st.x r) off) (st.x 0) } :=
      ⟨fun j h0 h32 hd => hag.x j h0 h32 hd, by
        show CallProbe.upd v.m _ 0 = CallProbe.upd st.m _ (st.x 0); rw [hag.m, hs0], hag.x0⟩
    have hh : π (q + 1) = h + 1 + (NTm.memW true 17 (armReg r) off).length := by
      rw [show π (q + 1) = _ from hft]; show h + ((NTm.memW true 17 (armReg r) off).length + 1) = _; omega
    exact ⟨0, _, _, s2, Nat.zero_le _, hrest, Runs.trans r1 r2, by rw [hh]; exact N,
      hagS.mono (fun r' hr' => Or.inl ⟨hr', by simp [NTm.writes]⟩), rfl, rfl, Or.inl rfl⟩
  · have hu' : mapped u = true := hu
    have vu : v.x u = st.x u := hag.x u (by omega) (mapped_lt hu') (fun hD => by simpa [NTm.reads] using hrd u hD)
    have ea1 : NTm.a π q h (NTm.sd u r off) = NTm.memW true (armReg u) (armReg r) off := by simp [NTm.a, hu0]
    have hlen : (NTm.sd u r off).alen = (NTm.memW true (armReg u) (armReg r) off).length := by
      simp [NTm.alen, NTm.a, hu0]
    have hA' : ∀ i, i < (NTm.memW true (armReg u) (armReg r) off).length →
        A[h + i]? = (NTm.memW true (armReg u) (armReg r) off)[i]? := fun i hi => by
      have := hA i (by rw [hlen]; exact hi)
      rwa [ea1] at this
    obtain ⟨s', rn, N⟩ := n_memSt S hM hB hA' (armReg_lt hu' hu0) (armReg_ne_scr (j := u)).1
      (hM.x u (by omega) (mapped_lt hu')) hr hr0 hoff ha hw
    rw [vu] at N
    have hagS : Agree D { v with m := CallProbe.upd v.m (CallProbe.ea (st.x r) off) (st.x u) }
        { st with m := CallProbe.upd st.m (CallProbe.ea (st.x r) off) (st.x u) } :=
      ⟨fun j h0 h32 hd => hag.x j h0 h32 hd, by
        show CallProbe.upd v.m _ (st.x u) = CallProbe.upd st.m _ (st.x u); rw [hag.m], hag.x0⟩
    exact ⟨0, _, _, s', Nat.zero_le _, hrest, rn, by rw [show π (q + 1) = _ from hft]; rw [hlen]; exact N,
      hagS.mono (fun r' hr' => Or.inl ⟨hr', by simp [NTm.writes]⟩), rfl, rfl, Or.inl rfl⟩

end JT
