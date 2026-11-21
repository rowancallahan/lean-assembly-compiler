/- The machine laws of the native AArch64 target for the atom images `NatV` (M3), from the per-atom simulations
(`ASim`, Nano/Run/NatA/) and the image lemmas (NatImgLaws.lean):
* `asim_all`: every well-formed atom has its simulation;
* `nat_seg`: the SEGMENT law: at an anchor the image has an atom; its simulation runs the machine to an exit of the atom,
  which is an anchor (fall-through boundary, jump target, or return point) whose dead flags cover what the atom
  leaves unrelated (`NWf.fall` / `tgt` / `ret`);
* `nat_addi`: the stubs' `addi a0/a1, x0, imm` with the wrapping sum (GenArm's `li` of the immediate);
* `nat_ret`: the return to the host (`br x30`);
* `natLawsOK : A64SemN M X W → NatLawsOK M X W NatV`.
Nothing here mentions a model. -/
import Nano.Run.NatImgLaws
import Nano.Run.NatA.Addi
import Nano.Run.NatA.BGetI
import Nano.Run.NatA.BPushI
import Nano.Run.NatA.BSetI
import Nano.Run.NatA.Bgeu
import Nano.Run.NatA.Cbz
import Nano.Run.NatA.Cj
import Nano.Run.NatA.Jump
import Nano.Run.NatA.Ldp
import Nano.Run.NatA.Ldrbx
import Nano.Run.NatA.Li
import Nano.Run.NatA.Mem
import Nano.Run.NatA.Start
import Nano.Run.NatA.Slli
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

/-- **every well-formed atom is simulated** -/
theorem asim_all (S : A64SemN M X W) : ∀ t : NTm, t.ok = true → ASim M X W t
  | .li _ _, h => asim_li S h
  | .addi d n imm, h => if hn : n = 0 then by subst hn; exact asim_addi_z S h else asim_addi_nz S h hn
  | .alu _ _ _ _, h => asim_alu S h
  | .ld _ _ _, h => asim_ld S h
  | .sd _ _ _, h => asim_sd S h
  | .ldp _ _ _ _, h => asim_ldp S h
  | .cj _ _ _ _, h => asim_cj S h
  | .bgeu _ _ _, h => asim_bgeu S h
  | .lpz _ _, h => asim_lpz S h
  | .bnez _ _, h => asim_bnez S h
  | .beqz _ _, h => asim_beqz S h
  | .jal _ _, h => asim_jal S h
  | .jalr _, h => asim_jalr S h
  | .ldrbx _ _ _, h => asim_ldrbx S h
  | .bgetI, _ => asim_bgetI S
  | .bsetI, h => asim_bsetI S h
  | .bpushI, h => asim_bpushI S h
  | .align8 _ _, h => asim_align8 S h
  | .sb _ _, h => asim_sb S h
  | .slli _ _ _, h => asim_slli S h

/-- an anchor inside the program is the start of an atom -/
theorem vis_at {tl : List NAt} {p : Nat} (hv : nVis tl p) (hp : p < (jOf tl).length) :
    ∃ pre x suf, tl = pre ++ x :: suf ∧ p = (jOf pre).length := by
  obtain ⟨pre, x, suf, i, e, en, hi⟩ := jOf_at tl p hp
  rcases Nat.eq_zero_or_pos i with h | h
  · exact ⟨pre, x, suf, e, by omega⟩
  · exact absurd (en ▸ hv) (at_inner e h hi)

/-- a pc with a link value is a return point: the anchor after a call atom -/
theorem low_ret {tl : List NAt} {p : Nat} (h : (imgOf tl).off p < 2 ^ 64) :
    ∃ pre d5 d6 suf off, tl = pre ++ ⟨.jal 1 off, d5, d6⟩ :: suf ∧ p = (jOf pre).length + 1 ∧ nVis tl p ∧
      p ∈ rets tl 0 := by
  have hr := off_low h
  obtain ⟨pre, ⟨t, d5, d6⟩, suf, off, e, ey, ep⟩ := rets_mem tl 0 p hr
  simp only at ey; subst ey
  have hv := at_vis_end e
  have ep' : p = (jOf pre).length + 1 := by omega
  exact ⟨pre, d5, d6, suf, off, e, ep', by rw [ep']; exact hv, hr⟩

theorem lay_bound (S : A64SemN M X W) {K : LayW} {tl : List NAt} (hl : JTarget.LayOK M (imgOf tl).code.length K) :
    K.base + 4 * (wordsOf tl).length ≤ 2 ^ 32 := by
  have h1 := hl.bhi; rw [imgOf_code_len] at h1; have := S.ram.2; omega

theorem outD_out {x : NAt} {r : Nat} (h : outD x.t (fun r => x.dead r = true) r) : x.out r = true := by
  rcases h with ⟨h1, h2⟩ | h3 <;> simp [NAt.out, *]

/-- **the segment law** of the native target -/
theorem nat_seg (S : A64SemN M X W) {K : LayW} {C : List J} {I : Img} {s0 : M.State} {a z : Nat × CallProbe.St}
    {s : M.State} {n : Nat} (hl : (natTarget M X W NatV).lay K C I) (hR : (natTarget M X W NatV).Rel K C I s0 a s)
    (va : I.vis a.1) (hrun : SRunN K C (n + 1) a z) (vz : I.vis z.1) :
    ∃ m c s', m ≤ n ∧ SRunN K C (n - m) c z ∧ I.vis c.1 ∧ Runs M s s' ∧ (natTarget M X W NatV).Rel K C I s0 c s' := by
  obtain ⟨hlay, tl, rfl, rfl, Wf⟩ := hl
  obtain ⟨q, st⟩ := a
  have hq : q < (jOf tl).length := by
    cases hrun with
    | head hS _ _ =>
      rcases Nat.lt_or_ge q (jOf tl).length with h | h
      · exact h
      · have : (jOf tl)[q]? = none := List.getElem?_eq_none h
        simp [SafeX, this] at hS
  obtain ⟨pre, x, suf, e, eq⟩ := vis_at va hq
  subst eq
  have hsz := Wf.size
  have hB := lay_bound S hlay
  have hxm : x ∈ tl := by rw [e]; simp
  obtain ⟨hM, hag⟩ := nmid_of_rel (A := wordsOf tl) (q := alenL pre) hlay hR rfl
    (by show (imgOf tl).off (jOf pre).length % 2 ^ 64 = _; rw [vis_off (at_vis e) hsz, at_widx e])
  have hag' : Agree (fun r => x.dead r = true) (mview s st) st := hag.mono (fun r hr => (at_dead e r).1 hr)
  have hlk : st.ly = (imgOf tl).ly := hR.lk
  have hlo : ∀ p, st.lo p = (imgOf tl).off p := fun p => by show st.ly.off p = _; rw [hlk]; rfl
  have H : ASim M X W x.t := asim_all S x.t (Wf.ok x hxm)
  obtain ⟨m, ⟨cq, cs⟩, v', s', hm, hc, r, N, ag, cb, cly, hex⟩ :=
    @H K (jOf tl) (wordsOf tl) s0 s (mview s st) st z n (widx (bnd tl 0 0)) (jOf pre).length (alenL pre)
      (fun r => x.dead r = true) (fun i hi => at_j e hi) (fun i hi => at_words e hi) hB hsz hM hag'
      (fun r hr => Wf.rd x hxm r hr) hR.bb (at_widx_end e)
      (fun hcall => by
        obtain ⟨off, ex⟩ := isCall_eq hcall
        have l1 : x.t.j.length = 1 := by rw [ex]; rfl
        have hr : (jOf pre).length + x.t.j.length ∈ rets tl 0 := by
          rw [l1, e]; simpa using mem_rets pre x suf 0 hcall
        rw [hlo, ret_off (at_vis_end e) hr hsz, at_widx_end e])
      (fun p hp => (at_tgt Wf e hp).2.1)
      (fun p hp => by
        rw [hlo] at hp ⊢
        obtain ⟨_, _, _, _, _, -, -, vp, hr⟩ := low_ret hp
        exact ⟨ret_off vp hr hsz, vis_le vp⟩)
      hrun (fun i h0 hi hz => at_inner e h0 hi (hz ▸ vz))
  have fin : nVis tl cq → (∀ r, x.out r = true → nDead tl cq r) →
      ∃ m c s', m ≤ n ∧ SRunN K (jOf tl) (n - m) c z ∧ (imgOf tl).vis c.1 ∧ Runs M s s' ∧
        (natTarget M X W NatV).Rel K (jOf tl) (imgOf tl) s0 c s' := fun vc hd =>
    ⟨m, (cq, cs), s', hm, hc, vc, r, rel_of_nmid (pc := cq) N (ag.mono fun r hr => hd r (outD_out hr)) rfl
      (vis_off vc hsz) (cb.trans hR.bb) (cly.trans hlk)⟩
  rcases hex with ⟨h1, hft⟩ | hp | ⟨hlow, rs, ex⟩
  · have h1' : cq = (jOf pre).length + x.t.j.length := h1
    subst h1'
    exact fin (at_vis_end e) (Wf.fall pre x suf e hft)
  · exact fin (at_tgt Wf e hp).1 (at_tgt Wf e hp).2.2
  · have hlow' : (imgOf tl).off cq < 2 ^ 64 := by
      have : cs.ly.off cq < 2 ^ 64 := hlow
      rw [show cs.ly = (imgOf tl).ly from cly.trans hlk] at this; exact this
    obtain ⟨pre', d5, d6, suf', off, e', ep, vp, -⟩ := low_ret hlow'
    refine fin vp (fun r hr => ?_)
    rw [ep]
    refine Wf.ret pre x suf rs e ex pre' off d5 d6 suf' e' r ?_
    simpa [NAt.out, ex, NTm.writes, NTm.kills] using hr

/-- the atom of an `addi a0/a1, x0, imm` -/
theorem addi0_atom {t : NTm} {a : Nat} {imm : Int} (hok : t.ok = true) (ha : a = 10 ∨ a = 11)
    (h : J.addi a 0 imm ∈ t.j) : t = .addi a 0 imm := by
  cases t <;> simp only [NTm.j] at h <;>
    first
    | (rcases liT_mem h with ⟨_, e⟩ | ⟨_, _, e⟩
       · cases e
       · cases e; simp [NTm.ok] at hok; omega)
    | (cases ‹NCmp› <;> simp_all)
    | (split at h <;> simp at h)
    | simp_all

/-- the atom of a `jalr` -/
theorem jalr_atom {t : NTm} {a b : Nat} (h : J.jalr a b ∈ t.j) : t = .jalr b := by
  cases t <;> simp only [NTm.j] at h <;>
    first
    | (rcases liT_mem h with ⟨_, e⟩ | ⟨_, _, e⟩ <;> cases e)
    | (cases ‹NCmp› <;> simp_all)
    | (split at h <;> simp at h)
    | simp_all

/-- **the stubs' `addi`** (a0 / a1 := the immediate, any sign) -/
theorem nat_addi (S : A64SemN M X W) {K : LayW} {C : List J} {I : Img} {s0 : M.State} {pc : Nat} {st : CallProbe.St}
    {s : M.State} {rd : Nat} {imm : Int} (hl : (natTarget M X W NatV).lay K C I)
    (hR : (natTarget M X W NatV).Rel K C I s0 (pc, st) s) (v0 : I.vis pc) (_v1 : I.vis (pc + 1))
    (hc : C[pc]? = some (.addi rd 0 imm)) (hrd : rd = 10 ∨ rd = 11) (_h1 : -2048 ≤ imm) (_h2 : imm < 2048) :
    ∃ s', Runs M s s' ∧
      (natTarget M X W NatV).Rel K C I s0 (pc + 1, CallProbe.wr st rd (st.x 0 + UInt64.ofInt imm)) s' := by
  obtain ⟨hlay, tl, rfl, rfl, Wf⟩ := hl
  obtain ⟨pre, ⟨t, d5, d6⟩, suf, e, eq⟩ := vis_at v0 (List.getElem?_eq_some_iff.1 hc).1
  subst eq
  have hsz := Wf.size
  have hB := lay_bound S hlay
  have hxm : (⟨t, d5, d6⟩ : NAt) ∈ tl := by rw [e]; simp
  have hj0 := at_j e (i := 0) (NTm.j_pos t)
  rw [Nat.add_zero, hc] at hj0
  have et : t = .addi rd 0 imm := addi0_atom (Wf.ok _ hxm) hrd (List.mem_of_getElem? hj0.symm)
  subst et
  obtain ⟨hM, hag⟩ := nmid_of_rel (A := wordsOf tl) (q := alenL pre) hlay hR rfl
    (by show (imgOf tl).off (jOf pre).length % 2 ^ 64 = _; rw [vis_off (at_vis e) hsz, at_widx e])
  have hmr : mapped rd = true ∧ rd ≠ 0 := by rcases hrd with rfl | rfl <;> exact ⟨by decide, by decide⟩
  have hal : (NTm.addi rd 0 imm).alen = (liL (armReg rd) (UInt64.ofInt imm).toNat).length := by
    simp [NTm.alen, NTm.a]
  obtain ⟨s', r, N⟩ := n_liN S hM hB (UInt64.toNat_lt _) hmr.1 hmr.2 (fun i hi => by
    have := at_words e (i := i) (by rw [hal]; exact hi)
    simpa [NTm.a] using this)
  refine ⟨s', r, rel_of_nmid (pc := (jOf pre).length + 1) N ?_ rfl ?_
    ((CallProbe.wr_b _ _ _).trans hR.bb) ((CallProbe.wr_w _ _ _).trans hR.lk)⟩
  · have e0 : st.x 0 + UInt64.ofInt imm = UInt64.ofNat (UInt64.ofInt imm).toNat := by
      rw [hR.x0, UInt64.zero_add, UInt64.ofNat_toNat]
    rw [e0]
    refine (agree_wr hag rd _).mono (fun r hr => ?_)
    have := Wf.fall pre _ suf e rfl r (by
      have hd := (at_dead e r).1 hr.1
      have hne : (rd == r) = false := by simp; exact fun h => hr.2 h.symm
      simp only [NAt.out, NTm.writes, NTm.kills, hne, Bool.not_false, Bool.and_true, Bool.or_false]; exact hd)
    exact this
  · have hv1 := at_vis_end e
    have hw := at_widx_end e
    simp only [NTm.j, List.length_singleton] at hv1 hw
    rw [vis_off hv1 hsz, hw, hal]

/-- **the return to the host**: `br x30` -/
theorem nat_ret (S : A64SemN M X W) {K : LayW} {C : List J} {I : Img} {s0 : M.State} {pc : Nat} {st : CallProbe.St}
    {s : M.State} (hl : (natTarget M X W NatV).lay K C I) (hR : (natTarget M X W NatV).Rel K C I s0 (pc, st) s)
    (v0 : I.vis pc) (hc : C[pc]? = some (.jalr 0 1)) (_h4 : (st.x 1).toNat % 4 = 0) :
    ∃ s', Runs M s s' ∧ (M.observe s').programCounter = st.x 1 ∧
      (∀ r, (M.observe s').register r = (M.observe s).register r) ∧
      (M.observe s').memory = (M.observe s).memory ∧ M.configured s' := by
  obtain ⟨hlay, tl, rfl, rfl, Wf⟩ := hl
  obtain ⟨pre, ⟨t, d5, d6⟩, suf, e, eq⟩ := vis_at v0 (List.getElem?_eq_some_iff.1 hc).1
  subst eq
  have hsz := Wf.size
  have hB := lay_bound S hlay
  have hj0 := at_j e (i := 0) (NTm.j_pos t)
  rw [Nat.add_zero, hc] at hj0
  have et : t = .jalr 1 := jalr_atom (List.mem_of_getElem? hj0.symm)
  subst et
  obtain ⟨hM, -⟩ := nmid_of_rel (A := wordsOf tl) (q := alenL pre) hlay hR rfl
    (by show (imgOf tl).off (jOf pre).length % 2 ^ 64 = _; rw [vis_off (at_vis e) hsz, at_widx e])
  have hA : (wordsOf tl)[alenL pre]? = some (ArmEnc.brR (armReg 1)) := by
    have := at_words e (i := 0) (NTm.alen_pos _)
    simpa [NTm.a] using this
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  obtain ⟨s', r, c, o, -⟩ := S.br s (armReg 1) hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (by decide) (nmid_word hM hA hB)
  have hx1 : (M.observe s).register (armReg 1) = st.x 1 := hR.x 1 (by omega) (by omega) (by
    rintro ⟨y, -, hd⟩
    simp [NAt.dead] at hd)
  exact ⟨s', r, by rw [o]; exact hx1, fun r => by rw [o]; rfl, by rw [o]; rfl, c⟩

/-- **the machine laws of the native target**, from the abstract A64 steps alone -/
theorem natLawsOK (S : A64SemN M X W) : NatLawsOK M X W NatV where
  entry := natV_entry
  off_le := natV_off_le
  vis_link := natV_vis_link
  vis_ret := natV_vis_ret
  live_ret C I pc h _ := natV_live_ret C I pc h
  vis_err := natV_vis_err
  seg := nat_seg S
  addi_ok := nat_addi S
  ret_ok := nat_ret S

end JT
