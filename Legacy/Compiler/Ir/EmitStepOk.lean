/- One step of a Lin run, simulated by the machine (`step_ok`), and the end of the run (`done_ok`). -/
import Legacy.Compiler.Ir.EmitStep

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

namespace Ctx
variable {T : Target} {C : Ctx T}

theorem drop_cons {l : List (Inst Nat)} {k : Nat} {i : Inst Nat} (hk : l[k]? = some i) :
    l.drop k = i :: l.drop (k + 1) := by
  have hkl : k < l.length := (List.getElem?_eq_some_iff.1 hk).1
  rw [List.drop_eq_getElem_cons hkl]; congr; exact (List.getElem?_eq_some_iff.1 hk).2

theorem emitIs_cons {E : Env} {nS ex q : Nat} {i : Inst Nat} {is : List (Inst Nat)} {c : List EOp}
    (h : T.emitIs E nS ex q (i :: is) = some c) :
    ∃ ci cr, T.emitI' E nS ex q i = some ci ∧ T.emitIs E nS ex (q + T.len ci) is = some cr ∧ c = ci ++ cr := by
  simp only [Target.emitIs] at h
  cases hci : T.emitI' E nS ex q i with
  | none => rw [hci] at h; exact nomatch h
  | some ci =>
    rw [hci] at h; simp only at h
    cases hcr : T.emitIs E nS ex (q + T.len ci) is with
    | none => rw [hcr] at h; exact nomatch h
    | some cr => rw [hcr] at h; cases h; exact ⟨ci, cr, rfl, hcr, rfl⟩

/-- cells in use fit when the cells are below the frame -/
theorem fits_of {cells fb : Nat} (hcap : C.wb + 8 * cells ≤ fb) (hfb : fb ≤ C.T0) (hal : fb % 8 = 0) :
    cells + (C.T0 - fb) / 8 ≤ C.wl / 8 := by
  have := C.T0_al; have : C.T0 = C.wb + C.wl / 8 * 8 := rfl; have := C.wal; omega

theorem over_of {cells fb : Nat} (hcap : fb < C.wb + 8 * cells) (hfb : fb ≤ C.T0) (hal : fb % 8 = 0) :
    C.wl / 8 < cells + (C.T0 - fb) / 8 := by
  have := C.T0_al; have : C.T0 = C.wb + C.wl / 8 * 8 := rfl; have := C.wal; omega

/-- **an instruction other than `call`** -/
theorem stepI_ok {Q : Prog Nat} {L : Lay} {qs : Nat} (hK : Code C Q L qs) {st st' : State Nat} {s : T.S}
    {fr : Frame Nat} {below : List (Frame Nat)} {F : Func Nat} {B : Block Nat} {fb : Nat} {sv : BitVec 64}
    {M : Nat → Option (BitVec 8)} {q : Nat} {c ct : List EOp} {i : Inst Nat}
    (hst : st.stack = fr :: below) (hF : Q.funcs[fr.f]? = some F) (hB : F.blocks.lookup fr.l = some B)
    (hc : T.emitIs (Q.env L) F.slots L.ex q (B.body.drop fr.pc) = some c)
    (hct : T.emitT F F.slots (L.posF fr.f) (q + T.len c) B.term = some ct) (hin : InW C.W q (T.words (c ++ ct)))
    (hA : C.AtQ s q) (hR : (C.fa F.slots fb sv M).MR st.mem fr.regs s)
    (hS : C.Stk Q L qs st.mem.blks below M fb F.slots sv fr.dst fr.f)
    (hiu : inUse (st.ev ++ [Ctx.base Q]) = st.mem.cells.length + (C.T0 - fb) / 8)
    (hpk : peak (st.ev ++ [Ctx.base Q]) ≤ C.wl / 8)
    (hk : B.body[fr.pc]? = some i) (hi : ∀ ds g as, i ≠ .call ds g as) (hs : step Q st = .next st')
    (hO : st'.mem.out.length ≤ C.outL) :
    T.runsTo s fun s' => C.Rel Q L qs st' s' ∨ (C.wl / 8 < inUse (st'.ev ++ [Ctx.base Q]) ∧ C.Exited s') := by
  rw [drop_cons hk] at hc
  obtain ⟨ci, cr, hci, hcr, rfl⟩ := emitIs_cons hc
  have hci' : T.emitI F.slots L.ex q i = some ci := by
    cases i with
    | call ds g as => exact absurd rfl (hi ds g as)
    | _ => exact hci
  have hnf : ∀ p, i ≠ .free p := by rintro p rfl; simp [Target.emitI] at hci'
  rw [step_inst hst hF hB hk hi] at hs
  cases hx : i.exec st.mem fr.regs with
  | none => simp only [hx] at hs; exact nomatch hs
  | some r =>
  obtain ⟨g', m', e⟩ := r
  simp only [hx] at hs; cases hs
  obtain ⟨hal', hiu'⟩ := exec_ev hx hnf
  obtain ⟨X, hX⟩ := exec_blks hx hnf
  have hin' : InW C.W q (T.words ci ++ (T.words cr ++ T.words ct)) := by
    simpa only [T.words_append, List.append_assoc] using hin
  obtain ⟨rex, hex⟩ := hK.exit
  have hfb := hS.fit; have hal := hR.fal; simp only [fa_F0, fa_nS] at hfb hal
  refine T.toCore.runsTo_mono (Ctx.inst_ok (C := C.fa F.slots fb sv M) hA hR hci' hin' hex hx hO) fun s' h => ?_
  have hiu2 : inUse (e ++ st.ev ++ [Ctx.base Q]) = m'.cells.length + (C.T0 - fb) / 8 := by
    rw [List.append_assoc, inUse_append_allocs _ _ hal', hiu, ← hiu']; omega
  rcases h with ⟨hA', hR'⟩ | ⟨hlt, hE⟩
  · refine .inl ⟨{ fr with pc := fr.pc + 1, regs := g' }, below, F, B, fb, sv, M, q + T.len ci, cr, ct, rfl, hF, hB,
      hcr, ?_, by rw [T.words_append]; exact hin'.right, hA', hR', ?_, hiu2, ?_⟩
    · have : q + T.len ci + T.len cr = q + T.len (ci ++ cr) := by rw [Target.len_append]; omega
      rw [this]; exact hct
    · simp only; rw [hX]; exact hS.ext X
    · have hfit := fits_of (C := C) (cells := m'.cells.length) (fb := fb) hR'.cap (by omega) hal
      have he : e = [] ∨ ∃ n, e = [.alloc n] := by
        cases i <;> simp only [Inst.exec] at hx <;> (repeat' split at hx) <;> (try cases hx) <;> simp
        all_goals first | exact absurd rfl (hnf _) | (exact absurd rfl (hi _ _ _))
      rcases he with rfl | ⟨n, rfl⟩
      · simpa using hpk
      · have h2 : [MemEvent.alloc n] ++ st.ev ++ [Ctx.base Q] = .alloc n :: (st.ev ++ [Ctx.base Q]) := rfl
        rw [h2] at hiu2 ⊢; exact peak_cons_le (by rw [hiu2]; exact hfit) hpk
  · exact .inr ⟨by rw [hiu2]; exact over_of hlt (by omega) hal, hE⟩


theorem emitCall_cond {E : Env} {nS ex q : Nat} {ds : List Nat} {g : FId} {as : List (Arg Nat)} {cc : List EOp}
    (h : T.emitCall E nS ex q ds g as = some cc) : ds.length ≤ 7 ∧ ∀ d ∈ ds, d < nS := by
  unfold Target.emitCall at h
  split at h
  · next hc => exact ⟨hc.2.1, fun d hd => of_decide_eq_true (List.all_eq_true.1 hc.2.2.2.1 d hd)⟩
  · exact nomatch h

theorem env_fs {Q : Prog Nat} {L : Lay} {g : FId} {G : Func Nat} (hG : Q.funcs[g]? = some G) :
    (Q.env L).fs g = G.slots := by simp [Prog.env, hG]

/-- **a call** -/
theorem stepC_ok {Q : Prog Nat} {L : Lay} {qs : Nat} (hK : Code C Q L qs) {st st' : State Nat} {s : T.S}
    {fr : Frame Nat} {below : List (Frame Nat)} {F : Func Nat} {B : Block Nat} {fb : Nat} {sv : BitVec 64}
    {M : Nat → Option (BitVec 8)} {q : Nat} {c ct : List EOp} {ds : List Nat} {g : FId} {as : List (Arg Nat)}
    (hst : st.stack = fr :: below) (hF : Q.funcs[fr.f]? = some F) (hB : F.blocks.lookup fr.l = some B)
    (hc : T.emitIs (Q.env L) F.slots L.ex q (B.body.drop fr.pc) = some c)
    (hct : T.emitT F F.slots (L.posF fr.f) (q + T.len c) B.term = some ct) (hin : InW C.W q (T.words (c ++ ct)))
    (hA : C.AtQ s q) (hR : (C.fa F.slots fb sv M).MR st.mem fr.regs s)
    (hS : C.Stk Q L qs st.mem.blks below M fb F.slots sv fr.dst fr.f)
    (hiu : inUse (st.ev ++ [Ctx.base Q]) = st.mem.cells.length + (C.T0 - fb) / 8)
    (hpk : peak (st.ev ++ [Ctx.base Q]) ≤ C.wl / 8)
    (hk : B.body[fr.pc]? = some (.call ds g as)) (hs : step Q st = .next st') :
    T.runsTo s fun s' => C.Rel Q L qs st' s' ∨ (C.wl / 8 < inUse (st'.ev ++ [Ctx.base Q]) ∧ C.Exited s') := by
  obtain ⟨G, hG, hl, rfl⟩ := step_call_inv hst hF hB hk hs
  rw [drop_cons hk] at hc
  obtain ⟨cc, cr, hcc, hcr, rfl⟩ := emitIs_cons hc
  have hcc' : T.emitCall (Q.env L) F.slots L.ex q ds g as = some cc := hcc
  obtain ⟨hd7, hdl⟩ := emitCall_cond hcc'
  have hK' := hK.fn g G hG
  obtain ⟨jg, rest'', hjg, hpro⟩ := hK'.pro
  obtain ⟨BG, hBG⟩ := hK'.ent
  obtain ⟨cg, ctg, hcg, hctg, hing⟩ := hK'.blocks _ _ hBG
  obtain ⟨rex, hex⟩ := hK.exit
  have hin' : InW C.W q (T.words cc ++ (T.words cr ++ T.words ct)) := by
    simpa only [T.words_append, List.append_assoc] using hin
  have hfb := hS.fit; have hal := hR.fal; simp only [fa_F0, fa_nS] at hfb hal
  refine T.toCore.runsTo_mono (Ctx.call_ok (C := C.fa F.slots fb sv M) (G := G) hA hR hcc' hin' hex (env_fs hG)
    hjg hpro hl.symm hK'.ps) fun s' h => ?_
  have hev : (MemEvent.alloc (G.slots + 1) :: st.ev) ++ [Ctx.base Q] = .alloc (G.slots + 1) :: (st.ev ++ [Ctx.base Q]) := rfl
  rcases h with ⟨c1, M', rfl, hsnap, hA', hfits, hR'⟩ | ⟨hlt, hE⟩
  · left
    simp only [fa_F0, fa_wb] at hfits hR'
    refine ⟨_, _, G, BG, fb - 8 * (G.slots + 1), _, M', L.posF g G.entry, cg, ctg, rfl, hG, hBG,
      by simpa using hcg, hctg, hing, hA', hR', ?_, ?_, ?_⟩
    · refine ⟨F, B, as, q + T.len c1, cr, ct, M, sv, hF, hB, Nat.le_add_left _ _, by simpa using hk, hd7, hdl, (env_fs hG).symm,
        rfl, ?_, ?_, ?_, ?_, hR.valid, ?_⟩
      · simpa only [Target.len_append, Nat.add_assoc] using hcr
      · have : q + T.len c1 + T.len (Target.callPost G.slots ds) + T.len cr =
            q + T.len (c1 ++ Target.callPost G.slots ds ++ cr) := by simp only [Target.len_append]; omega
        rw [this]; exact hct
      · have h2 := hin'
        rw [T.words_append, List.append_assoc] at h2
        have h3 := h2.right
        simp only [T.words_append, List.append_assoc] at h3 ⊢; exact h3
      · rw [show fb - 8 * (G.slots + 1) + 8 * (G.slots + 1) = fb by omega]; exact (Snap.blks).1 hsnap
      · rw [show fb - 8 * (G.slots + 1) + 8 * (G.slots + 1) = fb by omega]; exact hS
    · rw [hev, inUse, hiu]; have := C.T0_al; dsimp only; omega
    · rw [hev]; refine peak_cons_le ?_ hpk
      rw [inUse, hiu]
      have := fits_of (C := C) (cells := st.mem.cells.length) (fb := fb - 8 * (G.slots + 1)) (by omega) (by omega) (by omega)
      omega
  · right
    refine ⟨?_, hE⟩
    rw [hev, inUse, hiu]; simp only [fa_F0, fa_wb] at hlt
    have := C.T0_al; have : C.T0 = C.wb + C.wl / 8 * 8 := rfl; have := C.wal
    omega


/-- **a terminator other than `ret`** -/
theorem stepJ_ok {Q : Prog Nat} {L : Lay} {qs : Nat} (hK : Code C Q L qs) {st st' : State Nat} {s : T.S}
    {fr : Frame Nat} {below : List (Frame Nat)} {F : Func Nat} {B : Block Nat} {fb : Nat} {sv : BitVec 64}
    {M : Nat → Option (BitVec 8)} {q : Nat} {c ct : List EOp}
    (hst : st.stack = fr :: below) (hF : Q.funcs[fr.f]? = some F) (hB : F.blocks.lookup fr.l = some B)
    (hc : T.emitIs (Q.env L) F.slots L.ex q (B.body.drop fr.pc) = some c)
    (hct : T.emitT F F.slots (L.posF fr.f) (q + T.len c) B.term = some ct) (hin : InW C.W q (T.words (c ++ ct)))
    (hA : C.AtQ s q) (hR : (C.fa F.slots fb sv M).MR st.mem fr.regs s)
    (hS : C.Stk Q L qs st.mem.blks below M fb F.slots sv fr.dst fr.f)
    (hiu : inUse (st.ev ++ [Ctx.base Q]) = st.mem.cells.length + (C.T0 - fb) / 8)
    (hpk : peak (st.ev ++ [Ctx.base Q]) ≤ C.wl / 8)
    (hk : B.body[fr.pc]? = none) (hnr : ∀ vs, B.term ≠ .ret vs) (hs : step Q st = .next st') :
    T.runsTo s fun s' => C.Rel Q L qs st' s' := by
  rw [step_term hst hF hB hk] at hs
  have hd : B.body.drop fr.pc = [] := List.drop_eq_nil_of_le (by simpa using hk)
  rw [hd] at hc; simp only [Target.emitIs, Option.some.injEq] at hc; subst hc
  have hct' : T.emitT F (C.fa F.slots fb sv M).nS (L.posF fr.f) q B.term = some ct := by simp [Target.len] at hct; exact hct
  refine T.toCore.runsTo_mono (Ctx.termJ_ok (C := C.fa F.slots fb sv M) (rest := []) hA hR hct'
    (by simp [Target.words] at hin ⊢; exact hin) hs hnr) fun s' ⟨l', g', B', e, hB', hA', hR'⟩ => ?_
  subst e
  obtain ⟨c', ct', hc', hct'', hin'⟩ := (hK.fn _ _ hF).blocks _ _ hB'
  exact ⟨_, below, F, B', fb, sv, M, L.posF fr.f l', c', ct', rfl, hF, hB', by simpa using hc', hct'', hin', hA', hR',
    hS, hiu, hpk⟩

/-- **a return into the caller** -/
theorem stepR_ok {Q : Prog Nat} {L : Lay} {qs : Nat} (hK : Code C Q L qs) {st st' : State Nat} {s : T.S}
    {fr cfr : Frame Nat} {below : List (Frame Nat)} {F : Func Nat} {B : Block Nat} {fb : Nat} {sv : BitVec 64}
    {M : Nat → Option (BitVec 8)} {q : Nat} {c ct : List EOp} {vs : List (Arg Nat)}
    (hst : st.stack = fr :: cfr :: below) (hF : Q.funcs[fr.f]? = some F) (hB : F.blocks.lookup fr.l = some B)
    (hc : T.emitIs (Q.env L) F.slots L.ex q (B.body.drop fr.pc) = some c)
    (hct : T.emitT F F.slots (L.posF fr.f) (q + T.len c) B.term = some ct) (hin : InW C.W q (T.words (c ++ ct)))
    (hA : C.AtQ s q) (hR : (C.fa F.slots fb sv M).MR st.mem fr.regs s)
    (hS : C.Stk Q L qs st.mem.blks (cfr :: below) M fb F.slots sv fr.dst fr.f)
    (hiu : inUse (st.ev ++ [Ctx.base Q]) = st.mem.cells.length + (C.T0 - fb) / 8)
    (hpk : peak (st.ev ++ [Ctx.base Q]) ≤ C.wl / 8)
    (hk : B.body[fr.pc]? = none) (hret : B.term = .ret vs) (hs : step Q st = .next st') :
    T.runsTo s fun s' => C.Rel Q L qs st' s' := by
  rw [step_term hst hF hB hk, hret] at hs
  simp only [termStep] at hs
  split at hs
  case isFalse => exact nomatch hs
  rename_i hvl
  cases hs
  have hd : B.body.drop fr.pc = [] := List.drop_eq_nil_of_le (by simpa using hk)
  rw [hd] at hc; simp only [Target.emitIs, Option.some.injEq] at hc; subst hc
  rw [hret] at hct
  simp only [Target.emitT, Target.len_nil, Nat.add_zero] at hct
  split at hct
  case isFalse => exact nomatch hct
  rename_i hcond
  obtain ⟨hv7, hvok, -⟩ := hcond
  cases hct
  obtain ⟨Fc, Bc, as, qr, cr, ct', Mc, svc, hFc, hBc, hpc1, hcall, hd7, hdl, hnA, hsv, hcr, hct', hinr, hsnap, hval, hS'⟩ := hS
  have hKF := hK.fn _ _ hF; have hKc := hK.fn _ _ hFc
  have hfitc := hS'.fit
  have hfb := hR.fit; have hal := hR.fal; simp only [fa_F0, fa_nS, fa_T0] at hfb hal
  refine T.toCore.runsTo_trans (Ctx.ret_ok (C := C.fa F.slots fb sv M) (rest := []) hA hR hv7 hvok
    (by simp at hin ⊢; exact hin) (by rw [fa_sv, hsv]; exact retOK_at hinr))
    fun s1 ⟨hpc1', hP1, hab1, hv1⟩ => ?_
  rw [fa_sv, hsv] at hpc1'
  have hA1 : C.AtQ s1 qr := ⟨hP1.ok, hpc1', hP1.unch⟩
  have hinr' : InW C.W qr (T.words (Target.callPost F.slots fr.dst) ++ (T.words cr ++ T.words ct')) := by
    simpa only [T.words_append, List.append_assoc] using hinr
  have hP1' : (C.fa Fc.slots (fb + 8 * (F.slots + 1)) svc Mc).Pre st.mem
      ((C.fa Fc.slots (fb + 8 * (F.slots + 1)) svc Mc).F0 - 8 * (F.slots + 1)) F.slots s1 := by
    rw [fa_F0, show fb + 8 * (F.slots + 1) - 8 * (F.slots + 1) = fb by omega]; exact Pre.fa (Pre.unfa hP1)
  have hsnap1 : (C.fa Fc.slots (fb + 8 * (F.slots + 1)) svc Mc).Snap st.mem cfr.regs (T.mem s1) :=
    Snap.congr ((Snap.blks).2 hsnap) (by simp only [fa_F0, fa_nS, fa_T0]; omega)
      (fun x h1 h2 => by simp only [fa_F0, fa_T0] at h1 h2; exact hab1 x h1 h2)
  refine T.toCore.runsTo_mono (Ctx.resume_ok (C := C.fa Fc.slots (fb + 8 * (F.slots + 1)) svc Mc) (n := F.slots)
    (vals := vs.map (Arg.eval fr.regs)) hA1 hP1' (by simp only [fa_F0]; omega) hsnap1 hval hKc.nsl
    (by simp only [fa_F0, fa_nS, fa_T0]; omega) (by simp only [fa_F0]; omega) hKF.big hinr' hdl
    (by simp; omega) hd7 (fun i h => by simp only [List.getElem_map]; exact hv1 i (by simpa using h))
    (fun v hv => by obtain ⟨a, -, rfl⟩ := List.mem_map.1 hv; exact valid_eval hR.valid a))
    fun s2 ⟨hA2, hR2⟩ => ?_
  refine ⟨_, below, Fc, Bc, fb + 8 * (F.slots + 1), svc, Mc, qr + T.len (Target.callPost F.slots fr.dst), cr, ct',
    rfl, hFc, hBc, hcr, hct', by have := hinr'.right; rw [T.words_append]; exact this, hA2, hR2, hS', ?_, ?_⟩
  · show inUse (MemEvent.free (F.slots + 1) :: (st.ev ++ [Ctx.base Q])) =
      st.mem.cells.length + (C.T0 - (fb + 8 * (F.slots + 1))) / 8
    rw [inUse, hiu]; have := C.T0_al; omega
  · refine peak_cons_le ?_ hpk
    show inUse (MemEvent.free (F.slots + 1) :: (st.ev ++ [Ctx.base Q])) ≤ _
    rw [inUse, hiu]
    have := fits_of (C := C) (cells := st.mem.cells.length) (fb := fb) (by have := hR.cap; exact this) (by omega) hal
    omega


/-- **one step** -/
theorem step_ok {Q : Prog Nat} {L : Lay} {qs : Nat} (hK : Code C Q L qs) {st st' : State Nat} {s : T.S}
    (hrel : C.Rel Q L qs st s) (hs : step Q st = .next st') (hO : st'.mem.out.length ≤ C.outL) :
    T.runsTo s fun s' => C.Rel Q L qs st' s' ∨ (C.wl / 8 < inUse (st'.ev ++ [Ctx.base Q]) ∧ C.Exited s') := by
  obtain ⟨fr, below, F, B, fb, sv, M, q, c, ct, hst, hF, hB, hc, hct, hin, hA, hR, hS, hiu, hpk⟩ := hrel
  cases hk : B.body[fr.pc]? with
  | some i =>
    cases i with
    | call ds g as => exact C.stepC_ok hK hst hF hB hc hct hin hA hR hS hiu hpk hk hs
    | _ => exact C.stepI_ok hK hst hF hB hc hct hin hA hR hS hiu hpk hk (by intro _ _ _ h; cases h) hs hO
  | none =>
    cases ht : B.term with
    | ret vs =>
      cases below with
      | nil =>
        rw [step_term hst hF hB hk, ht] at hs; simp only [termStep] at hs; exact nomatch hs
      | cons cfr below' =>
        exact T.toCore.runsTo_mono (C.stepR_ok hK hst hF hB hc hct hin hA hR hS hiu hpk hk ht hs) fun _ h => .inl h
    | _ => exact T.toCore.runsTo_mono (C.stepJ_ok hK hst hF hB hc hct hin hA hR hS hiu hpk hk
        (by intro vs h; rw [ht] at h; cases h) hs) fun _ h => .inl h

/-- **the end of the run**: `main` returns to the stub, which returns to the caller -/
theorem done_ok {Q : Prog Nat} {L : Lay} {qs : Nat} (hK : Code C Q L qs) {st : State Nat} {s : T.S} {r : Result}
    (hrel : C.Rel Q L qs st s) (hs : step Q st = .done r) : T.runsTo s (C.Fin Q r) := by
  obtain ⟨fr, below, F, B, fb, sv, M, q, c, ct, hst, hF, hB, hc, hct, hin, hA, hR, hS, hiu, hpk⟩ := hrel
  cases hk : B.body[fr.pc]? with
  | some i =>
    cases i with
    | call ds g as =>
      unfold step at hs; rw [hst] at hs; simp only [hF, hB, hk] at hs
      split at hs <;> (try split at hs) <;> exact nomatch hs
    | _ =>
      unfold step at hs; rw [hst] at hs; simp only [hF, hB, hk] at hs
      split at hs <;> exact nomatch hs
  | none =>
    rw [step_term hst hF hB hk] at hs
    have hd : B.body.drop fr.pc = [] := List.drop_eq_nil_of_le (by simpa using hk)
    rw [hd] at hc; simp only [Target.emitIs, Option.some.injEq] at hc; subst hc
    cases ht : B.term with
    | ret vs =>
      rw [ht] at hs hct
      cases below with
      | cons cfr below' =>
        simp only [termStep] at hs; split at hs <;> exact nomatch hs
      | nil =>
      simp only [termStep] at hs; cases hs
      simp only [Target.emitT, Target.len_nil, Nat.add_zero] at hct
      split at hct
      case isFalse => exact nomatch hct
      rename_i hcond
      obtain ⟨hv7, hvok, -⟩ := hcond
      cases hct
      obtain ⟨hfit0, hsv, -, -, hgp⟩ := hS
      obtain ⟨rs, hin3⟩ := hK.stub
      have hfb := hR.fal; simp only [fa_F0] at hfb
      refine T.toCore.runsTo_trans (Ctx.ret_ok (C := C.fa F.slots fb sv M) (rest := []) hA hR hv7 hvok
        (by simp at hin ⊢; exact hin) (by rw [fa_sv, hsv]; exact retOK_at hin3)) fun s1 ⟨hpc1, hP1, hab1, hv1⟩ => ?_
      rw [fa_sv, hsv] at hpc1
      have hP1' := Pre.unfa hP1
      simp only [fa_F0, fa_nS] at hP1'
      have hin3' : InW C.W qs (T.encO (.leaveC 0) ++ (T.encO .leave ++ (T.encO (.w (.mov RLen R0)) ++
          (T.encO (.w .ret) ++ rs)))) := by
        simpa only [Target.stub3, Target.words_cons, Target.words_nil, List.append_nil, List.append_assoc] using hin3
      have hA1 : C.AtQ s1 qs := ⟨hP1'.ok, hpc1, hP1'.unch⟩
      have hT := C.T0_le; have hTa := C.T0_al; obtain ⟨hw1, hw2⟩ := C.wR; have hlt := T.ramHi_lt
      have hcap := hP1'.cap
      have hfr1 : (T.fr s1).toNat = C.T0 - 16 := by rw [hP1'.fr, ofNat_toNat' (by omega)]; omega
      refine T.toCore.runsTo_trans (T.c_leaveC (n := 0) (w := T.ra C.s0) (Nat.zero_le _) (C.at_of hA1 hin3'.left)
        (by rw [hfr1]; exact ⟨by omega, by omega⟩) (by rw [hfr1]; omega) (by rw [hfr1]; exact hP1'.stub))
        fun s2 ⟨hok2, hk2, hpc2, hra2, hfr2, hs2, hm2⟩ => ?_
      rw [hfr1] at hfr2
      have hfr2' : (T.fr s2).toNat = C.T0 - 8 := by rw [hfr2, ofNat_toNat' (by omega)]; omega
      have hA2 : C.AtQ s2 (qs + (T.encO (.leaveC 0)).length) :=
        ⟨hok2, by rw [← next_add]; exact hpc2, fun a h1 h2 => by rw [hm2]; exact hP1'.unch a h1 h2⟩
      have hgp2 : bytes (T.mem s2) (C.T0 - 8) 8 = (le8 (T.fr C.s0)).map some := by
        rw [hm2, ← hgp]; exact bytes_congr fun i hi => by
          rw [hab1 _ (by simp only [fa_F0, fa_nS]; omega) (by simp only [fa_T0]; omega)]; rfl
      refine T.toCore.runsTo_trans (T.f_leave (w := T.fr C.s0) (C.at_of hA2 hin3'.right.left)
        (by rw [hfr2']; exact ⟨by omega, by omega⟩) (by rw [hfr2']; omega) (by rw [hfr2']; exact hgp2))
        fun s3 ⟨hok3, hk3, hpc3, hfr3, hs3, hm3⟩ => ?_
      have hA3 : C.AtQ s3 (qs + (T.encO (.leaveC 0)).length + (T.encO .leave).length) :=
        ⟨hok3, by rw [← next_add]; exact hpc3, fun a h1 h2 => by rw [hm3]; exact hA2.2.2 a h1 h2⟩
      refine T.toCore.runsTo_trans (C.op hA3 hin3'.right.right fun h => T.toCore.runsTo_mono (T.w_mov h)
        fun s' ⟨d, st, hm⟩ => ⟨d, hm, st⟩) fun s4 ⟨hA4, hk4, hm4, st4⟩ => ?_
      have hra3 : T.ra s3 = T.ra C.s0 := by rw [T.keepF_ra hk3, hra2]
      have hra4 : T.ra s4 = T.ra C.s0 := by rw [T.keep_ra hk4, hra3]
      refine T.toCore.runsTo_mono (T.w_ret (by rw [hra4]; exact C.retOK) (C.at_of hA4 hin3'.right.right.right.left))
        fun s5 ⟨d5, hs5, hm5⟩ => ⟨d5.ok, by rw [← hra4]; exact d5.hpc,
          fun a h1 h2 => by rw [hm5]; exact hA4.2.2 a h1 h2, .inl ⟨hpk, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [hs5, Core.Set1.other T.toCore st4 (by decide), hs3, hs2]; exact hP1'.rin
      · intro i b hi; rw [hm5, hm4, hm3, hm2]; exact hP1'.out i b hi
      · exact T.keepC_trans (T.keepC_trans (T.keepC_trans hP1'.keep hk2) (T.keepC_of_keepF hk3))
          (T.keepC_of_keepF (T.keepF_of_keep (T.keep_trans hk4 d5.keep)))
      · rw [T.keep_fr d5.keep, T.keep_fr hk4, hfr3]
      · intro v hv
        rw [hs5, Core.Set1.same T.toCore st4, hs3, hs2]
        simp only [List.getElem?_map] at hv
        cases h0 : vs[0]? with
        | none => rw [h0] at hv; exact nomatch hv
        | some a =>
          rw [h0] at hv; simp only [Option.map_some, Option.some.injEq] at hv
          obtain ⟨h0l, h0e⟩ := List.getElem?_eq_some_iff.1 h0
          have := hv1 0 h0l
          rw [h0e, hv] at this
          exact this
    | _ =>
      rw [ht] at hs; simp only [termStep] at hs
      (repeat' split at hs) <;> exact nomatch hs

end Ctx
end Proven.Ir
