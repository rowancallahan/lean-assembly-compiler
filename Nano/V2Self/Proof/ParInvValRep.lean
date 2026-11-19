/- Nano/V2Self/Proof/ParInvValRep: the arena validation of task 60 (`v209`) against box B's `nodeOK`, on box C's representation
(parser lead).  Chains (`KidsR`) give `Links` with the kids' root ids; the input-local word `inpC` is `RN.isInp`; `v205` counts the
input-local kids. -/
import Nano.V2Self.Proof.ParInvVal
import Nano.V2Self.Proof.ParInvApi
import Nano.V2Self.Proof.ParRunArena
namespace ParInv
open C BufL ParSpec ParRun

theorem fld_eq (h : Buf) (u k : UInt64) : fld h u k = bget h ((d5 + 8*u) + k) := rfl

/-- the input-local word of a represented node -/
theorem inpC_rn {h : Buf} {u : UInt64} {n : RN} {ids : List UInt64} (r : RNRep h u n ids) :
    inpC h u = if n.tag = 2 ∧ n.b.toUInt64 = 0 then 1 else 0 := by
  cases r with
  | @mk u t a b sh p ks ids a0 a1 a2 a3 a4 a6 ht hab k =>
    unfold inpC
    rw [← fld_eq, ← fld_eq, a0, a2]
    simp only [RN.tag, RN.b, beq_iff_eq]
    have et : (t.toUInt64 = 2) ↔ t = 2 := by
      constructor
      · intro e; have := congrArg UInt64.toNat e; simp [Nat.toUInt64, Nat.mod_eq_of_lt ht] at this; exact this
      · intro e; subst e; rfl
    by_cases h1 : t = 2 <;> by_cases h2 : b.toUInt64 = 0 <;> simp [h1, h2, et, show k0 = 0 from rfl, show k1 = 1 from rfl]

/-- B's input test, as the machine reads it (holds once `RN.isInp` compares the width mod 2^64) -/
def IsInpW : Prop := ∀ n : RN, n.isInp = (n.tag == 2 && n.b.toUInt64 == 0)

theorem toU_beq0 (b : Nat) : (b.toUInt64 == 0) = (b % 2 ^ 64 == 0) := by
  have hz : b.toUInt64 = 0 ↔ b % 2 ^ 64 = 0 := by
    constructor
    · intro h; have := congrArg UInt64.toNat h; simpa using this
    · intro h; apply UInt64.toNat_inj.mp; simpa using h
  cases h1 : (b.toUInt64 == 0) <;> cases h2 : (b % 2 ^ 64 == 0) <;> simp_all

/-- B's `RN.isInp` compares the width word mod 2^64, so `IsInpW` holds -/
theorem isInpW : IsInpW := by
  intro n
  cases n with
  | mk t a b sh p ks => simp only [RN.isInp, RN.tag, RN.b, toU_beq0]

theorem inpC_isInp (hW : IsInpW) {h : Buf} {u : UInt64} {n : RN} {ids : List UInt64} (r : RNRep h u n ids) :
    inpC h u = if n.isInp then 1 else 0 := by
  rw [inpC_rn r, hW n]
  by_cases h1 : n.tag = 2 <;> by_cases h2 : n.b.toUInt64 = 0 <;> simp [h1, h2]

/-- a represented chain: the kids' root ids, linked by the next fields -/
theorem kidsR_links {h : Buf} : ∀ {f : UInt64} {ns : List RN} {ids : List UInt64}, KidsR h f ns ids →
    ∃ us : List UInt64, us.length = ns.length ∧ Links h f us ∧ (∀ u ∈ us, u ∈ ids) ∧
      ∀ i (hi : i < ns.length), ∃ ids', RNRep h (us.getD i 0) (ns[i]'hi) ids' ∧ ∀ v ∈ ids', v ∈ ids
  | _, [], [], .nil => ⟨[], rfl, trivial, by simp, fun i hi => absurd hi (by simp)⟩
  | f, n :: ns, _, .cons (i1 := i1) (ids := ids2) r k => by
    obtain ⟨us, hl, hk, hm, hr⟩ := kidsR_links k
    refine ⟨f :: us, by simp [hl], ⟨rfl, ?_⟩, ?_, ?_⟩
    · rw [← fld_eq]; exact hk
    · intro u hu
      rcases List.mem_cons.mp hu with e | e
      · subst e; exact List.mem_append_left _ r.mem
      · exact List.mem_append_right _ (hm u e)
    · intro i hi
      cases i with
      | zero => exact ⟨i1, by simpa using r, fun v hv => List.mem_append_left _ hv⟩
      | succ i =>
        obtain ⟨ids', r', hv⟩ := hr i (by simpa using hi)
        exact ⟨ids', by simpa using r', fun v hv' => List.mem_append_right _ (hv v hv')⟩

/-- the count of input-local kids, as the word `cntC` adds it up -/
theorem cntC_rn (hW : IsInpW) {h : Buf} : ∀ (us : List UInt64) (ns : List RN), us.length = ns.length →
    (∀ i (hi : i < ns.length), ∃ ids', RNRep h (us.getD i 0) (ns[i]'hi) ids') →
    cntC h us = ((ns.filter RN.isInp).length : Nat).toUInt64
  | [], [], _, _ => rfl
  | u :: us, n :: ns, hl, hr => by
    obtain ⟨_, r0⟩ := hr 0 (by simp)
    have ih := cntC_rn hW us ns (by simpa using hl) (fun i hi => by simpa using hr (i + 1) (by simpa using hi))
    simp only [cntC, ih]
    simp only [List.getElem_cons_zero, List.getD_cons_zero] at r0
    rw [inpC_isInp hW r0]
    cases hn : n.isInp <;> simp [hn, Nat.toUInt64]
    rw [UInt64.add_comm]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem shapeCode_ne0 {h : Buf} {c : UInt64} {s : Sh} (r : ShapeCode h c s) : c ≠ 0 := by
  cases r with
  | uw => decide
  | bf => decide
  | ls => decide
  | nt => decide
  | pr h5 => intro e; subst e; simp at h5

theorem shapeCode_ls {h : Buf} {c : UInt64} {s : Sh} (r : ShapeCode h c s) : (c = 3 ↔ s = .ls) := by
  constructor
  · intro e; subst e; exact ParInv.shapeCode3 r
  · intro e; subst e
    generalize hs : Sh.ls = s' at r
    cases r with
    | ls => rfl
    | _ => cases hs

/-- `v210`'s pure form implies B's `inpMatch` (parameter codes `ws` represent `ps`, kid words are `isInp`) -/
theorem imC_inpMatch {h : Buf} : ∀ (ps : List Sh) (ws : List UInt64) (ks : List RN) (g : Bool),
    ws.length = ps.length → ps.length = ks.length → (∀ i (hi : i < ps.length), ShapeCode h (ws.getD i 0) (ps[i]'hi)) →
    imC ws (if g then 1 else 0) (ks.map fun k => if k.isInp then 1 else 0) = 1 → inpMatch ps g ks = true
  | [], _, [], _, _, _, _, _ => rfl
  | p :: ps, w :: ws, k :: ks, g, hw, hk, hc, hi => by
    have c0 := hc 0 (by simp)
    simp only [List.getD_cons_zero, List.getElem_cons_zero] at c0
    have e3 := shapeCode_ls c0
    simp only [List.map_cons, imC] at hi
    simp only [inpMatch, Bool.and_eq_true, beq_iff_eq]
    have hrec : ∀ g', imC ws (if g' then 1 else 0) (ks.map fun k => if k.isInp then 1 else 0) = 1 → inpMatch ps g' ks = true :=
      fun g' => imC_inpMatch ps ws ks g' (by simpa using hw) (by simpa using hk)
        (fun i hi' => by simpa using hc (i + 1) (by simpa using hi'))
    have k0' : k0 = 0 := rfl
    have k1' : k1 = 1 := rfl
    by_cases hp : p = .ls
    · have hw3 : w = 3 := e3.mpr hp
      subst hp hw3
      cases g <;> cases hki : k.isInp <;> simp [hki, k0', k1'] at hi ⊢
      · exact hrec true (by simpa using hi)
      · exact hrec true (by simpa using hi)
    · have hw3 : w ≠ 3 := fun e => hp (e3.mp e)
      have hpl : (p == Sh.ls) = false := by simpa using hp
      cases g <;> cases hki : k.isInp <;> simp [hki, hw3, hpl, k0', k1'] at hi ⊢
      · exact hrec false (by simpa using hi)
      · exact hrec true (by simpa using hi)
  | [], _, _ :: _, _, _, hk, _, _ => by simp at hk
  | _ :: _, [], _, _, hw, _, _, _ => by simp at hw
  | _ :: _, _ :: _, [], _, _, hk, _, _ => by simp at hk

theorem toU_eq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : (x.toUInt64 = y.toUInt64) ↔ x = y := by
  constructor
  · intro e; have := congrArg UInt64.toNat e; simpa [Nat.toUInt64, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this
  · intro e; rw [e]

theorem toU_lt4 {x : Nat} (hx : x < 2 ^ 64) : (x.toUInt64 < 4) ↔ x < 4 := by
  rw [UInt64.lt_iff_toNat_lt]; simp [Nat.toUInt64, Nat.mod_eq_of_lt hx]

theorem filt_le (ks : List RN) : (ks.filter RN.isInp).length ≤ ks.length := List.length_filter_le _ _

/-- the first part of the per-node check (`rC`): where input-local kids may occur -/
theorem rC_ok (hW : IsInpW) {h : Buf} {u : UInt64} {t a b : Nat} {sh : Option Sh} {p : Bool} {ks : List RN} {ids : List UInt64}
    (r : RNRep h u (.mk t a b sh p ks) ids) (hk : ks.length < 16777216) (hc : rC h u = 1) :
    (let n := RN.mk t a b sh p ks
     let m := (n.kids.filter RN.isInp).length
     let p0 := match n.kids with | k :: _ => k.isInp | [] => false
     if m = 0 then (if n.tag = 9 then !(n.a < 4) else true)
     else if n.tag = 8 then true
     else if n.tag = 6 then n.sh.isNone
     else if n.tag = 9 then (if n.a < 4 then m = 1 && p0 else false)
     else false) = true := by
  cases r with
  | @mk u t a b sh p ks ids a0 a1 a2 a3 a4 a6 ht hab k =>
  obtain ⟨us, hl, hlk, _, hr⟩ := kidsR_links k
  have hm : v205 16777216 h (fld h u 5) ks.length.toUInt64 0 = ((ks.filter RN.isInp).length).toUInt64 := by
    rw [v205_eq h us 16777216 _ _ 0 (by omega) (by simp [Nat.toUInt64]; omega) hlk, UInt64.zero_add]
    exact cntC_rn hW us ks hl (fun i hi => by obtain ⟨ids', r', _⟩ := hr i hi; exact ⟨ids', r'⟩)
  have k0' : k0 = 0 := rfl
  have k1' : k1 = 1 := rfl
  have hmle := filt_le ks
  unfold rC at hc
  simp only [← fld_eq, a0, a1, a6] at hc
  rw [hm] at hc
  simp only [RN.kids, RN.tag, RN.a, RN.sh]
  obtain ⟨M, hM⟩ : ∃ M, (ks.filter RN.isInp).length = M := ⟨_, rfl⟩
  simp only [hM] at hc hmle ⊢
  have hM64 : M < 2 ^ 64 := by omega
  by_cases hm0 : M = 0
  · subst hm0
    simp only [show ((0 : Nat).toUInt64 == 0) = true from rfl, if_true] at hc
    by_cases h9 : t = 9
    · subst h9
      have ha : a < 2 ^ 64 := (hab (by decide) (by decide)).1
      by_cases ha4 : a < 4
      · simp [(toU_lt4 ha).mpr ha4, k0', k1'] at hc
      · simp [ha4]
    · simp [h9]
  · have hmw : (M.toUInt64 == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact hm0 ((toU_eq hM64 (by decide)).mp e)
    simp only [hmw, if_false, Bool.false_eq_true] at hc
    simp only [hm0, if_false]
    by_cases h8 : t = 8
    · simp [h8]
    have h8w : (t.toUInt64 == 8) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact h8 ((toU_eq ht (by decide)).mp e)
    simp only [h8w, h8, if_false, Bool.false_eq_true] at hc ⊢
    by_cases h6 : t = 6
    · subst h6
      simp only [show ((6 : Nat).toUInt64 == 6) = true from rfl, if_true] at hc
      simp only [if_true]
      cases sh with
      | none => rfl
      | some s =>
        have := shapeCode_ne0 (show ShapeCode h (fld h u 3) s from a3)
        simp [this, k0', k1'] at hc
    have h6w : (t.toUInt64 == 6) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact h6 ((toU_eq ht (by decide)).mp e)
    simp only [h6w, h6, if_false, Bool.false_eq_true] at hc ⊢
    by_cases h9 : t = 9
    · subst h9
      have ha : a < 2 ^ 64 := (hab (by decide) (by decide)).1
      simp only [show ((9 : Nat).toUInt64 == 9) = true from rfl, if_true] at hc ⊢
      by_cases ha4 : a < 4
      · simp only [(toU_lt4 ha).mpr ha4, ha4, if_true] at hc ⊢
        by_cases hm1 : M = 1
        · subst hm1
          simp only [show ((1 : Nat).toUInt64 == 1) = true from rfl, if_true] at hc
          simp only [decide_true, Bool.true_and]
          match ks, hl, hr, hlk, a6 with
          | [], _, _, _, _ => simp at hmle
          | kk :: kr, hl, hr, hlk, a6 =>
            have hk' : kr.length + 1 < 16777216 := by simpa using hk
            have hc0 : ((kk :: kr).length.toUInt64 == 0) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq]; intro e
              have := congrArg UInt64.toNat e; simp [Nat.toUInt64] at this; omega
            simp only [hc0, Bool.false_eq_true, if_false] at hc
            obtain ⟨ids', r0, _⟩ := hr 0 (by simp)
            match us, hlk with
            | u0 :: _, ⟨e0, _⟩ =>
              simp only [List.getD_cons_zero, List.getElem_cons_zero] at r0
              have hc' : inpC h (fld h u 5) = 1 := hc
              rw [e0, inpC_isInp hW r0] at hc'
              cases hi : kk.isInp
              · simp [hi] at hc'
              · simp [hi]
        · have hmw1 : (M.toUInt64 == 1) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact hm1 ((toU_eq hM64 (by decide)).mp e)
          simp [hmw1, k0', k1'] at hc
      · simp [(show ¬ (a.toUInt64 < 4) from fun e => ha4 ((toU_lt4 ha).mp e)), k0', k1'] at hc
    · have h9w : (t.toUInt64 == 9) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact h9 ((toU_eq ht (by decide)).mp e)
      simp [h9w, k0', k1'] at hc

/-- `v210` over a represented chain and a represented parameter-code list gives B's `inpMatch` -/
theorem v210_inpMatch (hW : IsInpW) {h : Buf} {f s1 : UInt64} {us : List UInt64} {ks : List RN} {ps : List Sh}
    (hl : us.length = ks.length) (hlk : Links h f us) (hr : ∀ i (hi : i < ks.length), ∃ ids', RNRep h (us.getD i 0) (ks[i]'hi) ids')
    (hk : ks.length < 16777216) (hp : ps.length = ks.length)
    (hcode : ∀ i (hi : i < ps.length), ShapeCode h (bget h (d7 + 4096 + s1 + i.toUInt64)) (ps[i]'hi))
    (hv : v210 16777216 h f s1 0 ks.length.toUInt64 0 = 1) : inpMatch ps false ks = true := by
  let ws := (List.range ps.length).map (fun j => bget h (d7 + 4096 + s1 + j.toUInt64))
  have hwl : ws.length = ps.length := by simp [ws]
  rw [v210_eq h s1 ks.length.toUInt64 us ws 16777216 f 0 0 (by omega) (by simp [Nat.toUInt64]; omega) (by omega) hlk
    (fun j hj => by simp [ws])] at hv
  have hmap : us.map (inpC h) = ks.map fun k => if k.isInp then 1 else 0 := by
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp only [List.getElem_map]
    obtain ⟨ids', r'⟩ := hr i (by simpa using h2)
    rw [← inpC_isInp hW r']
    congr 1
    simp [List.getD, List.getElem?_eq_getElem (show i < us.length by simpa using h1)]
  rw [hmap] at hv
  exact imC_inpMatch ps ws ks false hwl hp (fun i hi => by simpa [ws, List.getD, hi] using hcode i hi) (by simpa using hv)

/-- the "current (last) row" half of `r2C` (state tuples, single-state CONTINUEs): the machine's check gives B's
parameter count + input rule against the last def row -/
theorem lastRow_ok (hW : IsInpW) {h : Buf} {st : St} {bb : Bool} {f : UInt64} {ks : List RN} {ids : List UInt64}
    (hD : DefsRep h st bb) (k : KidsR h f ks ids) (hk : ks.length < 16777216)
    (hc : (if bget h 12 == 0 then k0 else if bget h (d7 + 8 * (bget h 12 - 1) + 6) == ks.length.toUInt64 + 1 then
      v210 16777216 h f (bget h (d7 + 8 * (bget h 12 - 1) + 5) + 1) 0 ks.length.toUInt64 0 else k0) = 1) :
    (match st.defs.getLast? with
      | some d => decide (d.params.length = ks.length + 1) && inpMatch d.params.tail false ks | none => false) = true := by
  obtain ⟨us, hl, hlk, _, hr⟩ := kidsR_links k
  have hr' : ∀ i (hi : i < ks.length), ∃ ids', RNRep h (us.getD i 0) (ks[i]'hi) ids' :=
    fun i hi => by obtain ⟨ids', r', _⟩ := hr i hi; exact ⟨ids', r'⟩
  obtain ⟨e12, hlt, _, hrows, _⟩ := hD
  have k0' : k0 = 0 := rfl
  by_cases hz : bget h 12 = 0
  · simp [hz, k0'] at hc
  · simp only [show (bget h 12 == 0) = false by simpa using hz, Bool.false_eq_true, if_false] at hc
    have hpos : 0 < st.defs.length := by
      rcases Nat.eq_zero_or_pos st.defs.length with e | e
      · exact absurd (UInt64.toNat_inj.mp (by rw [e12, e]; rfl)) hz
      · exact e
    have hj : bget h 12 - 1 = (st.defs.length - 1).toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
      simp [Nat.toUInt64, e12]; omega
    rw [hj] at hc
    obtain ⟨⟨_, _, _, _, _, h6', hs5, hcodes⟩, _⟩ := hrows (st.defs.length - 1) (by omega)
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    generalize hd : st.defs[st.defs.length - 1]'(by omega) = d at h6' hs5 hcodes
    have hplen : d.params.length = ks.length + 1 := by
      by_cases e : bget h (d7 + 8 * (st.defs.length - 1).toUInt64 + 6) = ks.length.toUInt64 + 1
      · rw [e] at h6'
        have : (ks.length.toUInt64 + 1).toNat = ks.length + 1 := by
          rw [UInt64.toNat_add]; simp [Nat.toUInt64]; omega
        omega
      · simp [e, k0'] at hc
    have e6 : bget h (d7 + 8 * (st.defs.length - 1).toUInt64 + 6) = ks.length.toUInt64 + 1 := by
      apply UInt64.toNat_inj.mp; rw [h6', hplen, UInt64.toNat_add]; simp [Nat.toUInt64]; omega
    simp only [e6, beq_self_eq_true, if_true] at hc
    refine ⟨hplen, v210_inpMatch hW hl hlk hr' hk (by simp [hplen]) (fun i hi => ?_) hc⟩
    have := hcodes (i + 1) (by simp at hi; omega)
    have e' : d7 + 4096 + bget h (d7 + 8 * (st.defs.length - 1).toUInt64 + 5) + (i + 1).toUInt64 =
        d7 + 4096 + (bget h (d7 + 8 * (st.defs.length - 1).toUInt64 + 5) + 1) + i.toUInt64 := by
      simp [Nat.toUInt64]; grind
    rw [e'] at this
    simpa [List.getElem_tail] using this


/-- the second part of the per-node check (`r2C`): CALL and CONTINUE-tuple arguments against the callee's parameter codes -/
theorem r2C_ok (hW : IsInpW) {h : Buf} {st : St} {bb : Bool} {u : UInt64} {t a b : Nat} {sh : Option Sh} {p : Bool} {ks : List RN}
    {ids : List UInt64} (r : RNRep h u (.mk t a b sh p ks) ids) (hk : ks.length < 16777216) (hD : DefsRep h st bb)
    (hcall : t = 8 → a < st.defs.length) (hc : r2C h u = 1) :
    (if t = 8 then (match st.defs[a]? with
        | some d => decide (d.params.length = ks.length) && inpMatch d.params false ks | none => false)
     else if t = 6 then (if sh.isNone then (match st.defs.getLast? with
        | some d => decide (d.params.length = ks.length + 1) && inpMatch d.params.tail false ks | none => false) else true)
     else if t = 11 then
      (if (match ks with | k :: _ => k.tag = 6 && k.sh.isNone | [] => false) then true
       else (match st.defs.getLast? with
        | some d => decide (d.params.length = ks.length + 1) && inpMatch d.params.tail false ks | none => false))
     else true) = true := by
  have hD0 := hD
  cases r with
  | @mk u t a b sh p ks ids a0 a1 a2 a3 a4 a6 ht hab k =>
  obtain ⟨us, hl, hlk, _, hr⟩ := kidsR_links k
  have hr' : ∀ i (hi : i < ks.length), ∃ ids', RNRep h (us.getD i 0) (ks[i]'hi) ids' :=
    fun i hi => by obtain ⟨ids', r', _⟩ := hr i hi; exact ⟨ids', r'⟩
  obtain ⟨e12, hlt, _, hrows, _⟩ := hD
  have k0' : k0 = 0 := rfl
  have k1' : k1 = 1 := rfl
  unfold r2C at hc
  simp only [← fld_eq, a0, a1, a6] at hc
  by_cases h8 : t = 8
  · subst h8
    simp only [show ((8 : Nat).toUInt64 == 8) = true from rfl, if_true] at hc
    simp only [if_true]
    have haD := hcall rfl
    obtain ⟨⟨_, _, _, _, _, h6, hs5, hcodes⟩, _⟩ := hrows a haD
    rw [List.getElem?_eq_getElem haD]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    generalize hd : st.defs[a]'haD = d at h6 hs5 hcodes
    have hplen : d.params.length = ks.length := by
      by_cases e : bget h (d7 + 8 * a.toUInt64 + 6) = ks.length.toUInt64
      · rw [e] at h6; simp [Nat.toUInt64] at h6; omega
      · simp [e, k0'] at hc
    have e6 : bget h (d7 + 8 * a.toUInt64 + 6) = ks.length.toUInt64 := by
      apply UInt64.toNat_inj.mp; rw [h6, hplen]; simp [Nat.toUInt64]; omega
    simp only [e6, beq_self_eq_true, if_true] at hc
    exact ⟨hplen, v210_inpMatch hW hl hlk hr' hk hplen hcodes hc⟩
  have h8w : (t.toUInt64 == 8) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact h8 ((toU_eq ht (by decide)).mp e)
  simp only [h8w, h8, if_false, Bool.false_eq_true] at hc ⊢
  by_cases h6 : t = 6
  · subst h6
    simp only [show ((6 : Nat).toUInt64 == 6) = true from rfl, if_true] at hc ⊢
    cases sh with
    | some s => rfl
    | none =>
      have w0 : fld h u 3 = 0 := a3
      simp only [w0, show ((0 : UInt64) == 0) = true from rfl, if_true, Option.isNone_none] at hc ⊢
      by_cases hz : bget h 12 = 0
      · simp [hz, k0'] at hc
      · simp only [show (bget h 12 == 0) = false by simpa using hz, Bool.false_eq_true, if_false] at hc
        have hpos : 0 < st.defs.length := by
          rcases Nat.eq_zero_or_pos st.defs.length with e | e
          · exact absurd (UInt64.toNat_inj.mp (by rw [e12, e]; rfl)) hz
          · exact e
        have hj : bget h 12 - 1 = (st.defs.length - 1).toUInt64 := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
          simp [Nat.toUInt64, e12]; omega
        rw [hj] at hc
        obtain ⟨⟨_, _, _, _, _, h6', hs5, hcodes⟩, _⟩ := hrows (st.defs.length - 1) (by omega)
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        generalize hd : st.defs[st.defs.length - 1]'(by omega) = d at h6' hs5 hcodes
        have hplen : d.params.length = ks.length + 1 := by
          by_cases e : bget h (d7 + 8 * (st.defs.length - 1).toUInt64 + 6) = ks.length.toUInt64 + 1
          · rw [e] at h6'
            have : (ks.length.toUInt64 + 1).toNat = ks.length + 1 := by
              rw [UInt64.toNat_add]; simp [Nat.toUInt64]; omega
            omega
          · simp [e, k0'] at hc
        have e6 : bget h (d7 + 8 * (st.defs.length - 1).toUInt64 + 6) = ks.length.toUInt64 + 1 := by
          apply UInt64.toNat_inj.mp; rw [h6', hplen, UInt64.toNat_add]; simp [Nat.toUInt64]; omega
        simp only [e6, beq_self_eq_true, if_true] at hc
        refine ⟨hplen, v210_inpMatch hW hl hlk hr' hk (by simp [hplen]) (fun i hi => ?_) hc⟩
        have := hcodes (i + 1) (by simp at hi; omega)
        have e' : d7 + 4096 + bget h (d7 + 8 * (st.defs.length - 1).toUInt64 + 5) + (i + 1).toUInt64 =
            d7 + 4096 + (bget h (d7 + 8 * (st.defs.length - 1).toUInt64 + 5) + 1) + i.toUInt64 := by
          simp [Nat.toUInt64]; grind
        rw [e'] at this
        simpa [List.getElem_tail] using this
  have h6w : (t.toUInt64 == 6) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact h6 ((toU_eq ht (by decide)).mp e)
  simp only [h6w, h6, if_false, Bool.false_eq_true] at hc ⊢
  by_cases h11 : t = 11
  · subst h11
    simp only [show ((11 : Nat).toUInt64 == 11) = true from rfl, if_true] at hc ⊢
    have LR := fun hc' => lastRow_ok hW hD0 k hk hc'
    cases ks with
    | nil =>
      have e0 : (([] : List RN).length.toUInt64 == 0) = true := rfl
      simp only [e0, if_true] at hc
      simpa using LR hc
    | cons k0 rest =>
      have hk' : rest.length + 1 < 16777216 := by simpa using hk
      have hne : ((k0 :: rest).length.toUInt64 == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro e
        have := congrArg UInt64.toNat e; simp [Nat.toUInt64] at this; omega
      simp only [hne, Bool.false_eq_true, if_false] at hc
      obtain ⟨b0, b3, bt⟩ : fld h (fld h u 5) 0 = k0.tag.toUInt64 ∧ ShOpt h (fld h (fld h u 5) 3) k0.sh ∧ k0.tag < 2 ^ 64 := by
        cases k with
        | cons r0 _ => cases r0 with
          | mk e0 _ _ e3 _ _ et _ _ => exact ⟨e0, e3, et⟩
      rw [b0] at hc
      by_cases hk6' : (decide (k0.tag = 6) && k0.sh.isNone) = true
      · simp only [hk6', if_true]
      · simp only [hk6', Bool.false_eq_true, if_false]
        have hk6 : k0.tag = 6 → ¬ k0.sh.isNone = true := by
          intro a b; apply hk6'; simp [a, b]
        apply LR
        by_cases t6 : k0.tag = 6
        · have hs := hk6 t6
          obtain ⟨s0, hs0⟩ : ∃ s0, k0.sh = some s0 := by
            cases e : k0.sh with
            | none => rw [e] at hs; exact absurd rfl hs
            | some s0 => exact ⟨s0, rfl⟩
          have hsc : fld h (fld h u 5) 3 ≠ 0 := by
            have := b3; rw [hs0] at this; exact shapeCode_ne0 this
          have e1 : (k0.tag.toUInt64 == 6) = true := by simp [t6]
          have e2 : (fld h (fld h u 5) 3 == 0) = false := by simpa using hsc
          simp only [e1, if_true, e2, Bool.false_eq_true, if_false] at hc
          exact hc
        · have e1 : (k0.tag.toUInt64 == 6) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact t6 ((toU_eq bt (by decide)).mp e)
          simp only [e1, Bool.false_eq_true, if_false] at hc
          exact hc
  · simp [h11]

/-- **per-node validation**: the machine's check of a represented node implies B's `nodeOK` -/
theorem nodeC_ok (hW : IsInpW) {h : Buf} {st : St} {bb : Bool} {u : UInt64} {n : RN} {ids : List UInt64}
    (r : RNRep h u n ids) (hk : n.kids.length < 16777216) (hD : DefsRep h st bb)
    (hcall : n.tag = 8 → n.a < st.defs.length) (hc : nodeC h u = true) : nodeOK st.defs n = true := by
  unfold nodeC at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  match n, r, hk, hcall with
  | .mk t a b sh p ks, r, hk, hcall =>
    have h1 := rC_ok hW r hk hc.1
    have h2 := r2C_ok hW r hk hD hcall hc.2
    unfold nodeOK
    simp only [RN.kids, RN.tag, RN.a, RN.sh] at h1 h2 ⊢
    rw [Bool.and_eq_true]; exact ⟨h1, h2⟩

/-- **task 60's validation**: on a heap representing the arena and the def rows, `v209 = 1` gives B's check on every arena node -/
theorem v209_nodeOK (hW : IsInpW) {h : Buf} {st : St} {bb : Bool} (hA : ArenaRep h st.arena st.vals) (hD : DefsRep h st bb)
    (hI : ArenaInv st) (hC : CallInv st) (hv : v209 16777216 h 0 = 1) : st.arena.all (nodeOK st.defs) = true := by
  obtain ⟨h9, hle, _, _, I, hrep, _⟩ := hA
  have hall := (v209_eq h (bget h 9).toNat 16777216 0 (by simp) (by simp) (by omega)).1.mp hv
  rw [List.all_eq_true]
  intro m hm
  obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem hm
  obtain ⟨r, _, _⟩ := hrep u hu
  have hk := kids_lt_arena hI hm
  exact nodeC_ok hW r (by omega) hD (fun e => hC _ hm e) (by simpa using hall u (by simp) (by omega))

end ParInv
