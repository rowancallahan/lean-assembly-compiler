/- Nano/V2Self/Proof/ParInvValRep: the arena validation of task 60 (`v209`) against box B's `nodeOK`, on box C's representation
(parser lead).  Chains (`KidsR`) give `Links` with the kids' root ids; the input-local word `inpC` is `RN.isInp`; `v205` counts the
input-local kids. -/
import Nano.V2Self.Proof.ParInvVal
import Nano.V2Self.Proof.ParInvApi
namespace ParInv
open C BufL ParSpec ParRun

theorem fld_eq (h : Buf) (u k : UInt64) : fld h u k = bget h ((d5 + 8*u) + k) := rfl

/-- the input-local word of a represented node -/
theorem inpC_rn {h : Buf} {u : UInt64} {n : RN} {ids : List UInt64} (r : RNRep h u n ids) :
    inpC h u = if n.isInp then 1 else 0 := by
  cases r with
  | @mk u t a b sh p ks ids a0 a1 a2 a3 a4 a6 ht ha hb k =>
    unfold inpC
    rw [← fld_eq, ← fld_eq, a0, a2]
    simp only [RN.isInp, RN.tag, RN.b, Bool.and_eq_true, beq_iff_eq]
    have et : (t.toUInt64 = 2) ↔ t = 2 := by
      constructor
      · intro e; have := congrArg UInt64.toNat e; simp [Nat.toUInt64, Nat.mod_eq_of_lt ht] at this; exact this
      · intro e; subst e; rfl
    have eb : (b.toUInt64 = 0) ↔ b = 0 := by
      constructor
      · intro e; have := congrArg UInt64.toNat e; simp [Nat.toUInt64, Nat.mod_eq_of_lt hb] at this; exact this
      · intro e; subst e; rfl
    by_cases h1 : t = 2 <;> by_cases h2 : b = 0 <;> simp [h1, h2, et, eb, show k0 = 0 from rfl, show k1 = 1 from rfl]

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
theorem cntC_rn {h : Buf} : ∀ (us : List UInt64) (ns : List RN), us.length = ns.length →
    (∀ i (hi : i < ns.length), ∃ ids', RNRep h (us.getD i 0) (ns[i]'hi) ids') →
    cntC h us = ((ns.filter RN.isInp).length : Nat).toUInt64
  | [], [], _, _ => rfl
  | u :: us, n :: ns, hl, hr => by
    obtain ⟨_, r0⟩ := hr 0 (by simp)
    have ih := cntC_rn us ns (by simpa using hl) (fun i hi => by simpa using hr (i + 1) (by simpa using hi))
    simp only [cntC, ih]
    simp only [List.getElem_cons_zero, List.getD_cons_zero] at r0
    rw [inpC_rn r0]
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

end ParInv
