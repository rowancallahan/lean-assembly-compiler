/- Nano/V2Self/Proof/Parser/ParInvApi: the fields of `RepAPI` (ParInvTop) that follow from box C's state relation directly (parser lead).
* `out_of` : `OutRep` ⇒ the heap tail after the token sentinel IS the emitted word list;
* `ntasks_of` : `TasksRep` ⇒ (h[5] = 0 ↔ no frame). -/
import Nano.V2Self.Proof.Parser.ParInvState
import Nano.V2Self.Proof.Parser.ParInvTop
namespace ParInv
open C BufL ParSpec ParRun

theorem ntasks_of {h : Buf} {arena : List RN} {fs : List Frame} (r : TasksRep h arena fs) : (bget h 5 = 0 ↔ fs = []) := by
  obtain ⟨h5, _, _⟩ := r
  constructor
  · intro e; rw [e] at h5; simp at h5; exact List.length_eq_zero_iff.mp h5.symm
  · intro e; subst e; apply UInt64.toNat_inj.mp; simpa using h5

theorem shapeCode3 {h : Buf} {s : Sh} (r : ShapeCode h 3 s) : s = .ls := by
  generalize hc : (3 : UInt64) = c at r
  cases r with
  | uw => simp at hc
  | bf => simp at hc
  | ls => rfl
  | nt => simp at hc
  | pr h5 => subst hc; simp at h5

/-- the main-def cells (incl. the arity cell `= 1`) give `mainOK` -/
theorem main_of {h : Buf} {st : St} {b : Bool} (hD : DefsRep h st b) (h12 : 0 < bget h 12) (hm : MainCells h)
    (hne : ∀ d ∈ st.defs, d.name ≠ []) : mainOK st = true := by
  obtain ⟨e12, hlt, _, hrows, _⟩ := hD
  have hpos : 0 < st.defs.length := by
    have := UInt64.lt_iff_toNat_lt.mp h12; simp at this; omega
  obtain ⟨hrow, _⟩ := hrows (st.defs.length - 1) (by omega)
  have hj : bget h 12 - 1 = (st.defs.length - 1).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
    simp [Nat.toUInt64, e12]; omega
  have hlast : st.defs.getLast? = some (st.defs[st.defs.length - 1]'(by omega)) := by
    rw [List.getLast?_eq_getElem?]; simp
  generalize hd : st.defs[st.defs.length - 1]'(by omega) = d at hrow hlast
  have hdn : d.name ≠ [] := hne d (by rw [← hd]; exact List.getElem_mem _)
  obtain ⟨hname, _, hnni, hres, _, hplen, _, hpar⟩ := hrow
  unfold MainCells at hm
  rw [hj] at hm
  obtain ⟨m1, m2, m3, hA, m4, m5⟩ := hm
  generalize hr : d7 + 8 * (st.defs.length - 1).toUInt64 = r at m1 m2 m3 m4 m5 hA hname hnni hres hplen hpar
  unfold mainOK
  rw [hlast]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨nm, ⟨_, hseq, _⟩, hmap⟩ := hname
    match nm, hseq, hmap with
    | [], _, hmap => exact absurd hmap.symm (by simpa using hdn)
    | c :: t, hseq, hmap =>
      simp only [NameSeq] at hseq
      obtain ⟨_, hc, ht⟩ := hseq
      have e2 : d11 + (bget h r + 1) + 1 = d11 + bget h r + 2 := by grind
      rw [e2, m1] at hc
      cases t with
      | nil => rw [← hmap, ← hc]; rfl
      | cons d' t' =>
        simp only [NameSeq] at ht
        have e3 : d11 + (bget h r + 1 + 2) = d11 + bget h r + 3 := by grind
        rw [e3, m2] at ht
        exact absurd ht.1 (by decide)
  · rw [m3] at hnni; simpa using hnni.symm
  · rw [hA] at hplen; simpa using hplen.symm
  · have hl1 : d.params.length = 1 := by rw [hA] at hplen; simpa using hplen.symm
    match hp : d.params, hl1 with
    | [p0], _ =>
      have := hpar 0 (by simp [hp])
      simp only [hp, List.getElem_cons_zero] at this
      rw [show (d7 + 4096 + bget h (r + 5) + (0 : Nat).toUInt64) = d7 + 4096 + bget h (r + 5) by grind, m4] at this
      simp [shapeCode3 this]
  · rw [m5] at hres
    cases hd2 : d.res with
    | none => rw [hd2] at hres; simp [ShOpt] at hres
    | some s => rw [hd2] at hres; simp [shapeCode3 hres]

end ParInv
