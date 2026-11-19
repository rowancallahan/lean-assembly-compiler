/- Nano/V2Self/Proof/ParRunPrimS: the primary (task 3) ↔ ParSpec `pApp` (box B): leaf atoms (G's `atomLeaf_spec`),
parentheses and tuples; the call-like heads (def call, prim token, self-call) are the hypothesis `HCall`. -/
import Nano.V2Self.Proof.ParRunTup
namespace ParRun
open ParSpec

/-- the conclusion of `PrimSpec` -/
def PrimConcl (n md : Nat) (ks : List Frame) (st fin : St) (cx : Cx) : Prop :=
  ∃ v st' n', n' < n ∧ Post st st' st.vals v ∧ st'.toks.length < st.toks.length ∧ StarN n' (ks, st') ([], fin) ∧ ShNN v.sh ∧
    (VT (rows st) v → ∃ ty, TyRel v ty ∧ (v.toNd.tailCont = true → v.pend = true) ∧
      ∀ f, 4 * st.toks.length + 2 ≤ f → pApp f cx (md == 1) st.toks st.nx = some (v.toNd, ty, st'.toks, st'.nx))

/-- the call-like heads of a primary (box G / box B: `args` runs) -/
def HCall (n : Nat) : Prop := ∀ md ks st fin cx, StarN n (.prim md :: ks, st) ([], fin) → CxRel st cx → CxNN st →
  ((∃ x r, st.toks = .id x :: r ∧ findB st.binds x = none) ∨ (∃ t r, st.toks = .k t :: r ∧ 38 < t ∧ t < 48)) →
  PrimConcl n md ks st fin cx

theorem leaf_tc {v : RN} (h : v.kids = []) : v.toNd.tailCont = false := by
  obtain ⟨t, a, b, s, p, ks⟩ := v
  simp only [RN.kids] at h; subst h
  rw [RN.toNd_mk]
  have h0 : (if t = 9 ∧ a < 4 then (match ([] : List RN) with | [] => [] | _ :: r => RN.toNdL r) else RN.toNdL []) = [] := by
    split <;> rfl
  simp only [h0]
  repeat' split
  all_goals first | rfl | simp [Nd.tailCont]

theorem pApp_num {f cx tl v r nx} : pApp (f + 1) cx tl (.num v :: r) nx = pAtom f cx tl (.num v :: r) nx := by
  simp [pApp]
theorem pApp_nil {f cx tl r nx} : pApp (f + 1) cx tl (.k 30 :: .k 31 :: r) nx = pAtom f cx tl (.k 30 :: .k 31 :: r) nx := by
  simp [pApp, primSig]
theorem pApp_paren {f cx tl r nx} : pApp (f + 1) cx tl (.k 6 :: r) nx = pAtom f cx tl (.k 6 :: r) nx := by
  simp [pApp, primSig]
theorem pApp_bound {f cx tl x r nx p} (h : findEnv cx.env x = some p) :
    pApp (f + 1) cx tl (.id x :: r) nx = pAtom f cx tl (.id x :: r) nx := by
  simp [pApp, h]


theorem pApp_bnew {f cx tl r nx} : pApp (f + 2) cx tl (.k 43 :: r) nx = some (.prim 5 [], .s .bf, r, nx) := by
  simp [pApp, primSig, pArgs, dropInp]

theorem findB_mem' {bs : List Bd} {x bd} (h : findB bs x = some bd) : bd ∈ bs := by
  unfold findB at h; exact List.mem_reverse.mp (List.mem_of_find?_eq_some h)

theorem defs_sub_rows {st : St} {d : DefR} (h : d ∈ st.defs) : d ∈ rows st := by simp [rows, h]

/-- a leaf atom on the primary path -/
theorem prim_leaf {n md ks st st1 fin cx} (hc : CxRel st cx) (hnn : CxNN st) (hl : AtomLeaf st st1)
    (hb : ∀ x r, st.toks = .id x :: r → (findB st.binds x).isSome) (h1 : StarN n (ks, st1) ([], fin)) :
    PrimConcl (n + 1) md ks st fin cx := by
  obtain ⟨r, v, hlt, hk, hp, hst⟩ := hl.eff
  refine ⟨v, st1, n, by omega, ?_, by rw [hst]; exact hlt, h1, ?_, fun _ => ?_⟩
  · rw [hst]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp; omega, Nat.le_refl _⟩
  · cases hl with
    | num ht => simp [leaf] at hst; obtain ⟨_, rfl, _⟩ := hst; exact ⟨.uw, rfl, rfl⟩
    | nil ht => simp [leaf] at hst; obtain ⟨_, rfl, _⟩ := hst; exact ⟨.ls, rfl, rfl⟩
    | bnew ht => simp [leaf] at hst; obtain ⟨_, rfl, _⟩ := hst; exact ⟨.bf, rfl, rfl⟩
    | loc ht hbd hlo =>
      unfold locOf at hlo; split at hlo
      · cases hlo
      · simp at hlo; subst hlo; simp at hst; obtain ⟨_, rfl, _⟩ := hst
        exact hnn.1 _ (findB_mem' hbd)
    | cst ht hbd hd hj hpar hm =>
      obtain ⟨_, rfl⟩ := mkNode_inv hm; simp at hst; obtain ⟨_, rfl, _⟩ := hst
      exact (hnn.2 _ (defs_sub_rows (List.mem_of_getElem? hj))).1
  · obtain ⟨v', ty, r', hst', hty, hp', hf⟩ := atomLeaf_spec hc hl (md == 1) st.nx
    rw [hst] at hst'
    have hv : v' = v := by
      have := congrArg St.vals hst'; simp at this; exact this.symm
    have hr : r' = r := by
      have := congrArg St.toks hst'; simp at this; exact this.symm
    subst hv hr
    refine ⟨ty, hty, (fun h' => by rw [leaf_tc hk] at h'; cases h'), fun f hf' => ?_⟩
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
    have hst1 : st1.toks = r' ∧ st1.nx = st.nx := by rw [hst]; exact ⟨rfl, rfl⟩
    rw [hst1.1, hst1.2]
    cases hl with
    | num ht => rw [ht, pApp_num, ← ht]; exact hf g
    | nil ht => rw [ht, pApp_nil, ← ht]; exact hf g
    | bnew ht =>
      rw [ht, pApp_bnew]; have := hf (g + 1); rw [ht] at this; simp [pAtom] at this
      obtain ⟨h1', h2', h3'⟩ := this; rw [← h1', ← h2', ← h3']
    | @loc x r0 bd _ ht hbd _ =>
      have henv := hc.env x; rw [hbd] at henv
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (hc.typed x bd hbd)
      have hps : (bdPs bd).isSome := by
        unfold bdPs; split
        · rfl
        · rw [hs]; cases s <;> rfl
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hps
      rw [ht, pApp_bound (p := (bd.slot, p)) (by rw [henv]; simp [hp]), ← ht]; exact hf g
    | cst ht hbd => exact absurd (hb _ _ ht) (by simp [hbd])

end ParRun
