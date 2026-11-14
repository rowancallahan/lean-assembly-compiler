/- The bottom-up merge sort of `Riscv/Direct/SortMergeSrc.lean` with the block indices as parameters:
`msortG s0 o sc` sorts block `s0` into block `o`, using block `sc` as scratch (`sc` may be `s0`: the source is
read only by the first pass).  `msortProg = msortG 0 2 1`.  Proved at source level (`msortG_mergeSort`), with
the same proof as `msortProg_mergeSort`; the heap is any list of blocks. -/
import Riscv.Direct.SortMergeSrc

set_option linter.unusedVariables false

namespace Proven

open MS

def mainBodyG (o sc : Nat) : BStmt :=
  .seq (.assign 13 (.var 14)) (.seq (passM o sc) (.seq (.assign 13 (addE (.var 14) (.var 14))) (.seq (passM sc o)
    (.assign 14 (addE (addE (.var 14) (.var 14)) (addE (.var 14) (.var 14)))))))

def msortG (s0 o sc : Nat) : BStmt :=
  .seq (.assign 13 (.const 1)) (.seq (passM s0 o) (.seq (.assign 14 (.const 2))
    (.loop (ltE (.var 14) (.var 1)) (mainBodyG o sc))))

theorem msortG_assigns (s0 o sc : Nat) : ∀ v ∈ (msortG s0 o sc).assigns, v ∈ [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] := by
  intro v hv
  simp only [msortG, mainBodyG, BStmt.assigns, passM_assigns, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hv ⊢
  omega

/-- **The generic merge sort computes `List.mergeSort`**: block `s0` holds `S`, blocks `o` and `sc` have
`|S|` bytes, `v1 = |S|`; at the end block `o` is `S.mergeSort leB`, block `sc` holds some list of length `|S|`,
every other block is unchanged. -/
theorem msortG_mergeSort (s0 o sc : Nat) (hs0o : s0 ≠ o) (hosc : o ≠ sc) (H : Heap) (S : List (BitVec 8))
    (hs0 : s0 < H.length) (ho : o < H.length) (hsc : sc < H.length) (hS : H[s0] = S)
    (hol : H[o].length = S.length) (hscl : H[sc].length = S.length)
    (σ : BState) (hh : σ.heap = H) (h1 : σ.env 1 = BitVec.ofNat 64 S.length) (hn : S.length < 2 ^ 32) :
    ∃ σ', BExec (msortG s0 o sc) σ σ' ∧ ∃ T, T.length = S.length ∧
      σ'.heap = (H.set sc T).set o (S.mergeSort leB) := by
  have hn64 : S.length < 2 ^ 64 := by omega
  have hoo : o < (H.set sc H[sc]).length := by simpa using ho
  -- first pass: s0 → o, width 1
  obtain ⟨σ₂, hex₂, hh₂⟩ := pass_exec s0 o S H 1 hs0o hs0 ho hS hol hn (by decide) (by decide)
    (σ.asg 13 (.const 1)) hh (by simp [h1]) (by simp [BExp.denote])
  have k1 : σ₂.env 1 = σ.env 1 := by rw [pass_keep hex₂ (by decide)]; simp
  have sl : ∀ {T : List (BitVec 8)} {G : Heap}, G.length = H.length → ((G.set sc T).length = H.length) := by
    intro T G h; simp [h]
  -- main loop
  obtain ⟨σ', hl, hq⟩ := BExec.loop_inv (c := ltE (.var 14) (.var 1)) (b := mainBodyG o sc)
    (fun τ => τ.env 1 = BitVec.ofNat 64 S.length ∧ ∃ ww s r, τ.env 14 = BitVec.ofNat 64 ww ∧ 2 ≤ ww ∧
      ww < 2 ^ 34 ∧ τ.heap = (H.set sc s).set o r ∧ s.length = S.length ∧ r.length = S.length ∧ r.Perm S ∧
      CS leB ww r)
    (fun τ => ∃ T, T.length = S.length ∧ τ.heap = (H.set sc T).set o (S.mergeSort leB))
    (fun τ => S.length - (τ.env 14).toNat)
    (fun τ ⟨e1, ww, s, r, e14, hww, hww', eh, hs, hr, hp, hcs⟩ hc => by
      have hlt : ww < S.length := by
        simp only [ltE, BExp.denote, e14, e1, ult_ofNat (show ww < 2 ^ 64 by omega) hn64] at hc
        exact Classical.byContradiction fun h => by simp [h] at hc
      let H₁ := (H.set sc s).set o r
      have hl₁ : H₁.length = H.length := by simp [H₁]
      have g1o : H₁[o]'(by omega) = r := by simp [H₁]
      have g1sc : (H₁[sc]'(by omega)).length = r.length := by
        simp only [H₁]; rw [List.getElem_set_ne hosc, List.getElem_set_self]; rw [hs, hr]
      obtain ⟨τ₂, hex₂, hh₂⟩ := pass_exec o sc r H₁ ww hosc (by omega) (by omega) g1o g1sc (by omega) (by omega)
        (by omega) (τ.asg 13 (.var 14)) eh (by simp [e1, hr]) (by simp [BExp.denote, e14])
      have k2 : ∀ v ∈ [1, 13, 14], τ₂.env v = (τ.asg 13 (.var 14)).env v := fun v hv => pass_keep hex₂ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; omega)
      have g14 : τ₂.env 14 = BitVec.ofNat 64 ww := by rw [k2 14 (by simp)]; simp [e14]
      have g1 : τ₂.env 1 = BitVec.ofNat 64 S.length := by rw [k2 1 (by simp)]; simp [e1]
      have hl1 : (runs leB ww r 0).length = S.length := by rw [runs_length leB (by omega), hr]; rfl
      let H₂ := (H.set sc (runs leB ww r 0)).set o r
      have e₂ : H₁.set sc (runs leB ww r 0) = H₂ := by
        simp only [H₁, H₂]; rw [List.set_comm _ _ hosc, List.set_set]
      have g2sc : H₂[sc]'(by simp [H₂]; omega) = runs leB ww r 0 := by
        simp only [H₂]; rw [List.getElem_set_ne hosc, List.getElem_set_self]
      have g2o : (H₂[o]'(by simp [H₂]; omega)).length = (runs leB ww r 0).length := by simp [H₂, hl1, hr]
      obtain ⟨τ₄, hex₄, hh₄⟩ := pass_exec sc o (runs leB ww r 0) H₂ (ww + ww) (Ne.symm hosc)
        (by simp [H₂]; omega) (by simp [H₂]; omega) g2sc g2o (by rw [hl1]; omega) (by omega) (by omega)
        (τ₂.asg 13 (addE (.var 14) (.var 14))) (by rw [BState.asg_heap, hh₂, e₂]) (by simp [g1, hl1])
        (by simp only [BState.asg_env, if_true, addE, BExp.denote, g14, add_ofNat])
      have k4 : ∀ v ∈ [1, 14], τ₄.env v = (τ₂.asg 13 (addE (.var 14) (.var 14))).env v := fun v hv =>
        pass_keep hex₄ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; omega)
      have g14' : τ₄.env 14 = BitVec.ofNat 64 ww := by rw [k4 14 (by simp)]; simp [g14]
      have g1' : τ₄.env 1 = BitVec.ofNat 64 S.length := by rw [k4 1 (by simp)]; simp [g1]
      refine ⟨τ₄.asg 14 (addE (addE (.var 14) (.var 14)) (addE (.var 14) (.var 14))),
        .seq BExec.asg (.seq hex₂ (.seq BExec.asg (.seq hex₄ BExec.asg))),
        ⟨?_, ww + ww + (ww + ww), runs leB ww r 0, runs leB (ww + ww) (runs leB ww r 0) 0, ?_, by omega, by omega,
          ?_, hl1, by rw [runs_length leB (by omega), hl1]; rfl, ?_, ?_⟩, ?_⟩
      · simp only [BState.asg_env, Nat.reduceEqDiff, if_false]; exact g1'
      · simp only [BState.asg_env, if_true, addE, BExp.denote, g14', add_ofNat]
      · rw [BState.asg_heap, hh₄]; simp only [H₂]; rw [List.set_set]
      · exact ((runs_perm leB (by omega) _ 0).trans (runs_perm leB (by omega) _ 0)).trans hp
      · have := runs_CS0 (show 0 < ww + ww by omega) (by rw [← Nat.two_mul]; exact runs_CS0 (by omega) hcs)
        rwa [show 2 * (ww + ww) = ww + ww + (ww + ww) by omega] at this
      · show S.length - (BExp.denote τ₄.env (addE (addE (.var 14) (.var 14)) (addE (.var 14) (.var 14)))).toNat <
          S.length - (τ.env 14).toNat
        simp only [addE, BExp.denote, g14', add_ofNat, e14]
        rw [toNat_ofNat' (by omega), toNat_ofNat' (by omega)]; omega)
    (fun τ ⟨e1, ww, s, r, e14, hww, hww', eh, hs, hr, hp, hcs⟩ hc => by
      have hge : ¬ ww < S.length := by
        simp only [ltE, BExp.denote, e14, e1, ult_ofNat (show ww < 2 ^ 64 by omega) hn64] at hc
        intro h; simp [h] at hc
      have hsort := CS_sorted leB hcs (by omega)
      exact ⟨s, hs, by rw [eh, sorted_perm_eq (hsort.imp fun h => (leB_iff _ _).mp h) (sorted_mergeSort S)
        (hp.trans (List.mergeSort_perm S leB).symm)]⟩)
    (σ₂.asg 14 (.const 2))
    ⟨by simp only [BState.asg_env, Nat.reduceEqDiff, if_false]; rw [k1, h1], 2, H[sc], runs leB 1 S 0,
      by simp [BExp.denote], by decide, by decide,
      by rw [BState.asg_heap, hh₂, List.set_getElem_self], hscl,
      by rw [runs_length leB (by decide)]; rfl, runs_perm leB (by decide) S 0, runs_CS0 (by decide) (CS_one leB S)⟩
  exact ⟨σ', .seq BExec.asg (.seq hex₂ (.seq BExec.asg hl)), hq⟩

end Proven
