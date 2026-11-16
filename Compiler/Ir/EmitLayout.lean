/- Where `emitF` puts things: the prologue at word 0, every block at its position, the exit at `ex`. -/
import Compiler.Ir.EmitSim

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

namespace Target
variable (T : Target)

theorem emitBs_code {F : Func Nat} {nS : Nat} {pos : Lbl → Nat} {ex : Nat} :
    ∀ {q : Nat} {bs : List (Lbl × Block Nat)} {code : List EOp}, T.emitBs F nS pos ex q bs = some code →
    (∀ l B, bs.lookup l = some B → ∃ c ct pre post, T.emitIs nS ex (pos l) B.body = some c ∧
      T.emitT F nS pos (pos l + T.len c) B.term = some ct ∧ T.words code = pre ++ T.words (c ++ ct) ++ post ∧
      q + pre.length = pos l) ∧ q + T.len code = ex
  | q, [], code, h => by
    simp only [emitBs] at h
    split at h
    · next e => cases h; exact ⟨fun _ _ h => (nomatch h), by simp [len, words, e]⟩
    · exact nomatch h
  | q, (l', B') :: bs, code, h => by
    simp only [emitBs] at h
    split at h
    · next hq =>
      cases hb : T.emitB F nS pos ex q B' with
      | none => rw [hb] at h; exact nomatch h
      | some cB =>
        rw [hb] at h; simp only at h
        cases hr : T.emitBs F nS pos ex (q + T.len cB) bs with
        | none => rw [hr] at h; exact nomatch h
        | some r =>
          rw [hr] at h; cases h
          obtain ⟨ih, hex⟩ := emitBs_code hr
          refine ⟨fun l B hl => ?_, by simp only [len, words_append, List.length_append] at hex ⊢; omega⟩
          rw [List.lookup_cons] at hl
          by_cases e : l = l'
          · subst e
            simp only [beq_self_eq_true] at hl
            obtain rfl : B' = B := Option.some.inj hl
            simp only [emitB] at hb
            cases hc : T.emitIs nS ex q B'.body with
            | none => rw [hc] at hb; exact nomatch hb
            | some c =>
              rw [hc] at hb; simp only at hb
              cases ht : T.emitT F nS pos (q + T.len c) B'.term with
              | none => rw [ht] at hb; exact nomatch hb
              | some ct =>
                rw [ht] at hb; cases hb
                exact ⟨c, ct, [], T.words r, by rw [hq]; exact hc, by rw [hq]; exact ht,
                  by simp [words_append], by simp [hq]⟩
          · have : (l == l') = false := by simpa using e
            rw [this] at hl
            obtain ⟨c, ct, pre, post, h1, h2, h3, h4⟩ := ih l B hl
            exact ⟨c, ct, T.words cB ++ pre, post, h1, h2, by rw [words_append, h3]; simp,
              by simp only [len] at h4; simp only [List.length_append]; omega⟩
    · exact nomatch h

end Target

namespace Ctx
variable {T : Target} {C : Ctx T}

/-- the code facts from `emitF` -/
theorem code_of {F : Func Nat} {pos : Lbl → Nat} {ex : Nat} {code : List EOp}
    (he : T.emitF F C.nS pos ex = some code) (hW : C.W = T.words code) :
    ∃ j, T.jTo (T.len (T.pro C.nS F)) (pos F.entry) = some j ∧
      (∃ rest, InW C.W 0 (T.words (T.pro C.nS F ++ j) ++ rest)) ∧ C.Code F pos ex := by
  unfold Target.emitF at he
  split at he
  · cases hj : T.jTo (T.len (T.pro C.nS F)) (pos F.entry) with
    | none => rw [hj] at he; exact nomatch he
    | some j =>
      rw [hj] at he; simp only at he
      cases hb : T.emitBs F C.nS pos ex (T.len (T.pro C.nS F ++ j)) F.blocks with
      | none => rw [hb] at he; exact nomatch he
      | some b =>
        rw [hb] at he; cases he
        obtain ⟨hl, hex⟩ := T.emitBs_code hb
        have hW' : C.W = T.words (T.pro C.nS F ++ j) ++ T.words b ++ T.words exit1 := by
          rw [hW]; simp only [T.words_append, List.append_assoc]
        refine ⟨j, rfl, ⟨T.words b ++ T.words exit1, [], [], by rw [hW']; simp, rfl⟩, ⟨?_, ?_⟩⟩
        · intro l B hB
          obtain ⟨c, ct, pre, post, h1, h2, h3, h4⟩ := hl l B hB
          refine ⟨c, ct, h1, h2, T.words (T.pro C.nS F ++ j) ++ pre, post ++ T.words exit1, ?_, ?_⟩
          · rw [hW', h3]; simp only [List.append_assoc]
          · simp only [List.length_append]; simp only [Target.len] at h4; omega
        · refine ⟨T.words (T.pro C.nS F ++ j) ++ T.words b, [], by rw [hW']; simp, ?_⟩
          simp only [List.length_append]; simp only [Target.len] at hex; omega
  · exact nomatch he

end Ctx
end Proven.Ir
