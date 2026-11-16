/- Where `emitP` puts things: the stub at word 0, every function at its start, every block at its position, the exit
at `L.ex` (`code_of`). -/
import Compiler.Ir.EmitSim

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

namespace Target
variable (T : Target)

theorem emitBs_code {E : Env} {F : Func Nat} {nS : Nat} {pos : Lbl → Nat} {ex qe : Nat} :
    ∀ {q : Nat} {bs : List (Lbl × Block Nat)} {code : List EOp}, T.emitBs E F nS pos ex qe q bs = some code →
    (∀ l B, bs.lookup l = some B → ∃ c ct pre post, T.emitIs E nS ex (pos l) B.body = some c ∧
      T.emitT F nS pos (pos l + T.len c) B.term = some ct ∧ T.words code = pre ++ T.words (c ++ ct) ++ post ∧
      q + pre.length = pos l) ∧ q + T.len code = qe
  | q, [], code, h => by
    simp only [emitBs] at h
    split at h
    · next e => cases h; exact ⟨fun _ _ h => (nomatch h), by simp [len, words, e]⟩
    · exact nomatch h
  | q, (l', B') :: bs, code, h => by
    simp only [emitBs] at h
    split at h
    · next hq =>
      cases hb : T.emitB E F nS pos ex q B' with
      | none => rw [hb] at h; exact nomatch h
      | some cB =>
        rw [hb] at h; simp only at h
        cases hr : T.emitBs E F nS pos ex qe (q + T.len cB) bs with
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
            cases hc : T.emitIs E nS ex q B'.body with
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

/-- the facts of one function's code -/
theorem emitF_code {E : Env} {F : Func Nat} {pos : Lbl → Nat} {ex q qe : Nat} {code : List EOp}
    (h : T.emitF E F pos ex q qe = some code) :
    F.slots ≤ T.maxSlots ∧ F.slots < 2 ^ 32 ∧ F.params.length ≤ 7 ∧ (∃ B, F.blocks.lookup F.entry = some B) ∧
      (∀ p ∈ F.params, p < F.slots) ∧
      (∃ j, T.jTo (q + T.len (proF F.slots F)) (pos F.entry) = some j ∧
        ∃ b, code = proF F.slots F ++ j ++ b ∧ T.emitBs E F F.slots pos ex qe (q + T.len (proF F.slots F ++ j)) F.blocks = some b) := by
  unfold emitF at h
  split at h
  · next hc =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hc
    refine ⟨h1, h2, h3, ?_, fun p hp => of_decide_eq_true (List.all_eq_true.1 h5 p hp), ?_⟩
    · cases e : F.blocks.lookup F.entry with
      | some B => exact ⟨B, rfl⟩
      | none => rw [e] at h4; exact nomatch h4
    · cases hj : T.jTo (q + T.len (proF F.slots F)) (pos F.entry) with
      | none => rw [hj] at h; exact nomatch h
      | some j =>
        rw [hj] at h; simp only at h
        cases hb : T.emitBs E F F.slots pos ex qe (q + T.len (proF F.slots F ++ j)) F.blocks with
        | none => rw [hb] at h; exact nomatch h
        | some b => rw [hb] at h; cases h; exact ⟨j, rfl, b, rfl, hb⟩
  · exact nomatch h

end Target

namespace Ctx
variable {T : Target} {C : Ctx T}

/-- the functions' code facts, from `emitFs` -/
theorem emitFs_code {Q : Prog Nat} {L : Lay} :
    ∀ (f0 : FId) {q : Nat} {Fs : List (Func Nat)} {cs : List EOp} (pre post : List (BitVec 32)),
    T.emitFs Q L f0 q Fs = some cs → C.W = pre ++ T.words cs ++ post → pre.length = q →
    (∀ i F, Fs[i]? = some F → Q.funcs[f0 + i]? = some F) →
    (∀ i F, Fs[i]? = some F → CodeF C Q L (f0 + i) F) ∧ q + T.len cs = L.ex
  | f0, q, [], cs, pre, post, h, _, _, _ => by
    simp only [Target.emitFs] at h
    split at h
    · next e => cases h; exact ⟨fun _ _ h => by simp at h, by simp [Target.len, Target.words, e]⟩
    · exact nomatch h
  | f0, q, F :: Fs, cs, pre, post, h, hW, hl, hQ => by
    simp only [Target.emitFs] at h
    split at h
    · next hq =>
      subst hq
      cases hc : T.emitF (Q.env L) F (L.posF f0) L.ex (L.fq.getD f0 0) (L.fq.getD (f0 + 1) L.ex) with
      | none => rw [hc] at h; exact nomatch h
      | some c =>
      rw [hc] at h; simp only at h
      cases hr : T.emitFs Q L (f0 + 1) (L.fq.getD f0 0 + T.len c) Fs with
      | none => rw [hr] at h; exact nomatch h
      | some r =>
      rw [hr] at h; cases h
      obtain ⟨ih, hend⟩ := emitFs_code (f0 + 1) (pre ++ T.words c) post hr
        (by rw [hW, T.words_append]; simp only [List.append_assoc]) (by rw [List.length_append, hl]; rfl)
        (fun i G hG => by rw [Nat.add_assoc, Nat.add_comm 1 i]; exact hQ (i + 1) G (by simpa using hG))
      refine ⟨fun i G hG => ?_, by rw [Target.len_append, ← Nat.add_assoc]; exact hend⟩
      cases i with
      | succ i =>
        have := ih i G (by simpa using hG); rwa [Nat.add_assoc, Nat.add_comm 1 i] at this
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hG; subst hG
        show CodeF C Q L f0 F
        obtain ⟨hns, h32, hp7, hent, hps, j, hj, b, rfl, hb⟩ := T.emitF_code hc
        obtain ⟨hbl, -⟩ := T.emitBs_code hb
        refine ⟨hns, by omega, hp7, hps, hent, ⟨j, T.words b ++ T.words r ++ post, hj, ?_⟩, fun l B hB => ?_⟩
        · exact ⟨pre, [], by rw [hW]; simp only [T.words_append, List.append_assoc, List.append_nil], hl⟩
        · obtain ⟨c', ct', pre', post', h1, h2, h3, h4⟩ := hbl l B hB
          refine ⟨c', ct', h1, h2, pre ++ T.words (Target.proF F.slots F ++ j) ++ pre', post' ++ T.words r ++ post, ?_, ?_⟩
          · rw [hW, T.words_append, T.words_append, h3]; simp only [List.append_assoc]
          · simp only [List.length_append, hl, T.words_append]; simp only [Target.len, T.words_append, List.length_append] at h4; omega
    · exact nomatch h


/-- **the code facts from `emitP`**: the stub at word 0, then the functions, the exit -/
theorem code_of {Q : Prog Nat} {L : Lay} {code : List EOp} (he : T.emitP Q L = some code) (hW : C.W = T.words code) :
    ∃ F c, Q.funcs[Q.main]? = some F ∧ F.params.length = 3 ∧
      T.callTo L.ex F.slots (T.len (T.stub1 ++ exit0 ++ Target.stub2)) (L.fq.getD Q.main 0) = some c ∧
      T.immOK .add 8 = true ∧ T.brOK false (T.lenBr + T.len exit0) = true ∧ T.brOK false (T.lenBr + T.lenJ) = true ∧
      F.slots ≤ T.maxSlots ∧
      8 * (F.slots + 1) < 2 ^ 64 ∧
      (∃ rest, InW C.W 0 (T.words (T.stub1 ++ exit0 ++ Target.stub2 ++ c) ++ rest)) ∧
      Code C Q L (T.len (T.stub1 ++ exit0 ++ Target.stub2 ++ c)) := by
  unfold Target.emitP at he
  split at he
  case isFalse => exact nomatch he
  rename_i hp3
  cases hF : Q.funcs[Q.main]? with
  | none => rw [hF] at hp3; exact nomatch hp3
  | some F =>
  rw [hF] at hp3 he; simp only [Option.map_some, Option.getD_some, Option.some.injEq] at hp3 he
  cases hst : T.emitStub L.ex F.slots (L.fq.getD Q.main 0) with
  | none => rw [hst] at he; exact nomatch he
  | some st =>
  rw [hst] at he; simp only at he
  cases hfs : T.emitFs Q L 0 (T.len st) Q.funcs with
  | none => rw [hfs] at he; exact nomatch he
  | some cs =>
  rw [hfs] at he; cases he
  unfold Target.emitStub at hst
  split at hst
  case isFalse => exact nomatch hst
  rename_i hcond
  obtain ⟨himm, hbr0, hbrJ, hns, h64⟩ := hcond
  cases hc : T.callTo L.ex F.slots (T.len (T.stub1 ++ exit0 ++ Target.stub2)) (L.fq.getD Q.main 0) with
  | none => rw [hc] at hst; exact nomatch hst
  | some c =>
  rw [hc] at hst; cases hst
  have hW' : C.W = [] ++ T.words (T.stub1 ++ exit0 ++ Target.stub2 ++ c ++ Target.stub3) ++ T.words cs ++
      (T.encO .exit ++ []) := by
    rw [hW]; simp only [T.words_append, Target.words_cons, Target.words_nil, List.append_assoc, List.nil_append]
  obtain ⟨hfn, hend⟩ := emitFs_code (C := C) 0 (T.words (T.stub1 ++ exit0 ++ Target.stub2 ++ c ++ Target.stub3))
    (T.encO .exit ++ []) hfs (by rw [hW']; simp only [List.nil_append]) rfl (fun i G hG => by simpa using hG)
  refine ⟨F, c, rfl, hp3, hc, himm, hbr0, hbrJ, hns, h64, ⟨T.words Target.stub3 ++ T.words cs ++ T.words [.exit],
    ⟨[], [], by rw [hW]; simp only [T.words_append, List.append_assoc, List.nil_append, List.append_nil], rfl⟩⟩,
    ⟨fun f G hG => by simpa using hfn f G hG, ?_, ?_⟩⟩
  · refine ⟨[], T.words (T.stub1 ++ exit0 ++ Target.stub2 ++ c ++ Target.stub3) ++ T.words cs, [], ?_, ?_⟩
    · rw [hW']; simp only [List.nil_append, List.append_nil]
    · simp only [List.length_append]; simp only [Target.len] at hend; omega
  · exact ⟨T.words cs ++ T.encO .exit, T.words (T.stub1 ++ exit0 ++ Target.stub2 ++ c), [],
      by rw [hW']; simp only [T.words_append, List.append_assoc, List.nil_append, List.append_nil], rfl⟩

end Ctx
end Proven.Ir
