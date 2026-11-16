/- Terminators that stay in the frame: `jmp`, `br`, `switch` (a chain of tests `r0 = i`, then the default). -/
import Compiler.Ir.EmitCall

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

theorem setMany_nil {ρ : Type} [DecidableEq ρ] (g : ρ → Val) : ∀ ps : List ρ, setMany g ps [] = g
  | [] => rfl
  | _ :: _ => rfl

theorem jump_inv {F : Func Nat} {fr fr' : Frame Nat} {l : Lbl} {vs : List Val} (h : jump F fr l vs = some fr') :
    ∃ B, F.blocks.lookup l = some B ∧ vs.length = B.params.length ∧
      fr' = { fr with l := l, pc := 0, regs := setMany fr.regs B.params vs } := by
  unfold jump at h
  split at h
  · next B hB => split at h
                 · next hl => cases h; exact ⟨B, hB, hl, rfl⟩
                 · exact nomatch h
  · exact nomatch h

namespace Ctx
variable {T : Target} {C : Ctx T}

theorem tst_eval {m : Mem} {regs : Nat → Val} {s : T.S} (hR : C.MR m regs s) {t : Tst Nat} {bv : Bool}
    (h : t.eval regs = some bv) :
    t.c.eval (C.repr m.blks (t.a.eval regs)) (C.repr m.blks (t.b.eval regs)) = bv := by
  have ne0 : ∀ v : Val, Valid m.blks v → (∀ x, v ≠ .w x) → C.repr m.blks v ≠ 0 := by
    intro v hv hw e
    have hlo := C.lo; obtain ⟨hi1, hi2⟩ := C.inR; obtain ⟨ho1, ho2⟩ := C.outR; obtain ⟨hw1, hw2⟩ := C.wR
    have hlt := T.ramHi_lt; have hcap := hR.cap; have hF := hR.F0_lt
    have z : ∀ x, x < 2 ^ 64 → 0 < x → BitVec.ofNat 64 x ≠ 0 := fun x h1 h2 e => by
      have := congrArg BitVec.toNat e; rw [ofNat_toNat' h1] at this; simp at this; omega
    match v, hv with
    | .w x, _ => exact hw x rfl
    | .p 0 o, ho => simp only [Valid] at ho; subst ho; exact z _ (by omega) (by omega) e
    | .p 1 o, ho => simp only [Valid] at ho; subst ho; exact z _ (by omega) (by omega) e
    | .p (k + 2) o, ⟨a, sz, hk, hos⟩ =>
      have := (hR.mok.blks k a sz true hk).1
      rw [C.repr_blk hk] at e; exact z _ (by omega) (by omega) e
  unfold Tst.eval at h
  split at h
  · next x y ha hb => cases h; rw [ha, hb]; rfl
  · next b o y ha hb =>
    split at h
    · next hy =>
      subst hy
      have hv : C.repr m.blks (t.a.eval regs) ≠ 0 := ne0 _ (by rw [ha]; have := valid_eval hR.valid t.a; rwa [ha] at this)
        (by rw [ha]; intro x e; cases e)
      rw [hb]
      cases hc : t.c <;> simp only [nullTest, hc] at h <;> cases h <;> simp [Cond.eval] <;> first | exact hv | exact Ne.symm hv
    · exact nomatch h
  · next x b o ha hb =>
    split at h
    · next hx =>
      subst hx
      have hv : C.repr m.blks (t.b.eval regs) ≠ 0 := ne0 _ (by rw [hb]; have := valid_eval hR.valid t.b; rwa [hb] at this)
        (by rw [hb]; intro x e; cases e)
      rw [ha]
      cases hc : t.c <;> simp only [nullTest, hc] at h <;> cases h <;> simp [Cond.eval] <;> first | exact hv | exact Ne.symm hv
    · exact nomatch h
  · exact nomatch h

/-- the switch chain: the first `i` with `r0 = i` jumps to its block, else past the chain -/
theorem swChain_ok {m : Mem} {regs : Nat → Val} {pos : Lbl → Nat} {k : BitVec 64} :
    ∀ (i : Nat) (ls : List Lbl) {s : T.S} {q : Nat} {os : List EOp} {rest : List (BitVec 32)},
    C.AtQ s q → C.MR m regs s → T.get s R0 = k → i ≤ k.toNat → i + ls.length < 2 ^ 32 →
    T.swChain pos q i ls = some os → InW C.W q (T.words os ++ rest) →
    T.runsTo s fun s' => C.MR m regs s' ∧
      ((∃ l, ls[k.toNat - i]? = some l ∧ C.AtQ s' (pos l)) ∨
       (i + ls.length ≤ k.toNat ∧ C.AtQ s' (q + T.len os)))
  | i, [], s, q, os, rest, hA, hR, h0, hi, _, hc, _ => by
    simp only [Target.swChain, Option.some.injEq] at hc; subst hc
    exact T.runsTo_of ⟨hR, .inr ⟨by simpa using hi, by simpa [Target.len, Target.words] using hA⟩⟩
  | i, l :: ls, s, q, os, rest, hA, hR, h0, hi, hl, hc, hin => by
    simp only [Target.swChain] at hc
    cases hb : T.brTo .eq (q + T.len [.w (.li R1 (BitVec.ofNat 64 i))]) (pos l) with
    | none => rw [hb] at hc; exact nomatch hc
    | some b =>
    rw [hb] at hc; simp only at hc
    cases hr : T.swChain pos (q + T.len ([.w (.li R1 (BitVec.ofNat 64 i))] ++ b)) (i + 1) ls with
    | none => rw [hr] at hc; exact nomatch hc
    | some c =>
    rw [hr] at hc; cases hc
    simp only [List.length_cons] at hl
    have hin' : InW C.W q (T.encO (.w (.li R1 (BitVec.ofNat 64 i))) ++ (T.words b ++ (T.words c ++ rest))) := by
      simpa only [T.words_append, Target.words_cons, Target.words_nil, List.append_nil, List.append_assoc] using hin
    refine T.toCore.runsTo_trans (C.reg_ok hA hR hin' (by decide) fun h => T.w_li h) fun s1 ⟨hA1, hR1, st1⟩ => ?_
    have e0 : T.get s1 R0 = k := by rw [Core.Set1.other T.toCore st1 (by decide), h0]
    have e1 : T.get s1 R1 = BitVec.ofNat 64 i := Core.Set1.same T.toCore st1
    have hq1 : q + (T.encO (.w (.li R1 (BitVec.ofNat 64 i)))).length = q + T.len [.w (.li R1 (BitVec.ofNat 64 i))] := by
      simp only [Target.len_cons, Target.len_nil, Nat.add_zero]
    rw [hq1] at hA1
    have hin1 := hin'.right; rw [hq1] at hin1
    refine T.toCore.runsTo_trans (C.brTo_ok hA1 hR1 hb hin1) fun s2 ⟨hR2, hs2, ht, hf⟩ => ?_
    rw [e0, e1] at ht hf
    have hkn : k.toNat < 2 ^ 64 := k.isLt
    by_cases hk : k.toNat = i
    · have hA2 := ht (by simp only [Cond.eval, decide_eq_true_eq]; apply BitVec.eq_of_toNat_eq; rw [ofNat_toNat' (by omega)]; exact hk)
      exact T.runsTo_of ⟨hR2, .inl ⟨l, by simp [hk], hA2⟩⟩
    · have hA2 := hf (by simp only [Cond.eval, decide_eq_false_iff_not]; intro e; apply hk; rw [e, ofNat_toNat' (by omega)])
      have h02 : T.get s2 R0 = k := by rw [hs2, e0]
      have hin2 := hin1.right
      have hq2 : q + T.len [.w (.li R1 (BitVec.ofNat 64 i))] + T.len b =
          q + T.len ([.w (.li R1 (BitVec.ofNat 64 i))] ++ b) := by simp only [Target.len_append]; omega
      rw [show q + T.len [.w (.li R1 (BitVec.ofNat 64 i))] + (T.words b).length =
        q + T.len [.w (.li R1 (BitVec.ofNat 64 i))] + T.len b from rfl, hq2] at hin2
      rw [hq2] at hA2
      refine T.toCore.runsTo_mono (swChain_ok (i + 1) ls hA2 hR2 h02 (by omega) (by omega) hr hin2)
        fun s' ⟨hR', h'⟩ => ⟨hR', ?_⟩
      rcases h' with ⟨l', hl', hA'⟩ | ⟨hle, hA'⟩
      · refine .inl ⟨l', ?_, hA'⟩
        rw [show k.toNat - i = (k.toNat - (i + 1)) + 1 by omega]; simpa using hl'
      · refine .inr ⟨by simp; omega, hA'.congr ?_⟩
        simp only [Target.len_append]; omega


theorem enter_of {F : Func Nat} {fr : Frame Nat} {rs : List (Frame Nat)} {m : Mem} {ev : List MemEvent}
    {l : Lbl} {vs : List Val} {fr' : Frame Nat} (hj : jump F fr l vs = some fr') :
    ∃ B', F.blocks.lookup l = some B' ∧ vs.length = B'.params.length ∧
      (⟨fr' :: rs, m, ev⟩ : State Nat) = ⟨{ fr with l := l, pc := 0, regs := setMany fr.regs B'.params vs } :: rs, m, ev⟩ := by
  obtain ⟨B', hB', hl, rfl⟩ := jump_inv hj; exact ⟨B', hB', hl, rfl⟩

/-- **a terminator other than `ret`**: to the code of the next block of the frame -/
theorem termJ_ok {F : Func Nat} {pos : Lbl → Nat} {m : Mem} {s : T.S} {q : Nat} {t : Term Nat} {ct : List EOp}
    {rest : List (BitVec 32)} {fr : Frame Nat} {rs : List (Frame Nat)} {ev : List MemEvent} {st' : State Nat}
    (hA : C.AtQ s q) (hR : C.MR m fr.regs s) (hct : T.emitT F C.nS pos q t = some ct)
    (hin : InW C.W q (T.words ct ++ rest)) (hs : termStep F fr rs m ev t = .next st') (hnr : ∀ vs, t ≠ .ret vs) :
    T.runsTo s fun s' => ∃ l' g' B', st' = ⟨{ fr with l := l', pc := 0, regs := g' } :: rs, m, ev⟩ ∧
      F.blocks.lookup l' = some B' ∧ C.AtQ s' (pos l') ∧ C.MR m g' s' := by
  cases t with
  | jmp l' as =>
    simp only [termStep] at hs
    split at hs
    · next fr' hj =>
      cases hs
      obtain ⟨B', hB', -, e⟩ := enter_of (rs := rs) (m := m) (ev := ev) hj
      simp only [Target.emitT] at hct
      exact T.toCore.runsTo_mono (C.edge_ok hA hR hct hin hB') fun s' ⟨hA', hR'⟩ => ⟨l', _, B', e, hB', hA', hR'⟩
    · exact nomatch hs
  | br tt l₁ a₁ l₂ a₂ =>
    simp only [Target.emitT] at hct
    split at hct
    · next hc =>
      obtain ⟨ha1, hta, htb⟩ := hc
      have ha1' : a₁ = [] := List.isEmpty_iff.1 ha1
      subst ha1'
      cases hb : T.brTo tt.c (q + T.len [ldArg R0 tt.a, ldArg R1 tt.b]) (pos l₁) with
      | none => rw [hb] at hct; exact nomatch hct
      | some b =>
        rw [hb] at hct; simp only at hct
        cases he : T.edge F C.nS pos (q + T.len ([ldArg R0 tt.a, ldArg R1 tt.b] ++ b)) l₂ a₂ with
        | none => rw [he] at hct; exact nomatch hct
        | some e =>
          rw [he] at hct; cases hct
          have hin2 : InW C.W q (T.words [ldArg R0 tt.a, ldArg R1 tt.b] ++ (T.words b ++ (T.words e ++ rest))) := by
            simpa only [T.words_append, List.append_assoc] using hin
          have hin2' : InW C.W q (T.encO (ldArg R0 tt.a) ++ (T.encO (ldArg R1 tt.b) ++ (T.words b ++ (T.words e ++ rest)))) := by
            simpa only [Target.words, List.append_assoc, List.append_nil] using hin2
          refine T.toCore.runsTo_trans (C.ldArg_ok hA hR hin2' (by decide) hta) fun s1 ⟨hA1, hR1, st1⟩ => ?_
          refine T.toCore.runsTo_trans (C.ldArg_ok hA1 hR1 hin2'.right (by decide) htb) fun s2 ⟨hA2, hR2, st2⟩ => ?_
          have e0 : T.get s2 R0 = C.repr m.blks (tt.a.eval fr.regs) := by
            rw [Core.Set1.other T.toCore st2 R0_ne_R1, Core.Set1.same T.toCore st1]
          have e1 : T.get s2 R1 = C.repr m.blks (tt.b.eval fr.regs) := Core.Set1.same T.toCore st2
          have hp : q + (T.encO (ldArg R0 tt.a)).length + (T.encO (ldArg R1 tt.b)).length =
              q + T.len [ldArg R0 tt.a, ldArg R1 tt.b] := by
            simp only [Target.len, Target.words, List.length_append, List.length_nil]; omega
          have hin3 := hin2'.right.right
          rw [hp] at hA2 hin3
          refine T.toCore.runsTo_trans (C.brTo_ok hA2 hR2 hb hin3) fun s3 ⟨hR3, _, ht, hf⟩ => ?_
          rw [e0, e1] at ht hf
          simp only [termStep] at hs
          cases htv : tt.eval fr.regs with
          | none => rw [htv] at hs; exact nomatch hs
          | some bv =>
            have hbv := tst_eval hR htv
            cases bv
            · rw [htv] at hs
              simp only at hs
              split at hs
              · next fr' hj =>
                cases hs
                obtain ⟨B', hB', -, e'⟩ := enter_of (rs := rs) (m := m) (ev := ev) hj
                have hA3 := hf hbv
                have hq : q + T.len [ldArg R0 tt.a, ldArg R1 tt.b] + T.len b =
                    q + T.len ([ldArg R0 tt.a, ldArg R1 tt.b] ++ b) := by
                  simp only [Target.len, T.words_append, List.length_append]; omega
                rw [hq] at hA3
                have hin4 := hin2.right.right
                have hq' : q + (T.words [ldArg R0 tt.a, ldArg R1 tt.b]).length + (T.words b).length =
                    q + T.len ([ldArg R0 tt.a, ldArg R1 tt.b] ++ b) := by
                  simp only [Target.len, T.words_append, List.length_append]; omega
                rw [hq'] at hin4
                exact T.toCore.runsTo_mono (C.edge_ok hA3 hR3 he hin4 hB') fun s' ⟨hA', hR'⟩ =>
                  ⟨l₂, _, B', e', hB', hA', hR'⟩
              · exact nomatch hs
            · rw [htv] at hs
              simp only at hs
              split at hs
              · next fr' hj =>
                cases hs
                obtain ⟨B', hB', hl, e'⟩ := enter_of (rs := rs) (m := m) (ev := ev) hj
                simp only [List.map_nil, setMany_nil] at e'
                exact T.runsTo_of ⟨l₁, _, B', e', hB', ht hbv, hR3⟩
              · exact nomatch hs
    · exact nomatch hct
  | switch x ls d =>
    simp only [Target.emitT] at hct
    split at hct
    · next hc =>
      obtain ⟨hx, hl32, hnp, hnd⟩ := hc
      cases hsw : T.swChain pos (q + T.len [.w (.ldS R0 x)]) 0 ls with
      | none => rw [hsw] at hct; exact nomatch hct
      | some c =>
      rw [hsw] at hct; simp only at hct
      cases hjd : T.jTo (q + T.len ([.w (.ldS R0 x)] ++ c)) (pos d) with
      | none => rw [hjd] at hct; exact nomatch hct
      | some j =>
      rw [hjd] at hct; cases hct
      simp only [termStep] at hs
      split at hs
      · next k hk =>
        split at hs
        · next fr' hj =>
          cases hs
          obtain ⟨B', hB', hl, e'⟩ := enter_of (rs := rs) (m := m) (ev := ev) hj
          simp only [List.map_nil, setMany_nil] at e'
          have hin0 : InW C.W q (T.encO (.w (.ldS R0 x)) ++ (T.words c ++ (T.words j ++ rest))) := by
            simpa only [T.words_append, Target.words_cons, Target.words_nil, List.append_nil, List.append_assoc] using hin
          refine T.toCore.runsTo_trans (C.ldS_ok hA hR hin0 (by decide) hx) fun s1 ⟨hA1, hR1, st1⟩ => ?_
          have e0 : T.get s1 R0 = k := by rw [Core.Set1.same T.toCore st1, hk]; rfl
          have hq1 : q + (T.encO (.w (.ldS R0 x))).length = q + T.len [.w (.ldS R0 x)] := by
            simp only [Target.len_cons, Target.len_nil, Nat.add_zero]
          rw [hq1] at hA1
          have hin1 := hin0.right; rw [hq1] at hin1
          refine T.toCore.runsTo_trans (C.swChain_ok 0 ls hA1 hR1 e0 (Nat.zero_le _) (by omega) hsw hin1)
            fun s2 ⟨hR2, h2⟩ => ?_
          rcases h2 with ⟨l, hl', hA2⟩ | ⟨hle, hA2⟩
          · rw [Nat.sub_zero] at hl'; rw [hl'] at e' hB'
            exact T.runsTo_of ⟨l, _, B', e', hB', hA2, hR2⟩
          · rw [List.getElem?_eq_none (by omega)] at e' hB'
            have hin2 := hin1.right
            rw [show q + T.len [.w (.ldS R0 x)] + (T.words c).length = q + T.len ([.w (.ldS R0 x)] ++ c) by
              rw [Target.len_append, ← Nat.add_assoc]; rfl] at hin2
            rw [show q + T.len [.w (.ldS R0 x)] + T.len c = q + T.len ([.w (.ldS R0 x)] ++ c) by
              rw [Target.len_append]; omega] at hA2
            exact T.toCore.runsTo_mono (C.jTo_ok hA2 hR2 hjd hin2) fun s3 ⟨hA3, hR3⟩ =>
              ⟨d, _, B', e', hB', hA3, hR3⟩
        · exact nomatch hs
      · exact nomatch hs
    · exact nomatch hct
  | ret vs => exact absurd rfl (hnr vs)

end Ctx
end Proven.Ir
