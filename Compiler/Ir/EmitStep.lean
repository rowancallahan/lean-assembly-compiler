/- The simulation of a Lin run by the machine: the relation `Rel` (the one frame at an instruction of a block, the
machine at that instruction's code, `MR`), one step (`step_ok`), the return (`done_ok`), and the whole run
(`sim`) by induction on its fuel. -/
import Compiler.Ir.EmitInstOk

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

theorem setMany_nil {ρ : Type} [DecidableEq ρ] (g : ρ → Val) : ∀ ps : List ρ, setMany g ps [] = g
  | [] => rfl
  | _ :: _ => rfl

theorem step_inst {P : Prog Nat} {st : State Nat} {fr : Frame Nat} {F : Func Nat} {B : Block Nat}
    {i : Inst Nat} (hst : st.stack = [fr]) (hP : P.funcs[fr.f]? = some F) (hB : F.blocks.lookup fr.l = some B)
    (hk : B.body[fr.pc]? = some i) (hi : ∀ ds g as, i ≠ .call ds g as) :
    step P st = match i.exec st.mem fr.regs with
      | some (g', m', e) => .next ⟨[{ fr with pc := fr.pc + 1, regs := g' }], m', e ++ st.ev⟩
      | none => .stuck := by
  unfold step; rw [hst]; simp only [hP, hB, hk]
  cases i with
  | call ds g as => exact absurd rfl (hi ds g as)
  | _ => (rcases hx : Inst.exec _ _ _ with _ | ⟨g', m', e⟩) <;> simp only

theorem step_term {P : Prog Nat} {st : State Nat} {fr : Frame Nat} {F : Func Nat} {B : Block Nat}
    (hst : st.stack = [fr]) (hP : P.funcs[fr.f]? = some F) (hB : F.blocks.lookup fr.l = some B)
    (hk : B.body[fr.pc]? = none) : step P st = termStep F fr [] st.mem st.ev B.term := by
  unfold step; rw [hst]; simp only [hP, hB, hk]

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
variable {T : Target} (C : Ctx T)

/-- where every block's code is, and the exit -/
structure Code (F : Func Nat) (pos : Lbl → Nat) (ex : Nat) : Prop where
  blocks : ∀ l B, F.blocks.lookup l = some B → ∃ c ct, T.emitIs C.nS ex (pos l) B.body = some c ∧
    T.emitT F C.nS pos (pos l + T.len c) B.term = some ct ∧ InW C.W (pos l) (T.words (c ++ ct))
  exit : InW C.W ex (T.words exit1 ++ [])

/-- **the relation** of a Lin state and a machine state -/
def Rel (P : Prog Nat) (F : Func Nat) (pos : Lbl → Nat) (ex : Nat) (st : State Nat) (s : T.S) : Prop :=
  ∃ (l k : Nat) (regs : Nat → Val) (B : Block Nat) (q : Nat) (c ct : List EOp),
    st.stack = [⟨P.main, l, k, regs, []⟩] ∧ F.blocks.lookup l = some B ∧
    T.emitIs C.nS ex q (B.body.drop k) = some c ∧ T.emitT F C.nS pos (q + T.len c) B.term = some ct ∧
    InW C.W q (T.words (c ++ ct)) ∧ C.AtQ s q ∧ C.MR st.mem regs s ∧ Allocs st.ev ∧
    inUse st.ev = st.mem.cells.length

/-- the end of a run: returned, and either the output is there or the flag (exactly when out of memory) -/
def Fin (r : Result) (s' : T.S) : Prop :=
  T.ok s' ∧ T.pcIs s' (T.ra C.s0) ∧ C.Unch s' ∧
  ((peak (r.ev ++ [.alloc (C.nS + 1)]) ≤ C.wl / 8 ∧ T.get s' RIn = BitVec.ofNat 64 C.inA ∧
      ∀ i b, r.mem.out[i]? = some (some b) → T.mem s' (C.outA + i) = some b.toBitVec) ∨
    (C.wl / 8 < peak (r.ev ++ [.alloc (C.nS + 1)]) ∧ T.get s' RIn = BitVec.allOnes 64))

variable {C}

/-- entering a block at its code -/
theorem enter_rel {P : Prog Nat} {F : Func Nat} {pos : Lbl → Nat} {ex : Nat} (hK : C.Code F pos ex) {l : Lbl}
    {B : Block Nat} (hB : F.blocks.lookup l = some B) {m : Mem} {regs : Nat → Val} {ev : List MemEvent}
    {s : T.S} (hA : C.AtQ s (pos l)) (hR : C.MR m regs s) (hal : Allocs ev) (hiu : inUse ev = m.cells.length) :
    C.Rel P F pos ex ⟨[⟨P.main, l, 0, regs, []⟩], m, ev⟩ s := by
  obtain ⟨c, ct, hc, hct, hin⟩ := hK.blocks l B hB
  exact ⟨l, 0, regs, B, pos l, c, ct, rfl, hB, by simpa using hc, hct, hin, hA, hR, hal, hiu⟩

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
      have e0 : C.repr m.blks (Val.w 0) = 0 := rfl
      cases hc : t.c <;> simp only [nullTest, hc] at h <;> cases h <;> simp [Cond.eval] <;> first | exact hv | exact Ne.symm hv
    · exact nomatch h
  · next x b o ha hb =>
    split at h
    · next hx =>
      subst hx
      have hv : C.repr m.blks (t.b.eval regs) ≠ 0 := ne0 _ (by rw [hb]; have := valid_eval hR.valid t.b; rwa [hb] at this)
        (by rw [hb]; intro x e; cases e)
      rw [ha]
      have e0 : C.repr m.blks (Val.w 0) = 0 := rfl
      cases hc : t.c <;> simp only [nullTest, hc] at h <;> cases h <;> simp [Cond.eval] <;> first | exact hv | exact Ne.symm hv
    · exact nomatch h
  · exact nomatch h

theorem inUse_append_allocs : ∀ (E L : List MemEvent), Allocs E → inUse (E ++ L) = inUse E + inUse L
  | [], L, _ => by simp [inUse]
  | .alloc n :: E, L, h => by
    show inUse (E ++ L) + n = inUse E + n + inUse L
    rw [inUse_append_allocs E L fun e he => h e (List.mem_cons_of_mem _ he)]; omega
  | .free n :: E, _, h => by obtain ⟨_, e⟩ := h _ (List.mem_cons_self ..); exact nomatch e

/-- **a terminator** -/
theorem term_ok {P : Prog Nat} {F : Func Nat} {pos : Lbl → Nat} {ex : Nat} (hK : C.Code F pos ex) {m : Mem}
    {regs : Nat → Val} {s : T.S} {q : Nat} {t : Term Nat} {ct : List EOp} {rest : List (BitVec 32)} {l k : Nat}
    {ev : List MemEvent} {st' : State Nat} (hA : C.AtQ s q) (hR : C.MR m regs s)
    (hct : T.emitT F C.nS pos q t = some ct) (hin : InW C.W q (T.words ct ++ rest))
    (hs : termStep F ⟨P.main, l, k, regs, []⟩ [] m ev t = .next st') (hal : Allocs ev)
    (hiu : inUse ev = m.cells.length) :
    T.runsTo s fun s' => C.Rel P F pos ex st' s' := by
  cases t with
  | jmp l' as =>
    simp only [termStep] at hs
    split at hs
    · next fr' hj =>
      cases hs
      obtain ⟨B', hB', -, rfl⟩ := jump_inv hj
      simp only [Target.emitT] at hct
      exact T.toCore.runsTo_mono (C.edge_ok hA hR hct hin hB') fun s' ⟨hA', hR'⟩ => C.enter_rel hK hB' hA' hR' hal hiu
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
          have e0 : T.get s2 R0 = C.repr m.blks (tt.a.eval regs) := by
            rw [Core.Set1.other T.toCore st2 R0_ne_R1, Core.Set1.same T.toCore st1]
          have e1 : T.get s2 R1 = C.repr m.blks (tt.b.eval regs) := Core.Set1.same T.toCore st2
          have hp : q + (T.encO (ldArg R0 tt.a)).length + (T.encO (ldArg R1 tt.b)).length =
              q + T.len [ldArg R0 tt.a, ldArg R1 tt.b] := by
            simp only [Target.len, Target.words, List.length_append, List.length_nil]; omega
          have hin3 := hin2'.right.right
          rw [hp] at hA2 hin3
          refine T.toCore.runsTo_trans (C.brTo_ok hA2 hR2 hb hin3) fun s3 ⟨hR3, ht, hf⟩ => ?_
          rw [e0, e1] at ht hf
          simp only [termStep] at hs
          cases htv : tt.eval regs with
          | none => rw [htv] at hs; exact nomatch hs
          | some bv =>
            have hbv := tst_eval hR htv
            cases bv
            · rw [htv] at hs
              simp only at hs
              split at hs
              · next fr' hj =>
                cases hs
                obtain ⟨B', hB', -, rfl⟩ := jump_inv hj
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
                  C.enter_rel hK hB' hA' hR' hal hiu
              · exact nomatch hs
            · rw [htv] at hs
              simp only at hs
              split at hs
              · next fr' hj =>
                cases hs
                obtain ⟨B', hB', hl, rfl⟩ := jump_inv hj
                simp only [List.map_nil, setMany_nil]
                exact T.runsTo_of (C.enter_rel hK hB' (ht hbv) hR3 hal hiu)
              · exact nomatch hs
    · exact nomatch hct
  | switch x ls d => simp only [Target.emitT] at hct; exact nomatch hct
  | ret vs => simp only [termStep] at hs; exact nomatch hs

/-- **one step** -/
theorem step_ok {P : Prog Nat} {F : Func Nat} {pos : Lbl → Nat} {ex : Nat} (hP : P.funcs[P.main]? = some F)
    (hK : C.Code F pos ex) {st st' : State Nat} {s : T.S} (hrel : C.Rel P F pos ex st s)
    (hs : step P st = .next st') (hO : st'.mem.out.length ≤ C.outL) :
    T.runsTo s fun s' => C.Rel P F pos ex st' s' ∨
      (C.wl / 8 < C.nS + 1 + inUse st'.ev ∧ Allocs st'.ev ∧ C.Exited s') := by
  obtain ⟨l, k, regs, B, q, c, ct, hst, hB, hc, hct, hin, hA, hR, hal, hiu⟩ := hrel
  cases hk : B.body[k]? with
  | none =>
    rw [step_term hst hP hB hk] at hs
    have hd : B.body.drop k = [] := List.drop_eq_nil_of_le (by simpa using hk)
    rw [hd] at hc; simp only [Target.emitIs, Option.some.injEq] at hc; subst hc
    exact T.toCore.runsTo_mono (C.term_ok hK hA hR (by simpa [Target.len] using hct)
      (rest := []) (by simpa [Target.words] using hin) hs hal hiu) fun _ h => .inl h
  | some i =>
    have hkl : k < B.body.length := (List.getElem?_eq_some_iff.1 hk).1
    have hdrop : B.body.drop k = i :: B.body.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hkl]; congr; exact (List.getElem?_eq_some_iff.1 hk).2
    rw [hdrop] at hc
    simp only [Target.emitIs] at hc
    cases hci : T.emitI C.nS ex q i with
    | none => rw [hci] at hc; exact nomatch hc
    | some ci =>
      rw [hci] at hc; simp only at hc
      cases hcr : T.emitIs C.nS ex (q + T.len ci) (B.body.drop (k + 1)) with
      | none => rw [hcr] at hc; exact nomatch hc
      | some cr =>
        rw [hcr] at hc; cases hc
        have hi : ∀ ds g as, i ≠ .call ds g as := by rintro ds g as rfl; simp [Target.emitI] at hci
        have hnf : ∀ p, i ≠ .free p := by rintro p rfl; simp [Target.emitI] at hci
        rw [step_inst hst hP hB hk hi] at hs
        cases hx : i.exec st.mem regs with
        | none => simp only [hx] at hs; exact nomatch hs
        | some r =>
          obtain ⟨g', m', e⟩ := r
          simp only [hx] at hs; cases hs
          obtain ⟨hal', hiu'⟩ := exec_ev hx hnf
          have hin' : InW C.W q (T.words ci ++ (T.words cr ++ T.words ct)) := by
            simpa only [T.words_append, List.append_assoc] using hin
          refine T.toCore.runsTo_mono (C.inst_ok hA hR hci hin' hK.exit hx hO) fun s' h => ?_
          have hiu2 : inUse (e ++ st.ev) = m'.cells.length := by
            rw [inUse_append_allocs _ _ hal', hiu, ← hiu']
          rcases h with ⟨hA', hR'⟩ | ⟨hlt, hE⟩
          · refine .inl ⟨l, k + 1, g', B, q + T.len ci, cr, ct, rfl, hB, hcr, ?_,
              by rw [T.words_append]; exact hin'.right, hA', hR',
              hal'.append hal, hiu2⟩
            have : q + T.len ci + T.len cr = q + T.len (ci ++ cr) := by
              simp only [Target.len, T.words_append, List.length_append]; omega
            rw [this]; exact hct
          · exact .inr ⟨by simp only at hiu2 ⊢; rw [hiu2]; exact hlt, hal'.append hal, hE⟩

end Ctx
end Proven.Ir
