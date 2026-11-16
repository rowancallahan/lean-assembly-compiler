/- The return, and the whole run: from the relation, a terminating Lin run's machine run ends in `Fin`. -/
import Compiler.Ir.EmitStep

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

namespace Ctx
variable {T : Target} {C : Ctx T}

theorem peak_frame {E : List MemEvent} (h : Allocs E) (n : Nat) :
    peak (E ++ [.alloc n]) = inUse E + n := by
  rw [peak_allocs _ (h.append fun e he => by simp at he; exact ⟨n, he⟩), inUse_append_alloc _ _ h]

/-- **the return** -/
theorem done_ok {P : Prog Nat} {F : Func Nat} {pos : Lbl → Nat} {ex : Nat} (hP : P.funcs[P.main]? = some F)
    {st : State Nat} {s : T.S} {r : Result} (hrel : C.Rel P F pos ex st s) (hs : step P st = .done r) :
    T.runsTo s (C.Fin r) := by
  obtain ⟨l, k, regs, B, q, c, ct, hst, hB, hc, hct, hin, hA, hR, hal, hiu⟩ := hrel
  cases hk : B.body[k]? with
  | some i =>
    have hkl : k < B.body.length := (List.getElem?_eq_some_iff.1 hk).1
    have hdrop : B.body.drop k = i :: B.body.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hkl]; congr; exact (List.getElem?_eq_some_iff.1 hk).2
    rw [hdrop] at hc
    simp only [Target.emitIs] at hc
    cases hci : T.emitI C.nS ex q i with
    | none => rw [hci] at hc; exact nomatch hc
    | some ci =>
      have hi : ∀ ds g as, i ≠ .call ds g as := by rintro ds g as rfl; simp [Target.emitI] at hci
      rw [step_inst hst hP hB hk hi] at hs
      split at hs <;> exact nomatch hs
  | none =>
    rw [step_term hst hP hB hk] at hs
    have hd : B.body.drop k = [] := List.drop_eq_nil_of_le (by simpa using hk)
    rw [hd] at hc; simp only [Target.emitIs, Option.some.injEq] at hc; subst hc
    cases ht : B.term with
    | ret vs =>
      rw [ht] at hs hct
      simp only [termStep] at hs; cases hs
      simp only [Target.emitT, Option.some.injEq] at hct; subst hct
      refine T.toCore.runsTo_mono (C.ret_ok hA hR (rest := []) (by simpa [Target.words] using hin))
        fun s' ⟨hok, hpc, hU, hin', hm⟩ => ⟨hok, hpc, hU, .inl ⟨?_, hin', fun i b hi => by rw [hm]; exact hR.out i b hi⟩⟩
      show peak (st.ev ++ [.alloc (C.nS + 1)]) ≤ C.wl / 8
      rw [peak_frame hal, hiu]
      have := hR.cap; have := hR.fit
      have : C.F0 = C.wb + C.wl / 8 * 8 - 8 * (C.nS + 1) := rfl
      omega
    | jmp l' as =>
      rw [ht] at hs; simp only [termStep] at hs; split at hs <;> exact nomatch hs
    | br t l₁ a₁ l₂ a₂ =>
      rw [ht] at hs; simp only [termStep] at hs
      (repeat' split at hs) <;> exact nomatch hs
    | switch x ls d =>
      rw [ht] at hct; simp only [Target.emitT] at hct; exact nomatch hct

/-- **the run** -/
theorem sim {P : Prog Nat} {F : Func Nat} {pos : Lbl → Nat} {ex : Nat} (hP : P.funcs[P.main]? = some F)
    (hK : C.Code F pos ex) : ∀ (n : Nat) {st : State Nat} {s : T.S} {r : Result}, C.Rel P F pos ex st s →
    run P n st = some r → r.mem.out.length ≤ C.outL → T.runsTo s (C.Fin r)
  | 0, _, _, _, _, h, _ => nomatch h
  | n + 1, st, s, r, hrel, h, hO => by
    rw [run_succ] at h
    split at h
    · next st' e =>
      have hO' := Nat.le_trans (run_mono_out h) hO
      refine T.toCore.runsTo_trans (C.step_ok hP hK hrel e hO') fun s' h' => ?_
      rcases h' with hrel' | ⟨hlt, hal, hE⟩
      · exact sim hP hK n hrel' h hO
      · obtain ⟨E, hE'⟩ := run_mono_ev h
        refine T.runsTo_of ⟨hE.1, hE.2.1, hE.2.2.1, .inr ⟨?_, hE.2.2.2⟩⟩
        have h1 := peak_append_ge E (st'.ev ++ [.alloc (C.nS + 1)])
        have h2 := inUse_le_peak' (st'.ev ++ [.alloc (C.nS + 1)])
        rw [inUse_append_alloc _ _ hal] at h2
        rw [hE', List.append_assoc]
        omega
    · next r' e => cases h; exact C.done_ok hP hrel e
    · exact nomatch h

end Ctx
end Proven.Ir
