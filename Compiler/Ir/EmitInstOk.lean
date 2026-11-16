/- Every instruction the emitter accepts: its code simulates its step (or exits out of memory). -/
import Compiler.Ir.EmitEdge

namespace Proven.Ir
open Proven Proven.Mach Proven.Top.Alloc
set_option autoImplicit false

/-- the events of an instruction other than `free` and `call` -/
theorem exec_ev {m : Mem} {g : Nat → Val} {i : Inst Nat} {g' : Nat → Val} {m' : Mem} {e : List MemEvent}
    (h : i.exec m g = some (g', m', e)) (hi : ∀ p, i ≠ .free p) :
    Allocs e ∧ inUse e + m.cells.length = m'.cells.length := by
  have hnil : ∀ m'' : Mem, m''.cells.length = m.cells.length → e = [] → Allocs e ∧ inUse e + m.cells.length = m''.cells.length :=
    fun m'' hl he => by subst he; exact ⟨fun _ h => (nomatch h), by show 0 + _ = _; rw [hl]; omega⟩
  cases i with
  | let_ d r => simp only [Inst.exec] at h; split at h <;> cases h; exact hnil _ rfl rfl
  | ldb d p x =>
    simp only [Inst.exec] at h; (repeat' split at h) <;> cases h <;> exact hnil _ rfl rfl
  | stb v p x => simp only [Inst.exec] at h; split at h <;> cases h; exact hnil _ rfl rfl
  | ld d p k => simp only [Inst.exec] at h; (repeat' split at h) <;> cases h <;> exact hnil _ rfl rfl
  | st v p k =>
    simp only [Inst.exec] at h; (repeat' split at h) <;> cases h <;> exact hnil _ (by simp) rfl
  | alloc d n =>
    simp only [Inst.exec] at h; split at h <;> cases h
    exact ⟨fun e he => by simp at he; exact ⟨_, he⟩, by simp [inUse]; omega⟩
  | free p => exact absurd rfl (hi p)
  | call ds f as => exact nomatch h

namespace Ctx
variable {T : Target} {C : Ctx T}

/-- **an instruction** -/
theorem inst_ok {m : Mem} {regs : Nat → Val} {s : T.S} {q ex : Nat} {i : Inst Nat} {ci : List EOp}
    {rest rest' : List (BitVec 32)} {g' : Nat → Val} {m' : Mem} {e : List MemEvent}
    (hA : C.AtQ s q) (hR : C.MR m regs s) (he : T.emitI C.nS ex q i = some ci)
    (hin : InW C.W q (T.words ci ++ rest)) (hex : InW C.W ex (T.words exit1 ++ rest'))
    (hx : i.exec m regs = some (g', m', e)) (hO : m'.out.length ≤ C.outL) :
    T.runsTo s fun s' => (C.AtQ s' (q + T.len ci) ∧ C.MR m' g' s') ∨
      (C.wl / 8 < C.nS + 1 + m'.cells.length ∧ C.Exited s') := by
  have L : ∀ {P Q : T.S → Prop}, T.runsTo s P → (∀ s', P s' → Q s') → T.runsTo s Q := T.toCore.runsTo_mono
  cases i with
  | let_ d r =>
    obtain ⟨v, hv, rfl, rfl, rfl⟩ : ∃ v, r.eval m regs = some v ∧ g' = upd regs d v ∧ m' = m ∧ e = [] := by
      simp only [Inst.exec] at hx; split at hx
      · next v hv => cases hx; exact ⟨v, hv, rfl, rfl, rfl⟩
      · exact nomatch hx
    cases r with
    | arg a =>
      simp only [Target.emitI] at he; split at he
      · next hc =>
        cases he; simp only [Rhs.eval] at hv; cases hv
        exact L (C.let_arg_ok hA hR hc.1 hc.2 hin) fun _ h => .inl h
      · exact nomatch he
    | op o a b =>
      simp only [Target.emitI] at he; split at he
      · next hc =>
        cases he; simp only [Rhs.eval] at hv
        split at hv
        · next x y ha hb =>
          cases hv
          exact L (C.let_bin_ok hA hR hc.1 hc.2.1 hc.2.2 hin ha hb fun h => T.w_bin h) fun _ h => .inl h
        · exact nomatch hv
      · exact nomatch he
    | mop mo a b =>
      simp only [Target.emitI] at he; split at he
      · next hc =>
        cases he; simp only [Rhs.eval] at hv
        split at hv
        · next x y ha hb =>
          cases hv
          exact L (C.let_bin_ok hA hR hc.1 hc.2.1 hc.2.2 hin ha hb fun h => T.w_mop h) fun _ h => .inl h
        · exact nomatch hv
      · exact nomatch he
    | padd p x =>
      simp only [Target.emitI] at he; split at he
      · next hc =>
        cases he; simp only [Rhs.eval] at hv
        split at hv
        · next b o k hp hk =>
          split at hv
          · next a0 sz hb =>
            split at hv
            · next hle =>
              cases hv
              exact L (C.padd_ok hA hR hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hin hp hk hb hle) fun _ h => .inl h
            · exact nomatch hv
          · exact nomatch hv
        · exact nomatch hv
      · exact nomatch he
  | ldb d p x =>
    simp only [Target.emitI] at he; split at he
    · next hc =>
      cases he; simp only [Inst.exec] at hx
      split at hx
      · next k hk hp =>
        split at hx
        · next b hb =>
          cases hx
          exact L (C.ldb_ok hA hR hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hin hk (.inl ⟨hp, b, hb, rfl⟩)) fun _ h => .inl h
        · exact nomatch hx
      · next k hk hp =>
        split at hx
        · next b hb =>
          cases hx
          exact L (C.ldb_ok hA hR hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hin hk (.inr ⟨hp, b, hb, rfl⟩)) fun _ h => .inl h
        · exact nomatch hx
      · exact nomatch hx
    · exact nomatch he
  | stb v p x =>
    simp only [Target.emitI] at he; split at he
    · next hc =>
      cases he; simp only [Inst.exec] at hx
      split at hx
      · next y k hy hk hp =>
        cases hx
        exact L (C.stb_ok hA hR hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hin hy hk hp hO) fun _ h => .inl h
      · exact nomatch hx
    · exact nomatch he
  | ld d p k =>
    simp only [Target.emitI] at he; split at he
    · next hc =>
      cases he; simp only [Inst.exec] at hx
      split at hx
      · next b o hp =>
        split at hx
        · next a0 sz hb =>
          split at hx
          · next hlt =>
            split at hx
            · next v hv =>
              cases hx
              exact L (C.ld_ok hA hR hc.1 hc.2.1 hc.2.2.2 hin hp hb hlt hv) fun _ h => .inl h
            · exact nomatch hx
          · exact nomatch hx
        · exact nomatch hx
      · exact nomatch hx
    · exact nomatch he
  | st v p k =>
    simp only [Target.emitI] at he; split at he
    · next hc =>
      cases he; simp only [Inst.exec] at hx
      split at hx
      · next b o hp =>
        split at hx
        · next a0 sz hb =>
          split at hx
          · next hlt =>
            cases hx
            exact L (C.st_ok hA hR hc.1 hc.2.1 hc.2.2.2 hin hp hb hlt) fun _ h => .inl h
          · exact nomatch hx
        · exact nomatch hx
      · exact nomatch hx
    · exact nomatch he
  | alloc d n =>
    simp only [Target.emitI] at he; split at he
    · next hc =>
      cases hj : T.jW (q + T.len (allocPre T n)) ex with
      | none => simp only [allocPre] at hj; rw [hj] at he; exact nomatch he
      | some j =>
        simp only [allocPre] at hj; rw [hj] at he; cases he
        simp only [Inst.exec] at hx
        split at hx
        · next c hcw =>
          cases hx
          exact L (C.alloc_ok hA hR hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2 (by simpa only [allocPre] using hj)
            hin hex hcw) fun _ h => h.imp id fun h' => ⟨by simpa using h'.1, h'.2⟩
        · exact nomatch hx
    · exact nomatch he
  | free p => simp only [Target.emitI] at he; exact nomatch he
  | call ds f as => simp only [Target.emitI] at he; exact nomatch he

end Ctx
end Proven.Ir
