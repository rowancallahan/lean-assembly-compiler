/- Reasoning rules over the interface (`Proven/Mach/Iface.lean`), proved from the `Core` laws only:
`runsTo` monotonicity / sequencing, the loop rule (port of `Proven/LoopRule.lean`), code placement
(`codeAt` / `codeOK` of concatenations), and the `Done` / `Set1` frames. -/
import Compiler.Iface

namespace Proven.Mach

theorem next_add (pc : BitVec 64) (a b : Nat) : next (next pc a) b = next pc (a + b) := by
  simp only [next]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]

theorem next_zero (pc : BitVec 64) : next pc 0 = pc := by
  simp only [next, Nat.mul_zero]; exact BitVec.add_zero pc

theorem next_jmp (pc : BitVec 64) (n : Nat) : next pc n - BitVec.ofNat 64 (4 * n) = pc :=
  BitVec.add_sub_cancel pc _

namespace Core
variable (C : Core)

theorem runsTo_mono {s : C.S} {P Q : C.S → Prop} (h : C.runsTo s P) (hpq : ∀ s, P s → Q s) : C.runsTo s Q :=
  C.runsTo_trans h fun s' hp => C.runsTo_of (hpq s' hp)

/-- **Loop rule.**  If from every `Inv` state the machine runs to `Post` (exit) or back to `Inv` with a
strictly smaller measure, then from every `Inv` state it runs to `Post`. -/
theorem runsTo_loop {Inv Post : C.S → Prop} (μ : C.S → Nat)
    (body : ∀ s, Inv s → C.runsTo s fun s' => Post s' ∨ (Inv s' ∧ μ s' < μ s)) :
    ∀ s, Inv s → C.runsTo s Post := by
  intro s
  induction h : μ s using Nat.strongRecOn generalizing s with
  | ind n ih =>
    intro hi
    refine C.runsTo_trans (body s hi) fun s' hs' => ?_
    rcases hs' with hp | ⟨hi', hlt⟩
    · exact C.runsTo_of hp
    · exact ih _ (h ▸ hlt) s' rfl hi'

/-- the loop rule with explicit head and exit PCs -/
theorem runsTo_while {Inv Post : C.S → Prop} (head exit : BitVec 64) (μ : C.S → Nat)
    (_hhead : ∀ s, Inv s → C.pcIs s head)
    (body : ∀ s, Inv s → C.runsTo s fun s' => (C.pcIs s' exit ∧ Post s') ∨ (Inv s' ∧ μ s' < μ s)) :
    ∀ s, Inv s → C.runsTo s fun s' => C.pcIs s' exit ∧ Post s' :=
  C.runsTo_loop μ body

/-! ## Addresses -/

theorem pc_toNat {pc : BitVec 64} {n a : Nat} (h : C.codeOK pc n) (ha : a ≤ n) :
    (next pc a).toNat = pc.toNat + 4 * a := by
  obtain ⟨_, _, h3⟩ := h
  have := C.ramHi_lt
  simp only [next, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 4 * a) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem codeOK_append {pc : BitVec 64} {a b : Nat} (h : C.codeOK pc (a + b)) :
    C.codeOK pc a ∧ C.codeOK (next pc a) b := by
  have e := C.pc_toNat h (a := a) (by omega)
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨⟨h1, h2, by omega⟩, ?_⟩
  simp only [Base.codeOK, e]; omega

theorem codeAt_append {s : C.S} {pc : BitVec 64} {l₁ l₂ : List (BitVec 32)} :
    C.codeAt s pc (l₁ ++ l₂) ↔ C.codeAt s pc l₁ ∧ C.codeAt s (next pc l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h i (by rw [List.length_append]; omega); rwa [List.getElem_append_left hi] at this
    · have := h (l₁.length + i) (by rw [List.length_append]; omega)
      rw [List.getElem_append_right (by omega)] at this
      have e := next_add pc l₁.length i
      simp only [next] at e ⊢
      rw [e]; simpa only [Nat.add_sub_cancel_left] using this
  · intro ⟨h₁, h₂⟩ i hi
    rw [List.length_append] at hi
    by_cases hi' : i < l₁.length
    · rw [List.getElem_append_left hi']; exact h₁ i hi'
    · have := h₂ (i - l₁.length) (by omega)
      rw [List.getElem_append_right (by omega)]
      have e := next_add pc l₁.length (i - l₁.length)
      simp only [next] at e this
      rwa [e, Nat.add_sub_cancel' (by omega)] at this

theorem codeAt_mem {s s' : C.S} {pc ws} (hm : C.mem s' = C.mem s) (h : C.codeAt s pc ws) : C.codeAt s' pc ws :=
  fun i hi => C.instrAt_frame (fun j _ => by rw [hm]) (h i hi)

/-! ## `At`, `Done`, `Set1` -/

theorem At.split {s : C.S} {pc : BitVec 64} {l₁ l₂ : List (BitVec 32)} (h : C.At s pc (l₁ ++ l₂)) :
    C.At s pc l₁ ∧ C.codeAt s (next pc l₁.length) l₂ ∧ C.codeOK (next pc l₁.length) l₂.length := by
  have hc := (C.codeAt_append).1 h.code
  have ho := C.codeOK_append (by simpa only [List.length_append] using h.codeOK)
  exact ⟨⟨h.ok, h.hpc, hc.1, ho.1⟩, hc.2, ho.2⟩

theorem Done.trans {s₁ s₂ s₃ : C.S} {p₂ p₃} (d₁ : C.Done s₁ s₂ p₂) (d₂ : C.Done s₂ s₃ p₃) : C.Done s₁ s₃ p₃ :=
  ⟨d₂.ok, C.keep_trans d₁.keep d₂.keep, d₂.hpc⟩

theorem Done.at {s s' : C.S} {pc ws} (d : C.Done s s' pc) (hc : C.codeAt s' pc ws) (ho : C.codeOK pc ws.length) :
    C.At s' pc ws := ⟨d.ok, d.hpc, hc, ho⟩

theorem Done.refl {s : C.S} {pc} (h : C.ok s) (hpc : C.pcIs s pc) : C.Done s s pc := ⟨h, C.keep_refl s, hpc⟩

theorem Set1.trans {s₁ s₂ s₃ : C.S} {d v w} (h₁ : C.Set1 s₁ s₂ d v) (h₂ : C.Set1 s₂ s₃ d w) : C.Set1 s₁ s₃ d w := by
  intro r; rw [h₂ r]; by_cases hr : r = d
  · rw [ite_pos hr, ite_pos hr]
  · rw [ite_neg hr, ite_neg hr, h₁ r, ite_neg hr]

theorem Set1.same {s s' : C.S} {d v} (h : C.Set1 s s' d v) : C.get s' d = v := by rw [h d, ite_pos rfl]

theorem Set1.other {s s' : C.S} {d v r} (h : C.Set1 s s' d v) (hr : r ≠ d) : C.get s' r = C.get s r := by
  rw [h r, ite_neg hr]

/-- sequencing: run to `pc₁`, then from there to `pc₂` -/
theorem seq_run {s : C.S} {pc₁ pc₂ : BitVec 64} {P Q : C.S → Prop}
    (h₁ : C.runsTo s fun s₁ => C.Done s s₁ pc₁ ∧ P s₁)
    (h₂ : ∀ s₁, C.Done s s₁ pc₁ → P s₁ → C.runsTo s₁ fun s₂ => C.Done s₁ s₂ pc₂ ∧ Q s₂) :
    C.runsTo s fun s₂ => C.Done s s₂ pc₂ ∧ Q s₂ :=
  C.runsTo_trans h₁ fun s₁ ⟨d₁, p₁⟩ => C.runsTo_mono (h₂ s₁ d₁ p₁) fun _ ⟨d₂, q⟩ => ⟨Done.trans C d₁ d₂, q⟩

end Core
end Proven.Mach
