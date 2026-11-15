/- A compiled function: IR code over virtual registers → register assignment `f` (checked injective on the
registers used, or liveness-checked: `allocOK`; moves `d := d` dropped) → lowering (checked `wf`) → words, then `ret`.  `fn_ok`: an IR execution from the machine's
registers (read through `f`) is simulated up to the return. -/
import Compiler.Opt.Lower
import Compiler.Opt.Alloc
import Compiler.Opt.Live
import Compiler.Opt.SR
import Compiler.Opt.Flow

namespace Proven.Mach
open IR

namespace Wide
variable (M : Wide) (sc : Reg) (f : Nat → Reg)

/-- the assignment is acceptable: injective on all registers used, or liveness-checked (`chk`) -/
def _root_.Proven.Mach.IR.allocOK (f : Nat → Reg) (vars : List Nat) (c : Code Nat) : Bool :=
  injOn f (vars ++ c.regs) || (chk f c vars).isSome

theorem _root_.Proven.Mach.IR.allocOK_run {f : Nat → Reg} {vars : List Nat} {c : Code Nat} (h : allocOK f vars c = true)
    {ram : Nat → Prop} {fp : Nat} {g : Regs Reg} {m : Mem} {σ' : St Nat}
    (hex : Exec ram fp c ⟨fun x => g (f x), m⟩ σ') :
    ∃ τ', Exec ram fp (dropMov (c.map f)) ⟨g, m⟩ τ' ∧ τ'.mem = σ'.mem ∧ ∀ x, x ∈ vars → τ'.reg (f x) = σ'.reg x := by
  unfold allocOK at h
  rcases Bool.or_eq_true_iff.1 h with hinj | hl
  · obtain ⟨τ', hx', hr'⟩ := map_ok (f := f) (U := fun x => x ∈ vars ++ c.regs) ram fp
      (fun x y hx hy => injOn_ok hinj hx hy) hex (fun x hx => List.mem_append.2 (.inr hx))
      (τ := ⟨g, m⟩) ⟨rfl, fun _ _ => rfl⟩
    exact ⟨τ', dropMov_ok ram fp hx', hr'.1, fun x hx => hr'.2 x (List.mem_append.2 (.inl hx))⟩
  · cases hc : chk f c vars with
    | none => rw [hc] at hl; exact nomatch hl
    | some Lin =>
      obtain ⟨τ', hx', hr'⟩ := chk_ok ram fp hex hc (τ := ⟨g, m⟩) ⟨rfl, fun _ _ => rfl⟩
      exact ⟨τ', dropMov_ok ram fp hx', hr'.1, hr'.2⟩


/-- the lowered body only (no `ret`) -/
def body (vars : List Nat) (c : Code Nat) : Option (List (BitVec 32)) :=
  if (allocOK f vars c && M.wf sc (dropMov (c.map f))) = true then some (M.W sc (dropMov (c.map f))) else none

def fn (vars : List Nat) (c : Code Nat) : Option (List (BitVec 32)) :=
  if (allocOK f vars c && M.wf sc (dropMov (c.map f))) = true then some (M.W sc (dropMov (c.map f)) ++ M.wenc .ret)
  else none

variable {M sc f}

theorem body_ok {ram : Nat → Prop} {fp : Nat} (hram : ∀ a, ram a → M.inRAM a 1)
    (hwr : ∀ a, ram a → ∀ s, M.ok s → M.writable s a) {vars : List Nat} {c : Code Nat}
    {ws : List (BitVec 32)} (hc : M.body sc f vars c = some ws) {s : M.S} {pc : BitVec 64} (hok : M.ok s)
    (hpc : M.pcIs s pc) (hf : M.Frag ram fp s pc ws) {σ' : St Nat}
    (hex : Exec ram fp c ⟨fun x => M.get s (f x), M.mem s⟩ σ') :
    M.RunTo ram s (next pc ws.length) fun s' =>
      (∀ x, x ∈ vars → f x ≠ sc → M.get s' (f x) = σ'.reg x) ∧ M.mem s' = σ'.mem := by
  unfold body at hc
  by_cases hchk : (allocOK f vars c && M.wf sc (dropMov (c.map f))) = true
  · rw [ite_pos hchk] at hc
    cases hc
    obtain ⟨hinj, hwf⟩ := and2 hchk
    obtain ⟨τ', hx', hm', hr'⟩ := allocOK_run hinj (g := M.get s) (m := M.mem s) hex
    exact (low_ok hram hwr hx' hwf hok hpc hf ⟨fun _ _ => rfl, rfl⟩).mono fun s₁ _ _ r₁ =>
      ⟨fun x hx hs => (r₁.1 _ hs).trans (hr' x hx), r₁.2.trans hm'⟩
  · rw [ite_neg hchk] at hc; exact nomatch hc

theorem fn_ok {ram : Nat → Prop} {fp : Nat} (hram : ∀ a, ram a → M.inRAM a 1)
    (hwr : ∀ a, ram a → ∀ s, M.ok s → M.writable s a) {vars : List Nat} {c : Code Nat}
    {ws : List (BitVec 32)} (hc : M.fn sc f vars c = some ws) {s : M.S} {pc : BitVec 64} (hok : M.ok s)
    (hpc : M.pcIs s pc) (hf : M.Frag ram fp s pc ws) (hra : M.retOK (M.ra s)) {σ' : St Nat}
    (hex : Exec ram fp c ⟨fun x => M.get s (f x), M.mem s⟩ σ') :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ (∀ x, x ∈ vars → f x ≠ sc → M.get s' (f x) = σ'.reg x) ∧
      M.ok s' ∧ M.mem s' = σ'.mem ∧ M.keep s s' := by
  unfold fn at hc
  by_cases hchk : (allocOK f vars c && M.wf sc (dropMov (c.map f))) = true
  · rw [ite_pos hchk] at hc
    cases hc
    obtain ⟨hinj, hwf⟩ := and2 hchk
    obtain ⟨τ', hx', hm', hr'⟩ := allocOK_run hinj (g := M.get s) (m := M.mem s) hex
    refine M.runsTo_trans (low_ok hram hwr hx' hwf hok hpc hf.left ⟨fun _ _ => rfl, rfl⟩) fun s₁ ⟨d₁, m₁, r₁⟩ => ?_
    have e₁ : M.ra s₁ = M.ra s := M.keep_ra d₁.keep
    refine M.runsTo_mono (M.w_ret (by rw [e₁]; exact hra) ((hf.right.mf m₁).at d₁.ok d₁.hpc))
      fun s₂ ⟨d₂, st₂, m₂⟩ => ?_
    have d := Core.Done.trans _ d₁ d₂
    rw [e₁] at d
    refine ⟨d.hpc, fun x hx hs => ?_, d.ok, ?_, d.keep⟩
    · rw [st₂, r₁.1 _ hs]; exact hr' x hx
    · rw [m₂, r₁.2, hm']
  · rw [ite_neg hchk] at hc; exact nomatch hc

/-! ### With strength reduction (`SR.sr`) tried first -/

/-- the bodies tried, in order: the control-flow clean-ups (`Flow.flow`) then strength reduction, strength
reduction alone, the code itself -/
def _root_.Proven.Mach.IR.cands (vars : List Nat) (c : Code Nat) : List (Code Nat) :=
  [SR.sr vars (Flow.flow vars c), SR.sr vars c, c]

theorem _root_.Proven.Mach.IR.cands_ok {ram : Nat → Prop} {fp : Nat} {vars : List Nat} {c c' : Code Nat}
    (hm : c' ∈ cands vars c) {σ σ' : St Nat} (h : Exec ram fp c σ σ') :
    ∃ τ', Exec ram fp c' σ τ' ∧ τ'.mem = σ'.mem ∧ ∀ x, x ∈ vars → τ'.reg x = σ'.reg x := by
  simp only [cands, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · obtain ⟨τ₁, x₁, m₁, r₁⟩ := Flow.flow_ok vars h
    obtain ⟨τ₂, x₂, m₂, r₂⟩ := SR.sr_ok vars x₁
    exact ⟨τ₂, x₂, m₂.trans m₁, fun x hx => (r₂ x hx).trans (r₁ x hx)⟩
  · exact SR.sr_ok vars h
  · exact ⟨σ', h, rfl, fun _ _ => rfl⟩

variable (M sc f) in
/-- the first of `cands vars c` that passes the checks -/
def bodySR (vars : List Nat) (c : Code Nat) : Option (List (BitVec 32)) :=
  (cands vars c).findSome? fun c' => M.body sc f vars c'

variable (M sc f) in
def fnSR (vars : List Nat) (c : Code Nat) : Option (List (BitVec 32)) :=
  match M.fn sc f vars (SR.sr vars c) with
  | some w => some w
  | none => M.fn sc f vars c

theorem bodySR_ok {ram : Nat → Prop} {fp : Nat} (hram : ∀ a, ram a → M.inRAM a 1)
    (hwr : ∀ a, ram a → ∀ s, M.ok s → M.writable s a) {vars : List Nat} {c : Code Nat}
    {ws : List (BitVec 32)} (hc : M.bodySR sc f vars c = some ws) {s : M.S} {pc : BitVec 64} (hok : M.ok s)
    (hpc : M.pcIs s pc) (hf : M.Frag ram fp s pc ws) {σ' : St Nat}
    (hex : Exec ram fp c ⟨fun x => M.get s (f x), M.mem s⟩ σ') :
    M.RunTo ram s (next pc ws.length) fun s' =>
      (∀ x, x ∈ vars → f x ≠ sc → M.get s' (f x) = σ'.reg x) ∧ M.mem s' = σ'.mem := by
  unfold bodySR at hc
  obtain ⟨c', hm, hs⟩ := List.exists_of_findSome?_eq_some hc
  obtain ⟨τ', hx', hm', hv'⟩ := cands_ok hm hex
  exact (body_ok hram hwr hs hok hpc hf hx').mono fun s₁ _ _ r₁ =>
    ⟨fun x hx hs => (r₁.1 x hx hs).trans (hv' x hx), r₁.2.trans hm'⟩

theorem fnSR_ok {ram : Nat → Prop} {fp : Nat} (hram : ∀ a, ram a → M.inRAM a 1)
    (hwr : ∀ a, ram a → ∀ s, M.ok s → M.writable s a) {vars : List Nat} {c : Code Nat}
    {ws : List (BitVec 32)} (hc : M.fnSR sc f vars c = some ws) {s : M.S} {pc : BitVec 64} (hok : M.ok s)
    (hpc : M.pcIs s pc) (hf : M.Frag ram fp s pc ws) (hra : M.retOK (M.ra s)) {σ' : St Nat}
    (hex : Exec ram fp c ⟨fun x => M.get s (f x), M.mem s⟩ σ') :
    M.runsTo s fun s' => M.pcIs s' (M.ra s) ∧ (∀ x, x ∈ vars → f x ≠ sc → M.get s' (f x) = σ'.reg x) ∧
      M.ok s' ∧ M.mem s' = σ'.mem ∧ M.keep s s' := by
  unfold fnSR at hc
  cases hs : M.fn sc f vars (SR.sr vars c) with
  | some w =>
    rw [hs] at hc; cases hc
    obtain ⟨τ', hx', hm', hv'⟩ := SR.sr_ok vars hex
    exact M.runsTo_mono (fn_ok hram hwr hs hok hpc hf hra hx') fun s₁ ⟨a, b, c, d, e⟩ =>
      ⟨a, fun x hx hs => (b x hx hs).trans (hv' x hx), c, d.trans hm', e⟩
  | none => rw [hs] at hc; exact fn_ok hram hwr hc hok hpc hf hra hex

end Wide
end Proven.Mach
