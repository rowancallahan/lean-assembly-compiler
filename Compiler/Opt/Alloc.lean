/- Register assignment as a renaming: IR code over registers `α` is mapped through `f : α → β`.
If `f` is injective on the registers the code mentions, executions are preserved (`map_ok`).  The
assignment `f` itself is untrusted: `injOn` is a decidable check on its result. -/
import Compiler.Opt.IR

namespace Proven.Mach.IR
variable {α β : Type}

def Arg.map (f : α → β) : Arg α → Arg β
  | .r x => .r (f x)
  | .i c => .i c

def Tst.map (f : α → β) (t : Tst α) : Tst β := ⟨t.c, t.a.map f, t.b.map f⟩

def Ins.map (f : α → β) : Ins α → Ins β
  | .set d a => .set (f d) (a.map f)
  | .bin op d a b => .bin op (f d) (a.map f) (b.map f)
  | .lbu d a off => .lbu (f d) (a.map f) off
  | .sb v a off => .sb (v.map f) (a.map f) off

def Code.map (f : α → β) : Code α → Code β
  | .skip => .skip
  | .ins i => .ins (i.map f)
  | .seq a b => .seq (a.map f) (b.map f)
  | .when t b => .when (t.map f) (b.map f)
  | .loop p t b => .loop (p.map f) (t.map f) (b.map f)
  | .loop2 p₁ t₁ p₂ t₂ b => .loop2 (p₁.map f) (t₁.map f) (p₂.map f) (t₂.map f) (b.map f)

def Arg.regs : Arg α → List α
  | .r x => [x]
  | .i _ => []

def Tst.regs (t : Tst α) : List α := t.a.regs ++ t.b.regs

def Ins.regs : Ins α → List α
  | .set d a => d :: a.regs
  | .bin _ d a b => d :: (a.regs ++ b.regs)
  | .lbu d a _ => d :: a.regs
  | .sb v a _ => v.regs ++ a.regs

def Code.regs : Code α → List α
  | .skip => []
  | .ins i => i.regs
  | .seq a b => a.regs ++ b.regs
  | .when t b => t.regs ++ b.regs
  | .loop p t b => p.regs ++ (t.regs ++ b.regs)
  | .loop2 p₁ t₁ p₂ t₂ b => p₁.regs ++ (t₁.regs ++ (p₂.regs ++ (t₂.regs ++ b.regs)))

/-- `f` is injective on the list `l` (checked) -/
def injOn [DecidableEq α] [DecidableEq β] (f : α → β) (l : List α) : Bool :=
  l.all fun x => l.all fun y => decide (f x = f y → x = y)

theorem injOn_ok [DecidableEq α] [DecidableEq β] {f : α → β} {l : List α} (h : injOn f l = true) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (e : f x = f y) : x = y :=
  of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h x hx) y hy) e

section
variable [DecidableEq α] [DecidableEq β] (f : α → β) (U : α → Prop)

/-- `τ` is `σ` renamed (on `U`) -/
def Ren (σ : St α) (τ : St β) : Prop := τ.mem = σ.mem ∧ ∀ x, U x → τ.reg (f x) = σ.reg x

variable {f U}

theorem Ren.arg {σ : St α} {τ : St β} (h : Ren f U σ τ) {a : Arg α} (ha : ∀ x, x ∈ a.regs → U x) :
    (a.map f).eval τ.reg = a.eval σ.reg := by
  cases a with
  | r x => exact h.2 x (ha x (List.mem_singleton.2 rfl))
  | i c => rfl

theorem Ren.upd (inj : ∀ x y, U x → U y → f x = f y → x = y) {σ : St α} {τ : St β} (h : Ren f U σ τ) {d : α}
    (hd : U d) (v : BitVec 64) : Ren f U ⟨upd σ.reg d v, σ.mem⟩ ⟨upd τ.reg (f d) v, τ.mem⟩ := by
  refine ⟨h.1, fun x hx => ?_⟩
  show (if f x = f d then v else τ.reg (f x)) = if x = d then v else σ.reg x
  by_cases e : x = d
  · rw [ite_pos e, ite_pos (congrArg f e)]
  · rw [ite_neg e, ite_neg (fun e' => e (inj x d hx hd e'))]; exact h.2 x hx

theorem Ren.tst {σ : St α} {τ : St β} (h : Ren f U σ τ) {t : Tst α} (ht : ∀ x, x ∈ t.regs → U x) :
    (t.map f).eval τ.reg = t.eval σ.reg := by
  unfold Tst.eval Tst.map
  rw [h.arg fun x hx => ht x (List.mem_append.2 (.inl hx)), h.arg fun x hx => ht x (List.mem_append.2 (.inr hx))]

omit [DecidableEq α] [DecidableEq β] in
theorem mem5 {x : α} {a b c d e : List α} (h : x ∈ a ∨ x ∈ b ∨ x ∈ c ∨ x ∈ d ∨ x ∈ e) :
    x ∈ a ++ (b ++ (c ++ (d ++ e))) := by
  simp only [List.mem_append]; exact h

/-- **Renaming preserves executions** when `f` is injective on the registers used. -/
theorem map_ok (ram : Nat → Prop) (inj : ∀ x y, U x → U y → f x = f y → x = y) :
    ∀ {c : Code α} {σ σ' : St α}, Exec ram c σ σ' → (∀ x, x ∈ c.regs → U x) → ∀ {τ : St β}, Ren f U σ τ →
    ∃ τ', Exec ram (c.map f) τ τ' ∧ Ren f U σ' τ' := by
  intro c σ σ' h
  induction h with
  | skip => exact fun _ τ hr => ⟨τ, .skip, hr⟩
  | @ins i s s' hst =>
    intro hu τ hr
    cases hst with
    | @set d a =>
      have hu' : U d ∧ ∀ x, x ∈ a.regs → U x := ⟨hu d (List.mem_cons_self ..), fun x hx => hu x (List.mem_cons_of_mem _ hx)⟩
      refine ⟨_, .ins .set, ?_⟩
      rw [hr.arg hu'.2]; exact hr.upd inj hu'.1 _
    | @bin op d a b =>
      have hd : U d := hu d (List.mem_cons_self ..)
      have ha : ∀ x, x ∈ a.regs → U x := fun x hx => hu x (List.mem_cons_of_mem _ (List.mem_append.2 (.inl hx)))
      have hb : ∀ x, x ∈ b.regs → U x := fun x hx => hu x (List.mem_cons_of_mem _ (List.mem_append.2 (.inr hx)))
      refine ⟨_, .ins .bin, ?_⟩
      rw [hr.arg ha, hr.arg hb]; exact hr.upd inj hd _
    | @lbu d a off _ v hra hv =>
      have hd : U d := hu d (List.mem_cons_self ..)
      have ha : ∀ x, x ∈ a.regs → U x := fun x hx => hu x (List.mem_cons_of_mem _ hx)
      refine ⟨_, .ins (.lbu (v := v) (by rw [hr.arg ha]; exact hra) (by rw [hr.arg ha, hr.1]; exact hv)), ?_⟩
      exact hr.upd inj hd _
    | @sb v a off _ hra =>
      have hv : ∀ x, x ∈ v.regs → U x := fun x hx => hu x (List.mem_append.2 (.inl hx))
      have ha : ∀ x, x ∈ a.regs → U x := fun x hx => hu x (List.mem_append.2 (.inr hx))
      refine ⟨_, .ins (.sb (by rw [hr.arg ha]; exact hra)), ?_, hr.2⟩
      show Mem.upd _ _ _ = Mem.upd _ _ _
      rw [hr.arg ha, hr.arg hv, hr.1]
  | seq _ _ iha ihb =>
    intro hu τ hr
    obtain ⟨τ₁, x₁, r₁⟩ := iha (fun x hx => hu x (List.mem_append.2 (.inl hx))) hr
    obtain ⟨τ₂, x₂, r₂⟩ := ihb (fun x hx => hu x (List.mem_append.2 (.inr hx))) r₁
    exact ⟨τ₂, .seq x₁ x₂, r₂⟩
  | whenT ht _ ih =>
    intro hu τ hr
    obtain ⟨τ₁, x₁, r₁⟩ := ih (fun x hx => hu x (List.mem_append.2 (.inr hx))) hr
    exact ⟨τ₁, .whenT ((hr.tst fun x hx => hu x (List.mem_append.2 (.inl hx))).trans ht) x₁, r₁⟩
  | whenF ht =>
    intro hu τ hr
    exact ⟨τ, .whenF ((hr.tst fun x hx => hu x (List.mem_append.2 (.inl hx))).trans ht), hr⟩
  | loopF _ ht ihp =>
    intro hu τ hr
    obtain ⟨τ₁, x₁, r₁⟩ := ihp (fun x hx => hu x (List.mem_append.2 (.inl hx))) hr
    exact ⟨τ₁, .loopF x₁ ((r₁.tst fun x hx => hu x (List.mem_append.2 (.inr (List.mem_append.2 (.inl hx))))).trans ht), r₁⟩
  | loopT _ ht _ _ ihp ihb ihl =>
    intro hu τ hr
    obtain ⟨τ₁, x₁, r₁⟩ := ihp (fun x hx => hu x (List.mem_append.2 (.inl hx))) hr
    obtain ⟨τ₂, x₂, r₂⟩ := ihb (fun x hx => hu x (List.mem_append.2 (.inr (List.mem_append.2 (.inr hx))))) r₁
    obtain ⟨τ₃, x₃, r₃⟩ := ihl hu r₂
    exact ⟨τ₃, .loopT x₁ ((r₁.tst fun x hx => hu x (List.mem_append.2 (.inr (List.mem_append.2 (.inl hx))))).trans ht)
      x₂ x₃, r₃⟩
  | loop2A _ ht ih₁ =>
    intro hu τ hr
    obtain ⟨τ₁, x₁, r₁⟩ := ih₁ (fun x hx => hu x (List.mem_append.2 (.inl hx))) hr
    exact ⟨τ₁, .loop2A x₁ ((r₁.tst fun x hx => hu x (mem5 (.inr (.inl hx)))).trans ht), r₁⟩
  | loop2B _ ht₁ _ ht₂ ih₁ ih₂ =>
    intro hu τ hr
    obtain ⟨τ₁, x₁, r₁⟩ := ih₁ (fun x hx => hu x (mem5 (.inl hx))) hr
    obtain ⟨τ₂, x₂, r₂⟩ := ih₂ (fun x hx => hu x (mem5 (.inr (.inr (.inl hx))))) r₁
    exact ⟨τ₂, .loop2B x₁ ((r₁.tst fun x hx => hu x (mem5 (.inr (.inl hx)))).trans ht₁) x₂
      ((r₂.tst fun x hx => hu x (mem5 (.inr (.inr (.inr (.inl hx)))))).trans ht₂), r₂⟩
  | loop2T _ ht₁ _ ht₂ _ _ ih₁ ih₂ ihb ihl =>
    intro hu τ hr
    obtain ⟨τ₁, x₁, r₁⟩ := ih₁ (fun x hx => hu x (mem5 (.inl hx))) hr
    obtain ⟨τ₂, x₂, r₂⟩ := ih₂ (fun x hx => hu x (mem5 (.inr (.inr (.inl hx))))) r₁
    obtain ⟨τ₃, x₃, r₃⟩ := ihb (fun x hx => hu x (mem5 (.inr (.inr (.inr (.inr hx)))))) r₂
    obtain ⟨τ₄, x₄, r₄⟩ := ihl hu r₃
    exact ⟨τ₄, .loop2T x₁ ((r₁.tst fun x hx => hu x (mem5 (.inr (.inl hx)))).trans ht₁) x₂
      ((r₂.tst fun x hx => hu x (mem5 (.inr (.inr (.inr (.inl hx)))))).trans ht₂) x₃ x₄, r₄⟩

end
end Proven.Mach.IR
