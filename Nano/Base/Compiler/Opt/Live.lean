/- Liveness-checked register assignment.  `map_ok` (`Alloc.lean`) needs the assignment `f` to be injective
on every register the code mentions; here `f` only has to keep apart registers that are LIVE at the same
time.  `chk f c L` computes the registers live before `c` when `L` is live after it, and fails unless every
definition `d` leaves the registers live after it (other than `d`, and other than the source of a move
`d := a`) in registers different from `f d`.  Loops: the invariant (registers live at the loop head) is
found by an untrusted fixpoint iteration (`lv`) and CHECKED (`chk` of the body and the test code must give
a subset of it).  `chk_ok`: executions are preserved, agreeing on the live registers.

`dropMov` removes the moves `d := d` that a coalescing assignment leaves behind (`dropMov_ok`). -/
import Nano.Base.Compiler.Opt.Alloc

namespace Proven.Mach.IR
variable {α β : Type}

section
variable [DecidableEq α]

/-- `a ∪ b` as lists -/
def lunion (a b : List α) : List α := a ++ b.filter fun x => !a.contains x

theorem mem_lunion {a b : List α} {x : α} : x ∈ lunion a b ↔ x ∈ a ∨ x ∈ b := by
  unfold lunion
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact .inl h
    · exact .inr (List.mem_filter.1 h).1
  · rintro (h | h)
    · exact List.mem_append_left _ h
    · by_cases ha : x ∈ a
      · exact List.mem_append_left _ ha
      · exact List.mem_append_right _ (List.mem_filter.2 ⟨h, by simpa using ha⟩)

/-- the registers an instruction reads -/
def Ins.uses : Ins α → List α
  | .set _ a => a.regs
  | .bin _ _ a b => a.regs ++ b.regs
  | .mop _ _ a b => a.regs ++ b.regs
  | .lbu _ a _ => a.regs
  | .sb v a _ => v.regs ++ a.regs
  | .ldS _ _ => []
  | .stS _ v => [v]
  | .ld _ a _ => [a]
  | .sd v a _ => [v, a]

/-- the register an instruction writes -/
def Ins.dst : Ins α → Option α
  | .set d _ => some d
  | .bin _ d _ _ => some d
  | .mop _ d _ _ => some d
  | .lbu d _ _ => some d
  | .ldS d _ => some d
  | .ld d _ _ => some d
  | _ => none

/-- the source of a move -/
def Ins.mv : Ins α → Option α
  | .set _ (.r a) => some a
  | _ => none

/-- untrusted liveness (live before, from live after); loops by a bounded fixpoint iteration -/
def lvIter (fpre fbody : List α → List α) (L tr : List α) : Nat → List α → List α
  | 0, I => I
  | n + 1, I =>
    let I' := lunion I (fpre (tr ++ lunion (fbody I) L))
    if I'.length = I.length then I else lvIter fpre fbody L tr n I'

def lvIter2 (f₁ f₂ fb : List α → List α) (L t₁ t₂ : List α) : Nat → List α → List α
  | 0, I => I
  | n + 1, I =>
    let I' := lunion I (f₁ (t₁ ++ lunion (f₂ (t₂ ++ lunion (fb I) L)) L))
    if I'.length = I.length then I else lvIter2 f₁ f₂ fb L t₁ t₂ n I'

def lvIns (i : Ins α) (L : List α) : List α :=
  match i.dst with
  | some d => lunion i.uses (L.filter fun x => !decide (x = d))
  | none => lunion i.uses L

def lv : Code α → List α → List α
  | .skip, L => L
  | .ins i, L => lvIns i L
  | .seq a b, L => lv a (lv b L)
  | .when t b, L => t.regs ++ lunion (lv b L) L
  | .loop p t b, L => lvIter (lv p) (lv b) L t.regs 10 L
  | .loop2 p₁ t₁ p₂ t₂ b, L => lvIter2 (lv p₁) (lv p₂) (lv b) L t₁.regs t₂.regs 10 L

variable [DecidableEq β] (f : α → β)

/-- the definition of `d` (a move from `mv`) does not clobber a live register -/
def defOK (d : α) (mv : Option α) (L : List α) : Bool :=
  L.all fun x => decide (x = d) || !decide (f x = f d) || decide (mv = some x)

def subL (a b : List α) : Bool := a.all fun x => b.contains x

/-- **the checker**: registers live before `c`, or `none` -/
def chk : Code α → List α → Option (List α)
  | .skip, L => some L
  | .ins i, L =>
    match i.dst with
    | some d => if defOK f d i.mv L then some (lvIns i L) else none
    | none => some (lvIns i L)
  | .seq a b, L => (chk b L).bind (chk a)
  | .when t b, L => (chk b L).map fun Lb => t.regs ++ lunion Lb L
  | .loop p t b, L =>
    let I := lvIter (lv p) (lv b) L t.regs 10 L
    match chk b I with
    | none => none
    | some Lb =>
      match chk p (t.regs ++ lunion Lb L) with
      | none => none
      | some I' => if subL I' I then some I else none
  | .loop2 p₁ t₁ p₂ t₂ b, L =>
    let I := lvIter2 (lv p₁) (lv p₂) (lv b) L t₁.regs t₂.regs 10 L
    match chk b I with
    | none => none
    | some Lb =>
      match chk p₂ (t₂.regs ++ lunion Lb L) with
      | none => none
      | some L₂ =>
        match chk p₁ (t₁.regs ++ lunion L₂ L) with
        | none => none
        | some I' => if subL I' I then some I else none

variable {f}

omit [DecidableEq α] [DecidableEq β] in
theorem Ren.sub {U V : α → Prop} {σ : St α} {τ : St β} (h : Ren f U σ τ) (hs : ∀ x, V x → U x) : Ren f V σ τ :=
  ⟨h.1, fun x hx => h.2 x (hs x hx)⟩

theorem subL_ok {a b : List α} (h : subL a b = true) {x : α} (hx : x ∈ a) : x ∈ b :=
  List.contains_iff_mem.1 (List.all_eq_true.1 h x hx)

theorem defOK_ok {d : α} {mv : Option α} {L : List α} (h : defOK f d mv L = true) {x : α} (hx : x ∈ L)
    (hd : x ≠ d) (he : f x = f d) : mv = some x := by
  have := List.all_eq_true.1 h x hx
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at this
  rcases this with (h1 | h1) | h1
  · exact absurd h1 hd
  · exact absurd he h1
  · exact h1

/-- the update of a defined register keeps the live registers -/
theorem Ren.updL {L Lin : List α} {σ : St α} {τ : St β} (h : Ren f (· ∈ Lin) σ τ) {d : α} {v : BitVec 64}
    (hsub : ∀ x, x ∈ L → x ≠ d → x ∈ Lin) (hok : ∀ x, x ∈ L → x ≠ d → f x = f d → σ.reg x = v) :
    Ren f (· ∈ L) ⟨IR.upd σ.reg d v, σ.mem⟩ ⟨IR.upd τ.reg (f d) v, τ.mem⟩ := by
  refine ⟨h.1, fun x hx => ?_⟩
  show (if f x = f d then v else τ.reg (f x)) = if x = d then v else σ.reg x
  by_cases e : x = d
  · rw [if_pos e, if_pos (congrArg f e)]
  · rw [if_neg e]
    by_cases e' : f x = f d
    · rw [if_pos e']; exact (hok x hx e e').symm
    · rw [if_neg e']; exact h.2 x (hsub x hx e)

theorem mem_lvIns_def {i : Ins α} {L : List α} {d : α} (hd : i.dst = some d) {x : α} (hx : x ∈ L) (hxd : x ≠ d) :
    x ∈ lvIns i L := by
  unfold lvIns; rw [hd]
  exact mem_lunion.2 (.inr (List.mem_filter.2 ⟨hx, by simpa using hxd⟩))

theorem mem_lvIns_use {i : Ins α} {L : List α} {x : α} (hx : x ∈ i.uses) : x ∈ lvIns i L := by
  unfold lvIns; cases i.dst <;> exact mem_lunion.2 (.inl hx)

theorem mem_lvIns_none {i : Ins α} {L : List α} (hd : i.dst = none) {x : α} (hx : x ∈ L) : x ∈ lvIns i L := by
  unfold lvIns; rw [hd]; exact mem_lunion.2 (.inr hx)

/-- **Liveness-checked renaming preserves executions.** -/
theorem chk_ok (ram : Nat → Prop) (fp : Nat) : ∀ {c : Code α} {σ σ' : St α}, Exec ram fp c σ σ' →
    ∀ {L Lin : List α}, chk f c L = some Lin → ∀ {τ : St β}, Ren f (· ∈ Lin) σ τ →
    ∃ τ', Exec ram fp (c.map f) τ τ' ∧ Ren f (· ∈ L) σ' τ' := by
  intro c σ σ' h
  induction h with
  | skip => intro L Lin hc τ hr; cases hc; exact ⟨τ, .skip, hr⟩
  | @ins i s s' hst =>
    intro L Lin hc τ hr
    have huse : ∀ x, x ∈ i.uses → x ∈ Lin := fun x hx => by
      unfold chk at hc
      cases hd : i.dst with
      | none => rw [hd] at hc; dsimp only at hc; cases hc; exact mem_lvIns_use hx
      | some d =>
        rw [hd] at hc; dsimp only at hc
        by_cases hk : defOK f d i.mv L = true
        · rw [if_pos hk] at hc; cases hc; exact mem_lvIns_use hx
        · rw [if_neg hk] at hc; exact nomatch hc
    have hdef : ∀ d, i.dst = some d → defOK f d i.mv L = true ∧ ∀ x, x ∈ L → x ≠ d → x ∈ Lin := fun d hd => by
      unfold chk at hc; rw [hd] at hc; dsimp only at hc
      by_cases hk : defOK f d i.mv L = true
      · rw [if_pos hk] at hc; cases hc; exact ⟨hk, fun x hx hxd => mem_lvIns_def hd hx hxd⟩
      · rw [if_neg hk] at hc; exact nomatch hc
    have hnd : i.dst = none → ∀ x, x ∈ L → x ∈ Lin := fun hd x hx => by
      unfold chk at hc; rw [hd] at hc; dsimp only at hc; cases hc; exact mem_lvIns_none hd hx
    cases hst with
    | @set d a =>
      obtain ⟨hk, hs⟩ := hdef d rfl
      have ha : ∀ x, x ∈ a.regs → x ∈ Lin := huse
      refine ⟨_, .ins .set, ?_⟩
      rw [hr.arg ha]
      refine hr.updL hs fun x hx hxd he => ?_
      have hm := defOK_ok hk hx hxd he
      cases a with
      | r y => cases hm; rfl
      | i _ => exact nomatch hm
    | @bin op d a b =>
      obtain ⟨hk, hs⟩ := hdef d rfl
      have ha : ∀ x, x ∈ a.regs → x ∈ Lin := fun x hx => huse x (List.mem_append_left _ hx)
      have hb : ∀ x, x ∈ b.regs → x ∈ Lin := fun x hx => huse x (List.mem_append_right _ hx)
      refine ⟨_, .ins .bin, ?_⟩
      rw [hr.arg ha, hr.arg hb]
      exact hr.updL hs fun x hx hxd he => nomatch defOK_ok hk hx hxd he
    | @mop m d a b =>
      obtain ⟨hk, hs⟩ := hdef d rfl
      have ha : ∀ x, x ∈ a.regs → x ∈ Lin := fun x hx => huse x (List.mem_append_left _ hx)
      have hb : ∀ x, x ∈ b.regs → x ∈ Lin := fun x hx => huse x (List.mem_append_right _ hx)
      refine ⟨_, .ins .mop, ?_⟩
      rw [hr.arg ha, hr.arg hb]
      exact hr.updL hs fun x hx hxd he => nomatch defOK_ok hk hx hxd he
    | @lbu d a off _ v hra hv =>
      obtain ⟨hk, hs⟩ := hdef d rfl
      have ha : ∀ x, x ∈ a.regs → x ∈ Lin := huse
      refine ⟨_, .ins (.lbu (v := v) (by rw [hr.arg ha]; exact hra) (by rw [hr.arg ha, hr.1]; exact hv)), ?_⟩
      exact hr.updL hs fun x hx hxd he => nomatch defOK_ok hk hx hxd he
    | @sb v a off _ hra =>
      have hv : ∀ x, x ∈ v.regs → x ∈ Lin := fun x hx => huse x (List.mem_append_left _ hx)
      have ha : ∀ x, x ∈ a.regs → x ∈ Lin := fun x hx => huse x (List.mem_append_right _ hx)
      refine ⟨_, .ins (.sb (by rw [hr.arg ha]; exact hra)), ?_, fun x hx => hr.2 x (hnd rfl x hx)⟩
      show Mem.upd _ _ _ = Mem.upd _ _ _
      rw [hr.arg ha, hr.arg hv, hr.1]
    | @ldS d j _ v hal hra hb =>
      obtain ⟨hk, hs⟩ := hdef d rfl
      exact ⟨_, .ins (.ldS (v := v) hal hra (by rw [hr.1]; exact hb)),
        hr.updL hs fun x hx hxd he => nomatch defOK_ok hk hx hxd he⟩
    | @stS j v _ hal hra =>
      refine ⟨_, .ins (.stS hal hra), ?_, fun x hx => hr.2 x (hnd rfl x hx)⟩
      show Mem.wr _ _ _ = Mem.wr _ _ _
      rw [hr.1, hr.2 v (huse v (List.mem_singleton.2 rfl))]
    | @ld d a off _ v hra hal hb =>
      obtain ⟨hk, hs⟩ := hdef d rfl
      have ea := hr.2 a (huse a (List.mem_singleton.2 rfl))
      exact ⟨_, .ins (.ld (v := v) (by rw [ea]; exact hra) (by rw [ea]; exact hal) (by rw [ea, hr.1]; exact hb)),
        hr.updL hs fun x hx hxd he => nomatch defOK_ok hk hx hxd he⟩
    | @sd v a off _ hra hal =>
      have ea := hr.2 a (huse a (by simp [Ins.uses]))
      refine ⟨_, .ins (.sd (by rw [ea]; exact hra) (by rw [ea]; exact hal)), ?_, fun x hx => hr.2 x (hnd rfl x hx)⟩
      show Mem.wr _ _ _ = Mem.wr _ _ _
      rw [hr.1, ea, hr.2 v (huse v (by simp [Ins.uses]))]
  | seq _ _ iha ihb =>
    intro L Lin hc τ hr
    unfold chk at hc
    cases hb : chk f _ L with
    | none => rw [hb] at hc; exact nomatch hc
    | some Lm =>
      rw [hb] at hc
      obtain ⟨τ₁, x₁, r₁⟩ := iha hc hr
      obtain ⟨τ₂, x₂, r₂⟩ := ihb hb r₁
      exact ⟨τ₂, .seq x₁ x₂, r₂⟩
  | @whenT t body s s' ht _ ih =>
    intro L Lin hc τ hr
    unfold chk at hc
    cases hb : chk f body L with
    | none => rw [hb] at hc; exact nomatch hc
    | some Lb =>
      rw [hb] at hc; cases hc
      obtain ⟨τ₁, x₁, r₁⟩ := ih hb (hr.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inl hx)))
      exact ⟨τ₁, .whenT ((hr.tst fun x hx => List.mem_append_left _ hx).trans ht) x₁, r₁⟩
  | @whenF t body s ht =>
    intro L Lin hc τ hr
    unfold chk at hc
    cases hb : chk f body L with
    | none => rw [hb] at hc; exact nomatch hc
    | some Lb =>
      rw [hb] at hc; cases hc
      exact ⟨τ, .whenF ((hr.tst fun x hx => List.mem_append_left _ hx).trans ht),
        hr.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inr hx))⟩
  | @loopF pre t body s s₁ _ ht ihp =>
    intro L Lin hc τ hr
    unfold chk at hc
    generalize lvIter (lv pre) (lv body) L t.regs 10 L = I at hc
    dsimp only at hc
    cases hb : chk f body I with
    | none => rw [hb] at hc; exact nomatch hc
    | some Lb =>
      rw [hb] at hc; dsimp only at hc
      cases hp : chk f pre (t.regs ++ lunion Lb L) with
      | none => rw [hp] at hc; exact nomatch hc
      | some I' =>
        rw [hp] at hc; dsimp only at hc
        by_cases hs : subL I' I = true
        · rw [if_pos hs] at hc; cases hc
          obtain ⟨τ₁, x₁, r₁⟩ := ihp hp (hr.sub fun x hx => subL_ok hs hx)
          exact ⟨τ₁, .loopF x₁ ((r₁.tst fun x hx => List.mem_append_left _ hx).trans ht),
            r₁.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inr hx))⟩
        · rw [if_neg hs] at hc; exact nomatch hc
  | @loopT pre t body s s₁ s₂ s₃ _ ht _ _ ihp ihb ihl =>
    intro L Lin hc τ hr
    have hc0 := hc
    unfold chk at hc
    generalize lvIter (lv pre) (lv body) L t.regs 10 L = I at hc
    dsimp only at hc
    cases hb : chk f body I with
    | none => rw [hb] at hc; exact nomatch hc
    | some Lb =>
      rw [hb] at hc; dsimp only at hc
      cases hp : chk f pre (t.regs ++ lunion Lb L) with
      | none => rw [hp] at hc; exact nomatch hc
      | some I' =>
        rw [hp] at hc; dsimp only at hc
        by_cases hs : subL I' I = true
        · rw [if_pos hs] at hc; cases hc
          obtain ⟨τ₁, x₁, r₁⟩ := ihp hp (hr.sub fun x hx => subL_ok hs hx)
          obtain ⟨τ₂, x₂, r₂⟩ := ihb hb (r₁.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inl hx)))
          obtain ⟨τ₃, x₃, r₃⟩ := ihl hc0 r₂
          exact ⟨τ₃, .loopT x₁ ((r₁.tst fun x hx => List.mem_append_left _ hx).trans ht) x₂ x₃, r₃⟩
        · rw [if_neg hs] at hc; exact nomatch hc
  | @loop2A p₁ t₁ p₂ t₂ body s s₁ _ ht ih₁ =>
    intro L Lin hc τ hr
    unfold chk at hc
    generalize lvIter2 (lv p₁) (lv p₂) (lv body) L t₁.regs t₂.regs 10 L = I at hc
    dsimp only at hc
    cases hb : chk f body I with
    | none => rw [hb] at hc; exact nomatch hc
    | some Lb =>
      rw [hb] at hc; dsimp only at hc
      cases hp₂ : chk f p₂ (t₂.regs ++ lunion Lb L) with
      | none => rw [hp₂] at hc; exact nomatch hc
      | some L₂ =>
        rw [hp₂] at hc; dsimp only at hc
        cases hp₁ : chk f p₁ (t₁.regs ++ lunion L₂ L) with
        | none => rw [hp₁] at hc; exact nomatch hc
        | some I' =>
          rw [hp₁] at hc; dsimp only at hc
          by_cases hs : subL I' I = true
          · rw [if_pos hs] at hc; cases hc
            obtain ⟨τ₁, x₁, r₁⟩ := ih₁ hp₁ (hr.sub fun x hx => subL_ok hs hx)
            exact ⟨τ₁, .loop2A x₁ ((r₁.tst fun x hx => List.mem_append_left _ hx).trans ht),
              r₁.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inr hx))⟩
          · rw [if_neg hs] at hc; exact nomatch hc
  | @loop2B p₁ t₁ p₂ t₂ body s s₁ s₂ _ ht₁ _ ht₂ ih₁ ih₂ =>
    intro L Lin hc τ hr
    unfold chk at hc
    generalize lvIter2 (lv p₁) (lv p₂) (lv body) L t₁.regs t₂.regs 10 L = I at hc
    dsimp only at hc
    cases hb : chk f body I with
    | none => rw [hb] at hc; exact nomatch hc
    | some Lb =>
      rw [hb] at hc; dsimp only at hc
      cases hp₂ : chk f p₂ (t₂.regs ++ lunion Lb L) with
      | none => rw [hp₂] at hc; exact nomatch hc
      | some L₂ =>
        rw [hp₂] at hc; dsimp only at hc
        cases hp₁ : chk f p₁ (t₁.regs ++ lunion L₂ L) with
        | none => rw [hp₁] at hc; exact nomatch hc
        | some I' =>
          rw [hp₁] at hc; dsimp only at hc
          by_cases hs : subL I' I = true
          · rw [if_pos hs] at hc; cases hc
            obtain ⟨τ₁, x₁, r₁⟩ := ih₁ hp₁ (hr.sub fun x hx => subL_ok hs hx)
            obtain ⟨τ₂, x₂, r₂⟩ := ih₂ hp₂ (r₁.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inl hx)))
            exact ⟨τ₂, .loop2B x₁ ((r₁.tst fun x hx => List.mem_append_left _ hx).trans ht₁) x₂
              ((r₂.tst fun x hx => List.mem_append_left _ hx).trans ht₂),
              r₂.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inr hx))⟩
          · rw [if_neg hs] at hc; exact nomatch hc
  | @loop2T p₁ t₁ p₂ t₂ body s s₁ s₂ s₃ s₄ _ ht₁ _ ht₂ _ _ ih₁ ih₂ ihb ihl =>
    intro L Lin hc τ hr
    have hc0 := hc
    unfold chk at hc
    generalize lvIter2 (lv p₁) (lv p₂) (lv body) L t₁.regs t₂.regs 10 L = I at hc
    dsimp only at hc
    cases hb : chk f body I with
    | none => rw [hb] at hc; exact nomatch hc
    | some Lb =>
      rw [hb] at hc; dsimp only at hc
      cases hp₂ : chk f p₂ (t₂.regs ++ lunion Lb L) with
      | none => rw [hp₂] at hc; exact nomatch hc
      | some L₂ =>
        rw [hp₂] at hc; dsimp only at hc
        cases hp₁ : chk f p₁ (t₁.regs ++ lunion L₂ L) with
        | none => rw [hp₁] at hc; exact nomatch hc
        | some I' =>
          rw [hp₁] at hc; dsimp only at hc
          by_cases hs : subL I' I = true
          · rw [if_pos hs] at hc; cases hc
            obtain ⟨τ₁, x₁, r₁⟩ := ih₁ hp₁ (hr.sub fun x hx => subL_ok hs hx)
            obtain ⟨τ₂, x₂, r₂⟩ := ih₂ hp₂ (r₁.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inl hx)))
            obtain ⟨τ₃, x₃, r₃⟩ := ihb hb (r₂.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inl hx)))
            obtain ⟨τ₄, x₄, r₄⟩ := ihl hc0 r₃
            exact ⟨τ₄, .loop2T x₁ ((r₁.tst fun x hx => List.mem_append_left _ hx).trans ht₁) x₂
              ((r₂.tst fun x hx => List.mem_append_left _ hx).trans ht₂) x₃ x₄, r₄⟩
          · rw [if_neg hs] at hc; exact nomatch hc

end

/-! ## Dropping moves `d := d` -/

section
variable [DecidableEq α]

def dropMov : Code α → Code α
  | .skip => .skip
  | .ins (.set d (.r a)) => if d = a then .skip else .ins (.set d (.r a))
  | .ins i => .ins i
  | .seq a b => .seq (dropMov a) (dropMov b)
  | .when t b => .when t (dropMov b)
  | .loop p t b => .loop (dropMov p) t (dropMov b)
  | .loop2 p₁ t₁ p₂ t₂ b => .loop2 (dropMov p₁) t₁ (dropMov p₂) t₂ (dropMov b)

theorem upd_self (σ : Regs α) (d : α) : upd σ d (σ d) = σ := by
  funext x; unfold upd; by_cases h : x = d
  · rw [if_pos h, h]
  · rw [if_neg h]

theorem dropMov_ok (ram : Nat → Prop) (fp : Nat) : ∀ {c : Code α} {σ σ' : St α}, Exec ram fp c σ σ' →
    Exec ram fp (dropMov c) σ σ' := by
  intro c σ σ' h
  induction h with
  | skip => exact .skip
  | @ins i s s' hst =>
    cases hst with
    | @set d a =>
      cases a with
      | r y =>
        show Exec ram fp (if d = y then .skip else .ins (.set d (.r y))) _ _
        by_cases e : d = y
        · rw [if_pos e]; subst e
          have : (⟨upd s.reg d ((Arg.r d).eval s.reg), s.mem⟩ : St α) = s := by
            show (⟨upd s.reg d (s.reg d), s.mem⟩ : St α) = s
            rw [upd_self]
          rw [this]; exact .skip
        · rw [if_neg e]; exact .ins .set
      | i c => exact .ins .set
    | bin => exact .ins .bin
    | mop => exact .ins .mop
    | lbu h1 h2 => exact .ins (.lbu h1 h2)
    | sb h1 => exact .ins (.sb h1)
    | ldS h1 h2 h3 => exact .ins (.ldS h1 h2 h3)
    | stS h1 h2 => exact .ins (.stS h1 h2)
    | ld h1 h2 h3 => exact .ins (.ld h1 h2 h3)
    | sd h1 h2 => exact .ins (.sd h1 h2)
  | seq _ _ iha ihb => exact .seq iha ihb
  | whenT ht _ ih => exact .whenT ht ih
  | whenF ht => exact .whenF ht
  | loopF _ ht ihp => exact .loopF ihp ht
  | loopT _ ht _ _ ihp ihb ihl => exact .loopT ihp ht ihb ihl
  | loop2A _ ht ih => exact .loop2A ih ht
  | loop2B _ ht₁ _ ht₂ ih₁ ih₂ => exact .loop2B ih₁ ht₁ ih₂ ht₂
  | loop2T _ ht₁ _ ht₂ _ _ ih₁ ih₂ ihb ihl => exact .loop2T ih₁ ht₁ ih₂ ht₂ ihb ihl

end
end Proven.Mach.IR
