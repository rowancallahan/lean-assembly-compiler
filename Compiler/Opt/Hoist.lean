/- Constants of a loop in registers (IR → IR on virtual registers, after strength reduction).

A constant that costs a load each time it is used (a test operand other than `0`, a first `bin` operand, a
second `bin` operand outside the 12-bit range, a stored constant, a `set` of a large constant) is loaded once
into a fresh register before the innermost loop that uses it, and the loop reads the register (the `k` used most
often).  The fresh registers (`≥ m`) are not written in the loop, so the loop runs as before.

`hoist vars c` and `hoist_ok`: an execution of `c` gives one of `hoist vars c` from the same state, same
memory, same `vars`. -/
import Compiler.Opt.SR

namespace Proven.Mach.IR
namespace Hoist
open SR

variable {ram : Nat → Prop} {fp : Nat}

/-! ## Replacing constants by registers -/

/-- the index of `c` in `L` -/
def pos : List (BitVec 64) → BitVec 64 → Option Nat
  | [], _ => none
  | d :: L, c => if d = c then some 0 else (pos L c).map (· + 1)

theorem pos_spec : ∀ {L : List (BitVec 64)} {c : BitVec 64} {j : Nat}, pos L c = some j →
    ∃ h : j < L.length, L[j] = c
  | [], _, _, h => nomatch h
  | d :: L, c, j, h => by
    simp only [pos] at h
    split at h
    · cases h; exact ⟨by simp, by simpa⟩
    · cases hp : pos L c with
      | none => rw [hp] at h; exact nomatch h
      | some k =>
        rw [hp] at h; cases h
        obtain ⟨hk, e⟩ := pos_spec hp
        exact ⟨by simp; omega, by simpa using e⟩

/-- `.i c` with `c ∈ L` becomes register `m + (index of c)` -/
def repA (m : Nat) (L : List (BitVec 64)) : Arg Nat → Arg Nat
  | .i c => match pos L c with | some j => .r (m + j) | none => .i c
  | a => a

def repT (m : Nat) (L : List (BitVec 64)) (t : Tst Nat) : Tst Nat := ⟨t.c, repA m L t.a, repA m L t.b⟩

def repI (m : Nat) (L : List (BitVec 64)) : Ins Nat → Ins Nat
  | .set d a => .set d (repA m L a)
  | .bin op d a b => .bin op d (repA m L a) (repA m L b)
  | .mop o d a b => .mop o d (repA m L a) (repA m L b)
  | .sb v a off => .sb (repA m L v) a off
  | i => i

def repC (m : Nat) (L : List (BitVec 64)) : Code Nat → Code Nat
  | .skip => .skip
  | .ins i => .ins (repI m L i)
  | .seq a b => .seq (repC m L a) (repC m L b)
  | .when t b => .when (repT m L t) (repC m L b)
  | .loop p t b => .loop (repC m L p) (repT m L t) (repC m L b)
  | .loop2 p₁ t₁ p₂ t₂ b => .loop2 (repC m L p₁) (repT m L t₁) (repC m L p₂) (repT m L t₂) (repC m L b)

/-- register `m + j` holds `L[j]` -/
def KOK (m : Nat) (L : List (BitVec 64)) (σ : Regs Nat) : Prop := ∀ j (h : j < L.length), σ (m + j) = L[j]

theorem repA_eval {m : Nat} {L : List (BitVec 64)} {σ : Regs Nat} (h : KOK m L σ) (a : Arg Nat) :
    (repA m L a).eval σ = a.eval σ := by
  cases a with
  | r x => rfl
  | i c =>
    simp only [repA]
    cases hp : pos L c with
    | none => rfl
    | some j =>
      obtain ⟨hj, e⟩ := pos_spec hp
      show σ _ = c
      rw [h _ hj, e]

theorem repT_eval {m : Nat} {L : List (BitVec 64)} {σ : Regs Nat} (h : KOK m L σ) (t : Tst Nat) :
    (repT m L t).eval σ = t.eval σ := by
  simp only [Tst.eval, repT, repA_eval h]

theorem repI_step {m : Nat} {L : List (BitVec 64)} {i : Ins Nat} {σ σ' : St Nat} (hst : Step ram fp i σ σ')
    (h : KOK m L σ.reg) : Step ram fp (repI m L i) σ σ' := by
  cases hst with
  | @set d a =>
    have := Step.set (ram := ram) (fp := fp) (d := d) (a := repA m L a) (s := σ); rwa [repA_eval h] at this
  | @bin op d a b =>
    have := Step.bin (ram := ram) (fp := fp) (op := op) (d := d) (a := repA m L a) (b := repA m L b) (s := σ)
    rwa [repA_eval h, repA_eval h] at this
  | @mop o d a b =>
    have := Step.mop (ram := ram) (fp := fp) (m := o) (d := d) (a := repA m L a) (b := repA m L b) (s := σ)
    rwa [repA_eval h, repA_eval h] at this
  | lbu h1 h2 => exact .lbu h1 h2
  | @sb v a off _ h1 =>
    have := Step.sb (ram := ram) (fp := fp) (v := repA m L v) (a := a) (off := off) (s := σ) h1
    rwa [repA_eval h] at this
  | ldS h1 h2 h3 => exact .ldS h1 h2 h3
  | stS h1 h2 => exact .stS h1 h2
  | ld h1 h2 h3 => exact .ld h1 h2 h3
  | sd h1 h2 => exact .sd h1 h2

theorem KOK.keep {m : Nat} {L : List (BitVec 64)} {c : Code Nat} {σ σ' : St Nat} (hx : Exec ram fp c σ σ')
    (hw : ∀ j, j < L.length → m + j ∉ wrs c) (h : KOK m L σ.reg) : KOK m L σ'.reg :=
  fun j hj => (wrs_exec hx (hw j hj)).trans (h j hj)

/-- **the code with the registers for the constants runs as before** (same states) -/
theorem repC_ok {m : Nat} {L : List (BitVec 64)} : ∀ {c : Code Nat} {σ σ' : St Nat}, Exec ram fp c σ σ' →
    (∀ j, j < L.length → m + j ∉ wrs c) → KOK m L σ.reg → Exec ram fp (repC m L c) σ σ' := by
  intro c σ σ' h
  induction h with
  | skip => exact fun _ _ => .skip
  | ins hst => exact fun _ hk => .ins (repI_step hst hk)
  | seq ha _ iha ihb =>
    intro hw hk
    have hwa : ∀ j, j < L.length → m + j ∉ wrs _ := fun j hj e => hw j hj (List.mem_append_left _ e)
    exact .seq (iha hwa hk) (ihb (fun j hj e => hw j hj (List.mem_append_right _ e)) (hk.keep ha hwa))
  | whenT ht _ ih => exact fun hw hk => .whenT (by rw [repT_eval hk]; exact ht) (ih hw hk)
  | whenF ht => exact fun _ hk => .whenF (by rw [repT_eval hk]; exact ht)
  | loopF hp ht ihp =>
    intro hw hk
    have hwp : ∀ j, j < L.length → m + j ∉ wrs _ := fun j hj e => hw j hj (List.mem_append_left _ e)
    exact .loopF (ihp hwp hk) (by rw [repT_eval (hk.keep hp hwp)]; exact ht)
  | loopT hp ht hb _ ihp ihb ihl =>
    intro hw hk
    have hwp : ∀ j, j < L.length → m + j ∉ wrs _ := fun j hj e => hw j hj (List.mem_append_left _ e)
    have hwb : ∀ j, j < L.length → m + j ∉ wrs _ := fun j hj e => hw j hj (List.mem_append_right _ e)
    have k₁ := hk.keep hp hwp
    exact .loopT (ihp hwp hk) (by rw [repT_eval k₁]; exact ht) (ihb hwb k₁) (ihl hw (k₁.keep hb hwb))
  | loop2A hp ht ihp =>
    intro hw hk
    have hwp : ∀ j, j < L.length → m + j ∉ wrs _ := fun j hj e => hw j hj (List.mem_append_left _ e)
    exact .loop2A (ihp hwp hk) (by rw [repT_eval (hk.keep hp hwp)]; exact ht)
  | loop2B hp ht hq hu ihp ihq =>
    intro hw hk
    have hwp : ∀ j, j < L.length → m + j ∉ wrs _ := fun j hj e => hw j hj (List.mem_append_left _ e)
    have hwq : ∀ j, j < L.length → m + j ∉ wrs _ := fun j hj e =>
      hw j hj (List.mem_append_right _ (List.mem_append_left _ e))
    have k₁ := hk.keep hp hwp
    exact .loop2B (ihp hwp hk) (by rw [repT_eval k₁]; exact ht) (ihq hwq k₁)
      (by rw [repT_eval (k₁.keep hq hwq)]; exact hu)
  | loop2T hp ht hq hu hb _ ihp ihq ihb ihl =>
    intro hw hk
    have hwp : ∀ j, j < L.length → m + j ∉ wrs _ := fun j hj e => hw j hj (List.mem_append_left _ e)
    have hwq : ∀ j, j < L.length → m + j ∉ wrs _ := fun j hj e =>
      hw j hj (List.mem_append_right _ (List.mem_append_left _ e))
    have hwb : ∀ j, j < L.length → m + j ∉ wrs _ := fun j hj e =>
      hw j hj (List.mem_append_right _ (List.mem_append_right _ e))
    have k₁ := hk.keep hp hwp
    have k₂ := k₁.keep hq hwq
    exact .loop2T (ihp hwp hk) (by rw [repT_eval k₁]; exact ht) (ihq hwq k₁) (by rw [repT_eval k₂]; exact hu)
      (ihb hwb k₂) (ihl hw (k₂.keep hb hwb))

/-! ## Which constants, and their loading -/

/-- outside the 12-bit immediate range -/
def big (c : BitVec 64) : Bool := !(decide (c.toInt < 2048) && decide (-2048 ≤ c.toInt))

def kA : Arg Nat → List (BitVec 64)
  | .i c => [c]
  | _ => []

def kBig : Arg Nat → List (BitVec 64)
  | .i c => if big c then [c] else []
  | _ => []

def kT (t : Tst Nat) : List (BitVec 64) := (kA t.a ++ kA t.b).filter (· != 0)

def kI : Ins Nat → List (BitVec 64)
  | .set _ a => kBig a
  | .bin _ _ a b => kA a ++ kBig b
  | .mop _ _ a b => kA a ++ kA b
  | .sb v _ _ => (kA v).filter (· != 0)
  | _ => []

/-- the constants worth a register -/
def kC : Code Nat → List (BitVec 64)
  | .ins i => kI i
  | .seq a b => kC a ++ kC b
  | .when t b => kT t ++ kC b
  | .loop p t b => kC p ++ kT t ++ kC b
  | .loop2 p₁ t₁ p₂ t₂ b => kC p₁ ++ kT t₁ ++ kC p₂ ++ kT t₂ ++ kC b
  | .skip => []

/-- `m + j := L[j]` -/
def sets (m : Nat) : List (BitVec 64) → Code Nat
  | [] => .skip
  | c :: L => .seq (.ins (.set m (.i c))) (sets (m + 1) L)

theorem sets_ok : ∀ (L : List (BitVec 64)) (m : Nat) (τ : St Nat), ∃ τ', Exec ram fp (sets m L) τ τ' ∧
    τ'.mem = τ.mem ∧ (∀ x, x < m → τ'.reg x = τ.reg x) ∧ KOK m L τ'.reg
  | [], _, τ => ⟨τ, .skip, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | c :: L, m, τ => by
    obtain ⟨τ', hx, hm, hr, hk⟩ := sets_ok L (m + 1) ⟨upd τ.reg m c, τ.mem⟩
    refine ⟨τ', .seq (.ins .set) hx, hm, fun x hx => (hr x (by omega)).trans (upd_ne _ _ (by omega)), ?_⟩
    intro j hj
    cases j with
    | zero => exact (hr m (by omega)).trans (upd_eq _ _ _)
    | succ j =>
      have := hk j (by simp only [List.length_cons] at hj; omega)
      rw [show m + (j + 1) = m + 1 + j by omega]; exact this

/-- stable insertion sort (structural: the kernel evaluates it; the order `mergeSort` gives) -/
def insS {α : Type} (le : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if le a b then a :: b :: l else b :: insS le a l

def isort {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | a :: l => insS le a (isort le l)

/-- the `k` constants of `c` used most often -/
def kSel (k : Nat) (c : Code Nat) : List (BitVec 64) :=
  ((kC c).eraseDups |> isort fun a b => (kC c).count b ≤ (kC c).count a).take k

/-- one loop with its (at most `k`) constants loaded first -/
def hoistL (k m : Nat) (c : Code Nat) : Code Nat :=
  if (kSel k c).isEmpty then c else .seq (sets m (kSel k c)) (repC m (kSel k c) c)

/-- some loop inside -/
def inner : Code Nat → Bool
  | .seq a b => inner a || inner b
  | .when _ b => inner b
  | .loop .. | .loop2 .. => true
  | _ => false

/-- every innermost loop -/
def hoistC (k m : Nat) : Code Nat → Code Nat
  | .seq a b => .seq (hoistC k m a) (hoistC k m b)
  | .when t b => .when t (hoistC k m b)
  | .loop p t b => if (inner p || inner b) = true then .loop (hoistC k m p) t (hoistC k m b) else hoistL k m (.loop p t b)
  | .loop2 p₁ t₁ p₂ t₂ b => if (inner p₁ || inner p₂ || inner b) = true then
      .loop2 (hoistC k m p₁) t₁ (hoistC k m p₂) t₂ (hoistC k m b) else hoistL k m (.loop2 p₁ t₁ p₂ t₂ b)
  | c => c

theorem hoistL_ok {k m : Nat} {c : Code Nat} {σ σ' : St Nat} (h : Exec ram fp c σ σ') (hc : ∀ x, x ∈ c.regs → x < m)
    {τ : St Nat} (hr : RM m σ τ) : ∃ τ', Exec ram fp (hoistL k m c) τ τ' ∧ RM m σ' τ' := by
  unfold hoistL
  split
  · exact same_RM h hc hr
  · generalize kSel k c = L
    obtain ⟨τ₁, x₁, m₁, r₁, k₁⟩ := sets_ok (ram := ram) (fp := fp) L m τ
    obtain ⟨τ', x', r'⟩ := same_RM h hc (τ := τ₁) ⟨m₁.trans hr.1, fun x hx => (r₁ x hx).trans (hr.2 x hx)⟩
    exact ⟨τ', .seq x₁ (repC_ok x' (fun j _ e => absurd (hc _ (wrs_regs e)) (by omega)) k₁), r'⟩

theorem tstRM {m : Nat} {t : Tst Nat} {σ τ : St Nat} (hr : RM m σ τ) (ht : ∀ x, x ∈ t.regs → x < m) :
    t.eval τ.reg = t.eval σ.reg := tst_eq fun y hy => hr.2 y (ht y hy)

theorem hoistC_ok {k m : Nat} : ∀ {c : Code Nat} {σ σ' : St Nat}, Exec ram fp c σ σ' → (∀ x, x ∈ c.regs → x < m) →
    ∀ {τ : St Nat}, RM m σ τ → ∃ τ', Exec ram fp (hoistC k m c) τ τ' ∧ RM m σ' τ' := by
  intro c σ σ' h
  induction h with
  | skip => intro _ τ hr; exact ⟨τ, .skip, hr⟩
  | ins hst => intro hc τ hr; exact same_RM (.ins hst) hc hr
  | seq _ _ iha ihb =>
    intro hc τ hr
    obtain ⟨τ₁, x₁, r₁⟩ := iha (fun x hx => hc x (List.mem_append_left _ hx)) hr
    obtain ⟨τ₂, x₂, r₂⟩ := ihb (fun x hx => hc x (List.mem_append_right _ hx)) r₁
    exact ⟨τ₂, .seq x₁ x₂, r₂⟩
  | whenT ht _ ih =>
    intro hc τ hr
    obtain ⟨τ₁, x₁, r₁⟩ := ih (fun x hx => hc x (List.mem_append_right _ hx)) hr
    exact ⟨τ₁, .whenT ((tstRM hr fun y hy => hc y (List.mem_append_left _ hy)).trans ht) x₁, r₁⟩
  | whenF ht =>
    intro hc τ hr
    exact ⟨τ, .whenF ((tstRM hr fun y hy => hc y (List.mem_append_left _ hy)).trans ht), hr⟩
  | @loopF p t b s s₁ hp ht ihp =>
    intro hc τ hr
    show ∃ τ', Exec ram fp (if (inner p || inner b) = true then _ else _) τ τ' ∧ _
    split
    · obtain ⟨τ₁, x₁, r₁⟩ := ihp (fun x hx => hc x (List.mem_append_left _ hx)) hr
      exact ⟨τ₁, .loopF x₁ ((tstRM r₁ fun y hy =>
        hc y (List.mem_append_right _ (List.mem_append_left _ hy))).trans ht), r₁⟩
    · exact hoistL_ok (.loopF hp ht) hc hr
  | @loopT p t b s s₁ s₂ s₃ hp ht hb hl ihp ihb ihl =>
    intro hc τ hr
    have ihl' := @ihl hc
    show ∃ τ', Exec ram fp (if (inner p || inner b) = true then _ else _) τ τ' ∧ _
    split
    · rename_i hi
      simp only [hoistC, if_pos hi] at ihl'
      obtain ⟨τ₁, x₁, r₁⟩ := ihp (fun x hx => hc x (List.mem_append_left _ hx)) hr
      obtain ⟨τ₂, x₂, r₂⟩ := ihb (fun x hx => hc x (List.mem_append_right _ (List.mem_append_right _ hx))) r₁
      obtain ⟨τ₃, x₃, r₃⟩ := ihl' r₂
      exact ⟨τ₃, .loopT x₁ ((tstRM r₁ fun y hy =>
        hc y (List.mem_append_right _ (List.mem_append_left _ hy))).trans ht) x₂ x₃, r₃⟩
    · exact hoistL_ok (.loopT hp ht hb hl) hc hr
  | @loop2A p₁ t₁ p₂ t₂ b s s₁ hp ht ihp =>
    intro hc τ hr
    show ∃ τ', Exec ram fp (if (inner p₁ || inner p₂ || inner b) = true then _ else _) τ τ' ∧ _
    split
    · obtain ⟨τ₁, x₁, r₁⟩ := ihp (fun x hx => hc x (List.mem_append_left _ hx)) hr
      exact ⟨τ₁, .loop2A x₁ ((tstRM r₁ fun y hy =>
        hc y (List.mem_append_right _ (List.mem_append_left _ hy))).trans ht), r₁⟩
    · exact hoistL_ok (.loop2A hp ht) hc hr
  | @loop2B p₁ t₁ p₂ t₂ b s s₁ s₂ hp ht hq hu ihp ihq =>
    intro hc τ hr
    show ∃ τ', Exec ram fp (if (inner p₁ || inner p₂ || inner b) = true then _ else _) τ τ' ∧ _
    split
    · obtain ⟨τ₁, x₁, r₁⟩ := ihp (fun x hx => hc x (List.mem_append_left _ hx)) hr
      obtain ⟨τ₂, x₂, r₂⟩ := ihq (fun x hx => hc x (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ hx)))) r₁
      exact ⟨τ₂, .loop2B x₁ ((tstRM r₁ fun y hy =>
        hc y (List.mem_append_right _ (List.mem_append_left _ hy))).trans ht) x₂ ((tstRM r₂ fun y hy =>
        hc y (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_left _ hy))))).trans hu), r₂⟩
    · exact hoistL_ok (.loop2B hp ht hq hu) hc hr
  | @loop2T p₁ t₁ p₂ t₂ b s s₁ s₂ s₃ s₄ hp ht hq hu hb hl ihp ihq ihb ihl =>
    intro hc τ hr
    have ihl' := @ihl hc
    show ∃ τ', Exec ram fp (if (inner p₁ || inner p₂ || inner b) = true then _ else _) τ τ' ∧ _
    split
    · rename_i hi
      simp only [hoistC, if_pos hi] at ihl'
      obtain ⟨τ₁, x₁, r₁⟩ := ihp (fun x hx => hc x (List.mem_append_left _ hx)) hr
      obtain ⟨τ₂, x₂, r₂⟩ := ihq (fun x hx => hc x (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_left _ hx)))) r₁
      obtain ⟨τ₃, x₃, r₃⟩ := ihb (fun x hx => hc x (List.mem_append_right _ (List.mem_append_right _
        (List.mem_append_right _ (List.mem_append_right _ hx))))) r₂
      obtain ⟨τ₄, x₄, r₄⟩ := ihl' r₃
      exact ⟨τ₄, .loop2T x₁ ((tstRM r₁ fun y hy =>
        hc y (List.mem_append_right _ (List.mem_append_left _ hy))).trans ht) x₂ ((tstRM r₂ fun y hy =>
        hc y (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
          (List.mem_append_left _ hy))))).trans hu) x₃ x₄, r₄⟩
    · exact hoistL_ok (.loop2T hp ht hq hu hb hl) hc hr

/-- **constants of loops in registers** -/
def hoist (k : Nat) (vars : List Nat) (c : Code Nat) : Code Nat :=
  hoistC k ((vars ++ c.regs).foldr max 0 + 1) c

/-- **Hoisting preserves executions** (same memory, same outputs). -/
theorem hoist_ok (k : Nat) (vars : List Nat) {c : Code Nat} {σ σ' : St Nat} (h : Exec ram fp c σ σ') :
    ∃ τ', Exec ram fp (hoist k vars c) σ τ' ∧ τ'.mem = σ'.mem ∧ ∀ x, x ∈ vars → τ'.reg x = σ'.reg x := by
  unfold hoist
  have hlt : ∀ x, x ∈ vars ++ c.regs → x < (vars ++ c.regs).foldr max 0 + 1 := fun x hx => lt_foldr_max hx
  obtain ⟨τ', x', r'⟩ := hoistC_ok h (fun x hx => hlt x (List.mem_append_right _ hx)) (τ := σ)
    ⟨rfl, fun _ _ => rfl⟩
  exact ⟨τ', x', r'.1, fun x hx => r'.2 x (hlt x (List.mem_append_left _ hx))⟩

end Hoist
end Proven.Mach.IR
