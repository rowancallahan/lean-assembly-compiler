/- Control-flow clean-ups of the IR (IR → IR on virtual registers, before strength reduction).

* `once`: a loop that runs at most once, `while a ≠ 0 do { B; a := 0 }`, becomes `if a ≠ 0 then B; a := 0`
  (the front end's conditionals, `Riscv/Frontx/Tree.lean`).
* `fuse`: a test `d ≠ 0` / `d = 0` on a register that holds a 0/1 comparison `x op y` (or a copy) becomes the
  comparison itself, while `d`, `x`, `y` are not written in between (same states).
* `rot`: `k := c (c ≠ 0); while T₁ ∧ k ≠ 0 do { Y; if k ≠ 0 then S }` (`S` keeps `k`) becomes
  `while T₁ ∧ (Y; k ≠ 0) do S` (the exit test of a search loop moves into the loop head).
* `nrm`: flat `seq`s, no `skip`s or empty `when`s; dead-code elimination is `SR.dce`.

`flow_ok`: an execution of `c` gives one of `flow vars c` from the same state, same memory, same `vars`. -/
import Compiler.Opt.SR

namespace Proven.Mach.IR

deriving instance DecidableEq for Arg
deriving instance DecidableEq for Tst

namespace Flow
open SR

variable {ram : Nat → Prop} {fp : Nat}

/-! ## Definitions -/

/-- right-nested concatenation without `skip`s -/
def cat : Code Nat → Code Nat → Code Nat
  | .skip, b => b
  | .seq a₁ a₂, b => .seq a₁ (cat a₂ b)
  | a, .skip => a
  | a, b => .seq a b

/-- flat `seq`s, no `skip`s, no `when` over nothing -/
def nrm : Code Nat → Code Nat
  | .seq a b => cat (nrm a) (nrm b)
  | .when t b => if triv (nrm b) = true then .skip else .when t (nrm b)
  | .loop p t b => .loop (nrm p) t (nrm b)
  | .loop2 p₁ t₁ p₂ t₂ b => .loop2 (nrm p₁) t₁ (nrm p₂) t₂ (nrm b)
  | c => c

/-- `while a ≠ 0 do { B; a := 0 }` (trivial head) as `if a ≠ 0 then B; a := 0` -/
def onceL (p : Code Nat) (t : Tst Nat) (b : Code Nat) : Code Nat :=
  match t, b with
  | ⟨.ne, .r a, .i z⟩, .seq B (.ins (.set a' (.i z'))) =>
    if (triv p && decide (a' = a) && decide (z = 0) && decide (z' = 0)) = true then
      .seq (.when t B) (.ins (.set a (.i 0)))
    else .loop p t b
  | _, _ => .loop p t b

def once : Code Nat → Code Nat
  | .seq a b => .seq (once a) (once b)
  | .when t b => .when t (once b)
  | .loop p t b => onceL (once p) t (once b)
  | .loop2 p₁ t₁ p₂ t₂ b => .loop2 (once p₁) t₁ (once p₂) t₂ (once b)
  | c => c

/-- a known value of a register: a 0/1 comparison or a copy -/
inductive Fact where
  | cmp (c : Cond) (a b : Arg Nat)
  | cp (a : Arg Nat)

def Fact.val (σ : Regs Nat) : Fact → BitVec 64
  | .cmp c a b => if c.eval (a.eval σ) (b.eval σ) then 1 else 0
  | .cp a => a.eval σ

def Fact.regs : Fact → List Nat
  | .cmp _ a b => a.regs ++ b.regs
  | .cp a => a.regs

abbrev Fs := List (Nat × Fact)

def FOK (F : Fs) (σ : Regs Nat) : Prop := ∀ d f, (d, f) ∈ F → σ d = f.val σ

def look : Fs → Nat → Option Fact
  | [], _ => none
  | (d, f) :: F, x => if d = x then some f else look F x

/-- one rewrite of a test against zero -/
def rw1 (F : Fs) (t : Tst Nat) : Tst Nat :=
  match t with
  | ⟨.ne, .r d, .i z⟩ =>
    if z = 0 then
      match look F d with
      | some (.cmp c a b) => ⟨c, a, b⟩
      | some (.cp a) => ⟨.ne, a, .i 0⟩
      | none => t
    else t
  | ⟨.eq, .r d, .i z⟩ =>
    if z = 0 then
      match look F d with
      | some (.cmp c a b) => ⟨c.neg, a, b⟩
      | some (.cp a) => ⟨.eq, a, .i 0⟩
      | none => t
    else t
  | _ => t

def rwT (F : Fs) : Nat → Tst Nat → Tst Nat
  | 0, t => t
  | n + 1, t => rwT F n (rw1 F t)

/-- the facts that survive writing `d` -/
def killF (F : Fs) (d : Nat) : Fs := F.filter fun p => !decide (p.1 = d) && !p.2.regs.contains d

/-- the facts that survive code writing `ws` -/
def keepF (F : Fs) (ws : List Nat) : Fs := F.filter fun p => !ws.contains p.1 && p.2.regs.all fun x => !ws.contains x

/-- the test of a comparison operator -/
def cmpOp : Op → Option Cond
  | .ult => some .ltu
  | .slt => some .lt
  | .eq => some .eq
  | _ => none

def factOf : Ins Nat → Option (Nat × Fact)
  | .bin op d a b => match cmpOp op with
    | some c => if (a.regs ++ b.regs).contains d then none else some (d, .cmp c a b)
    | none => none
  | .set d a => if a.regs.contains d then none else some (d, .cp a)
  | _ => none

def afterF (F : Fs) (i : Ins Nat) : Fs :=
  match i.dst with
  | some d => match factOf i with
    | some p => p :: killF F d
    | none => killF F d
  | none => F

/-- tests rewritten with the known facts (same states); the facts after the code -/
def fuse (F : Fs) : Code Nat → Code Nat × Fs
  | .skip => (.skip, F)
  | .ins i => (.ins i, afterF F i)
  | .seq a b => ((fuse F a).1.seq (fuse (fuse F a).2 b).1, (fuse (fuse F a).2 b).2)
  | .when t b => (.when (rwT F 4 t) (fuse F b).1, keepF F (wrs b))
  | .loop p t b => (.loop (fuse [] p).1 (rwT (fuse [] p).2 4 t) (fuse (fuse [] p).2 b).1, [])
  | .loop2 p₁ t₁ p₂ t₂ b =>
    (.loop2 (fuse [] p₁).1 (rwT (fuse [] p₁).2 4 t₁) (fuse (fuse [] p₁).2 p₂).1
      (rwT (fuse (fuse [] p₁).2 p₂).2 4 t₂) (fuse (fuse (fuse [] p₁).2 p₂).2 b).1, [])

/-- `c` is `Y; when t S` (right-nested) -/
def splitW : Code Nat → Option (Code Nat × Tst Nat × Code Nat)
  | .when t S => some (.skip, t, S)
  | .seq a b => (splitW b).map fun r => (.seq a r.1, r.2.1, r.2.2)
  | _ => none

/-- `while T₁ ∧ k ≠ 0 do { Y; when tS S }` with `tS ≡ k ≠ 0` after `Y` as `while T₁ ∧ (Y; tS) do S` -/
def rotL (p₁ : Code Nat) (t₁ : Tst Nat) (p₂ : Code Nat) (t₂ : Tst Nat) (b : Code Nat) : Code Nat :=
  match t₂, splitW b with
  | ⟨.ne, .r k, .i z⟩, some (Y, tS, S) =>
    if (triv p₁ && triv p₂ && decide (z = 0) && !(wrs S).contains k && decide (rwT (fuse [] Y).2 4 t₂ = tS)) = true
    then .loop2 p₁ t₁ Y tS S else .loop2 p₁ t₁ p₂ t₂ b
  | _, _ => .loop2 p₁ t₁ p₂ t₂ b

/-- `k := c` (`c ≠ 0`) followed by such a loop -/
def rotS (a b : Code Nat) : Code Nat :=
  match a, b with
  | .ins (.set k (.i c)), .loop2 p₁ t₁ p₂ t₂ body =>
    if (!decide (c = 0) && decide (t₂ = ⟨.ne, .r k, .i 0⟩)) = true then .seq a (rotL p₁ t₁ p₂ t₂ body) else .seq a b
  | .ins (.set k (.i c)), .seq (.loop2 p₁ t₁ p₂ t₂ body) r =>
    if (!decide (c = 0) && decide (t₂ = ⟨.ne, .r k, .i 0⟩)) = true then .seq a (.seq (rotL p₁ t₁ p₂ t₂ body) r)
    else .seq a b
  | _, _ => .seq a b

def rot : Code Nat → Code Nat
  | .seq a b => rotS (rot a) (rot b)
  | .when t b => .when t (rot b)
  | .loop p t b => .loop (rot p) t (rot b)
  | .loop2 p₁ t₁ p₂ t₂ b => .loop2 (rot p₁) t₁ (rot p₂) t₂ (rot b)
  | c => c

/-- dead-code elimination, or the code itself -/
def dceOr (vars : List Nat) (c : Code Nat) : Code Nat :=
  match dce c vars with
  | some (c', _) => c'
  | none => c

/-- some at-most-once loop -/
def hasOnce : Code Nat → Bool
  | .seq a b => hasOnce a || hasOnce b
  | .when _ b => hasOnce b
  | .loop p t b => hasOnce p || hasOnce b || match onceL p t b with | .loop .. => false | _ => true
  | .loop2 p₁ _ p₂ _ b => hasOnce p₁ || hasOnce p₂ || hasOnce b
  | _ => false

/-- **the clean-ups** (the input when it has no at-most-once loop) -/
def flow (vars : List Nat) (c : Code Nat) : Code Nat :=
  if hasOnce c then
    nrm (dceOr vars (fuse [] (nrm (rot (nrm (dceOr vars (fuse [] (nrm (once c))).1))))).1)
  else c

/-! ## Congruence -/

theorem loop_congr {p p' b b' : Code Nat} {t : Tst Nat} (hp : ∀ s s', Exec ram fp p s s' → Exec ram fp p' s s')
    (hb : ∀ s s', Exec ram fp b s s' → Exec ram fp b' s s') {σ σ' : St Nat} (h : Exec ram fp (.loop p t b) σ σ') :
    Exec ram fp (.loop p' t b') σ σ' := by
  generalize hc : Code.loop p t b = c at h
  induction h with
  | loopF h₁ ht => cases hc; exact .loopF (hp _ _ h₁) ht
  | loopT h₁ ht h₂ _ _ _ ih => cases hc; exact .loopT (hp _ _ h₁) ht (hb _ _ h₂) (ih rfl)
  | _ => cases hc

theorem loop2_congr {p₁ p₁' p₂ p₂' b b' : Code Nat} {t₁ t₂ : Tst Nat}
    (h1 : ∀ s s', Exec ram fp p₁ s s' → Exec ram fp p₁' s s') (h2 : ∀ s s', Exec ram fp p₂ s s' → Exec ram fp p₂' s s')
    (hb : ∀ s s', Exec ram fp b s s' → Exec ram fp b' s s') {σ σ' : St Nat}
    (h : Exec ram fp (.loop2 p₁ t₁ p₂ t₂ b) σ σ') : Exec ram fp (.loop2 p₁' t₁ p₂' t₂ b') σ σ' := by
  generalize hc : Code.loop2 p₁ t₁ p₂ t₂ b = c at h
  induction h with
  | loop2A x₁ ht => cases hc; exact .loop2A (h1 _ _ x₁) ht
  | loop2B x₁ ht₁ x₂ ht₂ => cases hc; exact .loop2B (h1 _ _ x₁) ht₁ (h2 _ _ x₂) ht₂
  | loop2T x₁ ht₁ x₂ ht₂ xb _ _ _ _ ih => cases hc; exact .loop2T (h1 _ _ x₁) ht₁ (h2 _ _ x₂) ht₂ (hb _ _ xb) (ih rfl)
  | _ => cases hc

/-! ## `nrm` -/

theorem cat_ok : ∀ {a b : Code Nat} {σ σ' : St Nat}, Exec ram fp (.seq a b) σ σ' → Exec ram fp (cat a b) σ σ'
  | .skip, b, σ, σ', h => by cases h with | seq h₁ h₂ => cases h₁; exact h₂
  | .seq a₁ a₂, b, σ, σ', h => by
    cases h with | seq h₁ h₂ => cases h₁ with | seq x₁ x₂ => exact .seq x₁ (cat_ok (.seq x₂ h₂))
  | .ins _, .skip, _, _, h | .when _ _, .skip, _, _, h | .loop _ _ _, .skip, _, _, h
  | .loop2 _ _ _ _ _, .skip, _, _, h => by cases h with | seq h₁ h₂ => cases h₂; exact h₁
  | .ins _, .ins _, _, _, h | .ins _, .seq _ _, _, _, h | .ins _, .when _ _, _, _, h | .ins _, .loop _ _ _, _, _, h
  | .ins _, .loop2 _ _ _ _ _, _, _, h | .when _ _, .ins _, _, _, h | .when _ _, .seq _ _, _, _, h
  | .when _ _, .when _ _, _, _, h | .when _ _, .loop _ _ _, _, _, h | .when _ _, .loop2 _ _ _ _ _, _, _, h
  | .loop _ _ _, .ins _, _, _, h | .loop _ _ _, .seq _ _, _, _, h | .loop _ _ _, .when _ _, _, _, h
  | .loop _ _ _, .loop _ _ _, _, _, h | .loop _ _ _, .loop2 _ _ _ _ _, _, _, h
  | .loop2 _ _ _ _ _, .ins _, _, _, h | .loop2 _ _ _ _ _, .seq _ _, _, _, h | .loop2 _ _ _ _ _, .when _ _, _, _, h
  | .loop2 _ _ _ _ _, .loop _ _ _, _, _, h | .loop2 _ _ _ _ _, .loop2 _ _ _ _ _, _, _, h => h

theorem nrm_ok : ∀ (c : Code Nat) {σ σ' : St Nat}, Exec ram fp c σ σ' → Exec ram fp (nrm c) σ σ'
  | .skip, _, _, h => h
  | .ins _, _, _, h => h
  | .seq a b, _, _, h => by cases h with | seq h₁ h₂ => exact cat_ok (.seq (nrm_ok a h₁) (nrm_ok b h₂))
  | .when t b, σ, σ', h => by
    simp only [nrm]
    by_cases ht : triv (nrm b) = true
    · rw [if_pos ht]
      cases h with
      | whenT _ hb => rw [triv_exec (nrm_ok b hb) ht]; exact .skip
      | whenF _ => exact .skip
    · rw [if_neg ht]
      cases h with
      | whenT h₁ hb => exact .whenT h₁ (nrm_ok b hb)
      | whenF h₁ => exact .whenF h₁
  | .loop p t b, _, _, h => loop_congr (fun _ _ => nrm_ok p) (fun _ _ => nrm_ok b) h
  | .loop2 p₁ t₁ p₂ t₂ b, _, _, h =>
    loop2_congr (fun _ _ => nrm_ok p₁) (fun _ _ => nrm_ok p₂) (fun _ _ => nrm_ok b) h

/-! ## `once` -/

theorem upd_self (σ : St Nat) (a : Nat) {v : BitVec 64} (h : σ.reg a = v) : (⟨upd σ.reg a v, σ.mem⟩ : St Nat) = σ := by
  cases σ with | mk reg mem =>
  simp only [St.mk.injEq, and_true]; funext x
  by_cases e : x = a
  · subst e; rw [upd_eq]; exact h.symm
  · exact upd_ne _ _ e

theorem onceL_ok {p b : Code Nat} {t : Tst Nat} {σ σ' : St Nat} (h : Exec ram fp (.loop p t b) σ σ') :
    Exec ram fp (onceL p t b) σ σ' := by
  unfold onceL
  split
  · rename_i a z B a' z'
    by_cases hc : (triv p && decide (a' = a) && decide (z = 0) && decide (z' = 0)) = true
    · rw [if_pos hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hp, rfl⟩, rfl⟩, rfl⟩ := hc
      have tz : ∀ s : St Nat, Tst.eval s.reg ⟨.ne, .r a', .i 0⟩ = false → s.reg a' = 0 := fun s ht => by
        simp [Tst.eval, Cond.eval, Arg.eval] at ht; exact of_decide_eq_true ht
      cases h with
      | loopF h₁ ht =>
        rw [triv_exec h₁ hp] at ht ⊢
        have e := upd_self σ a' (tz σ ht)
        have := Exec.seq (Exec.whenF (body := B) (ram := ram) (fp := fp) ht)
          (Exec.ins (Step.set (ram := ram) (fp := fp) (d := a') (a := .i 0) (s := σ)))
        rwa [show (Arg.i 0 : Arg Nat).eval σ.reg = 0 from rfl, e] at this
      | loopT h₁ ht h₂ h₃ =>
        rw [triv_exec h₁ hp] at ht h₂
        cases h₂ with
        | seq hB hs =>
          cases hs with
          | ins hs =>
            cases hs
            cases h₃ with
            | loopF h₄ _ =>
              rw [triv_exec h₄ hp]; exact .seq (.whenT ht hB) (.ins .set)
            | loopT h₄ ht' _ _ =>
              rw [triv_exec h₄ hp] at ht'
              simp [Tst.eval, Cond.eval, Arg.eval, upd_eq] at ht'
    · rw [if_neg hc]; exact h
  · exact h

theorem once_ok : ∀ (c : Code Nat) {σ σ' : St Nat}, Exec ram fp c σ σ' → Exec ram fp (once c) σ σ'
  | .skip, _, _, h => h
  | .ins _, _, _, h => h
  | .seq a b, _, _, h => by cases h with | seq h₁ h₂ => exact .seq (once_ok a h₁) (once_ok b h₂)
  | .when t b, _, _, h => by
    cases h with
    | whenT h₁ hb => exact .whenT h₁ (once_ok b hb)
    | whenF h₁ => exact .whenF h₁
  | .loop p t b, _, _, h => onceL_ok (loop_congr (fun _ _ => once_ok p) (fun _ _ => once_ok b) h)
  | .loop2 p₁ t₁ p₂ t₂ b, _, _, h =>
    loop2_congr (fun _ _ => once_ok p₁) (fun _ _ => once_ok p₂) (fun _ _ => once_ok b) h

/-! ## `fuse` -/

theorem Fact.val_eq {f : Fact} {σ τ : Regs Nat} (h : ∀ x, x ∈ f.regs → τ x = σ x) : f.val τ = f.val σ := by
  cases f with
  | cmp c a b =>
    simp only [Fact.val, arg_eq fun x hx => h x (List.mem_append_left _ hx),
      arg_eq fun x hx => h x (List.mem_append_right _ hx)]
  | cp a => exact arg_eq h

theorem look_mem : ∀ {F : Fs} {x : Nat} {f : Fact}, look F x = some f → (x, f) ∈ F
  | (d, g) :: F, x, f, h => by
    unfold look at h
    by_cases e : d = x
    · rw [if_pos e] at h; cases h; rw [e]; exact List.mem_cons_self ..
    · rw [if_neg e] at h; exact List.mem_cons_of_mem _ (look_mem h)

theorem rw1_eval {F : Fs} {σ : Regs Nat} (hF : FOK F σ) (t : Tst Nat) : (rw1 F t).eval σ = t.eval σ := by
  unfold rw1
  split
  · rename_i d z
    by_cases hz : z = 0
    · rw [if_pos hz]; subst hz
      split
      · rename_i c a b hl
        have := hF _ _ (look_mem hl)
        simp only [Fact.val] at this
        show c.eval (a.eval σ) (b.eval σ) = Cond.ne.eval (σ d) 0
        rw [this]; generalize c.eval (a.eval σ) (b.eval σ) = q; cases q <;> decide
      · rename_i a hl
        have := hF _ _ (look_mem hl)
        simp only [Fact.val] at this
        show Cond.ne.eval (a.eval σ) 0 = Cond.ne.eval (σ d) 0
        rw [this]
      · rfl
    · rw [if_neg hz]
  · rename_i d z
    by_cases hz : z = 0
    · rw [if_pos hz]; subst hz
      split
      · rename_i c a b hl
        have := hF _ _ (look_mem hl)
        simp only [Fact.val] at this
        show c.neg.eval (a.eval σ) (b.eval σ) = Cond.eq.eval (σ d) 0
        rw [Cond.eval_neg, this]; generalize c.eval (a.eval σ) (b.eval σ) = q; cases q <;> decide
      · rename_i a hl
        have := hF _ _ (look_mem hl)
        simp only [Fact.val] at this
        show Cond.eq.eval (a.eval σ) 0 = Cond.eq.eval (σ d) 0
        rw [this]
      · rfl
    · rw [if_neg hz]
  · rfl

theorem rwT_eval {F : Fs} {σ : Regs Nat} (hF : FOK F σ) : ∀ n (t : Tst Nat), (rwT F n t).eval σ = t.eval σ
  | 0, _ => rfl
  | n + 1, t => (rwT_eval hF n _).trans (rw1_eval hF t)

theorem FOK.filter {F : Fs} {σ : Regs Nat} (h : FOK F σ) (q : Nat × Fact → Bool) : FOK (F.filter q) σ :=
  fun d f hm => h d f (List.mem_filter.1 hm).1

theorem FOK.nil {σ : Regs Nat} : FOK [] σ := fun _ _ h => nomatch h

theorem killF_ok {F : Fs} {σ : Regs Nat} (h : FOK F σ) (d : Nat) (v : BitVec 64) : FOK (killF F d) (upd σ d v) := by
  intro x f hm
  simp only [killF, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hm
  obtain ⟨hm, hx, hr⟩ := hm
  rw [upd_ne _ _ hx, Fact.val_eq (τ := upd σ d v) (σ := σ) fun y hy => upd_ne _ _ fun e => by
    rw [e] at hy; exact absurd hy (by simpa using hr)]
  exact h x f hm

theorem cmpOp_eval {op : Op} {c : Cond} (h : cmpOp op = some c) (a b : BitVec 64) :
    op.eval a b = if c.eval a b then 1 else 0 := by
  cases op <;> simp only [cmpOp, reduceCtorEq] at h <;> cases h <;> simp [Op.eval, Cond.eval] <;> rfl

theorem afterF_ok {F : Fs} {i : Ins Nat} {σ σ' : St Nat} (hst : Step ram fp i σ σ') (h : FOK F σ.reg) :
    FOK (afterF F i) σ'.reg := by
  cases hst with
  | @set d a =>
    simp only [afterF, Ins.dst, factOf]
    by_cases hc : a.regs.contains d = true
    · rw [if_pos hc]; exact killF_ok h _ _
    · rw [if_neg hc]
      intro x f hm
      rcases List.mem_cons.1 hm with e | hm
      · cases e
        show upd σ.reg d _ d = (Fact.cp a).val (upd σ.reg d _)
        rw [upd_eq]; simp only [Fact.val]
        exact (arg_eq fun y hy => upd_ne _ _ fun e => hc (by rw [← e]; exact List.contains_iff_mem.2 hy)).symm
      · exact killF_ok h _ _ x f hm
  | @bin op d a b =>
    cases hc : cmpOp op with
    | none => simp only [afterF, Ins.dst, factOf, hc]; exact killF_ok h _ _
    | some c =>
      by_cases hd : (a.regs ++ b.regs).contains d = true
      · simp only [afterF, Ins.dst, factOf, hc, if_pos hd]; exact killF_ok h _ _
      · simp only [afterF, Ins.dst, factOf, hc, if_neg hd]
        intro x f hm
        rcases List.mem_cons.1 hm with e | hm
        · cases e
          show upd σ.reg d _ d = (Fact.cmp c a b).val (upd σ.reg d _)
          rw [upd_eq, cmpOp_eval hc]; simp only [Fact.val]
          rw [arg_eq (τ := upd σ.reg d _) (σ := σ.reg) (a := a) fun y hy => upd_ne _ _ fun e => hd (by
              rw [← e]; exact List.contains_iff_mem.2 (List.mem_append_left _ hy)),
            arg_eq (τ := upd σ.reg d _) (σ := σ.reg) (a := b) fun y hy => upd_ne _ _ fun e => hd (by
              rw [← e]; exact List.contains_iff_mem.2 (List.mem_append_right _ hy))]
        · exact killF_ok h _ _ x f hm
  | mop => exact killF_ok h _ _
  | lbu _ _ => exact killF_ok h _ _
  | sb _ => exact h
  | ldS _ _ _ => exact killF_ok h _ _
  | stS _ _ => exact h
  | ld _ _ _ => exact killF_ok h _ _
  | sd _ _ => exact h

theorem keepF_ok {F : Fs} {ws : List Nat} {σ σ' : Regs Nat} (h : FOK F σ) (hk : ∀ x, x ∉ ws → σ' x = σ x) :
    FOK (keepF F ws) σ' := by
  intro x f hm
  simp only [keepF, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hm
  obtain ⟨hm, hx, hr⟩ := hm
  have nm : ∀ y, ws.contains y = false → y ∉ ws := fun y hy e => by
    rw [List.contains_iff_mem.2 e] at hy; exact nomatch hy
  rw [hk x (nm x hx), Fact.val_eq fun y hy => hk y (nm y (by simpa using hr y hy))]
  exact h x f hm

/-- **the rewritten tests keep the execution** (same states) -/
theorem fuse_ok : ∀ {c : Code Nat} {σ σ' : St Nat}, Exec ram fp c σ σ' → ∀ {F : Fs}, FOK F σ.reg →
    Exec ram fp (fuse F c).1 σ σ' ∧ FOK (fuse F c).2 σ'.reg := by
  intro c σ σ' h
  induction h with
  | skip => exact fun h => ⟨.skip, h⟩
  | ins hst => exact fun h => ⟨.ins hst, afterF_ok hst h⟩
  | seq _ _ iha ihb =>
    intro F hF
    obtain ⟨x₁, k₁⟩ := iha hF
    obtain ⟨x₂, k₂⟩ := ihb k₁
    exact ⟨.seq x₁ x₂, k₂⟩
  | whenT ht hb ih =>
    intro F hF
    exact ⟨.whenT (by rw [rwT_eval hF]; exact ht) (ih hF).1,
      keepF_ok hF fun x hx => wrs_exec hb hx⟩
  | whenF ht =>
    intro F hF
    exact ⟨.whenF (by rw [rwT_eval hF]; exact ht), keepF_ok hF fun _ _ => rfl⟩
  | loopF _ ht ihp =>
    intro F _
    obtain ⟨x₁, k₁⟩ := ihp FOK.nil
    exact ⟨.loopF x₁ (by rw [rwT_eval k₁]; exact ht), FOK.nil⟩
  | loopT _ ht _ _ ihp ihb ihl =>
    intro F _
    obtain ⟨x₁, k₁⟩ := ihp FOK.nil
    exact ⟨.loopT x₁ (by rw [rwT_eval k₁]; exact ht) (ihb k₁).1 (ihl (F := []) FOK.nil).1, FOK.nil⟩
  | loop2A _ ht ih₁ =>
    intro F _
    obtain ⟨x₁, k₁⟩ := ih₁ FOK.nil
    exact ⟨.loop2A x₁ (by rw [rwT_eval k₁]; exact ht), FOK.nil⟩
  | loop2B _ ht₁ _ ht₂ ih₁ ih₂ =>
    intro F _
    obtain ⟨x₁, k₁⟩ := ih₁ FOK.nil
    obtain ⟨x₂, k₂⟩ := ih₂ k₁
    exact ⟨.loop2B x₁ (by rw [rwT_eval k₁]; exact ht₁) x₂ (by rw [rwT_eval k₂]; exact ht₂), FOK.nil⟩
  | loop2T _ ht₁ _ ht₂ _ _ ih₁ ih₂ ihb ihl =>
    intro F _
    obtain ⟨x₁, k₁⟩ := ih₁ FOK.nil
    obtain ⟨x₂, k₂⟩ := ih₂ k₁
    exact ⟨.loop2T x₁ (by rw [rwT_eval k₁]; exact ht₁) x₂ (by rw [rwT_eval k₂]; exact ht₂) (ihb k₂).1
      (ihl (F := []) FOK.nil).1, FOK.nil⟩

/-! ## `rot` -/

theorem splitW_ok : ∀ {c Y S : Code Nat} {t : Tst Nat}, splitW c = some (Y, t, S) → ∀ {σ σ' : St Nat},
    Exec ram fp c σ σ' → Exec ram fp (.seq Y (.when t S)) σ σ'
  | .when t' S', Y, S, t, hs, _, _, h => by
    simp only [splitW, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs; exact .seq .skip h
  | .seq a b, Y, S, t, hs, _, _, h => by
    simp only [splitW] at hs
    cases hb : splitW b with
    | none => rw [hb] at hs; exact nomatch hs
    | some r =>
      rw [hb] at hs; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      cases h with
      | seq h₁ h₂ =>
        cases splitW_ok hb h₂ with
        | seq x₁ x₂ => exact .seq (.seq h₁ x₁) x₂
  | .skip, _, _, _, hs, _, _, _ | .ins _, _, _, _, hs, _, _, _ | .loop _ _ _, _, _, _, hs, _, _, _
  | .loop2 _ _ _ _ _, _, _, _, hs, _, _, _ => nomatch hs

theorem seq_inv {a b : Code Nat} {σ σ' : St Nat} (h : Exec ram fp (.seq a b) σ σ') :
    ∃ s, Exec ram fp a σ s ∧ Exec ram fp b s σ' := by
  cases h with | seq h₁ h₂ => exact ⟨_, h₁, h₂⟩

theorem tne {s : Regs Nat} {k : Nat} : Tst.eval s ⟨.ne, .r k, .i 0⟩ = true ↔ s k ≠ 0 := by
  simp [Tst.eval, Cond.eval, Arg.eval]; exact decide_eq_false_iff_not

theorem rotL_ok {p₁ p₂ b : Code Nat} {t₁ t₂ : Tst Nat} {k : Nat} (hk : t₂ = ⟨.ne, .r k, .i 0⟩) {σ σ' : St Nat}
    (h : Exec ram fp (.loop2 p₁ t₁ p₂ t₂ b) σ σ') (h0 : σ.reg k ≠ 0) : Exec ram fp (rotL p₁ t₁ p₂ t₂ b) σ σ' := by
  subst hk
  unfold rotL
  cases hs : splitW b with
  | none => exact h
  | some r =>
    obtain ⟨Y, tS, S⟩ := r
    dsimp only
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
      obtain ⟨⟨⟨⟨hp₁, hp₂⟩, -⟩, hS⟩, hT⟩ := hc
      generalize hc : Code.loop2 p₁ t₁ p₂ ⟨.ne, .r k, .i 0⟩ b = c at h
      induction h with
      | loop2A x₁ ht => cases hc; exact .loop2A x₁ ht
      | loop2B x₁ ht₁ x₂ ht₂ =>
        cases hc
        rw [triv_exec x₂ hp₂, triv_exec x₁ hp₁] at ht₂
        exact absurd (by simp [Tst.eval, Cond.eval, Arg.eval] at ht₂; exact of_decide_eq_true ht₂) h0
      | @loop2T _ _ _ _ _ s s₁ s₂ s₃ s₄ x₁ ht₁ x₂ ht₂ xb hl _ _ _ ih =>
        cases hc
        rw [triv_exec x₂ hp₂] at xb ht₂
        rw [triv_exec x₁ hp₁] at xb ht₂ ht₁
        obtain ⟨sY, xY, xw⟩ := seq_inv (splitW_ok hs xb)
        have hYt : tS.eval sY.reg = Tst.eval sY.reg ⟨.ne, .r k, .i 0⟩ := by
          rw [← hT]; exact rwT_eval (fuse_ok xY (F := []) FOK.nil).2 _ _
        have hk0 : tS.eval sY.reg = false → sY.reg k = 0 := fun htS => by
          have := hYt ▸ htS; simp [Tst.eval, Cond.eval, Arg.eval] at this; exact of_decide_eq_true this
        cases xw with
        | whenT htS xS =>
          have hk3 : s₃.reg k ≠ 0 := by
            rw [nw_exec xS hS]; exact tne.1 (hYt ▸ htS)
          exact .loop2T (triv_run hp₁ s) ht₁ xY htS xS (ih hk3 rfl)
        | whenF htS =>
          have hk3 := hk0 htS
          cases hl with
          | loop2A y₁ yt =>
            rw [triv_exec y₁ hp₁]; rw [triv_exec y₁ hp₁] at yt
            exact .loop2B (triv_run hp₁ s) ht₁ xY htS
          | loop2B y₁ yt₁ y₂ yt₂ =>
            rw [triv_exec y₂ hp₂, triv_exec y₁ hp₁]
            exact .loop2B (triv_run hp₁ s) ht₁ xY htS
          | loop2T y₁ yt₁ y₂ yt₂ _ _ =>
            rw [triv_exec y₂ hp₂, triv_exec y₁ hp₁] at yt₂
            exact absurd hk3 (tne.1 yt₂)
      | _ => cases hc
    · exact h

theorem rotS_ok {a b : Code Nat} {σ σ' : St Nat} (h : Exec ram fp (.seq a b) σ σ') : Exec ram fp (rotS a b) σ σ' := by
  unfold rotS
  split
  · rename_i k c p₁ t₁ p₂ t₂ body
    by_cases hc : (!decide (c = 0) && decide (t₂ = ⟨.ne, .r k, .i 0⟩)) = true
    · rw [if_pos hc]
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hc
      cases h with
      | seq h₁ h₂ =>
        refine .seq h₁ (rotL_ok hc.2 h₂ ?_)
        cases h₁ with | ins hs => cases hs; show upd σ.reg k _ k ≠ 0; rw [upd_eq]; exact hc.1
    · rw [if_neg hc]; exact h
  · rename_i k c p₁ t₁ p₂ t₂ body r
    by_cases hc : (!decide (c = 0) && decide (t₂ = ⟨.ne, .r k, .i 0⟩)) = true
    · rw [if_pos hc]
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hc
      cases h with
      | seq h₁ h₂ =>
        cases h₂ with
        | seq h₃ h₄ =>
          refine .seq h₁ (.seq (rotL_ok hc.2 h₃ ?_) h₄)
          cases h₁ with | ins hs => cases hs; show upd σ.reg k _ k ≠ 0; rw [upd_eq]; exact hc.1
    · rw [if_neg hc]; exact h
  · exact h

theorem rot_ok : ∀ (c : Code Nat) {σ σ' : St Nat}, Exec ram fp c σ σ' → Exec ram fp (rot c) σ σ'
  | .skip, _, _, h => h
  | .ins _, _, _, h => h
  | .seq a b, _, _, h => by cases h with | seq h₁ h₂ => exact rotS_ok (.seq (rot_ok a h₁) (rot_ok b h₂))
  | .when t b, _, _, h => by
    cases h with
    | whenT h₁ hb => exact .whenT h₁ (rot_ok b hb)
    | whenF h₁ => exact .whenF h₁
  | .loop p t b, _, _, h => loop_congr (fun _ _ => rot_ok p) (fun _ _ => rot_ok b) h
  | .loop2 p₁ t₁ p₂ t₂ b, _, _, h =>
    loop2_congr (fun _ _ => rot_ok p₁) (fun _ _ => rot_ok p₂) (fun _ _ => rot_ok b) h

/-! ## The whole pass -/

/-- same memory, same values of `vars` -/
def Out (vars : List Nat) (σ τ : St Nat) : Prop := τ.mem = σ.mem ∧ ∀ x, x ∈ vars → τ.reg x = σ.reg x

theorem dceOr_ok (vars : List Nat) {c : Code Nat} {σ σ' : St Nat} (h : Exec ram fp c σ σ') :
    ∃ τ', Exec ram fp (dceOr vars c) σ τ' ∧ Out vars σ' τ' := by
  unfold dceOr
  split
  · rename_i c' Lin hd
    obtain ⟨τ', hx, r⟩ := dce_ok h hd (τ := σ) ⟨rfl, fun _ _ => rfl⟩
    exact ⟨τ', hx, r.1, r.2⟩
  · exact ⟨σ', h, rfl, fun _ _ => rfl⟩

theorem fuse_nil {c : Code Nat} {σ σ' : St Nat} (h : Exec ram fp c σ σ') : Exec ram fp (fuse [] c).1 σ σ' :=
  (fuse_ok h FOK.nil).1

/-- **The clean-ups preserve executions** (same memory, same outputs). -/
theorem flow_ok (vars : List Nat) {c : Code Nat} {σ σ' : St Nat} (h : Exec ram fp c σ σ') :
    ∃ τ', Exec ram fp (flow vars c) σ τ' ∧ τ'.mem = σ'.mem ∧ ∀ x, x ∈ vars → τ'.reg x = σ'.reg x := by
  unfold flow
  split
  · obtain ⟨τ₁, x₁, o₁⟩ := dceOr_ok vars (fuse_nil (nrm_ok _ (once_ok c h)))
    obtain ⟨τ₂, x₂, o₂⟩ := dceOr_ok vars (fuse_nil (nrm_ok _ (rot_ok _ (nrm_ok _ x₁))))
    exact ⟨τ₂, nrm_ok _ x₂, o₂.1.trans o₁.1, fun x hx => (o₂.2 x hx).trans (o₁.2 x hx)⟩
  · exact ⟨σ', h, rfl, fun _ _ => rfl⟩

end Flow
end Proven.Mach.IR
