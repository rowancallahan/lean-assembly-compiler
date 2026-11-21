/- Strength reduction of byte-loop indices, with copy propagation and dead-code elimination (IR → IR,
on virtual registers, before register assignment).

A loop `while i <u n do body` (trivial loop-head code) whose index `i` is used in `body` only as
`d := b + i` / `d := i + b` (`b` not written in the loop) and in one increment `i := i + 1` (executed at most
once per iteration) becomes
```
if i ≤u n then { e := b₀ + n; p_b := b + i (each base b); while p_{b₀} ≠ e do body'; i := p_{b₀} - b₀ }
```
where `body'` has `d := p_b` for the address sums and `p_b := p_b + 1` (all `b`) for the increment.
The pointers `p_b` and `e` are fresh registers (`≥ m`, above every register of the code and the outputs).
`i ≤ n` holds at every test (it holds on entry and the body adds at most one to `i < n`), so `i <u n` is
`i ≠ n`, i.e. `b₀ + i ≠ b₀ + n`.  Copy propagation then turns `d := p_b; mem[d]` into `mem[p_b]`, and
dead-code elimination (checked liveness, as `chk`) drops the dead `d := p_b`.

`sr vars c` (total: the input when nothing applies) and `sr_ok`: an execution of `c` gives one of `sr vars c`
from the same state, with the same memory and the same values of `vars`. -/
import Nano.Base.Compiler.Opt.Live

namespace Proven.Mach.IR
namespace SR

variable {ram : Nat → Prop} {fp : Nat}

/-! ## Generic facts -/

theorem upd_eq (σ : Regs Nat) (d : Nat) (v : BitVec 64) : upd σ d v d = v := if_pos rfl
theorem upd_ne (σ : Regs Nat) {d x : Nat} (v : BitVec 64) (h : x ≠ d) : upd σ d v x = σ x := if_neg h

theorem Arg.map_id (a : Arg Nat) : a.map id = a := by cases a <;> rfl

theorem Ins.map_id (i : Ins Nat) : i.map id = i := by
  cases i <;> simp only [Ins.map, Arg.map_id] <;> rfl

theorem Tst.map_id (t : Tst Nat) : t.map id = t := by
  cases t; simp only [Tst.map, Arg.map_id]

theorem Code.map_id : ∀ c : Code Nat, c.map id = c
  | .skip => rfl
  | .ins i => by simp only [Code.map, Ins.map_id]
  | .seq a b => by simp only [Code.map, Code.map_id a, Code.map_id b]
  | .when t b => by simp only [Code.map, Tst.map_id, Code.map_id b]
  | .loop p t b => by simp only [Code.map, Tst.map_id, Code.map_id p, Code.map_id b]
  | .loop2 p₁ t₁ p₂ t₂ b => by
    simp only [Code.map, Tst.map_id, Code.map_id p₁, Code.map_id p₂, Code.map_id b]

/-- registers written -/
def wrs : Code Nat → List Nat
  | .skip => []
  | .ins i => i.dst.toList
  | .seq a b => wrs a ++ wrs b
  | .when _ b => wrs b
  | .loop p _ b => wrs p ++ wrs b
  | .loop2 p₁ _ p₂ _ b => wrs p₁ ++ (wrs p₂ ++ wrs b)

theorem wrs_exec : ∀ {c : Code Nat} {σ σ' : St Nat}, Exec ram fp c σ σ' → ∀ {x}, x ∉ wrs c → σ'.reg x = σ.reg x := by
  intro c σ σ' h
  induction h with
  | skip => exact fun _ => rfl
  | ins hst =>
    intro x hx
    cases hst <;> first | rfl | exact upd_ne _ _ fun e => hx (by simp [wrs, Ins.dst, e])
  | seq _ _ iha ihb =>
    intro x hx; simp only [wrs, List.mem_append, not_or] at hx; rw [ihb hx.2, iha hx.1]
  | whenT _ _ ih => exact ih
  | whenF _ => exact fun _ => rfl
  | loopF _ _ ih => intro x hx; simp only [wrs, List.mem_append, not_or] at hx; exact ih hx.1
  | loopT _ _ _ _ ihp ihb ihl =>
    intro x hx
    have hx' := hx
    simp only [wrs, List.mem_append, not_or] at hx'
    rw [ihl hx, ihb hx'.2, ihp hx'.1]
  | loop2A _ _ ih => intro x hx; simp only [wrs, List.mem_append, not_or] at hx; exact ih hx.1
  | loop2B _ _ _ _ ih₁ ih₂ =>
    intro x hx; simp only [wrs, List.mem_append, not_or] at hx; rw [ih₂ hx.2.1, ih₁ hx.1]
  | loop2T _ _ _ _ _ _ ih₁ ih₂ ihb ihl =>
    intro x hx
    have hx' := hx
    simp only [wrs, List.mem_append, not_or] at hx'
    rw [ihl hx, ihb hx'.2.2, ih₂ hx'.2.1, ih₁ hx'.1]

theorem wrs_regs : ∀ {c : Code Nat} {x : Nat}, x ∈ wrs c → x ∈ c.regs
  | .skip, _, h => nomatch h
  | .ins i, x, h => by
    cases i <;> simp_all [wrs, Ins.dst, Code.regs, Ins.regs]
  | .seq a b, _, h => by
    simp only [wrs, Code.regs, List.mem_append] at h ⊢
    exact h.elim (fun h => .inl (wrs_regs h)) (fun h => .inr (wrs_regs h))
  | .when _ b, _, h => by
    simp only [wrs, Code.regs, List.mem_append] at h ⊢; exact .inr (wrs_regs h)
  | .loop p _ b, _, h => by
    simp only [wrs, Code.regs, List.mem_append] at h ⊢
    exact h.elim (fun h => .inl (wrs_regs h)) (fun h => .inr (.inr (wrs_regs h)))
  | .loop2 p₁ _ p₂ _ b, _, h => by
    simp only [wrs, Code.regs, List.mem_append] at h ⊢
    rcases h with h | h | h
    · exact .inl (wrs_regs h)
    · exact .inr (.inr (.inl (wrs_regs h)))
    · exact .inr (.inr (.inr (.inr (wrs_regs h))))

/-- the same code from a state agreeing on its registers -/
theorem same_exec {c : Code Nat} {σ σ' : St Nat} (h : Exec ram fp c σ σ') {τ : St Nat}
    (hr : ∀ x, x ∈ c.regs → τ.reg x = σ.reg x) (hm : τ.mem = σ.mem) :
    ∃ τ', Exec ram fp c τ τ' ∧ τ'.mem = σ'.mem ∧ ∀ x, x ∈ c.regs → τ'.reg x = σ'.reg x := by
  obtain ⟨τ', hx, r⟩ := map_ok (f := id) (U := fun x => x ∈ c.regs) ram fp (fun x y _ _ e => e) h (fun _ h => h)
    (τ := τ) ⟨hm, hr⟩
  rw [Code.map_id] at hx
  exact ⟨τ', hx, r.1, r.2⟩

/-- agreement below `m` (the fresh registers are `≥ m`) -/
def RM (m : Nat) (σ τ : St Nat) : Prop := τ.mem = σ.mem ∧ ∀ x, x < m → τ.reg x = σ.reg x

theorem same_RM {m : Nat} {c : Code Nat} {σ σ' : St Nat} (h : Exec ram fp c σ σ') (hc : ∀ x, x ∈ c.regs → x < m)
    {τ : St Nat} (hr : RM m σ τ) : ∃ τ', Exec ram fp c τ τ' ∧ RM m σ' τ' := by
  obtain ⟨τ', hx, hm, hr'⟩ := same_exec h (fun x hx => hr.2 x (hc x hx)) hr.1
  refine ⟨τ', hx, hm, fun x hx' => ?_⟩
  by_cases hxc : x ∈ c.regs
  · exact hr' x hxc
  · rw [wrs_exec hx fun e => hxc (wrs_regs e), wrs_exec h fun e => hxc (wrs_regs e)]; exact hr.2 x hx'

theorem arg_eq {a : Arg Nat} {σ τ : Regs Nat} (h : ∀ x, x ∈ a.regs → τ x = σ x) : a.eval τ = a.eval σ := by
  cases a with
  | r x => exact h x (List.mem_singleton.2 rfl)
  | i _ => rfl

theorem tst_eq {t : Tst Nat} {σ τ : Regs Nat} (h : ∀ x, x ∈ t.regs → τ x = σ x) : t.eval τ = t.eval σ := by
  unfold Tst.eval
  rw [arg_eq fun x hx => h x (List.mem_append_left _ hx), arg_eq fun x hx => h x (List.mem_append_right _ hx)]

/-! ## Copy propagation (same states; facts `a = b` between registers) -/

/-- known copies `(a, b)`: `reg a = reg b` -/
abbrev Cp := List (Nat × Nat)

def CpOK (K : Cp) (σ : Regs Nat) : Prop := ∀ a b, (a, b) ∈ K → σ a = σ b

def look : Cp → Nat → Nat
  | [], x => x
  | (a, b) :: K, x => if a = x then b else look K x

theorem look_ok : ∀ {K : Cp} {σ : Regs Nat}, CpOK K σ → ∀ x, σ (look K x) = σ x
  | [], _, _, _ => rfl
  | (a, b) :: K, σ, h, x => by
    unfold look
    by_cases e : a = x
    · rw [if_pos e, ← e]; exact (h a b (List.mem_cons_self ..)).symm
    · rw [if_neg e]; exact look_ok (fun a b hm => h a b (List.mem_cons_of_mem _ hm)) x

def cpA (K : Cp) : Arg Nat → Arg Nat
  | .r x => .r (look K x)
  | .i c => .i c

theorem cpA_eval {K : Cp} {σ : Regs Nat} (h : CpOK K σ) (a : Arg Nat) : (cpA K a).eval σ = a.eval σ := by
  cases a with
  | r x => exact look_ok h x
  | i _ => rfl

/-- the uses of `set`, `bin`, `lbu`, `sb` renamed through the known copies -/
def cpI (K : Cp) : Ins Nat → Ins Nat
  | .set d a => .set d (cpA K a)
  | .bin op d a b => .bin op d (cpA K a) (cpA K b)
  | .mop m d a b => .mop m d (cpA K a) (cpA K b)
  | .lbu d a off => .lbu d (cpA K a) off
  | .sb v a off => .sb (cpA K v) (cpA K a) off
  | i => i

def kill (K : Cp) (d : Nat) : Cp := K.filter fun p => !decide (p.1 = d) && !decide (p.2 = d)

/-- facts after an instruction -/
def after (K : Cp) : Ins Nat → Cp
  | .set d (.r a) => if a = d then kill K d else (d, a) :: kill K d
  | i => match i.dst with
    | some d => kill K d
    | none => K

def cp (K : Cp) : Code Nat → Code Nat × Cp
  | .skip => (.skip, K)
  | .ins i => (.ins (cpI K i), after K (cpI K i))
  | .seq a b => let A := cp K a; let B := cp A.2 b; (.seq A.1 B.1, B.2)
  | .when t b => (.when t (cp K b).1, [])
  | .loop p t b => (.loop (cp [] p).1 t (cp [] b).1, [])
  | .loop2 p₁ t₁ p₂ t₂ b => (.loop2 (cp [] p₁).1 t₁ (cp [] p₂).1 t₂ (cp [] b).1, [])

theorem kill_ok {K : Cp} {σ : Regs Nat} (h : CpOK K σ) (d : Nat) (v : BitVec 64) : CpOK (kill K d) (upd σ d v) := by
  intro a b hm
  simp only [kill, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hm
  rw [upd_ne _ _ hm.2.1, upd_ne _ _ hm.2.2]; exact h a b hm.1

theorem after_upd {K : Cp} {σ : Regs Nat} (h : CpOK K σ) (i : Ins Nat) (d : Nat) (hd : i.dst = some d)
    (v : BitVec 64) (hv : ∀ a, i = .set d (.r a) → v = σ a) : CpOK (after K i) (upd σ d v) := by
  cases i with
  | set d' a =>
    obtain rfl : d' = d := Option.some.inj hd
    cases a with
    | r a =>
      simp only [after]
      by_cases e : a = d'
      · rw [if_pos e]; exact kill_ok h _ _
      · rw [if_neg e]
        intro x y hm
        rcases List.mem_cons.1 hm with hm | hm
        · cases hm; rw [upd_eq, upd_ne _ _ e]; exact hv a rfl
        · exact kill_ok h _ _ x y hm
    | i _ => exact kill_ok h _ _
  | bin => cases hd; exact kill_ok h _ _
  | mop => cases hd; exact kill_ok h _ _
  | lbu => cases hd; exact kill_ok h _ _
  | ldS => cases hd; exact kill_ok h _ _
  | ld => cases hd; exact kill_ok h _ _
  | sb => cases hd
  | stS => cases hd
  | sd => cases hd

theorem cp_nil {σ : Regs Nat} : CpOK [] σ := fun _ _ h => by cases h

/-- copy propagation keeps the execution (same states) -/
theorem cp_ok : ∀ {c : Code Nat} {σ σ' : St Nat}, Exec ram fp c σ σ' → ∀ {K : Cp}, CpOK K σ.reg →
    Exec ram fp (cp K c).1 σ σ' ∧ CpOK (cp K c).2 σ'.reg := by
  intro c σ σ' h
  induction h with
  | skip => exact fun h => ⟨.skip, h⟩
  | @ins i s s' hst =>
    intro K hK
    show Exec ram fp (.ins (cpI K i)) s s' ∧ CpOK (after K (cpI K i)) s'.reg
    cases hst with
    | @set d a =>
      refine ⟨?_, after_upd hK (cpI K _) d rfl _ fun a' e => ?_⟩
      · show Exec ram fp (.ins (.set d (cpA K a))) _ _
        have := Exec.ins (ram := ram) (fp := fp) (Step.set (d := d) (a := cpA K a) (s := s))
        rwa [cpA_eval hK] at this
      · cases a with
        | r x => simp only [cpI, cpA, Ins.set.injEq, Arg.r.injEq] at e; rw [← e.2, look_ok hK]; rfl
        | i _ => simp [cpI, cpA] at e
    | @bin op d a b =>
      refine ⟨?_, after_upd hK (cpI K _) d rfl _ fun a' e => by simp [cpI] at e⟩
      show Exec ram fp (.ins (.bin op d (cpA K a) (cpA K b))) _ _
      have := Exec.ins (ram := ram) (fp := fp) (Step.bin (op := op) (d := d) (a := cpA K a) (b := cpA K b) (s := s))
      rwa [cpA_eval hK, cpA_eval hK] at this
    | @mop m d a b =>
      refine ⟨?_, after_upd hK (cpI K _) d rfl _ fun a' e => by simp [cpI] at e⟩
      show Exec ram fp (.ins (.mop m d (cpA K a) (cpA K b))) _ _
      have := Exec.ins (ram := ram) (fp := fp) (Step.mop (m := m) (d := d) (a := cpA K a) (b := cpA K b) (s := s))
      rwa [cpA_eval hK, cpA_eval hK] at this
    | @lbu d a off _ v hr hv =>
      refine ⟨?_, after_upd hK (cpI K _) d rfl _ fun a' e => by simp [cpI] at e⟩
      show Exec ram fp (.ins (.lbu d (cpA K a) off)) _ _
      exact .ins (.lbu (v := v) (by rw [cpA_eval hK]; exact hr) (by rw [cpA_eval hK]; exact hv))
    | @sb v a off _ hr =>
      refine ⟨?_, by exact hK⟩
      show Exec ram fp (.ins (.sb (cpA K v) (cpA K a) off)) _ _
      have := Exec.ins (ram := ram) (fp := fp) (Step.sb (v := cpA K v) (a := cpA K a) (off := off) (s := s)
        (by rw [cpA_eval hK]; exact hr))
      rwa [cpA_eval hK, cpA_eval hK] at this
    | @ldS d j _ v h1 h2 h3 => exact ⟨.ins (.ldS h1 h2 h3), after_upd hK (cpI K _) d rfl _ fun a' e => by simp [cpI] at e⟩
    | stS h1 h2 => exact ⟨.ins (.stS h1 h2), hK⟩
    | @ld d a off _ v h1 h2 h3 => exact ⟨.ins (.ld h1 h2 h3), after_upd hK (cpI K _) d rfl _ fun a' e => by simp [cpI] at e⟩
    | sd h1 h2 => exact ⟨.ins (.sd h1 h2), hK⟩
  | seq _ _ iha ihb =>
    intro K hK
    obtain ⟨x₁, k₁⟩ := iha hK
    obtain ⟨x₂, k₂⟩ := ihb k₁
    exact ⟨.seq x₁ x₂, k₂⟩
  | whenT ht _ ih => intro K hK; exact ⟨.whenT ht (ih hK).1, cp_nil⟩
  | whenF ht => intro K hK; exact ⟨.whenF ht, cp_nil⟩
  | loopF _ ht ihp => intro K _; exact ⟨.loopF (ihp cp_nil).1 ht, cp_nil⟩
  | loopT _ ht _ _ ihp ihb ihl =>
    intro K hK
    exact ⟨.loopT (ihp cp_nil).1 ht (ihb cp_nil).1 (ihl (K := []) cp_nil).1,
      cp_nil⟩
  | loop2A _ ht ih₁ => intro K _; exact ⟨.loop2A (ih₁ cp_nil).1 ht, cp_nil⟩
  | loop2B _ ht₁ _ ht₂ ih₁ ih₂ =>
    intro K _
    exact ⟨.loop2B (ih₁ cp_nil).1 ht₁ (ih₂ cp_nil).1 ht₂, cp_nil⟩
  | loop2T _ ht₁ _ ht₂ _ _ ih₁ ih₂ ihb ihl =>
    intro K hK
    exact ⟨.loop2T (ih₁ cp_nil).1 ht₁ (ih₂ cp_nil).1 ht₂
      (ihb cp_nil).1 (ihl (K := []) cp_nil).1, cp_nil⟩

/-! ## Dead-code elimination (liveness as in `chk`, loop invariants checked) -/

/-- the destination of a droppable instruction -/
def dropD : Ins Nat → Option Nat
  | .set d _ => some d
  | .bin _ d _ _ => some d
  | _ => none

/-- the code without dead `set`/`bin`, and the registers live before it; `none` if a loop invariant fails -/
def dce : Code Nat → List Nat → Option (Code Nat × List Nat)
  | .skip, L => some (.skip, L)
  | .ins i, L =>
    match dropD i with
    | some d => if L.contains d then some (.ins i, lvIns i L) else some (.skip, L)
    | none => some (.ins i, lvIns i L)
  | .seq a b, L =>
    match dce b L with
    | none => none
    | some (b', Lb) =>
      match dce a Lb with
      | none => none
      | some (a', La) => some (.seq a' b', La)
  | .when t b, L =>
    match dce b L with
    | none => none
    | some (b', Lb) => some (.when t b', t.regs ++ lunion Lb L)
  | .loop p t b, L =>
    let I := lvIter (lv p) (lv b) L t.regs 10 L
    match dce b I with
    | none => none
    | some (b', Lb) =>
      match dce p (t.regs ++ lunion Lb L) with
      | none => none
      | some (p', I') => if subL I' I then some (.loop p' t b', I) else none
  | .loop2 p₁ t₁ p₂ t₂ b, L =>
    let I := lvIter2 (lv p₁) (lv p₂) (lv b) L t₁.regs t₂.regs 10 L
    match dce b I with
    | none => none
    | some (b', Lb) =>
      match dce p₂ (t₂.regs ++ lunion Lb L) with
      | none => none
      | some (p₂', L₂) =>
        match dce p₁ (t₁.regs ++ lunion L₂ L) with
        | none => none
        | some (p₁', I') => if subL I' I then some (.loop2 p₁' t₁ p₂' t₂ b', I) else none

theorem defOK_id (d : Nat) (mv : Option Nat) (L : List Nat) : defOK id d mv L = true :=
  List.all_eq_true.2 fun x _ => by by_cases h : x = d <;> simp [h]

theorem keep_ins {i : Ins Nat} {σ σ' : St Nat} (hst : Step ram fp i σ σ') {L : List Nat} {τ : St Nat}
    (hr : Ren id (· ∈ lvIns i L) σ τ) : ∃ τ', Exec ram fp (.ins i) τ τ' ∧ Ren id (· ∈ L) σ' τ' := by
  have hc : chk id (.ins i) L = some (lvIns i L) := by
    simp only [chk]; split <;> simp [defOK_id]
  obtain ⟨τ', hx, r⟩ := chk_ok ram fp (.ins hst) hc hr
  rw [Code.map_id] at hx; exact ⟨τ', hx, r⟩

theorem tst_id {t : Tst Nat} {σ τ : St Nat} {U : Nat → Prop} (hr : Ren id U σ τ) (ht : ∀ x, x ∈ t.regs → U x) :
    t.eval τ.reg = t.eval σ.reg := by
  have := hr.tst ht; rwa [Tst.map_id] at this

/-- **dead-code elimination preserves executions**, agreeing on the live registers -/
theorem dce_ok : ∀ {c : Code Nat} {σ σ' : St Nat}, Exec ram fp c σ σ' →
    ∀ {L Lin : List Nat} {c' : Code Nat}, dce c L = some (c', Lin) → ∀ {τ : St Nat}, Ren id (· ∈ Lin) σ τ →
    ∃ τ', Exec ram fp c' τ τ' ∧ Ren id (· ∈ L) σ' τ' := by
  intro c σ σ' h
  induction h with
  | skip =>
    intro L Lin c' hc τ hr
    simp only [dce, Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
    exact ⟨τ, .skip, hr⟩
  | @ins i s s' hst =>
    intro L Lin c' hc τ hr
    unfold dce at hc
    cases hdd : dropD i with
    | none =>
      rw [hdd] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
      exact keep_ins hst hr
    | some d =>
      rw [hdd] at hc; dsimp only at hc
      by_cases hL : L.contains d = true
      · rw [if_pos hL] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
        exact keep_ins hst hr
      · rw [if_neg hL] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
        have hdL : d ∉ L := fun e => hL (List.contains_iff_mem.2 e)
        refine ⟨τ, .skip, ?_⟩
        cases hst <;> simp only [dropD, Option.some.injEq, reduceCtorEq] at hdd
        all_goals subst hdd
        all_goals exact ⟨hr.1, fun x hx => (hr.2 x hx).trans (upd_ne _ _ fun e => hdL (by rwa [e] at hx)).symm⟩
  | seq _ _ iha ihb =>
    intro L Lin c' hc τ hr
    unfold dce at hc
    cases hb : dce _ L with
    | none => rw [hb] at hc; exact nomatch hc
    | some r =>
      obtain ⟨b', Lb⟩ := r
      rw [hb] at hc; dsimp only at hc
      cases ha : dce _ Lb with
      | none => rw [ha] at hc; exact nomatch hc
      | some r =>
        obtain ⟨a', La⟩ := r
        rw [ha] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
        obtain ⟨τ₁, x₁, r₁⟩ := iha ha hr
        obtain ⟨τ₂, x₂, r₂⟩ := ihb hb r₁
        exact ⟨τ₂, .seq x₁ x₂, r₂⟩
  | @whenT t body s s' ht _ ih =>
    intro L Lin c' hc τ hr
    unfold dce at hc
    cases hb : dce body L with
    | none => rw [hb] at hc; exact nomatch hc
    | some r =>
      obtain ⟨b', Lb⟩ := r
      rw [hb] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨τ₁, x₁, r₁⟩ := ih hb (hr.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inl hx)))
      exact ⟨τ₁, .whenT ((tst_id hr fun x hx => List.mem_append_left _ hx).trans ht) x₁, r₁⟩
  | @whenF t body s ht =>
    intro L Lin c' hc τ hr
    unfold dce at hc
    cases hb : dce body L with
    | none => rw [hb] at hc; exact nomatch hc
    | some r =>
      obtain ⟨b', Lb⟩ := r
      rw [hb] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
      exact ⟨τ, .whenF ((tst_id hr fun x hx => List.mem_append_left _ hx).trans ht),
        hr.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inr hx))⟩
  | @loopF pre t body s s₁ _ ht ihp =>
    intro L Lin c' hc τ hr
    unfold dce at hc
    generalize lvIter (lv pre) (lv body) L t.regs 10 L = I at hc
    dsimp only at hc
    cases hb : dce body I with
    | none => rw [hb] at hc; exact nomatch hc
    | some r =>
      obtain ⟨b', Lb⟩ := r
      rw [hb] at hc; dsimp only at hc
      cases hp : dce pre (t.regs ++ lunion Lb L) with
      | none => rw [hp] at hc; exact nomatch hc
      | some r =>
        obtain ⟨p', I'⟩ := r
        rw [hp] at hc; dsimp only at hc
        by_cases hs : subL I' I = true
        · rw [if_pos hs] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
          obtain ⟨τ₁, x₁, r₁⟩ := ihp hp (hr.sub fun x hx => subL_ok hs hx)
          exact ⟨τ₁, .loopF x₁ ((tst_id r₁ fun x hx => List.mem_append_left _ hx).trans ht),
            r₁.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inr hx))⟩
        · rw [if_neg hs] at hc; exact nomatch hc
  | @loopT pre t body s s₁ s₂ s₃ _ ht _ _ ihp ihb ihl =>
    intro L Lin c' hc τ hr
    have hc0 := hc
    unfold dce at hc
    generalize lvIter (lv pre) (lv body) L t.regs 10 L = I at hc
    dsimp only at hc
    cases hb : dce body I with
    | none => rw [hb] at hc; exact nomatch hc
    | some r =>
      obtain ⟨b', Lb⟩ := r
      rw [hb] at hc; dsimp only at hc
      cases hp : dce pre (t.regs ++ lunion Lb L) with
      | none => rw [hp] at hc; exact nomatch hc
      | some r =>
        obtain ⟨p', I'⟩ := r
        rw [hp] at hc; dsimp only at hc
        by_cases hs : subL I' I = true
        · rw [if_pos hs] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
          obtain ⟨τ₁, x₁, r₁⟩ := ihp hp (hr.sub fun x hx => subL_ok hs hx)
          obtain ⟨τ₂, x₂, r₂⟩ := ihb hb (r₁.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inl hx)))
          obtain ⟨τ₃, x₃, r₃⟩ := ihl hc0 r₂
          exact ⟨τ₃, .loopT x₁ ((tst_id r₁ fun x hx => List.mem_append_left _ hx).trans ht) x₂ x₃, r₃⟩
        · rw [if_neg hs] at hc; exact nomatch hc
  | @loop2A p₁ t₁ p₂ t₂ body s s₁ _ ht ih₁ =>
    intro L Lin c' hc τ hr
    unfold dce at hc
    generalize lvIter2 (lv p₁) (lv p₂) (lv body) L t₁.regs t₂.regs 10 L = I at hc
    dsimp only at hc
    cases hb : dce body I with
    | none => rw [hb] at hc; exact nomatch hc
    | some r =>
      obtain ⟨b', Lb⟩ := r
      rw [hb] at hc; dsimp only at hc
      cases hp₂ : dce p₂ (t₂.regs ++ lunion Lb L) with
      | none => rw [hp₂] at hc; exact nomatch hc
      | some r =>
        obtain ⟨p₂', L₂⟩ := r
        rw [hp₂] at hc; dsimp only at hc
        cases hp₁ : dce p₁ (t₁.regs ++ lunion L₂ L) with
        | none => rw [hp₁] at hc; exact nomatch hc
        | some r =>
          obtain ⟨p₁', I'⟩ := r
          rw [hp₁] at hc; dsimp only at hc
          by_cases hs : subL I' I = true
          · rw [if_pos hs] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
            obtain ⟨τ₁, x₁, r₁⟩ := ih₁ hp₁ (hr.sub fun x hx => subL_ok hs hx)
            exact ⟨τ₁, .loop2A x₁ ((tst_id r₁ fun x hx => List.mem_append_left _ hx).trans ht),
              r₁.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inr hx))⟩
          · rw [if_neg hs] at hc; exact nomatch hc
  | @loop2B p₁ t₁ p₂ t₂ body s s₁ s₂ _ ht₁ _ ht₂ ih₁ ih₂ =>
    intro L Lin c' hc τ hr
    unfold dce at hc
    generalize lvIter2 (lv p₁) (lv p₂) (lv body) L t₁.regs t₂.regs 10 L = I at hc
    dsimp only at hc
    cases hb : dce body I with
    | none => rw [hb] at hc; exact nomatch hc
    | some r =>
      obtain ⟨b', Lb⟩ := r
      rw [hb] at hc; dsimp only at hc
      cases hp₂ : dce p₂ (t₂.regs ++ lunion Lb L) with
      | none => rw [hp₂] at hc; exact nomatch hc
      | some r =>
        obtain ⟨p₂', L₂⟩ := r
        rw [hp₂] at hc; dsimp only at hc
        cases hp₁ : dce p₁ (t₁.regs ++ lunion L₂ L) with
        | none => rw [hp₁] at hc; exact nomatch hc
        | some r =>
          obtain ⟨p₁', I'⟩ := r
          rw [hp₁] at hc; dsimp only at hc
          by_cases hs : subL I' I = true
          · rw [if_pos hs] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
            obtain ⟨τ₁, x₁, r₁⟩ := ih₁ hp₁ (hr.sub fun x hx => subL_ok hs hx)
            obtain ⟨τ₂, x₂, r₂⟩ := ih₂ hp₂ (r₁.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inl hx)))
            exact ⟨τ₂, .loop2B x₁ ((tst_id r₁ fun x hx => List.mem_append_left _ hx).trans ht₁) x₂
              ((tst_id r₂ fun x hx => List.mem_append_left _ hx).trans ht₂),
              r₂.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inr hx))⟩
          · rw [if_neg hs] at hc; exact nomatch hc
  | @loop2T p₁ t₁ p₂ t₂ body s s₁ s₂ s₃ s₄ _ ht₁ _ ht₂ _ _ ih₁ ih₂ ihb ihl =>
    intro L Lin c' hc τ hr
    have hc0 := hc
    unfold dce at hc
    generalize lvIter2 (lv p₁) (lv p₂) (lv body) L t₁.regs t₂.regs 10 L = I at hc
    dsimp only at hc
    cases hb : dce body I with
    | none => rw [hb] at hc; exact nomatch hc
    | some r =>
      obtain ⟨b', Lb⟩ := r
      rw [hb] at hc; dsimp only at hc
      cases hp₂ : dce p₂ (t₂.regs ++ lunion Lb L) with
      | none => rw [hp₂] at hc; exact nomatch hc
      | some r =>
        obtain ⟨p₂', L₂⟩ := r
        rw [hp₂] at hc; dsimp only at hc
        cases hp₁ : dce p₁ (t₁.regs ++ lunion L₂ L) with
        | none => rw [hp₁] at hc; exact nomatch hc
        | some r =>
          obtain ⟨p₁', I'⟩ := r
          rw [hp₁] at hc; dsimp only at hc
          by_cases hs : subL I' I = true
          · rw [if_pos hs] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
            obtain ⟨τ₁, x₁, r₁⟩ := ih₁ hp₁ (hr.sub fun x hx => subL_ok hs hx)
            obtain ⟨τ₂, x₂, r₂⟩ := ih₂ hp₂ (r₁.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inl hx)))
            obtain ⟨τ₃, x₃, r₃⟩ := ihb hb (r₂.sub fun x hx => List.mem_append_right _ (mem_lunion.2 (.inl hx)))
            obtain ⟨τ₄, x₄, r₄⟩ := ihl hc0 r₃
            exact ⟨τ₄, .loop2T x₁ ((tst_id r₁ fun x hx => List.mem_append_left _ hx).trans ht₁) x₂
              ((tst_id r₂ fun x hx => List.mem_append_left _ hx).trans ht₂) x₃ x₄, r₄⟩
          · rw [if_neg hs] at hc; exact nomatch hc

/-! ## Strength reduction of one loop -/

def fnd : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (b, p) :: l, a => if b = a then some p else fnd l a

theorem fnd_mem : ∀ {l : List (Nat × Nat)} {a p : Nat}, fnd l a = some p → (a, p) ∈ l
  | [], _, _, h => nomatch h
  | (b, q) :: l, a, p, h => by
    unfold fnd at h
    by_cases e : b = a
    · rw [if_pos e] at h; cases h; rw [e]; exact List.mem_cons_self ..
    · rw [if_neg e] at h; exact List.mem_cons_of_mem _ (fnd_mem h)

/-- `(d, b)` of an address sum `d := b + i` or `d := i + b` -/
def addrOf (i : Nat) : Ins Nat → Option (Nat × Nat)
  | .bin .add d (.r a) (.r b) =>
    if b = i ∧ a ≠ i ∧ d ≠ i then some (d, a) else if a = i ∧ b ≠ i ∧ d ≠ i then some (d, b) else none
  | _ => none

theorem addrOf_spec {i : Nat} {x : Ins Nat} {d a : Nat} (h : addrOf i x = some (d, a)) :
    d ≠ i ∧ (x = .bin .add d (.r a) (.r i) ∨ x = .bin .add d (.r i) (.r a)) := by
  unfold addrOf at h
  split at h
  · rename_i d' a' b'
    by_cases h1 : b' = i ∧ a' ≠ i ∧ d' ≠ i
    · rw [if_pos h1] at h; cases h; obtain ⟨rfl, -, h3⟩ := h1; exact ⟨h3, .inl rfl⟩
    · rw [if_neg h1] at h
      by_cases h2 : a' = i ∧ b' ≠ i ∧ d' ≠ i
      · rw [if_pos h2] at h; cases h; obtain ⟨rfl, -, h3⟩ := h2; exact ⟨h3, .inr rfl⟩
      · rw [if_neg h2] at h; exact nomatch h
  · exact nomatch h

def isInc (i : Nat) : Ins Nat → Bool
  | .bin .add d (.r a) (.i c) => decide (d = i) && decide (a = i) && decide (c = 1)
  | _ => false

theorem isInc_spec {i : Nat} {x : Ins Nat} (h : isInc i x = true) : x = .bin .add i (.r i) (.i 1) := by
  unfold isInc at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; rfl
  · exact nomatch h

/-- `p := p + 1` for every pointer -/
def incs : List (Nat × Nat) → Code Nat
  | [] => .skip
  | (_, p) :: l => .seq (.ins (.bin .add p (.r p) (.i 1))) (incs l)

/-- `p := b + i` for every base -/
def inits (i : Nat) : List (Nat × Nat) → Code Nat
  | [] => .skip
  | (b, p) :: l => .seq (.ins (.bin .add p (.r b) (.r i))) (inits i l)

theorem incs_exec : ∀ {PB : List (Nat × Nat)}, (PB.map Prod.snd).Nodup → ∀ τ : St Nat,
    ∃ τ', Exec ram fp (incs PB) τ τ' ∧ τ'.mem = τ.mem ∧ (∀ y, y ∉ PB.map Prod.snd → τ'.reg y = τ.reg y) ∧
      ∀ b p, (b, p) ∈ PB → τ'.reg p = τ.reg p + 1
  | [], _, τ => ⟨τ, .skip, rfl, fun _ _ => rfl, fun _ _ h => nomatch h⟩
  | (b, p) :: l, hnd, τ => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨τ', hx, hm, hy, hp⟩ := incs_exec hnd.2 ⟨upd τ.reg p (τ.reg p + 1), τ.mem⟩
    refine ⟨τ', .seq (.ins .bin) hx, hm, fun y hy' => ?_, fun b' p' hm' => ?_⟩
    · simp only [List.map_cons, List.mem_cons, not_or] at hy'
      rw [hy y hy'.2]; exact upd_ne _ _ hy'.1
    · rcases List.mem_cons.1 hm' with e | e
      · cases e; rw [hy p hnd.1]; exact upd_eq _ _ _
      · have hpl : p' ∈ l.map Prod.snd := List.mem_map.2 ⟨_, e, rfl⟩
        rw [hp b' p' e]
        exact congrArg (· + 1) (upd_ne _ _ fun e' => hnd.1 (e' ▸ hpl))

theorem inits_exec {i k : Nat} (hi : i < k) : ∀ {PB : List (Nat × Nat)}, (PB.map Prod.snd).Nodup →
    (∀ b p, (b, p) ∈ PB → b < k ∧ k ≤ p) → ∀ τ : St Nat,
    ∃ τ', Exec ram fp (inits i PB) τ τ' ∧ τ'.mem = τ.mem ∧ (∀ y, y ∉ PB.map Prod.snd → τ'.reg y = τ.reg y) ∧
      ∀ b p, (b, p) ∈ PB → τ'.reg p = τ.reg b + τ.reg i
  | [], _, _, τ => ⟨τ, .skip, rfl, fun _ _ => rfl, fun _ _ h => nomatch h⟩
  | (b, p) :: l, hnd, hlo, τ => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hbp := hlo b p (List.mem_cons_self ..)
    obtain ⟨τ', hx, hm, hy, hp⟩ := inits_exec hi hnd.2 (fun b p h => hlo b p (List.mem_cons_of_mem _ h))
      ⟨upd τ.reg p (τ.reg b + τ.reg i), τ.mem⟩
    refine ⟨τ', .seq (.ins .bin) hx, hm, fun y hy' => ?_, fun b' p' hm' => ?_⟩
    · simp only [List.map_cons, List.mem_cons, not_or] at hy'
      rw [hy y hy'.2]; exact upd_ne _ _ hy'.1
    · rcases List.mem_cons.1 hm' with e | e
      · cases e; rw [hy p hnd.1]; exact upd_eq _ _ _
      · have h' := hlo b' p' (List.mem_cons_of_mem _ e)
        rw [hp b' p' e]
        show upd τ.reg p _ b' + upd τ.reg p _ i = _
        rw [upd_ne _ _ (by omega), upd_ne _ _ (by omega)]

/-- the loop body with the index uses replaced -/
def rwI (i : Nat) (PB : List (Nat × Nat)) (x : Ins Nat) : Option (Code Nat) :=
  if x.regs.contains i then
    match addrOf i x with
    | some (d, a) => (fnd PB a).map fun p => .ins (.set d (.r p))
    | none => if isInc i x then some (incs PB) else none
  else some (.ins x)

def rwC (i : Nat) (PB : List (Nat × Nat)) : Code Nat → Option (Code Nat)
  | .skip => some .skip
  | .ins x => rwI i PB x
  | .seq a b =>
    match rwC i PB a, rwC i PB b with
    | some a', some b' => some (.seq a' b')
    | _, _ => none
  | .when t b => if t.regs.contains i then none else (rwC i PB b).map (.when t)
  | .loop p t b =>
    if t.regs.contains i then none else
    match rwC i PB p, rwC i PB b with
    | some p', some b' => some (.loop p' t b')
    | _, _ => none
  | .loop2 .. => none

/-- the bases `b` of the address sums `b + i` -/
def bases (i : Nat) : Code Nat → List Nat
  | .ins x => match addrOf i x with | some (_, a) => [a] | none => []
  | .seq a b => bases i a ++ bases i b
  | .when _ b => bases i b
  | .loop p _ b => bases i p ++ bases i b
  | _ => []

/-- `i` is incremented at most once (and not written otherwise) -/
def inc1 (i : Nat) : Code Nat → Bool
  | .ins x => match x.dst with | some d => !decide (d = i) || isInc i x | none => true
  | .seq a b => (inc1 i a && !(wrs b).contains i) || (!(wrs a).contains i && inc1 i b)
  | .when _ b => inc1 i b
  | c => !(wrs c).contains i

theorem nw_exec {c : Code Nat} {σ σ' : St Nat} (h : Exec ram fp c σ σ') {x : Nat} (hx : (wrs c).contains x = false) :
    σ'.reg x = σ.reg x :=
  wrs_exec h fun e => by rw [List.contains_iff_mem.2 e] at hx; exact nomatch hx

theorem inc1_ok {i : Nat} : ∀ {c : Code Nat} {σ σ' : St Nat}, Exec ram fp c σ σ' → inc1 i c = true →
    σ'.reg i = σ.reg i ∨ σ'.reg i = σ.reg i + 1 := by
  intro c σ σ' h
  induction h with
  | skip => exact fun _ => .inl rfl
  | @ins x s s' hst =>
    intro hc
    unfold inc1 at hc
    cases hd : x.dst with
    | none => exact .inl (wrs_exec (.ins hst) (by simp [wrs, hd]))
    | some d =>
      rw [hd] at hc
      by_cases e : d = i
      · rw [e] at hc; simp only [decide_true, Bool.not_true, Bool.false_or] at hc
        have := isInc_spec hc; subst this
        cases hst; right; exact upd_eq _ _ _
      · exact .inl (wrs_exec (.ins hst) (by simp [wrs, hd]; exact fun e' => e e'.symm))
  | seq ha hb iha ihb =>
    intro hc
    unfold inc1 at hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [nw_exec hb h2]; exact iha h1
    · rw [← nw_exec ha h1]; exact ihb h2
  | whenT _ _ ih => exact ih
  | whenF _ => exact fun _ => .inl rfl
  | loopF hp ht ihp =>
    intro hc; unfold inc1 at hc; simp only [Bool.not_eq_true'] at hc
    exact .inl (nw_exec (.loopF hp ht) hc)
  | loopT hp ht hb hl =>
    intro hc; unfold inc1 at hc; simp only [Bool.not_eq_true'] at hc
    exact .inl (nw_exec (.loopT hp ht hb hl) hc)
  | loop2A h1 ht =>
    intro hc; unfold inc1 at hc; simp only [Bool.not_eq_true'] at hc
    exact .inl (nw_exec (.loop2A h1 ht) hc)
  | loop2B h1 ht₁ h2 ht₂ =>
    intro hc; unfold inc1 at hc; simp only [Bool.not_eq_true'] at hc
    exact .inl (nw_exec (.loop2B h1 ht₁ h2 ht₂) hc)
  | loop2T h1 ht₁ h2 ht₂ hb hl =>
    intro hc; unfold inc1 at hc; simp only [Bool.not_eq_true'] at hc
    exact .inl (nw_exec (.loop2T h1 ht₁ h2 ht₂ hb hl) hc)

/-- loop-head code that does nothing -/
def triv : Code Nat → Bool
  | .skip => true
  | .seq a b => triv a && triv b
  | _ => false

theorem triv_exec : ∀ {c : Code Nat} {σ σ' : St Nat}, Exec ram fp c σ σ' → triv c = true → σ' = σ := by
  intro c σ σ' h
  induction h with
  | skip => exact fun _ => rfl
  | seq _ _ iha ihb =>
    intro hc; simp only [triv, Bool.and_eq_true] at hc; rw [ihb hc.2, iha hc.1]
  | _ => intro hc; simp [triv] at hc

theorem triv_run : ∀ {c : Code Nat}, triv c = true → ∀ τ : St Nat, Exec ram fp c τ τ
  | .skip, _, τ => .skip
  | .seq a b, h, τ => by
    simp only [triv, Bool.and_eq_true] at h; exact .seq (triv_run h.1 τ) (triv_run h.2 τ)
  | .ins _, h, _ => nomatch h
  | .when .., h, _ => nomatch h
  | .loop .., h, _ => nomatch h
  | .loop2 .., h, _ => nomatch h

/-- pointer registers `k, k + 1, …` for the bases -/
def mkPB : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | k, b :: l => (b, k) :: mkPB (k + 1) l

/-- the side conditions of one reduced loop (`e = m`, pointers `≥ m + 1`) -/
structure Side (m i : Nat) (n : Arg Nat) (b₀ : Nat) (PB : List (Nat × Nat)) : Prop where
  ptr : ∀ b p, (b, p) ∈ PB → b < m ∧ m + 1 ≤ p ∧ b ≠ i
  nd : (PB.map Prod.snd).Nodup
  nreg : ∀ y, y ∈ n.regs → y < m ∧ y ≠ i
  ilt : i < m
  b0 : b₀ < m ∧ b₀ ≠ i
  hb0 : (b₀, m + 1) ∈ PB

/-- the checked conditions -/
def okL (m i : Nat) (n : Arg Nat) (b₀ : Nat) (PB : List (Nat × Nat)) (body : Code Nat) : Bool :=
  PB.all (fun q => decide (q.1 < m) && decide (m + 1 ≤ q.2) && !decide (q.1 = i)) &&
  decide (PB.map Prod.snd).Nodup && n.regs.all (fun y => decide (y < m) && !decide (y = i)) &&
  decide (i < m) && decide (b₀ < m) && !decide (b₀ = i) && PB.contains (b₀, m + 1) &&
  (b₀ :: (PB.map Prod.fst ++ n.regs)).all fun y => !(wrs body).contains y

theorem okL_side {m i : Nat} {n : Arg Nat} {b₀ : Nat} {PB : List (Nat × Nat)} {body : Code Nat}
    (h : okL m i n b₀ PB body = true) :
    Side m i n b₀ PB ∧ ∀ y, y ∈ b₀ :: (PB.map Prod.fst ++ n.regs) → (wrs body).contains y = false := by
  simp only [okL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h9⟩ := h
  refine ⟨⟨fun b p hm => ?_, h2, fun y hy => h3 y hy, h4, ⟨h5, h6⟩, h7⟩, fun y hy => h9 y hy⟩
  have := h1 _ hm; exact ⟨this.1.1, this.1.2, this.2⟩

/-- the invariant of the reduced loop: all registers below `m` but `i` agree, pointers `= b + i`, `e = b₀ + n` -/
structure Inv (m i : Nat) (n : Arg Nat) (b₀ : Nat) (PB : List (Nat × Nat)) (σ τ : St Nat) : Prop where
  mem : τ.mem = σ.mem
  reg : ∀ x, x < m → x ≠ i → τ.reg x = σ.reg x
  ptr : ∀ b p, (b, p) ∈ PB → τ.reg p = σ.reg b + σ.reg i
  lim : τ.reg m = σ.reg b₀ + n.eval σ.reg

/-- the rewritten body simulates the body -/
theorem body_sim {m i : Nat} {n : Arg Nat} {b₀ : Nat} {PB : List (Nat × Nat)} (S : Side m i n b₀ PB) :
    ∀ {c : Code Nat} {σ σ' : St Nat}, Exec ram fp c σ σ' → ∀ {c' : Code Nat}, rwC i PB c = some c' →
    (∀ x, x ∈ c.regs → x < m) → (∀ y, y ∈ b₀ :: (PB.map Prod.fst ++ n.regs) → (wrs c).contains y = false) →
    ∀ {τ : St Nat}, Inv m i n b₀ PB σ τ → ∃ τ', Exec ram fp c' τ τ' ∧ Inv m i n b₀ PB σ' τ' := by
  have hNWb : ∀ b p, (b, p) ∈ PB → b ∈ b₀ :: (PB.map Prod.fst ++ n.regs) := fun b p h =>
    List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨_, h, rfl⟩))
  have hNWn : ∀ y, y ∈ n.regs → y ∈ b₀ :: (PB.map Prod.fst ++ n.regs) := fun y h =>
    List.mem_cons_of_mem _ (List.mem_append_right _ h)
  have hNW0 : b₀ ∈ b₀ :: (PB.map Prod.fst ++ n.regs) := List.mem_cons_self ..
  have hnP : ∀ y, y < m + 1 → y ∉ PB.map Prod.snd := fun y hy h => by
    obtain ⟨⟨b, p⟩, hm, rfl⟩ := List.mem_map.1 h
    have := (S.ptr b p hm).2.1; dsimp only at hy; omega
  intro c σ σ' h
  induction h with
  | skip => intro c' hc _ _ τ hI; cases hc; exact ⟨τ, .skip, hI⟩
  | @ins x s s' hst =>
    intro c' hc hreg hnw τ hI
    have hnwx : ∀ y, y ∈ b₀ :: (PB.map Prod.fst ++ n.regs) → s'.reg y = s.reg y := fun y hy => nw_exec (.ins hst) (hnw y hy)
    have hnarg : n.eval s'.reg = n.eval s.reg := arg_eq fun y hy => hnwx y (hNWn y hy)
    unfold rwC rwI at hc
    by_cases hi : x.regs.contains i = true
    · rw [if_pos hi] at hc
      cases ha : addrOf i x with
      | some da =>
        obtain ⟨d, a⟩ := da
        rw [ha] at hc; dsimp only at hc
        cases hf : fnd PB a with
        | none => rw [hf] at hc; exact nomatch hc
        | some p =>
          rw [hf] at hc; cases hc
          have hap := fnd_mem hf
          obtain ⟨hdi, hx⟩ := addrOf_spec ha
          have hdm : d < m := hreg d (by rcases hx with rfl | rfl <;> simp [Code.regs, Ins.regs])
          have hs' : s' = ⟨upd s.reg d (s.reg a + s.reg i), s.mem⟩ := by
            rcases hx with rfl | rfl <;> cases hst
            · rfl
            · show (⟨upd s.reg d (s.reg i + s.reg a), s.mem⟩ : St Nat) = _; rw [BitVec.add_comm]
          have hval : s'.reg = upd s.reg d (s.reg a + s.reg i) := by rw [hs']
          have hmem : s'.mem = s.mem := by rw [hs']
          refine ⟨_, .ins .set, ⟨hI.mem.trans hmem.symm, fun y hy hyi => ?_, fun b q hm => ?_, ?_⟩⟩
          · show upd τ.reg d (τ.reg p) y = s'.reg y
            rw [hval]
            by_cases e : y = d
            · subst e; rw [upd_eq, upd_eq]; exact hI.ptr a p hap
            · rw [upd_ne _ _ e, upd_ne _ _ e]; exact hI.reg y hy hyi
          · show upd τ.reg d (τ.reg p) q = s'.reg b + s'.reg i
            have := (S.ptr b q hm).2.1
            rw [upd_ne _ _ (by omega), hnwx b (hNWb b q hm), hval, upd_ne _ _ (Ne.symm hdi)]
            exact hI.ptr b q hm
          · show upd τ.reg d (τ.reg p) m = s'.reg b₀ + n.eval s'.reg
            rw [upd_ne _ _ (by omega), hnwx b₀ hNW0, hnarg]; exact hI.lim
      | none =>
        rw [ha] at hc; dsimp only at hc
        by_cases hinc : isInc i x = true
        · rw [if_pos hinc] at hc; cases hc
          have hx := isInc_spec hinc; subst hx
          cases hst
          obtain ⟨τ', hx', hm', hy', hp'⟩ := incs_exec (ram := ram) (fp := fp) S.nd τ
          refine ⟨τ', hx', ⟨hm'.trans hI.mem, fun y hy hyi => ?_, fun b q hm => ?_, ?_⟩⟩
          · rw [hy' y (hnP y (by omega))]; show _ = upd s.reg i _ y; rw [upd_ne _ _ hyi]; exact hI.reg y hy hyi
          · rw [hp' b q hm, hI.ptr b q hm]
            show _ = upd s.reg i _ b + upd s.reg i _ i
            rw [upd_ne _ _ (S.ptr b q hm).2.2, upd_eq, BitVec.add_assoc]; rfl
          · rw [hy' m (hnP m (by omega)), hI.lim]
            show _ = upd s.reg i _ b₀ + n.eval (upd s.reg i _)
            rw [upd_ne _ _ S.b0.2, arg_eq (σ := s.reg) fun y hy => upd_ne _ _ (S.nreg y hy).2]
        · rw [if_neg hinc] at hc; exact nomatch hc
    · rw [if_neg hi] at hc; cases hc
      have hin : i ∉ x.regs := fun e => hi (List.contains_iff_mem.2 e)
      have hreg' : ∀ y, y ∈ (Code.ins x).regs → y < m ∧ y ≠ i := fun y hy => ⟨hreg y hy, fun e => hin (e ▸ hy)⟩
      obtain ⟨τ', hx', hm', hr'⟩ := same_exec (.ins hst) (τ := τ)
        (fun y hy => hI.reg y (hreg' y hy).1 (hreg' y hy).2) hI.mem
      have hout : ∀ y, y ∉ (Code.ins x).regs → τ'.reg y = τ.reg y ∧ s'.reg y = s.reg y := fun y hy =>
        ⟨wrs_exec hx' fun e => hy (wrs_regs e), wrs_exec (.ins hst) fun e => hy (wrs_regs e)⟩
      have hm1 : ∀ y, m ≤ y → y ∉ (Code.ins x).regs := fun y hy e => by have := hreg y e; omega
      refine ⟨τ', hx', ⟨hm', fun y hy hyi => ?_, fun b q hm => ?_, ?_⟩⟩
      · by_cases e : y ∈ (Code.ins x).regs
        · exact hr' y e
        · rw [(hout y e).1, (hout y e).2]; exact hI.reg y hy hyi
      · have := (S.ptr b q hm).2.1
        rw [(hout q (hm1 q (by omega))).1, hI.ptr b q hm, hnwx b (hNWb b q hm), (hout i hin).2]
      · rw [(hout m (hm1 m (Nat.le_refl _))).1, hI.lim, hnwx b₀ hNW0, hnarg]
  | seq _ _ iha ihb =>
    intro c' hc hreg hnw τ hI
    unfold rwC at hc
    cases ha : rwC i PB _ with
    | none => rw [ha] at hc; exact nomatch hc
    | some a' =>
      cases hb : rwC i PB _ with
      | none => rw [ha, hb] at hc; exact nomatch hc
      | some b' =>
        rw [ha, hb] at hc; cases hc
        obtain ⟨τ₁, x₁, r₁⟩ := iha ha (fun x hx => hreg x (List.mem_append_left _ hx))
          (fun y hy => by have := hnw y hy; simp only [wrs, List.contains_append, Bool.or_eq_false_iff] at this; exact this.1) hI
        obtain ⟨τ₂, x₂, r₂⟩ := ihb hb (fun x hx => hreg x (List.mem_append_right _ hx))
          (fun y hy => by have := hnw y hy; simp only [wrs, List.contains_append, Bool.or_eq_false_iff] at this; exact this.2) r₁
        exact ⟨τ₂, .seq x₁ x₂, r₂⟩
  | @whenT t b s s' ht _ ih =>
    intro c' hc hreg hnw τ hI
    unfold rwC at hc
    by_cases hti : t.regs.contains i = true
    · rw [if_pos hti] at hc; exact nomatch hc
    · rw [if_neg hti] at hc
      cases hb : rwC i PB b with
      | none => rw [hb] at hc; exact nomatch hc
      | some b' =>
        rw [hb] at hc; cases hc
        obtain ⟨τ₁, x₁, r₁⟩ := ih hb (fun x hx => hreg x (List.mem_append_right _ hx)) hnw hI
        refine ⟨τ₁, .whenT ?_ x₁, r₁⟩
        rw [tst_eq (σ := s.reg) fun y hy => hI.reg y (hreg y (List.mem_append_left _ hy))
          fun e => hti (List.contains_iff_mem.2 (e ▸ hy))]
        exact ht
  | @whenF t b s ht =>
    intro c' hc hreg hnw τ hI
    unfold rwC at hc
    by_cases hti : t.regs.contains i = true
    · rw [if_pos hti] at hc; exact nomatch hc
    · rw [if_neg hti] at hc
      cases hb : rwC i PB b with
      | none => rw [hb] at hc; exact nomatch hc
      | some b' =>
        rw [hb] at hc; cases hc
        refine ⟨τ, .whenF ?_, hI⟩
        rw [tst_eq (σ := s.reg) fun y hy => hI.reg y (hreg y (List.mem_append_left _ hy))
          fun e => hti (List.contains_iff_mem.2 (e ▸ hy))]
        exact ht
  | @loopF p t b s s₁ _ ht ihp =>
    intro c' hc hreg hnw τ hI
    unfold rwC at hc
    by_cases hti : t.regs.contains i = true
    · rw [if_pos hti] at hc; exact nomatch hc
    · rw [if_neg hti] at hc
      cases hp : rwC i PB p with
      | none => rw [hp] at hc; exact nomatch hc
      | some p' =>
        cases hb : rwC i PB b with
        | none => rw [hp, hb] at hc; exact nomatch hc
        | some b' =>
          rw [hp, hb] at hc; cases hc
          obtain ⟨τ₁, x₁, r₁⟩ := ihp hp (fun x hx => hreg x (List.mem_append_left _ hx))
            (fun y hy => by have := hnw y hy; simp only [wrs, List.contains_append, Bool.or_eq_false_iff] at this; exact this.1) hI
          refine ⟨τ₁, .loopF x₁ ?_, r₁⟩
          rw [tst_eq (σ := s₁.reg) fun y hy => r₁.reg y (hreg y (List.mem_append_right _ (List.mem_append_left _ hy)))
            fun e => hti (List.contains_iff_mem.2 (e ▸ hy))]
          exact ht
  | @loopT p t b s s₁ s₂ s₃ _ ht _ _ ihp ihb ihl =>
    intro c' hc hreg hnw τ hI
    have hc0 := hc
    unfold rwC at hc
    by_cases hti : t.regs.contains i = true
    · rw [if_pos hti] at hc; exact nomatch hc
    · rw [if_neg hti] at hc
      cases hp : rwC i PB p with
      | none => rw [hp] at hc; exact nomatch hc
      | some p' =>
        cases hb : rwC i PB b with
        | none => rw [hp, hb] at hc; exact nomatch hc
        | some b' =>
          rw [hp, hb] at hc; cases hc
          obtain ⟨τ₁, x₁, r₁⟩ := ihp hp (fun x hx => hreg x (List.mem_append_left _ hx))
            (fun y hy => by have := hnw y hy; simp only [wrs, List.contains_append, Bool.or_eq_false_iff] at this; exact this.1) hI
          obtain ⟨τ₂, x₂, r₂⟩ := ihb hb (fun x hx => hreg x (List.mem_append_right _ (List.mem_append_right _ hx)))
            (fun y hy => by have := hnw y hy; simp only [wrs, List.contains_append, Bool.or_eq_false_iff] at this; exact this.2) r₁
          obtain ⟨τ₃, x₃, r₃⟩ := ihl hc0 hreg hnw r₂
          refine ⟨τ₃, .loopT x₁ ?_ x₂ x₃, r₃⟩
          rw [tst_eq (σ := s₁.reg) fun y hy => r₁.reg y (hreg y (List.mem_append_right _ (List.mem_append_left _ hy)))
            fun e => hti (List.contains_iff_mem.2 (e ▸ hy))]
          exact ht
  | loop2A => intro c' hc; exact nomatch hc
  | loop2B => intro c' hc; exact nomatch hc
  | loop2T => intro c' hc; exact nomatch hc

theorem ne_of_lt_le {a b : BitVec 64} (h1 : a < b) : a ≠ b := fun e => by rw [e] at h1; exact BitVec.lt_irrefl _ h1

/-- the reduced loop simulates the loop while `i ≤ n` -/
theorem loop_sim {m i : Nat} {n : Arg Nat} {b₀ : Nat} {PB : List (Nat × Nat)} (S : Side m i n b₀ PB)
    {pre body body' : Code Nat} (hpre : triv pre = true) (hrw : rwC i PB body = some body')
    (hreg : ∀ x, x ∈ body.regs → x < m)
    (hnw : ∀ y, y ∈ b₀ :: (PB.map Prod.fst ++ n.regs) → (wrs body).contains y = false) (hinc : inc1 i body = true) :
    ∀ {c : Code Nat} {σ σ' : St Nat}, Exec ram fp c σ σ' → c = .loop pre ⟨.ltu, .r i, n⟩ body →
    ∀ {τ : St Nat}, Inv m i n b₀ PB σ τ → ¬ (n.eval σ.reg < σ.reg i) →
    ∃ τ', Exec ram fp (.loop pre ⟨.ne, .r (m + 1), .r m⟩ body') τ τ' ∧ Inv m i n b₀ PB σ' τ' := by
  have htest : ∀ {σ τ : St Nat}, Inv m i n b₀ PB σ τ →
      (⟨.ne, .r (m + 1), .r m⟩ : Tst Nat).eval τ.reg = !decide (σ.reg i = n.eval σ.reg) := by
    intro σ τ hI
    show (!decide (τ.reg (m + 1) = τ.reg m)) = _
    rw [hI.ptr b₀ (m + 1) S.hb0, hI.lim]
    congr 1
    apply decide_eq_decide.2
    constructor
    · intro e
      have := congrArg (fun x => x - σ.reg b₀) e
      simp only [BitVec.add_comm (σ.reg b₀), BitVec.add_sub_cancel] at this; exact this
    · intro e; rw [e]
  intro c σ σ' h
  induction h with
  | skip => intro e; cases e
  | ins => intro e; cases e
  | seq => intro e; cases e
  | whenT => intro e; cases e
  | whenF => intro e; cases e
  | loop2A => intro e; cases e
  | loop2B => intro e; cases e
  | loop2T => intro e; cases e
  | @loopF p t b s s₁ hp ht _ =>
    intro e τ hI hle
    cases e
    rw [triv_exec hp hpre] at ht ⊢
    have hnl : ¬ s.reg i < n.eval s.reg := fun h' => by
      have : (⟨.ltu, .r i, n⟩ : Tst Nat).eval s.reg = true := decide_eq_true h'
      rw [this] at ht; exact nomatch ht
    have heq : s.reg i = n.eval s.reg := by
      rw [BitVec.lt_def] at hnl hle; apply BitVec.eq_of_toNat_eq; omega
    refine ⟨τ, .loopF (triv_run hpre τ) ?_, hI⟩
    rw [htest hI, heq]; simp
  | @loopT p t b s s₁ s₂ s₃ hp ht hb _ _ _ ihl =>
    intro e τ hI hle
    cases e
    rw [triv_exec hp hpre] at ht hb
    have hl : s.reg i < n.eval s.reg := of_decide_eq_true ht
    obtain ⟨τ₂, x₂, r₂⟩ := body_sim S hb hrw hreg hnw hI
    have hn2 : n.eval s₂.reg = n.eval s.reg := arg_eq fun y hy =>
      nw_exec hb (hnw y (List.mem_cons_of_mem _ (List.mem_append_right _ hy)))
    have hle2 : ¬ n.eval s₂.reg < s₂.reg i := by
      rw [hn2]
      rcases inc1_ok hb hinc with e | e
      · rw [e]; rw [BitVec.lt_def] at hl ⊢; omega
      · rw [e]; rw [BitVec.lt_def] at hl ⊢; rw [BitVec.toNat_add]; simp; omega
    obtain ⟨τ₃, x₃, r₃⟩ := ihl rfl r₂ hle2
    refine ⟨τ₃, .loopT (triv_run hpre τ) ?_ x₂ x₃, r₃⟩
    rw [htest hI]; simp only [Bool.not_eq_true', decide_eq_false_iff_not]; exact ne_of_lt_le hl

/-- **one loop, reduced** (or `none`) -/
def srL (m : Nat) (pre : Code Nat) (t : Tst Nat) (body : Code Nat) : Option (Code Nat) :=
  match t with
  | ⟨.ltu, .r i, n⟩ =>
    match (bases i body).eraseDups with
    | [] => none
    | b₀ :: B =>
      match rwC i (mkPB (m + 1) (b₀ :: B)) body with
      | none => none
      | some body' =>
        if (triv pre && inc1 i body && okL m i n b₀ (mkPB (m + 1) (b₀ :: B)) body) = true then
          some (.when ⟨.geu, n, .r i⟩
            (.seq (.seq (.ins (.bin .add m (.r b₀) n)) (inits i (mkPB (m + 1) (b₀ :: B))))
              (.seq (.loop pre ⟨.ne, .r (m + 1), .r m⟩ body') (.ins (.bin .sub i (.r (m + 1)) (.r b₀))))))
        else none
  | _ => none

theorem srL_ok {m : Nat} {pre : Code Nat} {t : Tst Nat} {body c' : Code Nat} (hs : srL m pre t body = some c')
    {σ σ' : St Nat} (h : Exec ram fp (.loop pre t body) σ σ') (hc : ∀ x, x ∈ (Code.loop pre t body).regs → x < m)
    {τ : St Nat} (hr : RM m σ τ) : ∃ τ', Exec ram fp c' τ τ' ∧ RM m σ' τ' := by
  unfold srL at hs
  split at hs
  · rename_i i n
    split at hs
    · exact nomatch hs
    · rename_i b₀ B _
      split at hs
      · exact nomatch hs
      · rename_i body' hrw
        by_cases hk : (triv pre && inc1 i body && okL m i n b₀ (mkPB (m + 1) (b₀ :: B)) body) = true
        · rw [if_pos hk] at hs; cases hs
          have hk' := hk
          simp only [Bool.and_eq_true] at hk'
          obtain ⟨⟨hpre, hinc⟩, hok⟩ := hk'
          obtain ⟨S, hnw⟩ := okL_side hok
          generalize mkPB (m + 1) (b₀ :: B) = PB at S hnw hrw
          have hreg : ∀ x, x ∈ body.regs → x < m := fun x hx =>
            hc x (List.mem_append_right _ (List.mem_append_right _ hx))
          have hni : n.eval τ.reg = n.eval σ.reg := arg_eq fun y hy => hr.2 y (S.nreg y hy).1
          have hii : τ.reg i = σ.reg i := hr.2 i S.ilt
          by_cases hlt : n.eval σ.reg < σ.reg i
          · -- the loop exits at once (the head code is trivial)
            have hσ : σ' = σ := by
              cases h with
              | loopF hp ht => exact triv_exec hp hpre
              | loopT hp ht _ _ =>
                rw [triv_exec hp hpre] at ht
                have : σ.reg i < n.eval σ.reg := of_decide_eq_true ht
                rw [BitVec.lt_def] at this hlt; omega
            subst hσ
            refine ⟨τ, .whenF ?_, hr⟩
            show (!decide (n.eval τ.reg < τ.reg i)) = false
            rw [hni, hii]; simp [hlt]
          · have hP : ∀ b p, (b, p) ∈ PB → b < m + 1 ∧ m + 1 ≤ p := fun b p hm => ⟨by have := (S.ptr b p hm).1; omega, (S.ptr b p hm).2.1⟩
            obtain ⟨τb, xb, mb, yb, pb⟩ := inits_exec (ram := ram) (fp := fp) (i := i) (k := m + 1) (by have := S.ilt; omega)
              S.nd hP ⟨upd τ.reg m (τ.reg b₀ + n.eval τ.reg), τ.mem⟩
            have hnP : ∀ y, y < m + 1 → y ∉ PB.map Prod.snd := fun y hy h => by
              obtain ⟨⟨b, p⟩, hm, rfl⟩ := List.mem_map.1 h
              have := (S.ptr b p hm).2.1; dsimp only at hy; omega
            have hI : Inv m i n b₀ PB σ τb := by
              refine ⟨mb.trans hr.1, fun x hx _ => ?_, fun b p hm => ?_, ?_⟩
              · rw [yb x (hnP x (by omega))]; show upd τ.reg m _ x = _; rw [upd_ne _ _ (by omega)]; exact hr.2 x hx
              · have hbm : b < m := (S.ptr b p hm).1
                rw [pb b p hm]; show upd τ.reg m _ b + upd τ.reg m _ i = _
                rw [upd_ne _ _ (by omega), upd_ne _ _ (by have := S.ilt; omega), hr.2 b hbm, hii]
              · rw [yb m (hnP m (by omega))]; show upd τ.reg m _ m = _; rw [upd_eq, hni, hr.2 b₀ S.b0.1]
            obtain ⟨τc, xc, rc⟩ := loop_sim S hpre hrw hreg hnw hinc h rfl hI hlt
            refine ⟨_, .whenT ?_ (.seq (.seq (.ins .bin) xb) (.seq xc (.ins .bin))), rc.mem, fun x hx => ?_⟩
            · show (!decide (n.eval τ.reg < τ.reg i)) = true
              rw [hni, hii]; simp [hlt]
            · show upd τc.reg i (τc.reg (m + 1) - τc.reg b₀) x = σ'.reg x
              by_cases e : x = i
              · subst e; rw [upd_eq, rc.ptr b₀ (m + 1) S.hb0, rc.reg b₀ S.b0.1 S.b0.2, BitVec.add_comm,
                  BitVec.add_sub_cancel]
              · rw [upd_ne _ _ e]; exact rc.reg x hx e
        · rw [if_neg hk] at hs; exact nomatch hs
  · exact nomatch hs

/-- reduce every loop that qualifies (not inside a reduced loop) -/
def srC (m : Nat) : Code Nat → Code Nat
  | .seq a b => .seq (srC m a) (srC m b)
  | .when t b => .when t (srC m b)
  | .loop p t b =>
    match srL m p t b with
    | some c => c
    | none => .loop (srC m p) t (srC m b)
  | c => c

/-- some loop qualifies -/
def hit (m : Nat) : Code Nat → Bool
  | .seq a b => hit m a || hit m b
  | .when _ b => hit m b
  | .loop p t b => (srL m p t b).isSome || hit m p || hit m b
  | _ => false

theorem srC_loop {m : Nat} {p b : Code Nat} {t : Tst Nat} (hs : srL m p t b = none) :
    srC m (.loop p t b) = .loop (srC m p) t (srC m b) := by
  simp only [srC, hs]

theorem srC_ok {m : Nat} : ∀ {c : Code Nat} {σ σ' : St Nat}, Exec ram fp c σ σ' → (∀ x, x ∈ c.regs → x < m) →
    ∀ {τ : St Nat}, RM m σ τ → ∃ τ', Exec ram fp (srC m c) τ τ' ∧ RM m σ' τ' := by
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
    refine ⟨τ₁, .whenT ?_ x₁, r₁⟩
    rw [tst_eq fun y hy => hr.2 y (hc y (List.mem_append_left _ hy))]; exact ht
  | whenF ht =>
    intro hc τ hr
    refine ⟨τ, .whenF ?_, hr⟩
    rw [tst_eq fun y hy => hr.2 y (hc y (List.mem_append_left _ hy))]; exact ht
  | @loopF p t b s s₁ hp ht ihp =>
    intro hc τ hr
    cases hs : srL m p t b with
    | some c' =>
      show ∃ τ', Exec ram fp (match srL m p t b with | some c => c | none => _) τ τ' ∧ _
      rw [hs]; exact srL_ok hs (.loopF hp ht) hc hr
    | none =>
      rw [srC_loop hs]
      obtain ⟨τ₁, x₁, r₁⟩ := ihp (fun x hx => hc x (List.mem_append_left _ hx)) hr
      refine ⟨τ₁, .loopF x₁ ?_, r₁⟩
      rw [tst_eq fun y hy => r₁.2 y (hc y (List.mem_append_right _ (List.mem_append_left _ hy)))]; exact ht
  | @loopT p t b s s₁ s₂ s₃ hp ht hb hl ihp ihb ihl =>
    intro hc τ hr
    cases hs : srL m p t b with
    | some c' =>
      show ∃ τ', Exec ram fp (match srL m p t b with | some c => c | none => _) τ τ' ∧ _
      rw [hs]; exact srL_ok hs (.loopT hp ht hb hl) hc hr
    | none =>
      have ihl' := @ihl hc
      rw [srC_loop hs] at ihl' ⊢
      obtain ⟨τ₁, x₁, r₁⟩ := ihp (fun x hx => hc x (List.mem_append_left _ hx)) hr
      obtain ⟨τ₂, x₂, r₂⟩ := ihb (fun x hx => hc x (List.mem_append_right _ (List.mem_append_right _ hx))) r₁
      obtain ⟨τ₃, x₃, r₃⟩ := ihl' r₂
      refine ⟨τ₃, .loopT x₁ ?_ x₂ x₃, r₃⟩
      rw [tst_eq fun y hy => r₁.2 y (hc y (List.mem_append_right _ (List.mem_append_left _ hy)))]; exact ht
  | loop2A h1 ht => intro hc τ hr; exact same_RM (.loop2A h1 ht) hc hr
  | loop2B h1 ht₁ h2 ht₂ => intro hc τ hr; exact same_RM (.loop2B h1 ht₁ h2 ht₂) hc hr
  | loop2T h1 ht₁ h2 ht₂ hb hl => intro hc τ hr; exact same_RM (.loop2T h1 ht₁ h2 ht₂ hb hl) hc hr

theorem lt_foldr_max : ∀ {l : List Nat} {x : Nat}, x ∈ l → x < l.foldr max 0 + 1
  | y :: l, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [List.foldr_cons]; omega
    · have := lt_foldr_max h; simp only [List.foldr_cons]; omega

/-- **strength reduction** (then copy propagation and dead-code elimination), the outputs `vars` live at
the end; the input unchanged when no loop qualifies -/
def sr (vars : List Nat) (c : Code Nat) : Code Nat :=
  let m := (vars ++ c.regs).foldr max 0 + 1
  if hit m c then
    let c₁ := (cp [] (srC m c)).1
    match dce c₁ vars with
    | some (c₂, _) => c₂
    | none => c₁
  else c

/-- **Strength reduction preserves executions** (same memory, same outputs). -/
theorem sr_ok (vars : List Nat) {c : Code Nat} {σ σ' : St Nat} (h : Exec ram fp c σ σ') :
    ∃ τ', Exec ram fp (sr vars c) σ τ' ∧ τ'.mem = σ'.mem ∧ ∀ x, x ∈ vars → τ'.reg x = σ'.reg x := by
  unfold sr
  generalize hm : (vars ++ c.regs).foldr max 0 + 1 = m
  have hlt : ∀ x, x ∈ vars ++ c.regs → x < m := fun x hx => hm ▸ lt_foldr_max hx
  dsimp only
  by_cases hh : hit m c = true
  · rw [if_pos hh]
    obtain ⟨τ₁, x₁, r₁⟩ := srC_ok h (fun x hx => hlt x (List.mem_append_right _ hx)) (τ := σ) ⟨rfl, fun _ _ => rfl⟩
    have x₁' := (cp_ok x₁ (K := []) cp_nil).1
    cases hd : dce (cp [] (srC m c)).1 vars with
    | none => exact ⟨τ₁, x₁', r₁.1, fun x hx => r₁.2 x (hlt x (List.mem_append_left _ hx))⟩
    | some r =>
      obtain ⟨c₂, Lin⟩ := r
      obtain ⟨τ₂, x₂, r₂⟩ := dce_ok x₁' hd (τ := σ) ⟨rfl, fun _ _ => rfl⟩
      exact ⟨τ₂, x₂, r₂.1.trans r₁.1, fun x hx => (r₂.2 x hx).trans (r₁.2 x (hlt x (List.mem_append_left _ hx)))⟩
  · rw [if_neg hh]; exact ⟨σ', h, rfl, fun _ _ => rfl⟩

end SR
end Proven.Mach.IR
