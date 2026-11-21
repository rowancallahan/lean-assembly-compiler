/- Selection clean-ups of the front end's code (IR → IR on virtual registers, after `Flow.flow`).

* `merge`: `if t then A; if t then B` (`A` keeps the registers of `t`) becomes `if t then (A; B)`; dead-code
  elimination then drops what `B` overwrites (`x < c ? x : (x < c ? 0 : x - c)` of `%` by a constant).
* `swap`: `d := x op y; if t then d := s` (`d` not read by `t`, `x`, `y`; `s ≠ d`) becomes
  `d := s; if ¬t then d := x op y`: the copy is the common case of a conditional subtraction.
Both keep the states.  `fast vars c`: the pipeline of the front end's candidate body (`flow`, these, strength
reduction, constants in registers); `fast_ok` in the shape of `sr_ok`. -/
import Nano.Base.Compiler.Opt.Flow
import Nano.Base.Compiler.Opt.Hoist

namespace Proven.Mach.IR
namespace Peep
open SR

variable {ram : Nat → Prop} {fp : Nat}

/-- `a` does not write the registers of `t` -/
def keeps (a : Code Nat) (t : Tst Nat) : Bool := (wrs a).all fun x => !t.regs.contains x

/-- `a; b` with two equal tests merged -/
def mergeS (a b : Code Nat) : Code Nat :=
  match a, b with
  | .when t A, .seq (.when t' B) r => if (decide (t = t') && keeps A t) = true then .seq (.when t (.seq A B)) r
      else .seq a b
  | .when t A, .when t' B => if (decide (t = t') && keeps A t) = true then .when t (.seq A B) else .seq a b
  | a, b => .seq a b

def mergeC : Code Nat → Code Nat
  | .seq a b => mergeS (mergeC a) (mergeC b)
  | .when t b => .when t (mergeC b)
  | .loop p t b => .loop (mergeC p) t (mergeC b)
  | .loop2 p₁ t₁ p₂ t₂ b => .loop2 (mergeC p₁) t₁ (mergeC p₂) t₂ (mergeC b)
  | c => c

/-- the conditions of `swap` -/
def swapOK (d : Nat) (x y : Arg Nat) (t : Tst Nat) (d' s : Nat) : Bool :=
  decide (d' = d) && decide (s ≠ d) && !t.regs.contains d && !x.regs.contains d && !y.regs.contains d

def swapS (a b : Code Nat) : Code Nat :=
  match a, b with
  | .ins (.bin op d x y), .seq (.when t (.ins (.set d' (.r s)))) r =>
    if swapOK d x y t d' s then .seq (.ins (.set d (.r s))) (.seq (.when t.neg (.ins (.bin op d x y))) r)
    else .seq a b
  | .ins (.bin op d x y), .when t (.ins (.set d' (.r s))) =>
    if swapOK d x y t d' s then .seq (.ins (.set d (.r s))) (.when t.neg (.ins (.bin op d x y)))
    else .seq a b
  | a, b => .seq a b

def swapC : Code Nat → Code Nat
  | .seq a b => swapS (swapC a) (swapC b)
  | .when t b => .when t (swapC b)
  | .loop p t b => .loop (swapC p) t (swapC b)
  | .loop2 p₁ t₁ p₂ t₂ b => .loop2 (swapC p₁) t₁ (swapC p₂) t₂ (swapC b)
  | c => c

/-! ## Proofs (same states) -/

theorem keeps_eval {a : Code Nat} {t : Tst Nat} (hk : keeps a t = true) {σ σ' : St Nat} (h : Exec ram fp a σ σ') :
    t.eval σ'.reg = t.eval σ.reg :=
  tst_eq fun y hy => wrs_exec h fun hw => by
    have := List.all_eq_true.1 hk y hw
    rw [List.contains_iff_mem.2 hy] at this; exact nomatch this

theorem when2 {t : Tst Nat} {A B : Code Nat} (hk : keeps A t = true) {σ σ₁ σ₂ : St Nat}
    (h1 : Exec ram fp (.when t A) σ σ₁) (h2 : Exec ram fp (.when t B) σ₁ σ₂) : Exec ram fp (.when t (.seq A B)) σ σ₂ := by
  cases h1 with
  | whenT ht hA =>
    cases h2 with
    | whenT _ hB => exact .whenT ht (.seq hA hB)
    | whenF hf => rw [keeps_eval hk hA, ht] at hf; exact nomatch hf
  | whenF hf =>
    cases h2 with
    | whenT ht _ => rw [hf] at ht; exact nomatch ht
    | whenF _ => exact .whenF hf

theorem mergeS_ok {a b : Code Nat} {σ σ' : St Nat} (h : Exec ram fp (.seq a b) σ σ') :
    Exec ram fp (mergeS a b) σ σ' := by
  unfold mergeS
  split
  · rename_i t A t' B r
    split
    · rename_i hc
      obtain ⟨he, hk⟩ := Bool.and_eq_true_iff.1 hc
      cases of_decide_eq_true he
      cases h with
      | seq h1 h2 => cases h2 with
        | seq h2 h3 => exact .seq (when2 hk h1 h2) h3
    · exact h
  · rename_i t A t' B
    split
    · rename_i hc
      obtain ⟨he, hk⟩ := Bool.and_eq_true_iff.1 hc
      cases of_decide_eq_true he
      cases h with
      | seq h1 h2 => exact when2 hk h1 h2
    · exact h
  · exact h

theorem mergeC_ok : ∀ (c : Code Nat) {σ σ' : St Nat}, Exec ram fp c σ σ' → Exec ram fp (mergeC c) σ σ'
  | .seq a b, _, _, h => by
    cases h with | seq ha hb => exact mergeS_ok (.seq (mergeC_ok a ha) (mergeC_ok b hb))
  | .when t b, _, _, h => by
    cases h with
    | whenT ht hb => exact .whenT ht (mergeC_ok b hb)
    | whenF ht => exact .whenF ht
  | .loop p t b, _, _, h => Flow.loop_congr (fun _ _ => mergeC_ok p) (fun _ _ => mergeC_ok b) h
  | .loop2 p₁ t₁ p₂ t₂ b, _, _, h =>
    Flow.loop2_congr (fun _ _ => mergeC_ok p₁) (fun _ _ => mergeC_ok p₂) (fun _ _ => mergeC_ok b) h
  | .skip, _, _, h => h
  | .ins _, _, _, h => h

theorem upd_upd (σ : Regs Nat) (d : Nat) (a b : BitVec 64) : upd (upd σ d a) d b = upd σ d b := by
  funext x; simp only [upd]; split <;> rfl

theorem arg_upd {a : Arg Nat} {d : Nat} (h : a.regs.contains d = false) (σ : Regs Nat) (v : BitVec 64) :
    a.eval (upd σ d v) = a.eval σ :=
  arg_eq fun x hx => upd_ne _ _ fun e => by subst e; rw [List.contains_iff_mem.2 hx] at h; exact nomatch h

theorem swap2 {op : Op} {d s : Nat} {x y : Arg Nat} {t : Tst Nat} (hc : swapOK d x y t d s = true) {σ σ₂ : St Nat}
    (h : Exec ram fp (.seq (.ins (.bin op d x y)) (.when t (.ins (.set d (.r s))))) σ σ₂) :
    Exec ram fp (.seq (.ins (.set d (.r s))) (.when t.neg (.ins (.bin op d x y)))) σ σ₂ := by
  simp only [swapOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨-, hs⟩, ht⟩, hx⟩, hy⟩ := hc
  have htu : ∀ (ρ : Regs Nat) v, t.eval (upd ρ d v) = t.eval ρ := fun ρ v =>
    tst_eq fun z hz => upd_ne _ _ fun e => by subst e; rw [List.contains_iff_mem.2 hz] at ht; exact nomatch ht
  cases h with
  | seq h1 h2 =>
    cases h1 with
    | ins st1 =>
      cases st1
      cases h2 with
      | whenT h3 h4 =>
        cases h4 with
        | ins st =>
          cases st
          have e : (⟨upd (upd σ.reg d (op.eval (x.eval σ.reg) (y.eval σ.reg))) d
              ((Arg.r s).eval (upd σ.reg d (op.eval (x.eval σ.reg) (y.eval σ.reg)))), σ.mem⟩ : St Nat) =
              ⟨upd σ.reg d ((Arg.r s).eval σ.reg), σ.mem⟩ := by
            simp only [Arg.eval, upd_upd, upd_ne _ _ hs]
          rw [e]
          refine .seq (.ins .set) (.whenF ?_)
          rw [Tst.eval_neg, htu]; rw [htu] at h3; rw [h3]; rfl
      | whenF h3 =>
        have e : (⟨upd σ.reg d (op.eval (x.eval σ.reg) (y.eval σ.reg)), σ.mem⟩ : St Nat) =
            ⟨upd (upd σ.reg d ((Arg.r s).eval σ.reg)) d
              (op.eval (x.eval (upd σ.reg d ((Arg.r s).eval σ.reg))) (y.eval (upd σ.reg d ((Arg.r s).eval σ.reg)))),
              σ.mem⟩ := by
          rw [upd_upd, arg_upd hx, arg_upd hy]
        rw [e]
        refine .seq (.ins .set) (.whenT ?_ (.ins .bin))
        rw [Tst.eval_neg]; simp only [htu]; rw [htu] at h3; rw [h3]; rfl

theorem swapS_ok {a b : Code Nat} {σ σ' : St Nat} (h : Exec ram fp (.seq a b) σ σ') :
    Exec ram fp (swapS a b) σ σ' := by
  unfold swapS
  split
  · rename_i op d x y t d' s r
    split
    · rename_i hc
      have hd : d' = d := by simp only [swapOK, Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1.1.1.1
      subst hd
      cases h with
      | seq h1 h2 => cases h2 with
        | seq h2 h3 =>
          have := swap2 hc (.seq h1 h2)
          cases this with | seq a b => exact .seq a (.seq b h3)
    · exact h
  · rename_i op d x y t d' s
    split
    · rename_i hc
      have hd : d' = d := by simp only [swapOK, Bool.and_eq_true, decide_eq_true_eq] at hc; exact hc.1.1.1.1
      subst hd
      exact swap2 hc h
    · exact h
  · exact h

theorem swapC_ok : ∀ (c : Code Nat) {σ σ' : St Nat}, Exec ram fp c σ σ' → Exec ram fp (swapC c) σ σ'
  | .seq a b, _, _, h => by
    cases h with | seq ha hb => exact swapS_ok (.seq (swapC_ok a ha) (swapC_ok b hb))
  | .when t b, _, _, h => by
    cases h with
    | whenT ht hb => exact .whenT ht (swapC_ok b hb)
    | whenF ht => exact .whenF ht
  | .loop p t b, _, _, h => Flow.loop_congr (fun _ _ => swapC_ok p) (fun _ _ => swapC_ok b) h
  | .loop2 p₁ t₁ p₂ t₂ b, _, _, h =>
    Flow.loop2_congr (fun _ _ => swapC_ok p₁) (fun _ _ => swapC_ok p₂) (fun _ _ => swapC_ok b) h
  | .skip, _, _, h => h
  | .ins _, _, _, h => h

/-! ## The front end's pipeline -/

/-- merge, dead code, swap -/
def peep (vars : List Nat) (c : Code Nat) : Code Nat :=
  Flow.nrm (swapC (Flow.nrm (Flow.dceOr vars (mergeC c))))

theorem peep_ok (vars : List Nat) {c : Code Nat} {σ σ' : St Nat} (h : Exec ram fp c σ σ') :
    ∃ τ', Exec ram fp (peep vars c) σ τ' ∧ τ'.mem = σ'.mem ∧ ∀ x, x ∈ vars → τ'.reg x = σ'.reg x := by
  obtain ⟨τ₁, x₁, o₁⟩ := Flow.dceOr_ok vars (mergeC_ok c h)
  exact ⟨τ₁, Flow.nrm_ok _ (swapC_ok _ (Flow.nrm_ok _ x₁)), o₁.1, o₁.2⟩

/-- **the front end's candidate**: clean-ups, selection clean-ups, strength reduction, constants in
registers, at most `k` per loop (strength reduction alone for code without at-most-once loops) -/
def fast (k : Nat) (vars : List Nat) (c : Code Nat) : Code Nat :=
  if Flow.hasOnce c then Hoist.hoist k vars (sr vars (peep vars (Flow.flow vars c))) else sr vars c

theorem fast_ok (k : Nat) (vars : List Nat) {c : Code Nat} {σ σ' : St Nat} (h : Exec ram fp c σ σ') :
    ∃ τ', Exec ram fp (fast k vars c) σ τ' ∧ τ'.mem = σ'.mem ∧ ∀ x, x ∈ vars → τ'.reg x = σ'.reg x := by
  unfold fast
  split
  · obtain ⟨τ₁, x₁, m₁, r₁⟩ := Flow.flow_ok vars h
    obtain ⟨τ₂, x₂, m₂, r₂⟩ := peep_ok vars x₁
    obtain ⟨τ₃, x₃, m₃, r₃⟩ := sr_ok vars x₂
    obtain ⟨τ₄, x₄, m₄, r₄⟩ := Hoist.hoist_ok k vars x₃
    exact ⟨τ₄, x₄, m₄.trans (m₃.trans (m₂.trans m₁)),
      fun x hx => (r₄ x hx).trans ((r₃ x hx).trans ((r₂ x hx).trans (r₁ x hx)))⟩
  · exact sr_ok vars h

end Peep
end Proven.Mach.IR
