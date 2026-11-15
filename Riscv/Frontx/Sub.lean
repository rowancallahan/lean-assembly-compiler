/- Calls to other translated functions, inlined: the callee's whole program runs as a sub-program of the caller
(`Tree.sub`), its variables renamed into a free range of the caller's (`ren`), its temporaries cleared afterwards
(`callP`).  Source level, once and for all: determinism of `BExec`, runs of a renamed program (`exec_ren`), runs
from a state that agrees on the variables a program uses (`exec_agree`), and `callP_exec`. -/
import Riscv.Direct.Arr2Src

namespace Proven.Frontx
open Proven

/-! ## Determinism -/

theorem _root_.Proven.BExec.detF {p : BStmt} {σ σ₁ σ₂ : BState} (h₁ : BExec p σ σ₁) (h₂ : BExec p σ σ₂) : σ₁ = σ₂ := by
  induction h₁ generalizing σ₂ with
  | assign => cases h₂; rfl
  | load => cases h₂; rfl
  | store => cases h₂; rfl
  | mop => cases h₂; rfl
  | seq _ _ ih1 ih2 => cases h₂ with | seq a b => exact ih2 ((ih1 a) ▸ b)
  | loopF hc => cases h₂ with | loopF => rfl | loopT hc' => exact absurd hc hc'
  | loopT hc _ _ ih1 ih2 => cases h₂ with
    | loopF hc' => exact absurd hc' hc
    | loopT _ a b => exact ih2 ((ih1 a) ▸ b)

/-! ## Variables of a statement -/

/-- every variable a statement reads or writes is `< m` (as a `Bool`, decided by evaluation) -/
def _root_.Proven.BExp.vltF (m : Nat) : BExp → Bool
  | .var i => decide (i < m)
  | .const _ => true
  | .bin _ a b => a.vltF m && b.vltF m
  | .ite c a b => c.vltF m && a.vltF m && b.vltF m

def _root_.Proven.BStmt.vltF (m : Nat) : BStmt → Bool
  | .assign v e | .load v _ e => decide (v < m) && e.vltF m
  | .store _ i e => i.vltF m && e.vltF m
  | .seq p q => p.vltF m && q.vltF m
  | .loop c b => c.vltF m && b.vltF m
  | .mop _ v a b => decide (v < m) && a.vltF m && b.vltF m

theorem _root_.Proven.BStmt.vltF_assigns {m : Nat} : ∀ {p : BStmt}, p.vltF m = true → ∀ v ∈ p.assigns, v < m
  | .assign _ _, h, v, hv | .load _ _ _, h, v, hv => by
    simp only [BStmt.vltF, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [BStmt.assigns, List.mem_singleton] at hv; subst hv; exact h.1
  | .store .., _, _, hv => by simp [BStmt.assigns] at hv
  | .mop _ _ _ _, h, v, hv => by
    simp only [BStmt.vltF, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [BStmt.assigns, List.mem_singleton] at hv; subst hv; exact h.1.1
  | .seq p q, h, v, hv => by
    simp only [BStmt.vltF, Bool.and_eq_true] at h
    simp only [BStmt.assigns, List.mem_append] at hv
    exact hv.elim (vltF_assigns h.1 v) (vltF_assigns h.2 v)
  | .loop _ p, h, v, hv => by
    simp only [BStmt.vltF, Bool.and_eq_true] at h
    exact vltF_assigns h.2 v hv

theorem _root_.Proven.BExp.denote_agreeF {m : Nat} {ρ ρ' : BEnv} (h : ∀ v, v < m → ρ' v = ρ v) :
    ∀ e : BExp, e.vltF m = true → e.denote ρ' = e.denote ρ
  | .var i, hv => h i (by simpa [BExp.vltF] using hv)
  | .const _, _ => rfl
  | .bin _ a b, hv => by
    simp only [BExp.vltF, Bool.and_eq_true] at hv
    simp only [BExp.denote, denote_agreeF h a hv.1, denote_agreeF h b hv.2]
  | .ite c a b, hv => by
    simp only [BExp.vltF, Bool.and_eq_true] at hv
    simp only [BExp.denote, denote_agreeF h c hv.1.1, denote_agreeF h a hv.1.2, denote_agreeF h b hv.2]

/-- a run from a state that agrees on the variables `< m` the program uses: the same run, the variables `≥ m`
untouched -/
theorem exec_agree {m : Nat} {p : BStmt} (hp : p.vltF m = true) {σ σ' : BState} (h : BExec p σ σ') :
    ∀ τ : BState, (∀ v, v < m → τ.env v = σ.env v) → τ.heap = σ.heap →
    ∃ τ', BExec p τ τ' ∧ (∀ v, v < m → τ'.env v = σ'.env v) ∧ τ'.heap = σ'.heap ∧
      ∀ v, m ≤ v → τ'.env v = τ.env v := by
  induction h with
  | @assign v e σ =>
    intro τ hA hH
    simp only [BStmt.vltF, Bool.and_eq_true, decide_eq_true_eq] at hp
    refine ⟨_, .assign, fun x hx => ?_, hH, fun x hx => ?_⟩
    · simp only [BEnv.set]; split
      · exact BExp.denote_agreeF hA e hp.2
      · exact hA x hx
    · simp only [BEnv.set]; rw [if_neg (by omega)]
  | @load v b i σ hb hi =>
    intro τ hA hH
    simp only [BStmt.vltF, Bool.and_eq_true, decide_eq_true_eq] at hp
    have hi' := BExp.denote_agreeF hA i hp.2
    have hb' : b < τ.heap.length := hH ▸ hb
    have hl : (i.denote τ.env).toNat < τ.heap[b].length := by simp only [hH, hi']; exact hi
    refine ⟨_, .load hb' hl, fun x hx => ?_, hH, fun x hx => ?_⟩
    · simp only [BEnv.set]; split
      · simp only [hH, hi']
      · exact hA x hx
    · simp only [BEnv.set]; rw [if_neg (by omega)]
  | @store b i e σ hb hi =>
    intro τ hA hH
    simp only [BStmt.vltF, Bool.and_eq_true] at hp
    have hi' := BExp.denote_agreeF hA i hp.1
    have he' := BExp.denote_agreeF hA e hp.2
    have hb' : b < τ.heap.length := hH ▸ hb
    have hl : (i.denote τ.env).toNat < τ.heap[b].length := by simp only [hH, hi']; exact hi
    exact ⟨_, .store hb' hl, hA, by simp only [hH, hi', he'], fun _ _ => rfl⟩
  | @mop o v a b σ =>
    intro τ hA hH
    simp only [BStmt.vltF, Bool.and_eq_true, decide_eq_true_eq] at hp
    refine ⟨_, .mop, fun x hx => ?_, hH, fun x hx => ?_⟩
    · simp only [BEnv.set]; split
      · rw [BExp.denote_agreeF hA a hp.1.2, BExp.denote_agreeF hA b hp.2]
      · exact hA x hx
    · simp only [BEnv.set]; rw [if_neg (by omega)]
  | seq _ _ ih1 ih2 =>
    intro τ hA hH
    simp only [BStmt.vltF, Bool.and_eq_true] at hp
    obtain ⟨τ₁, h1, hA1, hH1, hk1⟩ := ih1 hp.1 τ hA hH
    obtain ⟨τ₂, h2, hA2, hH2, hk2⟩ := ih2 hp.2 τ₁ hA1 hH1
    exact ⟨τ₂, .seq h1 h2, hA2, hH2, fun v hv => (hk2 v hv).trans (hk1 v hv)⟩
  | loopF hc =>
    intro τ hA hH
    simp only [BStmt.vltF, Bool.and_eq_true] at hp
    exact ⟨τ, .loopF (by rw [BExp.denote_agreeF hA _ hp.1]; exact hc), hA, hH, fun _ _ => rfl⟩
  | loopT hc _ _ ih1 ih2 =>
    intro τ hA hH
    have hp' := hp
    simp only [BStmt.vltF, Bool.and_eq_true] at hp'
    obtain ⟨τ₁, h1, hA1, hH1, hk1⟩ := ih1 hp'.2 τ hA hH
    obtain ⟨τ₂, h2, hA2, hH2, hk2⟩ := ih2 hp τ₁ hA1 hH1
    exact ⟨τ₂, .loopT (by rw [BExp.denote_agreeF hA _ hp'.1]; exact hc) h1 h2, hA2, hH2,
      fun v hv => (hk2 v hv).trans (hk1 v hv)⟩

/-! ## Renaming -/

/-- the callee's variables `0 .. 3` are the caller's (block bases and lengths); `4 + j` is the caller's `b + j` -/
def rho (b : Nat) (v : Nat) : Nat := if v < 4 then v else b + (v - 4)

def _root_.Proven.BExp.renF (b : Nat) : BExp → BExp
  | .var i => .var (rho b i)
  | .const c => .const c
  | .bin op x y => .bin op (x.renF b) (y.renF b)
  | .ite c x y => .ite (c.renF b) (x.renF b) (y.renF b)

def _root_.Proven.BStmt.renF (b : Nat) : BStmt → BStmt
  | .assign v e => .assign (rho b v) (e.renF b)
  | .load v k i => .load (rho b v) k (i.renF b)
  | .store k i e => .store k (i.renF b) (e.renF b)
  | .seq p q => .seq (p.renF b) (q.renF b)
  | .loop c p => .loop (c.renF b) (p.renF b)
  | .mop o v x y => .mop o (rho b v) (x.renF b) (y.renF b)

theorem _root_.Proven.BExp.denote_renF (b : Nat) (E : BEnv) : ∀ e : BExp, (e.renF b).denote E = e.denote (fun v => E (rho b v))
  | .var _ => rfl
  | .const _ => rfl
  | .bin _ x y => by simp only [BExp.renF, BExp.denote, denote_renF b E x, denote_renF b E y]
  | .ite c x y => by simp only [BExp.renF, BExp.denote, denote_renF b E c, denote_renF b E x, denote_renF b E y]

theorem rho_inj {b : Nat} (hb : 4 ≤ b) {v w : Nat} (h : rho b v = rho b w) : v = w := by
  unfold rho at h; split at h <;> split at h <;> omega

/-- a run of `p` seen through the renaming: the caller's run of `p.renF b`; the caller's variables outside the
image of `rho b` are untouched -/
theorem exec_ren {b : Nat} (hb : 4 ≤ b) {p : BStmt} {σ σ' : BState} (h : BExec p σ σ') :
    ∀ E : BEnv, (∀ v, E (rho b v) = σ.env v) →
    ∃ E', BExec (p.renF b) ⟨E, σ.heap⟩ ⟨E', σ'.heap⟩ ∧ (∀ v, E' (rho b v) = σ'.env v) ∧
      ∀ x, (∀ v, rho b v ≠ x) → E' x = E x := by
  have hset : ∀ (E : BEnv) (env : BEnv) (v : Nat) (x : BitVec 64), (∀ w, E (rho b w) = env w) →
      ∀ w, (E.set (rho b v) x) (rho b w) = (env.set v x) w := fun E env v x hE w => by
    simp only [BEnv.set]
    by_cases hw : w = v
    · subst hw; simp
    · rw [if_neg (fun e => hw (rho_inj hb e)), if_neg hw]; exact hE w
  induction h with
  | @assign v e σ =>
    intro E hE
    refine ⟨_, .assign, ?_, fun x hx => ?_⟩
    · have := hset E σ.env v (e.denote σ.env) hE
      rw [BExp.denote_renF, show (fun w => E (rho b w)) = σ.env from funext hE]; exact this
    · simp only [BEnv.set]; rw [if_neg (fun e => hx v e.symm)]
  | @load v k i σ hk hi =>
    intro E hE
    have hi' : (i.renF b).denote E = i.denote σ.env := by
      rw [BExp.denote_renF, show (fun w => E (rho b w)) = σ.env from funext hE]
    refine ⟨_, .load (σ := ⟨E, σ.heap⟩) hk (by simp only [hi']; exact hi), ?_, fun x hx => ?_⟩
    · intro w; simp only [hi']; exact hset E σ.env v _ hE w
    · simp only [BEnv.set]; rw [if_neg (fun e => hx v e.symm)]
  | @store k i e σ hk hi =>
    intro E hE
    have hfe : (fun w => E (rho b w)) = σ.env := funext hE
    have hi' : (i.renF b).denote E = i.denote σ.env := by rw [BExp.denote_renF, hfe]
    have he' : (e.renF b).denote E = e.denote σ.env := by rw [BExp.denote_renF, hfe]
    refine ⟨E, ?_, hE, fun _ _ => rfl⟩
    have := BExec.store (b := k) (i := i.renF b) (e := e.renF b) (σ := ⟨E, σ.heap⟩) hk (by simp only [hi']; exact hi)
    simp only [hi', he'] at this; exact this
  | @mop o v x y σ =>
    intro E hE
    have hfe : (fun w => E (rho b w)) = σ.env := funext hE
    refine ⟨_, .mop, ?_, fun z hz => ?_⟩
    · have := hset E σ.env v (o.eval (x.denote σ.env) (y.denote σ.env)) hE
      rw [BExp.denote_renF, BExp.denote_renF, hfe]; exact this
    · simp only [BEnv.set]; rw [if_neg (fun e => hz v e.symm)]
  | seq _ _ ih1 ih2 =>
    intro E hE
    obtain ⟨E₁, h1, hE1, hk1⟩ := ih1 E hE
    obtain ⟨E₂, h2, hE2, hk2⟩ := ih2 E₁ hE1
    exact ⟨E₂, .seq h1 h2, hE2, fun x hx => (hk2 x hx).trans (hk1 x hx)⟩
  | loopF hc =>
    intro E hE
    refine ⟨E, .loopF ?_, hE, fun _ _ => rfl⟩
    rw [BExp.denote_renF, show (fun w => E (rho b w)) = _ from funext hE]; exact hc
  | loopT hc _ _ ih1 ih2 =>
    intro E hE
    obtain ⟨E₁, h1, hE1, hk1⟩ := ih1 E hE
    obtain ⟨E₂, h2, hE2, hk2⟩ := ih2 E₁ hE1
    refine ⟨E₂, .loopT ?_ h1 h2, hE2, fun x hx => (hk2 x hx).trans (hk1 x hx)⟩
    rw [BExp.denote_renF, show (fun w => E (rho b w)) = _ from funext hE]; exact hc

/-! ## The call: renamed program, then the callee's temporaries cleared -/

/-- `v := 0` for `v = b + 1, …, b + n - 1` -/
def clr (b : Nat) : Nat → BStmt
  | 0 => .assign b (.var b)
  | n + 1 => .seq (clr b n) (.assign (b + n + 1) (.const 0))

/-- the caller's variables after a call: `r` in `b`, `0` in `b + 1, …, b + n`, the others kept -/
def callEnv (E : BEnv) (b n : Nat) (r : BitVec 64) : BEnv :=
  fun x => if x = b then r else if b < x ∧ x ≤ b + n then 0 else E x

theorem clr_exec (b : Nat) : ∀ (n : Nat) (E : BEnv) (H : Heap),
    BExec (clr b n) ⟨E, H⟩ ⟨fun x => if b < x ∧ x ≤ b + n then 0 else E x, H⟩
  | 0, E, H => BExec.assign' (by
    simp only [BState.mk.injEq, and_true]; funext x; simp only [BEnv.set, BExp.denote]
    by_cases h1 : x = b
    · subst h1; simp
    · rw [if_neg h1, if_neg (by omega)])
  | n + 1, E, H => .seq (clr_exec b n E H) (BExec.assign' (by
    simp only [BState.mk.injEq, and_true]; funext x; simp only [BEnv.set, BExp.denote]
    by_cases h1 : x = b + n + 1
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1]
      by_cases h2 : b < x ∧ x ≤ b + n
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]))

/-- the program of a call: the callee `p` (variables `< 4 + n + 1`, never assigning `0 .. 3`) renamed to base `b`,
then its temporaries cleared -/
def callP (p : BStmt) (b n : Nat) : BStmt := .seq (p.renF b) (clr b n)

/-- **A call.**  If the callee, started with its variables read from the caller's (`E ∘ rho b`), computes `r` in
its variable `out = 4` and keeps the heap, the call program leaves `callEnv E b n r`. -/
theorem callP_exec {p : BStmt} {b n : Nat} (hb : 4 ≤ b) (hp : p.vltF (5 + n) = true) (hlow : ∀ v ∈ p.assigns, 4 ≤ v)
    {E : BEnv} {H : Heap} {r : BitVec 64}
    (hg : ∃ σ', BExec p ⟨fun v => E (rho b v), H⟩ σ' ∧ σ'.env 4 = r ∧ σ'.heap = H) :
    BExec (callP p b n) ⟨E, H⟩ ⟨callEnv E b n r, H⟩ := by
  obtain ⟨σ', hx, h4, hh⟩ := hg
  obtain ⟨E', h1, hE', hk⟩ := exec_ren hb hx E (fun _ => rfl)
  rw [hh] at h1
  refine .seq h1 ?_
  have hc := clr_exec b n E' H
  suffices e : callEnv E b n r = fun x => if b < x ∧ x ≤ b + n then 0 else E' x by rw [e]; exact hc
  funext x
  simp only [callEnv]
  by_cases hx0 : x = b
  · subst hx0
    rw [if_pos rfl, if_neg (by omega)]
    have := hE' 4; simp only [rho, show ¬ (4 < 4) from by omega, if_false, Nat.sub_self, Nat.add_zero] at this
    rw [this, h4]
  · rw [if_neg hx0]
    by_cases hr : b < x ∧ x ≤ b + n
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr]
      by_cases hlt : x < 4
      · -- a block variable: never assigned by the callee
        have := hE' x; simp only [rho, if_pos hlt] at this
        rw [this, BExec.env_keep hx (fun hm => by have := hlow x hm; omega)]
        show E x = E (rho b x); simp only [rho, if_pos hlt]
      · by_cases hhi : b + n < x
        · -- above the callee's range: not in the image of `rho b` for the variables the callee uses
          by_cases hin : ∃ v, rho b v = x
          · obtain ⟨v, hv⟩ := hin
            have hv' : 4 + n < v := by unfold rho at hv; split at hv <;> omega
            rw [← hv, hE' v, BExec.env_keep hx (fun hm => by
              have := BStmt.vltF_assigns hp v hm; omega)]
          · exact (hk x fun v hv => hin ⟨v, hv⟩).symm
        · exact (hk x fun v hv => by unfold rho at hv; split at hv <;> omega).symm

end Proven.Frontx

namespace Proven.Frontx
open Proven

/-- no store -/
def _root_.Proven.BStmt.roF : BStmt → Bool
  | .assign .. | .load .. | .mop .. => true
  | .store .. => false
  | .seq p q => p.roF && q.roF
  | .loop _ p => p.roF

theorem _root_.Proven.BExec.heap_roF {p : BStmt} {σ σ' : BState} (h : BExec p σ σ') (hr : p.roF = true) :
    σ'.heap = σ.heap := by
  induction h with
  | assign | load | loopF | mop => rfl
  | store => simp [BStmt.roF] at hr
  | seq _ _ ih1 ih2 =>
    simp only [BStmt.roF, Bool.and_eq_true] at hr; exact (ih2 hr.2).trans (ih1 hr.1)
  | loopT _ _ _ ih1 ih2 => exact (ih2 hr).trans (ih1 hr)

theorem renF_roF (b : Nat) : ∀ p : BStmt, (p.renF b).roF = p.roF
  | .assign .. | .load .. | .store .. | .mop .. => rfl
  | .seq p q => by simp only [BStmt.renF, BStmt.roF, renF_roF b p, renF_roF b q]
  | .loop _ p => by simp only [BStmt.renF, BStmt.roF, renF_roF b p]

theorem clr_roF (b : Nat) : ∀ n, (clr b n).roF = true
  | 0 => rfl
  | n + 1 => by simp only [clr, BStmt.roF, clr_roF b n, Bool.true_and]

theorem callP_roF (p : BStmt) (b n : Nat) (h : p.roF = true) : (callP p b n).roF = true := by
  simp only [callP, BStmt.roF, renF_roF, h, clr_roF, Bool.and_self]

theorem rho_lt {b n v : Nat} (hb : 4 ≤ b) (hv : v < 5 + n) : rho b v < b + n + 1 := by
  unfold rho; split <;> omega

theorem renF_vltF_e {b n m : Nat} (hb : 4 ≤ b) (hm : b + n + 1 ≤ m) : ∀ e : BExp, e.vltF (5 + n) = true →
    (e.renF b).vltF m = true
  | .var i, h => by
    simp only [BExp.vltF, decide_eq_true_eq] at h
    simp only [BExp.renF, BExp.vltF, decide_eq_true_eq]; have := rho_lt (b := b) hb h; omega
  | .const _, _ => rfl
  | .bin _ x y, h => by
    simp only [BExp.vltF, Bool.and_eq_true] at h
    simp only [BExp.renF, BExp.vltF, renF_vltF_e hb hm x h.1, renF_vltF_e hb hm y h.2, Bool.and_self]
  | .ite c x y, h => by
    simp only [BExp.vltF, Bool.and_eq_true] at h
    simp only [BExp.renF, BExp.vltF, renF_vltF_e hb hm c h.1.1, renF_vltF_e hb hm x h.1.2,
      renF_vltF_e hb hm y h.2, Bool.and_self]

theorem renF_vltF {b n m : Nat} (hb : 4 ≤ b) (hm : b + n + 1 ≤ m) : ∀ p : BStmt, p.vltF (5 + n) = true →
    (p.renF b).vltF m = true
  | .assign v e, h | .load v _ e, h => by
    simp only [BStmt.vltF, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [BStmt.renF, BStmt.vltF, renF_vltF_e hb hm e h.2, Bool.and_true, decide_eq_true_eq]
    have := rho_lt (b := b) hb h.1; omega
  | .store _ i e, h => by
    simp only [BStmt.vltF, Bool.and_eq_true] at h
    simp only [BStmt.renF, BStmt.vltF, renF_vltF_e hb hm i h.1, renF_vltF_e hb hm e h.2, Bool.and_self]
  | .mop _ v x y, h => by
    simp only [BStmt.vltF, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [BStmt.renF, BStmt.vltF, renF_vltF_e hb hm x h.1.2, renF_vltF_e hb hm y h.2, Bool.and_true,
      decide_eq_true_eq]
    have := rho_lt (b := b) hb h.1.1; omega
  | .seq p q, h => by
    simp only [BStmt.vltF, Bool.and_eq_true] at h
    simp only [BStmt.renF, BStmt.vltF, renF_vltF hb hm p h.1, renF_vltF hb hm q h.2, Bool.and_self]
  | .loop c p, h => by
    simp only [BStmt.vltF, Bool.and_eq_true] at h
    simp only [BStmt.renF, BStmt.vltF, renF_vltF_e hb hm c h.1, renF_vltF hb hm p h.2, Bool.and_self]

theorem clr_vltF {b m : Nat} : ∀ n, b + n + 1 ≤ m → (clr b n).vltF m = true
  | 0, h => by simp only [clr, BStmt.vltF, BExp.vltF, decide_eq_true_eq, Bool.and_self]; omega
  | n + 1, h => by
    simp only [clr, BStmt.vltF, BExp.vltF, clr_vltF (b := b) (m := m) n (by omega), Bool.and_true, Bool.true_and, decide_eq_true_eq]
    omega

/-- the variables of a call program are below `m` -/
@[simp] theorem callP_vltF {p : BStmt} {b n m : Nat} (hb : 4 ≤ b) (hm : b + n + 1 ≤ m) (hp : p.vltF (5 + n) = true) :
    (callP p b n).vltF m = true := by
  simp only [callP, BStmt.vltF, renF_vltF hb hm p hp, clr_vltF n hm, Bool.and_self]

end Proven.Frontx

/-! ## Multiply / divide / remainder (NOTES section 22): one `BStmt.mop`, the division guarded -/

namespace Proven.Frontx
open Proven

/-- the value `mopS` leaves: Lean's `BitVec` operation (`x / 0 = 0`, `x % 0 = x`) -/
def mopV : Mach.MOp → BitVec 64 → BitVec 64 → BitVec 64
  | .mul, x, y => x * y
  | .divu, x, y => x / y
  | .remu, x, y => x % y

/-- `v := a m b`; for `divu` the machine's all-ones quotient by zero is replaced by `0` -/
def mopS (m : Mach.MOp) (v : Nat) (a b : BExp) : BStmt :=
  match m with
  | .divu => .seq (.mop .divu v a b) (.assign v (.ite (.bin .eq b (.const 0)) (.const 0) (.var v)))
  | _ => .mop m v a b

theorem mopS_exec (m : Mach.MOp) (v : Nat) (a b : BExp) (hb : b.vltF v = true) (E : BEnv) (H : Heap) :
    BExec (mopS m v a b) ⟨E, H⟩ ⟨E.set v (mopV m (a.denote E) (b.denote E)), H⟩ := by
  cases m with
  | mul => exact .mop
  | remu => exact .mop
  | divu =>
    refine .seq .mop (BExec.assign' ?_)
    have hb' : b.denote (E.set v (Mach.MOp.eval .divu (a.denote E) (b.denote E))) = b.denote E :=
      BExp.denote_agreeF (m := v) (fun x hx => by simp [BEnv.set, Nat.ne_of_lt hx]) b hb
    simp only [BState.mk.injEq, and_true]
    funext x
    simp only [BEnv.set, BExp.denote, Op.eval, hb']
    split
    · subst x; simp only [if_true, mopV, Mach.MOp.eval]
      by_cases h0 : b.denote E = 0
      · rw [if_pos h0, if_pos h0, if_neg (by decide), h0]; exact BitVec.udiv_zero
      · rw [if_neg h0, if_neg h0, if_pos rfl]
    · rfl

theorem mopS_vltF (m : Mach.MOp) (v M : Nat) (a b : BExp) (hv : v < M) (ha : a.vltF M = true) (hb : b.vltF M = true) :
    (mopS m v a b).vltF M = true := by
  cases m <;> simp [mopS, BStmt.vltF, BExp.vltF, hv, ha, hb]

@[simp] theorem vltF_var' (i m : Nat) : (BExp.var i).vltF m = decide (i < m) := rfl
@[simp] theorem vltF_const' (c : BitVec 64) (m : Nat) : (BExp.const c).vltF m = true := rfl
@[simp] theorem vltF_bin' (op : Op) (a b : BExp) (m : Nat) : (BExp.bin op a b).vltF m = (a.vltF m && b.vltF m) := rfl
@[simp] theorem vltF_ite' (c a b : BExp) (m : Nat) : (BExp.ite c a b).vltF m = (c.vltF m && a.vltF m && b.vltF m) := rfl

@[simp] theorem mopS_vltF_eq (m : Mach.MOp) (v M : Nat) (a b : BExp) :
    (mopS m v a b).vltF M = (decide (v < M) && a.vltF M && b.vltF M) := by
  cases m <;> simp only [mopS, BStmt.vltF, BExp.vltF] <;>
    cases decide (v < M) <;> cases a.vltF M <;> cases b.vltF M <;> rfl

@[simp] theorem mopS_roF (m : Mach.MOp) (v : Nat) (a b : BExp) : (mopS m v a b).roF = true := by
  cases m <;> rfl

theorem mopV_mul (x y : BitVec 64) : mopV .mul x y = x * y := rfl
theorem mopV_divu (x y : BitVec 64) : mopV .divu x y = x / y := rfl
theorem mopV_remu (x y : BitVec 64) : mopV .remu x y = x % y := rfl

end Proven.Frontx
