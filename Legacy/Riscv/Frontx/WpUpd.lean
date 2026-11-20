/- Paged dynamic arrays (NOTES section 30), part 5: in-place updates of a paged array (`set!`, `push`, `if`).

As in `WaUpd.lean`, an update `A` at a `call` leaf is compiled in two phases: `A.preP` evaluates every index and
value into temporaries `e ..` (the same `A.Tmps`), then `A.stP` does the stores.  A `set!` checks `i < size`
(as `Array.set!`); a `push` takes a page from the pool when the size is a multiple of `P` (`pushEl`).  Every
store step after the first runs only while `vOk = 1`: once a push found no page, nothing more is stored.

The page events of an update (`A.evs`): one `alloc 1` per push onto a full last page. -/
import Legacy.Riscv.Frontx.WpEv

namespace Proven.WA
open Proven Proven.WP Proven.Top.Alloc
open Proven.Frontx (rN rN_toNat rN_lt rN_add rN_inj rB)

/-! ## Elements after `push` and `set!` -/

theorem arr_get_push {α : Type} [Inhabited α] (a : Array α) (x : α) (j : Nat) :
    (a.push x)[j]! = if j < a.size then a[j]! else if j = a.size then x else default := by
  by_cases h : j < a.size
  · rw [if_pos h]; simp [getElem!_def, Array.getElem?_push, h, Nat.ne_of_lt h]
  · rw [if_neg h]; by_cases h2 : j = a.size
    · subst h2; simp
    · rw [if_neg h2]; simp [getElem!_def, Array.getElem?_push, h2]; rw [Array.getElem?_eq_none (by omega)]

theorem AK.size_push : ∀ (k : AK) (a : k.T) (x : k.el.T), AK.size k (AK.push k a x) = AK.size k a + 1
  | .ba, a, x => by show (a.data.push x).size = a.data.size + 1; exact Array.size_push ..
  | .arr .u8, _, _ | .arr .u16, _, _ | .arr .u32, _, _ | .arr .u64, _, _ | .arr .nat, _, _
  | .arr .bool, _, _ | .arr .int, _, _ => by exact Array.size_push ..

theorem AK.get_push : ∀ (k : AK) (a : k.T) (x : k.el.T) (j : Nat),
    AK.get k (AK.push k a x) j = if j < AK.size k a then AK.get k a j else if j = AK.size k a then x else default
  | .ba, a, x, j => by
    show (a.push x)[j]! = if j < a.size then a[j]! else if j = a.size then x else default
    rw [← AK.get_set_eq.ba_data_get', ← AK.get_set_eq.ba_data_get']
    exact arr_get_push a.data x j
  | .arr .u8, a, x, j | .arr .u16, a, x, j | .arr .u32, a, x, j | .arr .u64, a, x, j | .arr .nat, a, x, j
  | .arr .bool, a, x, j | .arr .int, a, x, j => arr_get_push a x j

theorem words_push (k : AK) (a : k.T) (x : k.el.T) : words k (AK.push k a x) = words k a ++ [k.el.rep x] := by
  apply List.ext_getElem?; intro j
  by_cases h : j < AK.size k a
  · rw [List.getElem?_append_left (by rw [words_length]; exact h), words_get k _ h,
      words_get k _ (by rw [AK.size_push]; omega)]
    simp only [AK.w, AK.get_push, if_pos h]
  · by_cases h2 : j = AK.size k a
    · subst h2
      rw [List.getElem?_append_right (by rw [words_length]; exact Nat.le_refl _), words_length, Nat.sub_self,
        words_get k _ (by rw [AK.size_push]; omega)]
      simp only [AK.w, AK.get_push, if_neg h, if_true]; rfl
    · rw [List.getElem?_eq_none (by rw [words_length, AK.size_push]; omega),
        List.getElem?_eq_none (by simp [words_length]; omega)]

theorem words_set (k : AK) (a : k.T) (i : Nat) (x : k.el.T) (h : i < AK.size k a) :
    words k (AK.set k a i x) = (words k a).set i (k.el.rep x) := by
  apply List.ext_getElem?; intro j
  rw [List.getElem?_set]
  by_cases hj : j < AK.size k a
  · rw [words_get k _ (by rw [AK.size_set]; exact hj), words_get k _ hj]
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, if_pos (by rw [words_length]; exact h)]
      simp only [AK.w, AK.get_set_eq k a i x h]
    · rw [if_neg hij]; simp only [AK.w, AK.get_set_ne k a i j x (Ne.symm hij)]
  · rw [List.getElem?_eq_none (by rw [words_length, AK.size_set]; omega)]
    split
    · omega
    · rw [List.getElem?_eq_none (by rw [words_length]; omega)]

/-! ## The two phases -/

def A.preP (L : List PLoc) {Γ : List Sl} {k : AK} : A Γ k → Nat → MS
  | .var _, e => skipAt e
  | .set a i x, e => .seq (a.preP L e) (.seq (E.compP L i (e + a.nt)) (E.compP L x (e + a.nt + 1)))
  | .push a x, e => .seq (a.preP L e) (E.compP L x (e + a.nt))
  | .ite c a b, e =>
    .seq (E.compP L c e) (.seq (.assign (e + 1) (.bin .eq (.var e) (.const 0)))
      (.seq (.assign (e + 2) (.var e)) (.seq (.assign (e + 3) (.var (e + 1)))
        (.seq (when e (a.preP L (e + 4))) (when (e + 1) (b.preP L (e + 4 + a.nt)))))))

/-- the stores into the array at `l` (scratch variables `sc ..`) -/
def A.stP (l : PLoc) (sc : Nat) {Γ : List Sl} {k : AK} : A Γ k → Nat → MS
  | .var _, _ => .assign l.v (.var l.v)
  | .set a _ _, e => .seq (a.stP l sc e) (.seq
      (.assign sc (.bin .and (.bin .ult (.var (e + a.nt)) (.var l.v)) (.var vOk)))
      (when sc (setEl l.pt (e + a.nt) (e + a.nt + 1) (sc + 1))))
  | .push a _, e => .seq (a.stP l sc e) (.seq (.assign sc (.var vOk)) (when sc (pushEl l.pt l.v (e + a.nt) (sc + 1))))
  | .ite _ a b, e => .seq (when (e + 2) (a.stP l sc (e + 4))) (when (e + 3) (b.stP l sc (e + 4 + a.nt)))

def A.wfP (L : List PLoc) {Γ : List Sl} {k : AK} : A Γ k → Bool
  | .var _ => true
  | .set a i x => a.wfP L && E.wfP L i && E.wfP L x
  | .push a x => a.wfP L && E.wfP L x
  | .ite c a b => E.wfP L c && a.wfP L && b.wfP L && a.base.idx == b.base.idx

def A.okP {Γ : List Sl} {k : AK} : A Γ k → Vals Γ → Prop
  | .var _, _ => True
  | .set a i x, v => a.okP v ∧ E.ok i v ∧ E.ok x v ∧ @LT.lt Nat _ (i.den v) (2 ^ 64)
  | .push a x, v => a.okP v ∧ E.ok x v ∧ AK.size k (a.den v) < P * P
  | .ite c a b, v => E.ok c v ∧ if c.den v = true then a.okP v else b.okP v

/-- the page events of an update -/
def A.evs {Γ : List Sl} {k : AK} : A Γ k → Vals Γ → List MemEvent
  | .var _, _ => []
  | .set a _ _, v => a.evs v
  | .push a _, v => a.evs v ++ (if AK.size k (a.den v) % P = 0 then [.alloc 1] else [])
  | .ite c a b, v => if c.den v = true then a.evs v else b.evs v

set_option maxHeartbeats 1000000 in
theorem A.preP_ok (L : List PLoc) {Γ : List Sl} {k : AK} : ∀ (a : A Γ k) (v : Vals Γ) (σ : MSt) (e : Nat),
    EnvOK Γ L v σ → Γ.length ≤ L.length → BelowP L e → a.wfP L = true → a.okP v →
    ∃ σ', Mach.BExec (a.preP L e) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap ∧
      (∀ j, j < e → σ'.env j = σ.env j) ∧ a.Tmps σ' v e
  | .var _, v, σ, e, _, _, _, _, _ => by
    simp only [A.preP]
    exact ⟨_, .assign, rfl, rfl, fun j hj => set_ne (by omega), trivial⟩
  | .set a i x, v, σ, e, hR, hl, hb, hwf, hok => by
    simp only [A.wfP, Bool.and_eq_true] at hwf; simp only [A.okP] at hok
    simp only [A.preP]
    obtain ⟨σ1, e1, h1, w1, k1, t1⟩ := A.preP_ok L a v σ e hR hl hb hwf.1.1 hok.1
    have r1 := hR.frame hb k1 h1 w1
    obtain ⟨σ2, e2, v2, k2, h2, w2, r2⟩ := (E.compP_ok L i v σ1 (e + a.nt) r1 hl (hb.mono (by omega)) hwf.1.2
      hok.2.1).frameP r1 (hb.mono (by omega)) hl
    obtain ⟨σ3, e3, v3, k3, h3, w3, r3⟩ := (E.compP_ok L x v σ2 (e + a.nt + 1) r2 hl (hb.mono (by omega)) hwf.2
      hok.2.2.1).frameP r2 (hb.mono (by omega)) hl
    refine ⟨σ3, .seq e1 (.seq e2 e3), by rw [h3, h2, h1], by rw [w3, w2, w1],
      fun j hj => by rw [k3 j (by omega), k2 j (by omega), k1 j hj], ?_⟩
    simp only [A.Tmps]
    refine ⟨A.Tmps.frame t1 fun j h1 h2 => by rw [k3 j (by omega), k2 j (by omega)], by rw [k3 _ (by omega)]; exact v2,
      v3⟩
  | .push a x, v, σ, e, hR, hl, hb, hwf, hok => by
    simp only [A.wfP, Bool.and_eq_true] at hwf; simp only [A.okP] at hok
    simp only [A.preP]
    obtain ⟨σ1, e1, h1, w1, k1, t1⟩ := A.preP_ok L a v σ e hR hl hb hwf.1 hok.1
    have r1 := hR.frame hb k1 h1 w1
    obtain ⟨σ2, e2, v2, k2, h2, w2, r2⟩ := (E.compP_ok L x v σ1 (e + a.nt) r1 hl (hb.mono (by omega)) hwf.2
      hok.2.1).frameP r1 (hb.mono (by omega)) hl
    refine ⟨σ2, .seq e1 e2, by rw [h2, h1], by rw [w2, w1], fun j hj => by rw [k2 j (by omega), k1 j hj], ?_⟩
    simp only [A.Tmps]
    exact ⟨A.Tmps.frame t1 fun j h1 h2 => by rw [k2 j (by omega)], v2⟩
  | .ite c a b, v, σ, e, hR, hl, hb, hwf, hok => by
    simp only [A.wfP, Bool.and_eq_true] at hwf; simp only [A.okP] at hok
    obtain ⟨⟨⟨hwc, hwa⟩, hwb⟩, _⟩ := hwf
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.compP_ok L c v σ e hR hl hb hwc hok.1).frameP hR hb hl
    let c0 := (Mach.BExp.bin .eq (.var e) (.const 0)).denote σ1.env
    let σ2 : MSt := ⟨σ1.env.set (e + 1) c0, σ1.heap, σ1.wheap⟩
    let σ3 : MSt := ⟨σ2.env.set (e + 2) (σ2.env e), σ2.heap, σ2.wheap⟩
    let σ4 : MSt := ⟨σ3.env.set (e + 3) (σ3.env (e + 1)), σ3.heap, σ3.wheap⟩
    have hc0 : c0 = rB (!c.den v) := by simp only [c0, Mach.BExp.denote, Op.eval, v1]; cases c.den v <;> rfl
    have k4 : ∀ j, j < e → σ4.env j = σ1.env j := fun j hj => by
      simp only [σ4, σ3, σ2, set_ne (show j ≠ e + 3 by omega), set_ne (show j ≠ e + 2 by omega),
        set_ne (show j ≠ e + 1 by omega)]
    have r4 : EnvOK Γ L v σ4 := r1.frame hb k4 rfl rfl
    have v4e : σ4.env e = rB (c.den v) := by
      simp only [σ4, σ3, σ2, set_ne (show e ≠ e + 3 by omega), set_ne (show e ≠ e + 2 by omega),
        set_ne (show e ≠ e + 1 by omega)]; exact v1
    have v41 : σ4.env (e + 1) = rB (!c.den v) := by
      simp only [σ4, σ3, σ2, set_ne (show e + 1 ≠ e + 3 by omega), set_ne (show e + 1 ≠ e + 2 by omega), set_eq]
      exact hc0
    have v42 : σ4.env (e + 2) = rB (c.den v) := by
      simp only [σ4, σ3, σ2, set_ne (show e + 2 ≠ e + 3 by omega), set_eq, set_ne (show e ≠ e + 1 by omega)]; exact v1
    have v43 : σ4.env (e + 3) = rB (!c.den v) := by
      simp only [σ4, σ3, σ2, set_eq, set_ne (show e + 1 ≠ e + 2 by omega)]; exact hc0
    simp only [A.preP]
    cases hcv : c.den v with
    | true =>
      have hoa := hok.2; rw [hcv, if_pos rfl] at hoa
      obtain ⟨σ5, e5, h5, w5, k5, t5⟩ := A.preP_ok L a v σ4 (e + 4) r4 hl (hb.mono (by omega)) hwa hoa
      have hne : σ4.env e ≠ 0 := by rw [v4e, hcv]; decide
      let σ6 : MSt := ⟨σ5.env.set e 0, σ5.heap, σ5.wheap⟩
      have hz : σ6.env (e + 1) = 0 := by
        simp only [σ6, set_ne (show e + 1 ≠ e by omega)]; rw [k5 _ (by omega), v41, hcv]; rfl
      refine ⟨σ6, .seq e1 (.seq .assign (.seq .assign (.seq .assign (.seq (when_true hne e5) (when_false hz))))),
        by simp only [σ6]; rw [h5]; simp only [σ4, σ3, σ2]; rw [h1],
        by simp only [σ6]; rw [w5]; simp only [σ4, σ3, σ2]; rw [w1], fun j hj => ?_, ?_⟩
      · simp only [σ6, set_ne (show j ≠ e by omega)]; rw [k5 j (by omega), k4 j hj, k1 j hj]
      · simp only [A.Tmps, hcv, if_true, Bool.not_true]
        refine ⟨?_, ?_, A.Tmps.frame t5 fun j h1 h2 => by simp only [σ6, set_ne (show j ≠ e by omega)]⟩
        · simp only [σ6, set_ne (show e + 2 ≠ e by omega)]; rw [k5 _ (by omega), v42, hcv]
        · simp only [σ6, set_ne (show e + 3 ≠ e by omega)]; rw [k5 _ (by omega), v43, hcv]; rfl
    | false =>
      have hob := hok.2; rw [hcv] at hob; simp only [Bool.false_eq_true, if_false] at hob
      obtain ⟨σ5, e5, h5, w5, k5, t5⟩ := A.preP_ok L b v σ4 (e + 4 + a.nt) r4 hl (hb.mono (by omega)) hwb hob
      have hz : σ4.env e = 0 := by rw [v4e, hcv]; rfl
      have hne : σ4.env (e + 1) ≠ 0 := by rw [v41, hcv]; decide
      refine ⟨_, .seq e1 (.seq .assign (.seq .assign (.seq .assign (.seq (when_false hz) (when_true hne e5))))),
        by simp only; rw [h5]; simp only [σ4, σ3, σ2]; rw [h1],
        by simp only; rw [w5]; simp only [σ4, σ3, σ2]; rw [w1], fun j hj => ?_, ?_⟩
      · simp only [set_ne (show j ≠ e + 1 by omega)]; rw [k5 j (by omega), k4 j hj, k1 j hj]
      · simp only [A.Tmps, hcv, Bool.false_eq_true, if_false, Bool.not_false]
        refine ⟨?_, ?_, A.Tmps.frame t5 fun j h1 h2 => by simp only [set_ne (show j ≠ e + 1 by omega)]⟩
        · simp only [set_ne (show e + 2 ≠ e + 1 by omega)]; rw [k5 _ (by omega), v42, hcv]
        · simp only [set_ne (show e + 3 ≠ e + 1 by omega)]; rw [k5 _ (by omega), v43, hcv]; rfl

/-! ## Store phase -/

/-- the branches of an `if` update the same array -/
def A.baseOK {Γ : List Sl} {k : AK} : A Γ k → Prop
  | .var _ => True
  | .set a _ _ => a.baseOK
  | .push a _ => a.baseOK
  | .ite _ a b => a.baseOK ∧ b.baseOK ∧ a.base.idx = b.base.idx

theorem A.baseOK_of_wf (L : List PLoc) {Γ : List Sl} {k : AK} : ∀ (a : A Γ k), a.wfP L = true → a.baseOK
  | .var _, _ => trivial
  | .set a _ _, h => by simp only [A.wfP, Bool.and_eq_true] at h; exact A.baseOK_of_wf L a h.1.1
  | .push a _, h => by simp only [A.wfP, Bool.and_eq_true] at h; exact A.baseOK_of_wf L a h.1
  | .ite _ a b, h => by
    simp only [A.wfP, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨A.baseOK_of_wf L a h.1.1.2, A.baseOK_of_wf L b h.1.2, h.2⟩

theorem pageCount_cons (a : Nat × W64) (as : List (Nat × W64)) :
    pageCount (a :: as) = 1 + npages a.2.length + pageCount as := by
  simp [pageCount]

theorem _root_.Proven.WP.Store.env {C : Nat} {env env' : Mach.BEnv} {W : W64} {arrs : List (Nat × W64)} (h : Store C env W arrs)
    (he : ∀ j, j = vCap ∨ j = vBump ∨ j = vFh → env' j = env j) : Store C env' W arrs :=
  ⟨h.1.frame he rfl (fun _ _ => rfl), h.2⟩

theorem _root_.Proven.WP.Store.count_le {C : Nat} {env : Mach.BEnv} {W : W64} {arrs : List (Nat × W64)} (h : Store C env W arrs) :
    pageCount arrs ≤ C := by rw [← owned_length]; exact h.1.length_le

theorem npages_push (n : Nat) : npages (n + 1) = npages n + (if n % P = 0 then 1 else 0) := by
  have hP : P = 1024 := rfl
  unfold npages; rw [hP]; split <;> omega

theorem pool_ne {j : Nat} (h : 8 ≤ j) : j ≠ vCap ∧ j ≠ vBump ∧ j ≠ vFh ∧ j ≠ vOk := by
  simp only [vCap, vBump, vFh, vOk]; omega

theorem pool_vars {j : Nat} (h : j = vCap ∨ j = vBump ∨ j = vFh) : j < 8 := by
  rcases h with rfl | rfl | rfl <;> decide

set_option maxHeartbeats 4000000 in
/-- **the stores of an update**: the array at `l` becomes `a.den v`, or a push found no page (`vOk = 0`,
exactly when the update's page events exceed `C`) -/
theorem A.stP_ok (l : PLoc) (sc : Nat) {Γ : List Sl} {k : AK} (C : Nat) (pt : Nat) (others : List (Nat × W64)) :
    ∀ (a : A Γ k) (v : Vals Γ) (σ : MSt) (e : Nat) (W : W64),
    σ.wheap = [W] → Store C σ.env W ((pt, words k (a.base.get v)) :: others) →
    σ.env l.pt = rN pt → σ.env l.v = rN (AK.size k (a.base.get v)) →
    a.Tmps σ v e → a.okP v → a.baseOK → σ.env vOk = 1 →
    8 ≤ l.v → 8 ≤ l.pt → l.v ≠ l.pt → l.v < e → l.pt < e → e + a.nt ≤ sc →
    ∃ σ' W', Mach.BExec (a.stP l sc e) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧
      (∀ j, (j < e ∨ (e + a.nt ≤ j ∧ j < sc)) → j ≠ l.v → j ≠ vFh → j ≠ vBump → j ≠ vOk → σ'.env j = σ.env j) ∧
      ((σ'.env vOk = 1 ∧ σ'.env l.v = rN (AK.size k (a.den v)) ∧
          Store C σ'.env W' ((pt, words k (a.den v)) :: others) ∧
          finE (pageCount ((pt, words k (a.base.get v)) :: others)) (a.evs v) =
            pageCount ((pt, words k (a.den v)) :: others) ∧
          pk (pageCount ((pt, words k (a.base.get v)) :: others)) (a.evs v) ≤ C) ∨
        (σ'.env vOk = 0 ∧ C < pk (pageCount ((pt, words k (a.base.get v)) :: others)) (a.evs v)))
  | .var m, v, σ, e, W, hW, hS, h1, h2, ht, hok, hbo, hok1, h8v, h8p, hvp, hve, hpe, hsc => by
    simp only [A.stP, A.base, A.den, A.evs]
    refine ⟨_, W, .assign, rfl, hW, fun j hj a b c d => by simp only [set_ne a], .inl ⟨?_, ?_, ?_, rfl, ?_⟩⟩
    · show (σ.env.set l.v _) vOk = 1; rw [set_ne (pool_ne h8v).2.2.2.symm]; exact hok1
    · simp only [set_eq, Mach.BExp.denote]; exact h2
    · exact hS.env fun j hj => set_ne (fun e => by have := pool_vars hj; omega)
    · exact hS.count_le
  | .set a i x, v, σ, e, W, hW, hS, h1, h2, ht, hok, hbo, hok1, h8v, h8p, hvp, hve, hpe, hsc => by
    simp only [A.stP, A.base, A.den, A.evs, A.okP, A.Tmps, A.nt] at *
    obtain ⟨t1, ti, tx⟩ := ht
    obtain ⟨σ1, W1, e1, hh1, hw1, k1, r1⟩ := A.stP_ok l sc C pt others a v σ e W hW hS h1 h2 t1 hok.1 hbo hok1
      h8v h8p hvp hve hpe (by omega)
    have ti1 : σ1.env (e + a.nt) = rN (i.den v) := by
      rw [k1 _ (.inr ⟨by omega, by omega⟩) (by omega) (by simp only [vFh]; omega) (by simp only [vBump]; omega)
        (by simp only [vOk]; omega)]; exact ti
    have tx1 : σ1.env (e + a.nt + 1) = k.el.rep (x.den v) := by
      rw [k1 _ (.inr ⟨by omega, by omega⟩) (by omega) (by simp only [vFh]; omega) (by simp only [vBump]; omega)
        (by simp only [vOk]; omega)]; exact tx
    have hpt1 : σ1.env l.pt = rN pt := by
      rw [k1 _ (.inl hpe) (Ne.symm hvp) (pool_ne h8p).2.2.1 (pool_ne h8p).2.1 (pool_ne h8p).2.2.2]; exact h1
    let c := (Mach.BExp.bin .and (.bin .ult (.var (e + a.nt)) (.var l.v)) (.var vOk)).denote σ1.env
    let σ2 : MSt := ⟨σ1.env.set sc c, σ1.heap, σ1.wheap⟩
    have hk2 : ∀ j, (j < e ∨ (e + a.nt + 2 ≤ j ∧ j < sc)) → j ≠ l.v → j ≠ vFh → j ≠ vBump → j ≠ vOk →
        σ2.env j = σ.env j := fun j a b c' d f => by
      simp only [σ2, set_ne (show j ≠ sc by omega)]; exact k1 j (by omega) b c' d f
    rcases r1 with ⟨ok1, sz1, S1, fin1, pk1⟩ | ⟨ok1, pk1⟩
    · have hsz := AK.size k (a.den v)
      by_cases hi : i.den v < AK.size k (a.den v)
      · have hc : c = 1 := by
          simp only [c, Mach.BExp.denote, Op.eval, ti1, sz1, ok1,
            rN_lt hok.2.2.2 (show AK.size k (a.den v) < 2 ^ 64 by
              have := S1.2 _ (List.mem_cons_self ..); have := this.len; rw [words_length] at this
              rw [P] at this; omega), if_pos hi]; decide
        have hnz : σ2.env sc ≠ 0 := by simp only [σ2, set_eq, hc]; decide
        have hA1 : ArrAt W1 pt (words k (a.den v)) := S1.2 _ (List.mem_cons_self ..)
        have hW32 := S1.1.wlen.2
        obtain ⟨W2, e3, hl2, hw2, hA2, hpg2⟩ := setEl_ok hA1 σ2.heap σ2.env l.pt (e + a.nt) (e + a.nt + 1) (sc + 1)
          ⟨by omega, by omega, by omega⟩ (by simp only [σ2, set_ne (show l.pt ≠ sc by omega)]; exact hpt1) (i.den v)
          (by simp only [σ2, set_ne (show e + a.nt ≠ sc by omega)]; exact ti1)
          (by rw [words_length]; exact hi) hW32
        rw [show σ2.env (e + a.nt + 1) = k.el.rep (x.den v) by
          simp only [σ2, set_ne (show e + a.nt + 1 ≠ sc by omega)]; exact tx1] at hA2 hpg2
        have hw := when_true (σ := ⟨σ2.env, σ2.heap, [W1]⟩) hnz e3
        rw [← words_set k _ _ _ hi] at hA2 hpg2
        refine ⟨_, W2, .seq e1 (.seq .assign (by simpa [σ2, hw1] using hw)), by simp [σ2, hh1], rfl,
          fun j a b c' d f => ?_, .inl ⟨?_, ?_, ?_, ?_, ?_⟩⟩
        · have := hk2 j (by omega) b c' d f
          simp only [σ2, set_ne (show j ≠ sc by omega), set_ne (show j ≠ sc + 1 by omega)] at this ⊢; exact this
        · simp only [set_ne (show vOk ≠ sc by simp only [vOk]; omega), set_ne (show vOk ≠ sc + 1 by simp only [vOk]; omega),
            σ2]; exact ok1
        · simp only [set_ne (show l.v ≠ sc by omega), set_ne (show l.v ≠ sc + 1 by omega), σ2, AK.size_set]; exact sz1
        · have := Store.write (pre := []) (env' := ((σ2.env.set (sc + 1) (rN (ent W1 pt (i.den v / P)))).set sc 0))
            S1 (fun j hj => by
              have := pool_vars hj
              simp only [σ2, set_ne (show j ≠ sc by omega), set_ne (show j ≠ sc + 1 by omega)]) hl2 hw2 hA2
            (by simp only [words_length, AK.size_set] at hpg2 ⊢; exact hpg2)
          simpa using this
        · rw [fin1]; simp only [pageCount_cons, words_length, AK.size_set]
        · exact pk1
      · have hc : c = 0 := by
          simp only [c, Mach.BExp.denote, Op.eval, ti1, sz1, ok1,
            rN_lt hok.2.2.2 (show AK.size k (a.den v) < 2 ^ 64 by
              have := S1.2 _ (List.mem_cons_self ..); have := this.len; rw [words_length] at this
              rw [P] at this; omega), if_neg hi]; decide
        have hz : σ2.env sc = 0 := by simp only [σ2, set_eq, hc]
        rw [AK.set_oob k (a.den v) (i.den v) (x.den v) (Nat.le_of_not_lt hi)]
        refine ⟨_, W1, .seq e1 (.seq .assign (when_false hz)), by simp [σ2, hh1], by simp [σ2, hw1],
          fun j a b c' d f => hk2 j (by omega) b c' d f, .inl ⟨?_, ?_, ?_, fin1, pk1⟩⟩
        · simp only [σ2, set_ne (show vOk ≠ sc by simp only [vOk]; omega)]; exact ok1
        · simp only [σ2, set_ne (show l.v ≠ sc by omega)]; exact sz1
        · exact S1.env fun j hj => by have := pool_vars hj; simp only [σ2, set_ne (show j ≠ sc by omega)]
    · have hz : σ2.env sc = 0 := by
        simp only [σ2, set_eq, c, Mach.BExp.denote, Op.eval, ok1]; simp
      refine ⟨_, W1, .seq e1 (.seq .assign (when_false hz)), by simp [σ2, hh1], by simp [σ2, hw1],
        fun j a b c' d f => hk2 j (by omega) b c' d f, .inr ⟨?_, pk1⟩⟩
      simp only [σ2, set_ne (show vOk ≠ sc by simp only [vOk]; omega)]; exact ok1
  | .push a x, v, σ, e, W, hW, hS, h1, h2, ht, hok, hbo, hok1, h8v, h8p, hvp, hve, hpe, hsc => by
    simp only [A.stP, A.base, A.den, A.evs, A.okP, A.Tmps, A.nt] at *
    obtain ⟨t1, tx⟩ := ht
    obtain ⟨σ1, W1, e1, hh1, hw1, k1, r1⟩ := A.stP_ok l sc C pt others a v σ e W hW hS h1 h2 t1 hok.1 hbo hok1
      h8v h8p hvp hve hpe (by omega)
    have tx1 : σ1.env (e + a.nt) = k.el.rep (x.den v) := by
      rw [k1 _ (.inr ⟨by omega, by omega⟩) (by omega) (by simp only [vFh]; omega) (by simp only [vBump]; omega)
        (by simp only [vOk]; omega)]; exact tx
    have hpt1 : σ1.env l.pt = rN pt := by
      rw [k1 _ (.inl hpe) (Ne.symm hvp) (pool_ne h8p).2.2.1 (pool_ne h8p).2.1 (pool_ne h8p).2.2.2]; exact h1
    let σ2 : MSt := ⟨σ1.env.set sc (σ1.env vOk), σ1.heap, σ1.wheap⟩
    rcases r1 with ⟨ok1, sz1, S1, fin1, pk1⟩ | ⟨ok1, pk1⟩
    · have hnz : σ2.env sc ≠ 0 := by simp only [σ2, set_eq, ok1]; decide
      have S2 : Store C σ2.env W1 ((pt, words k (a.den v)) :: others) :=
        S1.env fun j hj => by have := pool_vars hj; simp only [σ2, set_ne (show j ≠ sc by omega)]
      obtain ⟨env3, W3, e3, k3, r3⟩ := pushEl_ok σ2.heap S2 l.pt l.v (e + a.nt) (sc + 1)
        ⟨h8p, h8v, by omega, by omega, by omega, by omega, hvp, by omega⟩
        (by simp only [σ2, set_ne (show l.pt ≠ sc by omega)]; exact hpt1)
        (by simp only [σ2, set_ne (show l.v ≠ sc by omega)]; rw [words_length]; exact sz1)
        (by rw [words_length]; exact hok.2.2) (by simp only [σ2, set_ne (show vOk ≠ sc by simp only [vOk]; omega)]; exact ok1)
      have hw := when_true (σ := ⟨σ2.env, σ2.heap, [W1]⟩) hnz e3
      have hxv : σ2.env (e + a.nt) = k.el.rep (x.den v) := by
        simp only [σ2, set_ne (show e + a.nt ≠ sc by omega)]; exact tx1
      have hfin : finE (pageCount ((pt, words k ((a.base).get v)) :: others))
          (a.evs v ++ if AK.size k (a.den v) % P = 0 then [MemEvent.alloc 1] else []) =
          pageCount ((pt, words k (a.den v) ++ [k.el.rep (x.den v)]) :: others) := by
        rw [finE_append, fin1]
        simp only [pageCount_cons, List.length_append, List.length_cons, List.length_nil, words_length, npages_push]
        split <;> simp [finE, stepE] <;> omega
      refine ⟨_, W3, .seq e1 (.seq .assign (by simp [σ2, hw1]; exact hw)), by simp [σ2, hh1], rfl,
        fun j a b c' d f => ?_, ?_⟩
      · simp only [set_ne (show j ≠ sc by omega)]
        rw [k3 j b c' d f (by omega)]; simp only [σ2, set_ne (show j ≠ sc by omega)]
        exact k1 j (by omega) b c' d f
      · rcases r3 with ⟨ok3, sz3, S3⟩ | ⟨ok3, hm3, hc3⟩
        · refine .inl ⟨?_, ?_, ?_, ?_, ?_⟩
          · simp only [set_ne (show vOk ≠ sc by simp only [vOk]; omega)]; exact ok3
          · simp only [set_ne (show l.v ≠ sc by omega)]; rw [sz3, words_length, AK.size_push]
          · rw [words_push, ← hxv]
            exact S3.env fun j hj => by have := pool_vars hj; simp only [set_ne (show j ≠ sc by omega)]
          · rw [words_push, hfin]
          · have hle := S3.count_le
            rw [hxv] at hle
            split
            · rw [pk_alloc1]; refine Nat.max_le.2 ⟨pk1, ?_⟩
              rw [fin1]; simp only [pageCount_cons, List.length_append, List.length_cons, List.length_nil,
                words_length, npages_push] at hle ⊢
              rename_i hm; rw [if_pos hm] at hle; omega
            · simpa using pk1
        · refine .inr ⟨by simp only [set_ne (show vOk ≠ sc by simp only [vOk]; omega)]; exact ok3, ?_⟩
          rw [words_length] at hm3
          rw [if_pos hm3, pk_alloc1, fin1, hc3]; omega
    · have hz : σ2.env sc = 0 := by simp only [σ2, set_eq, ok1]
      refine ⟨_, W1, .seq e1 (.seq .assign (when_false hz)), by simp [σ2, hh1], by simp [σ2, hw1],
        fun j a b c' d f => ?_, .inr ⟨?_, Nat.lt_of_lt_of_le pk1 (pk_mono_left _ _ _)⟩⟩
      · simp only [σ2, set_ne (show j ≠ sc by omega)]; exact k1 j (by omega) b c' d f
      · simp only [σ2, set_ne (show vOk ≠ sc by simp only [vOk]; omega)]; exact ok1
  | .ite c a b, v, σ, e, W, hW, hS, h1, h2, ht, hok, hbo, hok1, h8v, h8p, hvp, hve, hpe, hsc => by
    simp only [A.stP, A.okP, A.Tmps, A.nt, A.base, A.baseOK] at *
    obtain ⟨t2, t3, tb⟩ := ht
    obtain ⟨hba, hbb, hidx⟩ := hbo
    have hbe : b.base.get v = a.base.get v := (Mem.get_idx _ _ v hidx).symm
    cases hcv : c.den v with
    | true =>
      rw [hcv, if_pos rfl] at hok tb
      obtain ⟨σ1, W1, e1, hh1, hw1, k1, r1⟩ := A.stP_ok l sc C pt others a v σ (e + 4) W hW hS h1 h2 tb hok.2 hba
        hok1 h8v h8p hvp (by omega) (by omega) (by omega)
      have hne : σ.env (e + 2) ≠ 0 := by rw [t2, hcv]; decide
      have hw1' := when_true hne e1
      have hz : σ1.env (e + 3) = 0 := by
        rw [k1 _ (.inl (by omega)) (by omega) (by simp only [vFh]; omega) (by simp only [vBump]; omega)
          (by simp only [vOk]; omega), t3, hcv]; rfl
      refine ⟨_, W1, .seq hw1' (when_false (by simp only [set_ne (show e + 3 ≠ e + 2 by omega)]; exact hz)),
        hh1, hw1, fun j hj b' c' d f => ?_, ?_⟩
      · simp only [set_ne (show j ≠ e + 2 by omega)]; exact k1 j (by omega) b' c' d f
      · simp only [A.den, A.evs, hcv, if_true, set_ne (show vOk ≠ e + 2 by simp only [vOk]; omega),
          set_ne (show l.v ≠ e + 2 by omega)]
        rcases r1 with ⟨o, s', S, f', p⟩ | ⟨o, p⟩
        · exact .inl ⟨o, s', S.env fun j hj => by have := pool_vars hj; rw [set_ne (by omega)], f', p⟩
        · exact .inr ⟨o, p⟩
    | false =>
      rw [hcv] at hok tb; simp only [Bool.false_eq_true, if_false] at hok tb
      rw [← hbe] at hS h2
      have hne : σ.env (e + 3) ≠ 0 := by rw [t3, hcv]; decide
      have hz : σ.env (e + 2) = 0 := by rw [t2, hcv]; rfl
      obtain ⟨σ1, W1, e1, hh1, hw1, k1, r1⟩ := A.stP_ok l sc C pt others b v σ (e + 4 + a.nt) W hW hS h1 h2 tb hok.2
        hbb hok1 h8v h8p hvp (by omega) (by omega) (by omega)
      refine ⟨_, W1, .seq (when_false hz) (when_true hne e1), hh1, hw1, fun j hj b' c' d f => ?_, ?_⟩
      · simp only [set_ne (show j ≠ e + 3 by omega)]; exact k1 j (by omega) b' c' d f
      · simp only [A.den, A.evs, hcv, Bool.false_eq_true, if_false, set_ne (show vOk ≠ e + 3 by simp only [vOk]; omega),
          set_ne (show l.v ≠ e + 3 by omega)]
        rw [← hbe]
        rcases r1 with ⟨o, s', S, f', p⟩ | ⟨o, p⟩
        · exact .inl ⟨o, s', S.env fun j hj => by have := pool_vars hj; rw [set_ne (by omega)], f', p⟩
        · exact .inr ⟨o, p⟩

end Proven.WA
