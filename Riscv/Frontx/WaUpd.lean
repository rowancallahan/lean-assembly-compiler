/- Word arrays (NOTES section 20), compiler part 2b: in-place array updates (`A`: `set!` chains under `if`).

At a `call` leaf at most one array component is not its own slot unchanged; its update `A` is compiled in two
phases: `A.pre` evaluates every index and value (all in the old state) into temporaries `e, e + 1, ...`
(`A.nt` of them; an `if` evaluates only its taken branch), then `A.st` does the stores into the slot's words
(a `set!` checks `i < size` at run time, as `Array.set!` does). -/
import Riscv.Frontx.WaExp

namespace Proven.WA
open Proven Proven.Frontx

/-! ## `set!` on the array kinds -/

/-- Lean 4.34.1: `simp` does not see through `k.T` / `k.el.T` in the cases below; the array facts are stated at a
plain element type and applied by `exact` -/
private theorem arr_size_set {α : Type} (a : Array α) (i : Nat) (x : α) : (a.set! i x).size = a.size := by simp
private theorem arr_get_set_eq {α : Type} [Inhabited α] (a : Array α) (i : Nat) (x : α) (h : i < a.size) :
    (a.set! i x)[i]! = x := by simp [h]
private theorem arr_get_set_ne {α : Type} [Inhabited α] (a : Array α) (i j : Nat) (x : α) (h : j ≠ i) :
    (a.set! i x)[j]! = a[j]! := by simp [getElem!_def, Ne.symm h]

theorem AK.size_set : ∀ (k : AK) (a : k.T) (i : Nat) (x : k.el.T), AK.size k (AK.set k a i x) = AK.size k a
  | .ba, a, i, x => by show (a.data.set! i x).size = a.data.size; exact arr_size_set ..
  | .arr .u8, _, _, _ | .arr .u16, _, _, _ | .arr .u32, _, _, _ | .arr .u64, _, _, _ | .arr .nat, _, _, _
  | .arr .bool, _, _, _ | .arr .int, _, _, _ => by exact arr_size_set ..

theorem AK.get_set_eq : ∀ (k : AK) (a : k.T) (i : Nat) (x : k.el.T), i < AK.size k a →
    AK.get k (AK.set k a i x) i = x
  | .ba, a, i, x, h => by
    show (ByteArray.set! a i x)[i]! = x
    rw [← ba_data_get']; show (a.data.set! i x)[i]! = x; exact arr_get_set_eq _ _ _ h
  | .arr .u8, _, _, _, h | .arr .u16, _, _, _, h | .arr .u32, _, _, _, h | .arr .u64, _, _, _, h
  | .arr .nat, _, _, _, h | .arr .bool, _, _, _, h | .arr .int, _, _, _, h => by exact arr_get_set_eq _ _ _ h
where
  ba_data_get' (xs : ByteArray) (j : Nat) : xs.data[j]! = xs[j]! := by
    by_cases h : j < xs.size
    · rw [getElem!_pos xs j h, getElem!_pos xs.data j h]; rfl
    · rw [getElem!_neg xs j h, getElem!_neg xs.data j h]

theorem AK.get_set_ne : ∀ (k : AK) (a : k.T) (i j : Nat) (x : k.el.T), j ≠ i →
    AK.get k (AK.set k a i x) j = AK.get k a j
  | .ba, a, i, j, x, h => by
    show (ByteArray.set! a i x)[j]! = a[j]!
    rw [← AK.get_set_eq.ba_data_get', ← AK.get_set_eq.ba_data_get']
    show (a.data.set! i x)[j]! = a.data[j]!; exact arr_get_set_ne _ _ _ _ h
  | .arr .u8, _, _, _, _, h | .arr .u16, _, _, _, _, h | .arr .u32, _, _, _, _, h | .arr .u64, _, _, _, _, h
  | .arr .nat, _, _, _, _, h | .arr .bool, _, _, _, _, h | .arr .int, _, _, _, _, h => by exact arr_get_set_ne _ _ _ _ h

theorem AK.set_oob : ∀ (k : AK) (a : k.T) (i : Nat) (x : k.el.T), AK.size k a ≤ i → AK.set k a i x = a
  | .ba, a, i, x, h => by
    simp only [AK.size] at h
    show ByteArray.mk (a.data.set! i x) = a
    have : a.data.set! i x = a.data := by
      simp only [Array.set!, Array.setIfInBounds]; rw [dif_neg (by show ¬ i < a.data.size; exact Nat.not_lt.2 h)]
    rw [this]
  | .arr .u8, a, i, _, h | .arr .u16, a, i, _, h | .arr .u32, a, i, _, h | .arr .u64, a, i, _, h
  | .arr .nat, a, i, _, h | .arr .bool, a, i, _, h | .arr .int, a, i, _, h => by
    simp only [AK.size] at h
    simp only [AK.set, Array.set!, Array.setIfInBounds]; rw [dif_neg (Nat.not_lt.2 h)]

theorem store64_at {σ : MSt} {W : List (BitVec 64)} (hW : σ.wheap = [W]) (i e : MB) (p : Nat)
    (hp : (i.denote σ.env).toNat = p) (hpl : p < W.length) :
    Mach.BExec (.store64 0 i e) σ ⟨σ.env, σ.heap, [W.set p (e.denote σ.env)]⟩ := by
  have := Mach.BExec.store64 (b := 0) (i := i) (e := e) (σ := σ) (by rw [hW]; simp)
    (by simp only [hW, List.getElem_cons_zero, hp]; exact hpl)
  simp only [hW, List.getElem_cons_zero, hp, List.set_cons_zero] at this
  exact this

/-! ## The two phases -/

def A.nt {Γ : List Sl} {k : AK} : A Γ k → Nat
  | .var _ => 0
  | .set a _ _ => a.nt + 2
  | .push a _ => a.nt + 1
  | .ite _ a b => 4 + a.nt + b.nt

/-- the array at the bottom of an update -/
def A.base {Γ : List Sl} {k : AK} : A Γ k → Mem Γ (.ar k)
  | .var m => m
  | .set a _ _ => a.base
  | .push a _ => a.base
  | .ite _ a _ => a.base

def A.pre (L : List Loc) {Γ : List Sl} {k : AK} : A Γ k → Nat → MS
  | .var _, e => skipAt e
  | .set a i x, e => .seq (a.pre L e) (.seq (E.comp L i (e + a.nt)) (E.comp L x (e + a.nt + 1)))
  | .push a x, e => .seq (a.pre L e) (E.comp L x (e + a.nt))
  | .ite c a b, e =>
    .seq (E.comp L c e) (.seq (.assign (e + 1) (.bin .eq (.var e) (.const 0)))
      (.seq (.assign (e + 2) (.var e)) (.seq (.assign (e + 3) (.var (e + 1)))
        (.seq (when e (a.pre L (e + 4))) (when (e + 1) (b.pre L (e + 4 + a.nt)))))))

/-- the stores into the words of `l`; `sc` is a scratch variable -/
def A.st (l : Loc) (sc : Nat) {Γ : List Sl} {k : AK} : A Γ k → Nat → MS
  | .var _, _ => .assign l.v (.var l.v)
  | .set a _ _, e => .seq (a.st l sc e) (.seq (.assign sc (.bin .ult (.var (e + a.nt)) (.var l.v)))
      (when sc (.store64 0 (.bin .add (.var (e + a.nt)) (.const (BitVec.ofNat 64 l.off))) (.var (e + a.nt + 1)))))
  | .push a _, e => a.st l sc e
  | .ite _ a b, e => .seq (when (e + 2) (a.st l sc (e + 4))) (when (e + 3) (b.st l sc (e + 4 + a.nt)))

def A.wf (L : List Loc) {Γ : List Sl} {k : AK} : A Γ k → Bool
  | .var _ => true
  | .set a i x => a.wf L && E.wf L i && E.wf L x
  | .push _ _ => false
  | .ite c a b => E.wf L c && a.wf L && b.wf L && a.base.idx == b.base.idx

def A.ok {Γ : List Sl} {k : AK} : A Γ k → Vals Γ → Prop
  | .var _, _ => True
  | .set a i x, v => a.ok v ∧ E.ok i v ∧ E.ok x v ∧ @LT.lt Nat _ (i.den v) (2 ^ 64)
  | .push _ _, _ => False
  | .ite c a b, v => E.ok c v ∧ if c.den v = true then a.ok v else b.ok v

/-- the temporaries hold the update's indices and values -/
def A.Tmps (σ : MSt) {Γ : List Sl} {k : AK} : A Γ k → Vals Γ → Nat → Prop
  | .var _, _, _ => True
  | .set a i x, v, e => a.Tmps σ v e ∧ σ.env (e + a.nt) = rN (i.den v) ∧ σ.env (e + a.nt + 1) = k.el.rep (x.den v)
  | .push a x, v, e => a.Tmps σ v e ∧ σ.env (e + a.nt) = k.el.rep (x.den v)
  | .ite c a b, v, e => σ.env (e + 2) = rB (c.den v) ∧ σ.env (e + 3) = rB (!c.den v) ∧
      if c.den v = true then a.Tmps σ v (e + 4) else b.Tmps σ v (e + 4 + a.nt)

theorem A.Tmps.frame {σ σ' : MSt} {Γ : List Sl} {k : AK} : ∀ {a : A Γ k} {v : Vals Γ} {e : Nat}, a.Tmps σ v e →
    (∀ j, e ≤ j → j < e + a.nt → σ'.env j = σ.env j) → a.Tmps σ' v e
  | .var _, _, _, _, _ => trivial
  | .set a i x, v, e, h, hf => by
    simp only [A.Tmps, A.nt] at h hf ⊢
    exact ⟨A.Tmps.frame h.1 fun j h1 h2 => hf j h1 (by omega), by rw [hf _ (by omega) (by omega)]; exact h.2.1,
      by rw [hf _ (by omega) (by omega)]; exact h.2.2⟩
  | .push a x, v, e, h, hf => by
    simp only [A.Tmps, A.nt] at h hf ⊢
    exact ⟨A.Tmps.frame h.1 fun j h1 h2 => hf j h1 (by omega), by rw [hf _ (by omega) (by omega)]; exact h.2⟩
  | .ite c a b, v, e, h, hf => by
    simp only [A.Tmps, A.nt] at h hf ⊢
    refine ⟨by rw [hf _ (by omega) (by omega)]; exact h.1, by rw [hf _ (by omega) (by omega)]; exact h.2.1, ?_⟩
    have h3 := h.2.2
    split at h3
    · rw [if_pos ‹_›]; exact A.Tmps.frame h3 fun j h1 h2 => hf j (by omega) (by omega)
    · rw [if_neg ‹_›]; exact A.Tmps.frame h3 fun j h1 h2 => hf j (by omega) (by omega)

set_option maxHeartbeats 1000000 in
theorem A.pre_ok (L : List Loc) {Γ : List Sl} {k : AK} : ∀ (a : A Γ k) (v : Vals Γ) (σ : MSt) (e : Nat),
    Rel Γ L v σ → Γ.length ≤ L.length → Below L e → a.wf L = true → a.ok v →
    ∃ σ', Mach.BExec (a.pre L e) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap ∧
      (∀ j, j < e → σ'.env j = σ.env j) ∧ a.Tmps σ' v e
  | .var _, v, σ, e, _, _, _, _, _ => by
    simp only [A.pre]
    exact ⟨_, .assign, rfl, rfl, fun j hj => set_ne (by omega), trivial⟩
  | .set a i x, v, σ, e, hR, hl, hb, hwf, hok => by
    simp only [A.wf, Bool.and_eq_true] at hwf; simp only [A.ok] at hok
    simp only [A.pre]
    obtain ⟨σ1, e1, h1, w1, k1, t1⟩ := A.pre_ok L a v σ e hR hl hb hwf.1.1 hok.1
    have r1 := Rel.below hR hb hl k1 h1 w1
    obtain ⟨σ2, e2, v2, k2, h2, w2, r2⟩ := (E.comp_ok L i v σ1 (e + a.nt) r1 hl (hb.mono (by omega)) hwf.1.2
      hok.2.1).frame r1 (hb.mono (by omega)) hl
    obtain ⟨σ3, e3, v3, k3, h3, w3, r3⟩ := (E.comp_ok L x v σ2 (e + a.nt + 1) r2 hl (hb.mono (by omega)) hwf.2
      hok.2.2.1).frame r2 (hb.mono (by omega)) hl
    refine ⟨σ3, .seq e1 (.seq e2 e3), by rw [h3, h2, h1], by rw [w3, w2, w1],
      fun j hj => by rw [k3 j (by omega), k2 j (by omega), k1 j hj], ?_⟩
    simp only [A.Tmps]
    refine ⟨A.Tmps.frame t1 fun j h1 h2 => by rw [k3 j (by omega), k2 j (by omega)], by rw [k3 _ (by omega)]; exact v2,
      v3⟩
  | .push _ _, _, _, _, _, _, _, _, hok => by simp [A.ok] at hok
  | .ite c a b, v, σ, e, hR, hl, hb, hwf, hok => by
    simp only [A.wf, Bool.and_eq_true] at hwf; simp only [A.ok] at hok
    obtain ⟨⟨⟨hwc, hwa⟩, hwb⟩, _⟩ := hwf
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.comp_ok L c v σ e hR hl hb hwc hok.1).frame hR hb hl
    let c0 := (Mach.BExp.bin .eq (.var e) (.const 0)).denote σ1.env
    let σ2 : MSt := ⟨σ1.env.set (e + 1) c0, σ1.heap, σ1.wheap⟩
    let σ3 : MSt := ⟨σ2.env.set (e + 2) (σ2.env e), σ2.heap, σ2.wheap⟩
    let σ4 : MSt := ⟨σ3.env.set (e + 3) (σ3.env (e + 1)), σ3.heap, σ3.wheap⟩
    have hc0 : c0 = rB (!c.den v) := by simp only [c0, Mach.BExp.denote, Op.eval, v1]; cases c.den v <;> rfl
    have k4 : ∀ j, j < e → σ4.env j = σ1.env j := fun j hj => by
      simp only [σ4, σ3, σ2, set_ne (show j ≠ e + 3 by omega), set_ne (show j ≠ e + 2 by omega),
        set_ne (show j ≠ e + 1 by omega)]
    have r4 : Rel Γ L v σ4 := Rel.below r1 hb hl k4 rfl rfl
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
    simp only [A.pre]
    cases hcv : c.den v with
    | true =>
      have hoa := hok.2; rw [hcv, if_pos rfl] at hoa
      obtain ⟨σ5, e5, h5, w5, k5, t5⟩ := A.pre_ok L a v σ4 (e + 4) r4 hl (hb.mono (by omega)) hwa hoa
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
      obtain ⟨σ5, e5, h5, w5, k5, t5⟩ := A.pre_ok L b v σ4 (e + 4 + a.nt) r4 hl (hb.mono (by omega)) hwb hob
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

theorem Mem.get_idx : ∀ {Γ : List Sl} {s : Sl} (m1 m2 : Mem Γ s) (v : Vals Γ), m1.idx = m2.idx → m1.get v = m2.get v
  | _, _, .hd, .hd, _, _ => rfl
  | _, _, .tl m1, .tl m2, v, h => by
    simp only [Mem.idx, Nat.add_right_cancel_iff] at h; exact Mem.get_idx m1 m2 v.2 h
  | _, _, .hd, .tl m2, _, h => by simp [Mem.idx] at h
  | _, _, .tl m1, .hd, _, h => by simp [Mem.idx] at h

/-- word `q` belongs to the words of `l` (none for the input or a scalar) -/
def Loc.inReg (l : Loc) (q : Nat) : Prop := l.inp = false ∧ l.off ≤ q ∧ ∀ c, l.cap = some c → q < l.off + c

/-- the words of `l1` and `l2` do not overlap -/
def Loc.sep (l1 l2 : Loc) : Bool :=
  l1.inp || l2.inp || (match l1.cap with | some c => decide (l1.off + c ≤ l2.off) | none => false) ||
    (match l2.cap with | some c => decide (l2.off + c ≤ l1.off) | none => false)

/-- the work words outside the words of `w` are kept -/
def WOut (w : Loc) (W W' : List (BitVec 64)) : Prop := W'.length = W.length ∧ ∀ q, ¬ w.inReg q → W'[q]? = W[q]?

theorem WOut.refl (w : Loc) (W : List (BitVec 64)) : WOut w W W := ⟨rfl, fun _ _ => rfl⟩
theorem WOut.trans {w : Loc} {W W1 W2 : List (BitVec 64)} (h1 : WOut w W W1) (h2 : WOut w W1 W2) : WOut w W W2 :=
  ⟨h2.1.trans h1.1, fun q hq => (h2.2 q hq).trans (h1.2 q hq)⟩

/-- a slot whose words are separate from `w` survives writes into `w` -/
theorem SR.wsep {σ σ' : MSt} {s : Sl} {l w : Loc} {x : s.T} {W W' : List (BitVec 64)} (h : SR σ s l x)
    (hv : σ'.env l.v = σ.env l.v) (hh : σ'.heap = σ.heap) (hW : σ.wheap = [W]) (hW' : σ'.wheap = [W'])
    (ho : WOut w W W') (hs : Loc.sep l w = true) : SR σ' s l x := by
  cases s with
  | sc t => show σ'.env l.v = _; rw [hv]; exact h
  | ar k =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by rw [hv]; exact h1, h2, ?_⟩
    unfold AR at h3 ⊢
    rw [hh, hW']; rw [hW] at h3
    split
    · rename_i hi; rw [if_pos hi] at h3; exact h3
    · rename_i hi; rw [if_neg hi] at h3
      simp only [List.getD_cons_zero] at h3 ⊢
      obtain ⟨a1, a2, a3, a4⟩ := h3
      refine ⟨by rw [ho.1]; exact a1, by rw [ho.1]; exact a2, a3, fun j hj => ?_⟩
      rw [ho.2 _ ?_]; exact a4 j hj
      rintro ⟨hw0, hw1, hw2⟩
      simp only [Loc.sep, Bool.or_eq_true, hi, Bool.false_eq_true, false_or, hw0] at hs
      rcases hs with hs | hs
      · split at hs
        · rename_i c hc; simp only [decide_eq_true_eq] at hs; have := a3 c hc; omega
        · cases hs
      · split at hs
        · rename_i c hc; simp only [decide_eq_true_eq] at hs; have := hw2 c hc; omega
        · cases hs

set_option maxHeartbeats 1000000 in
theorem A.st_ok (L : List Loc) (l : Loc) (sc : Nat) {Γ : List Sl} {k : AK} : ∀ (a : A Γ k) (v : Vals Γ) (σ : MSt)
    (e : Nat) (W : List (BitVec 64)), l.inp = false → l.v < e → e + a.nt ≤ sc → σ.wheap = [W] → a.wf L = true →
    a.Tmps σ v e → a.ok v → SR σ (.ar k) l (a.base.get v) →
    ∃ σ' W', Mach.BExec (a.st l sc e) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧ W'.length = W.length ∧
      (∀ q, ¬ l.inReg q → W'[q]? = W[q]?) ∧
      (∀ j, j ≠ l.v → j ≠ sc → (j < e ∨ e + a.nt ≤ j) → σ'.env j = σ.env j) ∧ SR σ' (.ar k) l (A.den a v)
  | .var m, v, σ, e, W, hin, hle, hsc, hW, _, _, _, hS => by
    simp only [A.st]
    refine ⟨_, W, .assign, rfl, hW, rfl, fun _ _ => rfl, fun j h1 _ _ => set_ne h1, ?_⟩
    refine SR.frame hS (by simp only [set_eq, Mach.BExp.denote]) rfl rfl
  | .set a i x, v, σ, e, W, hin, hle, hsc, hW, hwf, ht, hok, hS => by
    simp only [A.wf, Bool.and_eq_true] at hwf
    simp only [A.ok] at hok
    simp only [A.Tmps] at ht
    simp only [A.nt] at hsc
    simp only [A.st]
    obtain ⟨σ1, W1, e1, h1, w1, l1, o1, k1, s1⟩ := A.st_ok L l sc a v σ e W hin hle (by omega) hW hwf.1.1 ht.1 hok.1 hS
    obtain ⟨iv, hiv⟩ : ∃ iv : Nat, iv = i.den v := ⟨_, rfl⟩
    have hi64 : iv < 2 ^ 64 := by rw [hiv]; exact hok.2.2.2
    rw [← hiv] at ht
    have hi : σ1.env (e + a.nt) = rN iv := by rw [k1 _ (by omega) (by omega) (.inr (by omega))]; exact ht.2.1
    have hx : σ1.env (e + a.nt + 1) = k.el.rep (x.den v) := by
      rw [k1 _ (by omega) (by omega) (.inr (by omega))]; exact ht.2.2
    obtain ⟨hsz, h32, hA⟩ := s1.ar
    unfold AR at hA; rw [if_neg (by simp [hin])] at hA
    rw [w1] at hA; simp only [List.getD_cons_zero] at hA
    obtain ⟨a1, a2, a3, a4⟩ := hA
    let σ2 : MSt := ⟨σ1.env.set sc ((Mach.BExp.bin .ult (.var (e + a.nt)) (.var l.v)).denote σ1.env), σ1.heap,
      σ1.wheap⟩
    have hc : σ2.env sc = if iv < AK.size k (A.den a v) then 1#64 else 0#64 := by
      simp only [σ2, set_eq, Mach.BExp.denote, Op.eval, hi, hsz]
      simp only [rN_lt hi64 (by omega : AK.size k (A.den a v) < 2 ^ 64)]; rfl
    simp only [A.den]; rw [← hiv]
    by_cases hlt : iv < AK.size k (A.den a v)
    · have hne : σ2.env sc ≠ 0 := by rw [hc, if_pos hlt]; decide
      have e3 := store64_at (σ := σ2) w1 (.bin .add (.var (e + a.nt)) (.const (BitVec.ofNat 64 l.off)))
        (.var (e + a.nt + 1)) (l.off + iv)
        (by simp only [σ2, Mach.BExp.denote, Op.eval, set_ne (show e + a.nt ≠ sc by omega), hi, rN,
              BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by omega)
      refine ⟨_, _, .seq e1 (.seq .assign (when_true hne e3)), by rw [h1], rfl, by rw [List.length_set, l1],
        fun q hq => ?_, fun j h1' h2 h3 => ?_, ?_⟩
      · rw [List.getElem?_set_ne (fun h => hq ⟨hin, by omega, fun c hc => by have := a3 c hc; omega⟩)]; exact o1 q hq
      · simp only [set_ne h2, σ2]; exact k1 j h1' h2 (h3.elim .inl fun h => .inr (by simp only [A.nt] at h; omega))
      · refine ⟨by simp only [set_ne (show l.v ≠ sc by omega), σ2, AK.size_set]; exact hsz,
          by simp only [AK.size_set]; exact h32, ?_⟩
        unfold AR; rw [if_neg (by simp [hin])]
        simp only [List.getD_cons_zero, AK.size_set, List.length_set]
        refine ⟨a1, a2, a3, fun j hj => ?_⟩
        by_cases hji : j = iv
        · subst hji
          rw [List.getElem?_set_self (by omega)]
          simp only [AK.w, AK.get_set_eq k _ _ _ hlt, σ2, Mach.BExp.denote, set_ne (show e + a.nt + 1 ≠ sc by omega),
            hx]
        · rw [List.getElem?_set_ne (by omega), a4 j hj]
          simp only [AK.w, AK.get_set_ne k _ _ _ _ hji]
    · have hz : σ2.env sc = 0 := by rw [hc, if_neg hlt]; rfl
      refine ⟨_, W1, .seq e1 (.seq .assign (when_false hz)), by rw [h1], w1, l1, o1, fun j h1' h2 h3 => ?_, ?_⟩
      · simp only [set_ne h2, σ2]; exact k1 j h1' h2 (h3.elim .inl fun h => .inr (by simp only [A.nt] at h; omega))
      · rw [AK.set_oob k _ _ _ (by omega)]
        exact SR.frame s1 (by simp only [σ2, set_ne (show l.v ≠ sc by omega)]) rfl rfl
  | .push _ _, _, _, _, _, _, _, _, _, _, _, hok, _ => by simp [A.ok] at hok
  | .ite c a b, v, σ, e, W, hin, hle, hsc, hW, hwf, ht, hok, hS => by
    simp only [A.wf, Bool.and_eq_true, beq_iff_eq] at hwf
    obtain ⟨⟨⟨hwc, hwa⟩, hwb⟩, hbase⟩ := hwf
    simp only [A.ok] at hok; simp only [A.Tmps] at ht; simp only [A.nt] at hsc; simp only [A.st, A.den]
    obtain ⟨t2, t3, trest⟩ := ht
    have hSa : SR σ (.ar k) l (a.base.get v) := hS
    have hSb : SR σ (.ar k) l (b.base.get v) := by rw [Mem.get_idx b.base a.base v hbase.symm]; exact hSa
    cases hcv : c.den v with
    | true =>
      rw [hcv, if_pos rfl] at trest; have hoa := hok.2; rw [hcv, if_pos rfl] at hoa
      obtain ⟨σ1, W1, e1, h1, w1, l1, o1, k1, s1⟩ := A.st_ok L l sc a v σ (e + 4) W hin (by omega) (by omega) hW hwa
        trest hoa hSa
      have hne : σ.env (e + 2) ≠ 0 := by rw [t2, hcv]; decide
      have hz : (σ1.env.set (e + 2) 0) (e + 3) = 0 := by
        rw [set_ne (by omega), k1 _ (by omega) (by omega) (.inl (by omega)), t3, hcv]; rfl
      refine ⟨_, W1, .seq (when_true hne e1) (when_false (σ := ⟨_, _, _⟩) hz), h1, w1, l1, o1,
        fun j h1' h2 h3 => ?_, ?_⟩
      · simp only [A.nt] at h3
        show (σ1.env.set (e + 2) 0) j = _
        rw [set_ne (by omega), k1 j h1' h2 (h3.elim (fun h => .inl (by omega)) fun h => .inr (by omega))]
      · rw [if_pos rfl]; exact SR.frame s1 (set_ne (by omega)) rfl rfl
    | false =>
      rw [hcv] at trest; simp only [Bool.false_eq_true, if_false] at trest
      have hob := hok.2; rw [hcv] at hob; simp only [Bool.false_eq_true, if_false] at hob
      obtain ⟨σ1, W1, e1, h1, w1, l1, o1, k1, s1⟩ := A.st_ok L l sc b v σ (e + 4 + a.nt) W hin (by omega) (by omega)
        hW hwb trest hob hSb
      have hz : σ.env (e + 2) = 0 := by rw [t2, hcv]; rfl
      have hne : σ.env (e + 3) ≠ 0 := by rw [t3, hcv]; decide
      refine ⟨_, W1, .seq (when_false hz) (when_true hne e1), h1, w1, l1, o1, fun j h1' h2 h3 => ?_, ?_⟩
      · simp only [A.nt] at h3
        show (σ1.env.set (e + 3) 0) j = _
        rw [set_ne (by omega), k1 j h1' h2 (h3.elim (fun h => .inl (by omega)) fun h => .inr (by omega))]
      · simp only [Bool.false_eq_true, if_false]; exact SR.frame s1 (set_ne (by omega)) rfl rfl

end Proven.WA
