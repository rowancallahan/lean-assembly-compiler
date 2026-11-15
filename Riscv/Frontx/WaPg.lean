/- Word arrays (NOTES section 20), compiler part 4: fresh arrays, programs.

`Pg.comp L d wo p` compiles a program in an environment at `L` with free variables from `d` and free words
of the work block from `wo`; it returns the statements, the location of the result and the next free word.
A constant table is stored word by word into fresh words (`store64`), `Array.replicate n x` is a fill
loop, a view (`xs.data`) or an alias copies only the size.  A loop gets its state slots at `d, d + 1, ...`,
then `res`, `fl`, temporaries above. -/
import Riscv.Frontx.WaStmt

namespace Proven.WA
open Proven Proven.Frontx

/-! ## Static values -/

/-- a closed `Nat` expression's value (capacities of `replicate`) -/
def E.natVal {Γ : List Sl} : E Γ .nat → Option Nat
  | .lit _ c => some c
  | .bin .add a b => do let x ← a.natVal; let y ← b.natVal; pure (x + y)
  | _ => none

/-! ## Fresh arrays -/

/-- `W[wo + j] := c[j]` for the elements of a table -/
def tblStores (t : Ty) (wo d : Nat) : List t.T → Nat → MS
  | [], _ => skipAt d
  | x :: xs, j => .seq (.store64 0 (.const (BitVec.ofNat 64 (wo + j))) (.const (t.rep x))) (tblStores t wo d xs (j + 1))

/-- `j := 0; while j < n { W[wo + j] := x; j := j + 1 }` with `n` in `d`, `x` in `d + 1`, `j` in `d + 2` -/
def fillLoop (wo d : Nat) : MS :=
  .seq (.assign (d + 2) (.const 0)) (.loop (.bin .ult (.var (d + 2)) (.var d))
    (.seq (.store64 0 (.bin .add (.var (d + 2)) (.const (BitVec.ofNat 64 wo))) (.var (d + 1)))
      (.assign (d + 2) (.bin .add (.var (d + 2)) (.const 1)))))

/-- the code of a fresh array in slot variable `d`, its location and the next free word -/
def F.comp (L : List Loc) {Γ : List Sl} : {k : AK} → F Γ k → Nat → Nat → MS × Loc × Nat
  | _, @F.rep _ t n x, d, wo =>
    let c := (n.natVal).getD 0
    (.seq (E.comp L n d) (.seq (E.comp L x (d + 1)) (fillLoop wo d)), ⟨d, false, wo, some c⟩, wo + c)
  | _, @F.const _ t tb, d, wo =>
    (.seq (tblStores t wo d tb.toList 0) (.assign d (.const (BitVec.ofNat 64 tb.size))), ⟨d, false, wo, some tb.size⟩,
      wo + tb.size)
  | _, .empty, d, wo => (skipAt d, ⟨d, false, wo, none⟩, wo)
  | _, .extract _ _ _, d, wo => (skipAt d, ⟨d, false, wo, none⟩, wo)
  | _, .data m, d, wo => (.assign d (.var (m.loc L).v), { m.loc L with v := d }, wo)
  | _, .alias m, d, wo => (.assign d (.var (m.loc L).v), { m.loc L with v := d }, wo)

def F.wf (L : List Loc) {Γ : List Sl} : {k : AK} → F Γ k → Bool
  | _, .rep n x => n.natVal.isSome && E.wf L n && E.wf L x
  | _, .const tb => decide (tb.size < 2 ^ 32)
  | _, .data _ | _, .alias _ => true
  | _, .empty | _, .extract _ _ _ => false

def F.ok {Γ : List Sl} : {k : AK} → F Γ k → Vals Γ → Prop
  | _, .rep n x, v => E.ok n v ∧ E.ok x v
  | _, _, _ => True

theorem E.natVal_den {Γ : List Sl} (v : Vals Γ) : ∀ (n : E Γ .nat) (c : Nat), n.natVal = some c → n.den v = c
  | .lit _ c', c, h => by simp only [E.natVal, Option.some.injEq] at h; subst h; rfl
  | .bin .add a b, c, h => by
    simp only [E.natVal, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    simp only [E.den, Op2.den, E.natVal_den v a x hx, E.natVal_den v b y hy]
  | .var _, _, h | .bin .sub _ _, _, h | .bin .mul _ _, _, h | .bin .div _ _, _, h | .bin .mod _ _, _, h
  | .bin .and _ _, _, h | .bin .or _ _, _, h | .bin .xor _ _, _, h | .bin .shl _ _, _, h | .bin .shr _ _, _, h
  | .bin .band _ _, _, h | .bin .bor _ _, _, h | .cast _ _, _, h | .ite _ _ _, _, h | .getA _ _ _, _, h
  | .size _, _, h => by simp [E.natVal] at h

/-! ## Word block frames -/

/-- the work words outside `[lo, hi)` are kept -/
def WKeep (W W' : List (BitVec 64)) (lo hi : Nat) : Prop :=
  W'.length = W.length ∧ ∀ j, (j < lo ∨ hi ≤ j) → W'[j]? = W[j]?

/-- the arrays of the environment are in the input or below word `wo` -/
def LowLocs (L : List Loc) (wo : Nat) : Prop := ∀ l ∈ L, l.inp = true ∨ ∃ c, l.cap = some c ∧ l.off + c ≤ wo

theorem SR.wkeep {σ σ' : MSt} {s : Sl} {l : Loc} {x : s.T} {lo hi : Nat} (h : SR σ s l x)
    (hv : σ'.env l.v = σ.env l.v) (hh : σ'.heap = σ.heap) (hw : WKeep (σ.wheap.getD 0 []) (σ'.wheap.getD 0 []) lo hi)
    (hlo : l.inp = true ∨ ∃ c, l.cap = some c ∧ l.off + c ≤ lo) : SR σ' s l x := by
  cases s with
  | sc t => show σ'.env l.v = _; rw [hv]; exact h
  | ar k =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by rw [hv]; exact h1, h2, ?_⟩
    unfold AR at h3 ⊢
    rw [hh]
    split
    · rename_i hi; rw [if_pos hi] at h3; exact h3
    · rename_i hi; rw [if_neg hi] at h3
      obtain ⟨a1, a2, a3, a4⟩ := h3
      obtain ⟨c, hc, hcl⟩ := hlo.resolve_left hi
      have hs := a3 c hc
      refine ⟨by rw [hw.1]; exact a1, by rw [hw.1]; exact a2, a3, fun j hj => ?_⟩
      rw [hw.2 _ (.inl (by omega))]; exact a4 j hj

theorem Rel.wkeep : ∀ {Γ : List Sl} {L : List Loc} {v : Vals Γ} {σ σ' : MSt} {lo hi : Nat}, Rel Γ L v σ →
    (∀ l ∈ L, σ'.env l.v = σ.env l.v) → σ'.heap = σ.heap → WKeep (σ.wheap.getD 0 []) (σ'.wheap.getD 0 []) lo hi →
    LowLocs L lo → Γ.length ≤ L.length → Rel Γ L v σ'
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, hl => by simp at hl
  | _ :: _, l :: L, _, _, _, _, _, h, hv, hh, hw, hlo, hl =>
    ⟨SR.wkeep h.1 (hv l (by simp)) hh hw (hlo l (by simp)),
      Rel.wkeep h.2 (fun l' h' => hv l' (List.mem_cons_of_mem _ h')) hh hw
        (fun l' h' => hlo l' (List.mem_cons_of_mem _ h')) (by simp at hl ⊢; omega)⟩

/-! ## Stores into the word block -/

/-- `W` with `xs` written from `p` on -/
def wset : List (BitVec 64) → Nat → List (BitVec 64) → List (BitVec 64)
  | W, _, [] => W
  | W, p, x :: xs => wset (W.set p x) (p + 1) xs

theorem wset_length : ∀ (W : List (BitVec 64)) (p : Nat) (xs : List (BitVec 64)), (wset W p xs).length = W.length
  | _, _, [] => rfl
  | W, p, x :: xs => by rw [wset, wset_length, List.length_set]

theorem wset_get : ∀ (W : List (BitVec 64)) (p : Nat) (xs : List (BitVec 64)) (q : Nat), p + xs.length ≤ W.length →
    (wset W p xs)[q]? = if p ≤ q ∧ q < p + xs.length then xs[q - p]? else W[q]?
  | W, p, [], q, _ => by simp [wset]; omega
  | W, p, x :: xs, q, h => by
    simp only [List.length_cons] at h
    rw [wset, wset_get _ _ _ _ (by rw [List.length_set]; omega)]
    by_cases hq : q = p
    · subst hq
      rw [if_neg (by omega), List.getElem?_set_self (by omega), if_pos (by simp)]; simp
    · rw [List.getElem?_set_ne (Ne.symm hq)]
      by_cases h1 : p + 1 ≤ q ∧ q < p + 1 + xs.length
      · rw [if_pos h1, if_pos (by simp; omega)]
        rw [show q - p = (q - (p + 1)) + 1 by omega, List.getElem?_cons_succ]
      · rw [if_neg h1, if_neg (by simp; omega)]

theorem store64_at {σ : MSt} {W : List (BitVec 64)} (hW : σ.wheap = [W]) (i e : MB) (p : Nat)
    (hp : (i.denote σ.env).toNat = p) (hpl : p < W.length) :
    Mach.BExec (.store64 0 i e) σ ⟨σ.env, σ.heap, [W.set p (e.denote σ.env)]⟩ := by
  have := Mach.BExec.store64 (b := 0) (i := i) (e := e) (σ := σ) (by rw [hW]; simp)
    (by simp only [hW, List.getElem_cons_zero, hp]; exact hpl)
  simp only [hW, List.getElem_cons_zero, hp, List.set_cons_zero] at this
  exact this

theorem tblStores_ok (t : Ty) (wo d : Nat) : ∀ (xs : List t.T) (j : Nat) (σ : MSt) (W : List (BitVec 64)),
    σ.wheap = [W] → wo + j + xs.length ≤ W.length → W.length < 2 ^ 32 →
    Mach.BExec (tblStores t wo d xs j) σ ⟨σ.env.set d 0, σ.heap, [wset W (wo + j) (xs.map t.rep)]⟩
  | [], j, σ, W, hW, _, _ => by
    have : Mach.BExec (skipAt d) σ ⟨σ.env.set d 0, σ.heap, σ.wheap⟩ := .assign
    rw [hW] at this; exact this
  | x :: xs, j, σ, W, hW, hl, h32 => by
    simp only [List.length_cons] at hl
    have e1 := store64_at hW (.const (BitVec.ofNat 64 (wo + j))) (.const (t.rep x)) (wo + j)
      (by simp only [Mach.BExp.denote, BitVec.toNat_ofNat]; omega) (by omega)
    have e2 := tblStores_ok t wo d xs (j + 1) ⟨σ.env, σ.heap, [W.set (wo + j) (t.rep x)]⟩ (W.set (wo + j) (t.rep x)) rfl
      (by rw [List.length_set]; omega) (by rw [List.length_set]; omega)
    simp only [Mach.BExp.denote] at e1
    have := Mach.BExec.seq e1 e2
    simp only [tblStores, List.map_cons, wset] at this ⊢
    rwa [show wo + (j + 1) = wo + j + 1 by omega] at this

/-- the fill loop from counter `j`: afterwards `W'[wo + i] = x` for `i < n`, nothing else written -/
theorem fill_ok (wo d n : Nat) (x : BitVec 64) (W0 : List (BitVec 64)) (hn : wo + n ≤ W0.length)
    (h32 : W0.length < 2 ^ 32) : ∀ (m j : Nat) (σ : MSt) (W : List (BitVec 64)), n - j = m → j ≤ n →
    σ.env d = rN n → σ.env (d + 1) = x → σ.env (d + 2) = rN j → σ.wheap = [W] → WKeep W0 W wo (wo + n) →
    (∀ i, i < j → W[wo + i]? = some x) →
    ∃ σ' W', Mach.BExec (.loop (.bin .ult (.var (d + 2)) (.var d))
        (.seq (.store64 0 (.bin .add (.var (d + 2)) (.const (BitVec.ofNat 64 wo))) (.var (d + 1)))
          (.assign (d + 2) (.bin .add (.var (d + 2)) (.const 1))))) σ σ' ∧
      σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧ WKeep W0 W' wo (wo + n) ∧ (∀ i, i < n → W'[wo + i]? = some x) ∧
      ∀ i, i ≠ d + 2 → σ'.env i = σ.env i
  | 0, j, σ, W, hm, hj, hd, hx, hc, hW, hk, hf => by
    have hjn : j = n := by omega
    subst hjn
    refine ⟨σ, W, .loopF ?_, rfl, hW, hk, hf, fun _ _ => rfl⟩
    simp only [Mach.BExp.denote, Op.eval, hc, hd]
    simp
  | m + 1, j, σ, W, hm, hj, hd, hx, hc, hW, hk, hf => by
    have hjn : j < n := by omega
    have hWl : W.length = W0.length := hk.1
    have hlt : (Mach.BExp.bin .ult (.var (d + 2)) (.var d)).denote σ.env ≠ 0 := by
      simp only [Mach.BExp.denote, Op.eval, hc, hd]
      rw [if_pos (by simp only [rN_lt (by omega : j < 2 ^ 64) (by omega : n < 2 ^ 64)]; exact hjn)]; decide
    have e1 := store64_at hW (.bin .add (.var (d + 2)) (.const (BitVec.ofNat 64 wo))) (.var (d + 1)) (wo + j)
      (by simp only [Mach.BExp.denote, Op.eval, hc, rN, BitVec.toNat_add, BitVec.toNat_ofNat]; omega) (by omega)
    simp only [Mach.BExp.denote, hx] at e1
    let σ1 : MSt := ⟨σ.env, σ.heap, [W.set (wo + j) x]⟩
    let σ2 : MSt := ⟨σ1.env.set (d + 2) ((Mach.BExp.bin .add (.var (d + 2)) (.const 1)).denote σ1.env), σ1.heap, σ1.wheap⟩
    have hc2 : σ2.env (d + 2) = rN (j + 1) := by
      simp only [σ2, σ1, set_eq, Mach.BExp.denote, Op.eval, hc, rN_add]; rfl
    obtain ⟨σ3, W3, e3, h3, w3, k3, f3, o3⟩ := fill_ok wo d n x W0 hn h32 m (j + 1) σ2 (W.set (wo + j) x) (by omega)
      (by omega) (by simp only [σ2, σ1, set_ne (show d ≠ d + 2 by omega)]; exact hd)
      (by simp only [σ2, σ1, set_ne (show d + 1 ≠ d + 2 by omega)]; exact hx) hc2 rfl
      ⟨by rw [List.length_set]; exact hWl, fun i hi => by
        rw [List.getElem?_set_ne (by omega)]; exact hk.2 i hi⟩
      (fun i hi => by
        by_cases hij : i = j
        · subst hij; rw [List.getElem?_set_self (by omega)]
        · rw [List.getElem?_set_ne (by omega)]; exact hf i (by omega))
    refine ⟨σ3, W3, .loopT hlt (.seq e1 .assign) e3, h3, w3, k3, f3, fun i hi => ?_⟩
    rw [o3 i hi]; simp only [σ2, σ1, set_ne hi]

/-! ## Arrays: sizes and elements -/

theorem AK.size_arr (t : Ty) (a : Array t.T) : AK.size (.arr t) a = a.size := by cases t <;> rfl
theorem AK.get_arr (t : Ty) (a : Array t.T) (i : Nat) : AK.get (.arr t) a i = a[i]! := by cases t <;> rfl
theorem F.den_rep {Γ : List Sl} {t : Ty} (n : E Γ .nat) (x : E Γ t) (v : Vals Γ) :
    F.den (.rep n x) v = Array.replicate (n.den v) (x.den v) := by
  cases t <;> rfl

theorem Ty.rep_lt (t : Ty) (x : t.T) : (t.rep x).toNat < 2 ^ 64 := (t.rep x).isLt

theorem ba_data_get (xs : ByteArray) (j : Nat) : xs.data[j]! = xs[j]! := by
  by_cases h : j < xs.size
  · rw [getElem!_pos xs j h, getElem!_pos xs.data j h]; rfl
  · rw [getElem!_neg xs j h, getElem!_neg xs.data j h]

/-- **Fresh arrays.** -/
theorem F.comp_ok (L : List Loc) {Γ : List Sl} : ∀ {k : AK} (f : F Γ k) (v : Vals Γ) (σ : MSt) (d wo : Nat)
    (W : List (BitVec 64)), Rel Γ L v σ → Γ.length ≤ L.length → Below L d → LowLocs L wo → f.wf L = true →
    f.ok v → σ.wheap = [W] → (F.comp L f d wo).2.2 ≤ W.length → W.length < 2 ^ 32 →
    ∃ σ' W', Mach.BExec (F.comp L f d wo).1 σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧
      WKeep W W' wo (F.comp L f d wo).2.2 ∧ (∀ j, j < d → σ'.env j = σ.env j) ∧
      SR σ' (.ar k) (F.comp L f d wo).2.1 (F.den f v) ∧ (F.comp L f d wo).2.1.v = d ∧
      wo ≤ (F.comp L f d wo).2.2 ∧ LowLocs [(F.comp L f d wo).2.1] (F.comp L f d wo).2.2
  | _, @F.rep _ t n x, v, σ, d, wo, W, hR, hl, hb, hlo, hwf, hok, hW, hcap, h32 => by
    simp only [F.wf, Bool.and_eq_true, Option.isSome_iff_exists] at hwf
    obtain ⟨⟨⟨c, hc⟩, hwn⟩, hwx⟩ := hwf
    obtain ⟨hon, hox⟩ := hok
    simp only [F.comp, hc, Option.getD_some] at hcap ⊢
    have hnv := E.natVal_den v n c hc
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.comp_ok L n v σ d hR hl hb hwn hon).frame hR hb hl
    obtain ⟨σ2, e2, v2, k2, h2, w2, r2⟩ :=
      (E.comp_ok L x v σ1 (d + 1) r1 hl (hb.mono (by omega)) hwx hox).frame r1 (hb.mono (by omega)) hl
    let σ3 : MSt := ⟨σ2.env.set (d + 2) 0, σ2.heap, σ2.wheap⟩
    have hW3 : σ3.wheap = [W] := by simp only [σ3]; rw [w2, w1, hW]
    obtain ⟨σ4, W4, e4, h4, w4, k4, f4, o4⟩ := fill_ok wo d c (t.rep (x.den v)) W (by omega) h32 c 0 σ3 W
      (by omega) (by omega) (by simp only [σ3, set_ne (show d ≠ d + 2 by omega)]; rw [k2 d (by omega), v1, hnv]; rfl)
      (by simp only [σ3, set_ne (show d + 1 ≠ d + 2 by omega)]; exact v2) (by simp only [σ3, set_eq]; rfl) hW3
      ⟨rfl, fun _ _ => rfl⟩ (fun i hi => by omega)
    refine ⟨σ4, W4, .seq e1 (.seq e2 (.seq .assign e4)), by rw [h4]; simp only [σ3]; rw [h2, h1], w4, k4,
      fun j hj => ?_, ?_, trivial, by omega, ?_⟩
    · rw [o4 j (by omega)]; simp only [σ3, set_ne (show j ≠ d + 2 by omega)]; rw [k2 j (by omega), k1 j hj]
    · have hsz : AK.size (.arr t) (F.den (.rep n x) v) = c := by rw [F.den_rep, AK.size_arr, hnv]; simp
      refine ⟨?_, ?_, ?_⟩
      · rw [hsz, o4 d (by omega)]; simp only [σ3, set_ne (show d ≠ d + 2 by omega)]
        rw [k2 d (by omega), v1, hnv]; rfl
      · rw [hsz]; omega
      · unfold AR
        rw [if_neg (by simp), w4]
        simp only [List.getD_cons_zero, hsz]
        refine ⟨by rw [k4.1]; exact hcap, by rw [k4.1]; exact h32, fun c' hc' => by cases hc'; omega,
          fun j hj => ?_⟩
        rw [f4 j hj]; congr 1
        simp only [AK.w, AK.el, AK.get_arr, F.den_rep, hnv]
        rw [getElem!_pos _ _ (by simp; omega)]; simp
    · intro l hl'; simp only [List.mem_singleton] at hl'; subst hl'; exact .inr ⟨c, rfl, Nat.le_refl _⟩
  | _, @F.const _ t tb, v, σ, d, wo, W, hR, hl, hb, hlo, hwf, hok, hW, hcap, h32 => by
    simp only [F.wf, decide_eq_true_eq] at hwf
    simp only [F.comp] at hcap ⊢
    have hlen : wo + 0 + (tb.toList).length ≤ W.length := by simp; omega
    have e1 := tblStores_ok t wo d tb.toList 0 σ W hW hlen h32
    let W1 := wset W (wo + 0) (tb.toList.map t.rep)
    have hl1 : W1.length = W.length := wset_length _ _ _
    refine ⟨_, W1, .seq e1 .assign, rfl, rfl, ⟨hl1, fun j hj => ?_⟩, fun j hj => ?_, ?_, trivial, by omega, ?_⟩
    · simp only [W1]; rw [wset_get _ _ _ _ (by simp; omega), if_neg (by simp; omega)]
    · simp only [set_ne (show j ≠ d by omega)]
    · simp only [F.den]
      refine ⟨by simp only [set_eq]; rw [AK.size_arr]; rfl, by rw [AK.size_arr]; exact hwf, ?_⟩
      unfold AR
      rw [if_neg (by simp)]
      simp only [List.getD_cons_zero, AK.size_arr]
      refine ⟨by rw [hl1]; omega, by rw [hl1]; exact h32, fun c' hc' => by cases hc'; omega, fun j hj => ?_⟩
      show (wset W (wo + 0) (tb.toList.map t.rep))[wo + j]? = _
      rw [wset_get _ _ _ _ (by simp; omega), if_pos (by simp; omega)]
      simp only [Nat.add_zero, Nat.add_sub_cancel_left, List.getElem?_map, Array.getElem?_toList,
        Array.getElem?_eq_getElem hj, Option.map_some, AK.w, AK.el, AK.get_arr]
      rw [getElem!_pos tb j hj]
    · intro l hl'; simp only [List.mem_singleton] at hl'; subst hl'; exact .inr ⟨_, rfl, Nat.le_refl _⟩
  | _, .empty, _, _, _, _, _, _, _, _, _, hwf, _, _, _, _ => by simp [F.wf] at hwf
  | _, .extract _ _ _, _, _, _, _, _, _, _, _, _, hwf, _, _, _, _ => by simp [F.wf] at hwf
  | _, .data m, v, σ, d, wo, W, hR, hl, hb, hlo, hwf, hok, hW, hcap, h32 => by
    simp only [F.comp]
    have hS := (Rel.get m hR).ar
    have hm := hb _ (Mem.loc_mem m L hl)
    refine ⟨_, W, .assign, rfl, hW, ⟨rfl, fun _ _ => rfl⟩, fun j hj => set_ne (by omega), ?_, trivial, Nat.le_refl _, ?_⟩
    · refine ⟨by simp only [set_eq, Mach.BExp.denote]; rw [hS.1]; rfl, by exact hS.2.1, ?_⟩
      have h3 := hS.2.2
      have hw : ∀ j, AK.w (.arr .u8) (m.get v).data j = AK.w .ba (m.get v) j := fun j => by
        simp only [AK.w, AK.el, AK.get, ba_data_get]
      have hs : AK.size (.arr .u8) (m.get v).data = AK.size .ba (m.get v) := rfl
      unfold AR at h3 ⊢
      simp only [F.den, hw, hs]
      exact h3
    · intro l hl'; simp only [List.mem_singleton] at hl'; subst hl'
      have := hlo _ (Mem.loc_mem m L hl); exact this
  | _, .alias m, v, σ, d, wo, W, hR, hl, hb, hlo, hwf, hok, hW, hcap, h32 => by
    simp only [F.comp]
    have hS := (Rel.get m hR).ar
    have hm := hb _ (Mem.loc_mem m L hl)
    refine ⟨_, W, .assign, rfl, hW, ⟨rfl, fun _ _ => rfl⟩, fun j hj => set_ne (by omega), ?_, trivial, Nat.le_refl _, ?_⟩
    · exact ⟨by simp only [set_eq, Mach.BExp.denote]; rw [hS.1]; rfl, hS.2.1, hS.2.2⟩
    · intro l hl'; simp only [List.mem_singleton] at hl'; subst hl'
      have := hlo _ (Mem.loc_mem m L hl); exact this

/-! ## Loop starts -/

def Ini.comp (L : List Loc) {Γ : List Sl} : (s : Sl) → Ini Γ s → Nat → Nat → MS × Loc × Nat
  | .sc _, e, d, wo => (E.comp L e d, scLoc d, wo)
  | .ar _, f, d, wo => F.comp L f d wo

def Ini.wf (L : List Loc) {Γ : List Sl} : (s : Sl) → Ini Γ s → Bool
  | .sc _, e => E.wf L e
  | .ar _, f => F.wf L f

def Ini.ok {Γ : List Sl} : (s : Sl) → Ini Γ s → Vals Γ → Prop
  | .sc _, e, v => E.ok e v
  | .ar _, f, v => F.ok f v

/-- the start of a loop: slot `j` in variable `d + j` -/
def Inis.comp (L : List Loc) {Γ : List Sl} : {Δ : List Sl} → Inis Γ Δ → Nat → Nat → MS × List Loc × Nat
  | _, .nil, d, wo => (skipAt d, [], wo)
  | _, .cons (s := s) x xs, d, wo =>
    let r := Ini.comp L s x d wo
    let q := xs.comp L (d + 1) r.2.2
    (.seq r.1 q.1, r.2.1 :: q.2.1, q.2.2)

def Inis.wf (L : List Loc) {Γ : List Sl} : {Δ : List Sl} → Inis Γ Δ → Bool
  | _, .nil => true
  | _, .cons (s := s) x xs => Ini.wf L s x && xs.wf L

def Inis.ok {Γ : List Sl} : {Δ : List Sl} → Inis Γ Δ → Vals Γ → Prop
  | _, .nil, _ => True
  | _, .cons (s := s) x xs, v => Ini.ok s x v ∧ xs.ok v

theorem Ini.comp_ok (L : List Loc) {Γ : List Sl} (s : Sl) (x : Ini Γ s) (v : Vals Γ) (σ : MSt) (d wo : Nat)
    (W : List (BitVec 64)) (hR : Rel Γ L v σ) (hl : Γ.length ≤ L.length) (hb : Below L d) (hlo : LowLocs L wo)
    (hwf : Ini.wf L s x = true) (hok : Ini.ok s x v) (hW : σ.wheap = [W]) (hcap : (Ini.comp L s x d wo).2.2 ≤ W.length)
    (h32 : W.length < 2 ^ 32) :
    ∃ σ' W', Mach.BExec (Ini.comp L s x d wo).1 σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧
      WKeep W W' wo (Ini.comp L s x d wo).2.2 ∧ (∀ j, j < d → σ'.env j = σ.env j) ∧
      SR σ' s (Ini.comp L s x d wo).2.1 (Ini.den s x v) ∧ (Ini.comp L s x d wo).2.1.v = d ∧
      wo ≤ (Ini.comp L s x d wo).2.2 ∧ LowLocs [(Ini.comp L s x d wo).2.1] (Ini.comp L s x d wo).2.2 := by
  cases s with
  | sc t =>
    obtain ⟨σ1, e1, v1, k1, h1, w1⟩ := E.comp_ok L x v σ d hR hl hb hwf hok
    exact ⟨σ1, W, e1, h1, by rw [w1, hW], ⟨rfl, fun _ _ => rfl⟩, k1, v1, rfl, Nat.le_refl _,
      fun l h => by simp only [List.mem_singleton] at h; subst h; exact .inl rfl⟩
  | ar k => exact F.comp_ok L x v σ d wo W hR hl hb hlo hwf hok hW hcap h32

theorem WKeep.trans {W W1 W2 : List (BitVec 64)} {a b c : Nat} (h1 : WKeep W W1 a b) (h2 : WKeep W1 W2 b c)
    (hab : a ≤ b) (hbc : b ≤ c) : WKeep W W2 a c :=
  ⟨h2.1.trans h1.1, fun j hj => by rw [h2.2 j (by omega), h1.2 j (by omega)]⟩

theorem LowLocs.mono {L : List Loc} {a b : Nat} (h : LowLocs L a) (hab : a ≤ b) : LowLocs L b :=
  fun l hl => (h l hl).elim .inl fun ⟨c, hc, hle⟩ => .inr ⟨c, hc, by omega⟩

theorem F.comp_mono (L : List Loc) {Γ : List Sl} : ∀ {k : AK} (f : F Γ k) (d wo : Nat), wo ≤ (F.comp L f d wo).2.2
  | _, .rep _ _, _, _ | _, .const _, _, _ => by simp only [F.comp]; omega
  | _, .empty, _, _ | _, .extract _ _ _, _, _ | _, .data _, _, _ | _, .alias _, _, _ => Nat.le_refl _

theorem Ini.comp_mono (L : List Loc) {Γ : List Sl} (s : Sl) (x : Ini Γ s) (d wo : Nat) :
    wo ≤ (Ini.comp L s x d wo).2.2 := by
  cases s with
  | sc _ => exact Nat.le_refl _
  | ar _ => exact F.comp_mono L x d wo

theorem Inis.comp_mono (L : List Loc) {Γ : List Sl} : ∀ {Δ : List Sl} (xs : Inis Γ Δ) (d wo : Nat),
    wo ≤ (xs.comp L d wo).2.2
  | _, .nil, _, _ => Nat.le_refl _
  | _, .cons (s := s) x xs, d, wo => by
    simp only [Inis.comp]
    exact Nat.le_trans (Ini.comp_mono L s x d wo) (Inis.comp_mono L xs (d + 1) _)

theorem Inis.comp_ok (L : List Loc) {Γ : List Sl} : ∀ {Δ : List Sl} (xs : Inis Γ Δ) (v : Vals Γ) (σ : MSt) (d wo : Nat)
    (W : List (BitVec 64)), Rel Γ L v σ → Γ.length ≤ L.length → Below L d → LowLocs L wo → xs.wf L = true →
    xs.ok v → σ.wheap = [W] → (xs.comp L d wo).2.2 ≤ W.length → W.length < 2 ^ 32 →
    ∃ σ' W', Mach.BExec (xs.comp L d wo).1 σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧
      WKeep W W' wo (xs.comp L d wo).2.2 ∧ (∀ j, j < d → σ'.env j = σ.env j) ∧
      Rel Δ (xs.comp L d wo).2.1 (xs.den v) σ' ∧ vsOf (xs.comp L d wo).2.1 = List.range' d Δ.length ∧
      LowLocs (xs.comp L d wo).2.1 (xs.comp L d wo).2.2
  | _, .nil, v, σ, d, wo, W, hR, hl, hb, hlo, hwf, hok, hW, hcap, h32 =>
    ⟨_, W, .assign, rfl, hW, ⟨rfl, fun _ _ => rfl⟩, fun j hj => set_ne (by omega), trivial, rfl,
      fun _ h => by simp [Inis.comp] at h⟩
  | _, .cons (s := s) x xs, v, σ, d, wo, W, hR, hl, hb, hlo, hwf, hok, hW, hcap, h32 => by
    simp only [Inis.wf, Bool.and_eq_true] at hwf
    simp only [Inis.ok] at hok
    simp only [Inis.comp] at hcap ⊢
    have hm2 := Inis.comp_mono L xs (d + 1) (Ini.comp L s x d wo).2.2
    obtain ⟨σ1, W1, e1, h1, w1, k1, f1, s1, v1, o1, l1⟩ := Ini.comp_ok L s x v σ d wo W hR hl hb hlo hwf.1 hok.1 hW
      (by omega) h32
    have r1 : Rel Γ L v σ1 := Rel.wkeep hR (fun l hl' => f1 _ (hb l hl')) h1 (by rw [hW, w1]; exact k1) hlo hl
    obtain ⟨σ2, W2, e2, h2, w2, k2, f2, r2, v2, l2⟩ := Inis.comp_ok L xs v σ1 (d + 1) _ W1 r1 hl (hb.mono (by omega))
      (hlo.mono o1) hwf.2 hok.2 w1 (by rw [k1.1]; omega) (by rw [k1.1]; exact h32)
    refine ⟨σ2, W2, .seq e1 e2, h2.trans h1, w2, k1.trans k2 o1 hm2, fun j hj => by rw [f2 j (by omega), f1 j hj],
      ⟨?_, r2⟩, ?_, ?_⟩
    · exact SR.wkeep s1 (by simp only [List.headD_cons]; rw [v1]; exact f2 d (by omega)) h2
        (by rw [w1, w2]; exact k2) (l1 _ (by simp))
    · simp only [vsOf, List.map_cons] at v2 ⊢; rw [v1, v2]; simp [List.range'_succ]
    · intro l hl'
      simp only [List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · exact (l1 _ (by simp)).elim .inl fun ⟨c, hc, hle⟩ => .inr ⟨c, hc, by omega⟩
      · exact l2 l hl'

/-! ## Programs -/

/-- where an array result of a loop body lives (the first `ret` leaf) -/
def T.rl : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → List Loc → Nat → Option Loc
  | _, _, .ar _, .ret a, L, _ => match a with | .var m => some (m.loc L) | _ => none
  | _, _, .sc _, .ret _, _, _ => none
  | _, _, _, .call _, _, _ => none
  | _, _, _, .ite _ a b, L, d => match a.rl L (d + 2) with | some l => some l | none => b.rl L (d + 2)
  | _, _, _, .let_ _ k, L, d => k.rl (scLoc d :: L) (d + 1)

/-- the result location of a loop: `res` for a scalar, the array's slot otherwise -/
def resLoc : (s : Sl) → Nat → Loc → Loc
  | .sc _, res, _ => scLoc res
  | .ar _, _, rl => rl

def Pg.comp (L : List Loc) {Γ : List Sl} : {R : Sl} → Pg Γ R → Nat → Nat → MS × Loc × Nat
  | .sc _, .ret e, d, wo => (E.comp L e d, scLoc d, wo)
  | .ar _, .ret a, d, wo => (skipAt d, (match a with | .var m => m.loc L | _ => default), wo)
  | _, .let_ (s := s) x k, d, wo =>
    let r := Ini.comp L s x d wo
    let q := k.comp (r.2.1 :: L) (d + 1) r.2.2
    (.seq r.1 q.1, q.2)
  | _, .loop (s := s) Δ b init k, d, wo =>
    let r := init.comp L d wo
    let st := r.2.1
    let res := d + Δ.length
    let d1 := res + 2
    let rl := (b.rl (st ++ L) d1).getD default
    let q := k.comp (resLoc s res rl :: L) d1 r.2.2
    (.seq r.1 (.seq (b.loopCode st res (res + 1) (st ++ L) d1) q.1), q.2)

def Sl.isAr : Sl → Bool | .sc _ => false | .ar _ => true

def Pg.wf (L : List Loc) {Γ : List Sl} : {R : Sl} → Pg Γ R → Nat → Nat → Bool
  | .sc _, .ret e, _, _ => E.wf L e
  | .ar _, .ret a, _, _ => match a with | .var _ => true | _ => false
  | _, .let_ (s := s) x k, d, wo =>
    let r := Ini.comp L s x d wo
    Ini.wf L s x && k.wf (r.2.1 :: L) (d + 1) r.2.2
  | _, .loop (s := s) Δ b init k, d, wo =>
    let r := init.comp L d wo
    let st := r.2.1
    let res := d + Δ.length
    let d1 := res + 2
    let rl := (b.rl (st ++ L) d1).getD default
    init.wf L && b.wf st rl (st ++ L) d1 && decide (rl.v < d1) && rl.v != res + 1 &&
      (!s.isAr || (st ++ L).contains rl) &&
      k.wf (resLoc s res rl :: L) d1 r.2.2

/-- the meaning of a program together with its run-time conditions (per loop an invariant `P`) -/
def Pg.Good : {Γ : List Sl} → {R : Sl} → Pg Γ R → Vals Γ → R.T → Prop
  | _, .sc _, .ret e, v, y => y = E.den e v ∧ E.ok e v
  | _, .ar _, .ret a, v, y => y = A.den a v
  | _, _, .let_ (s := s) x k, v, y => Ini.ok s x v ∧ k.Good (Ini.den s x v, v) y
  | _, _, .loop Δ b init k, v, y => init.ok v ∧ ∃ r, ∃ P : Vals Δ → Prop, P (init.den v) ∧
      (∀ s, P s → b.ok (Vals.app s v)) ∧ (∀ s s', P s → b.out (Vals.app s v) = .inl s' → P s') ∧
      Runs b v (init.den v) r ∧ k.Good (r, v) y

theorem Pg.comp_mono (L : List Loc) {Γ : List Sl} : ∀ {R : Sl} (p : Pg Γ R) (d wo : Nat), wo ≤ (p.comp L d wo).2.2
  | .sc _, .ret _, _, _ | .ar _, .ret _, _, _ => Nat.le_refl _
  | _, .let_ (s := s) x k, d, wo => by
    simp only [Pg.comp]; exact Nat.le_trans (Ini.comp_mono L s x d wo) (Pg.comp_mono _ k _ _)
  | _, .loop Δ b init k, d, wo => by
    simp only [Pg.comp]; exact Nat.le_trans (Inis.comp_mono L init d wo) (Pg.comp_mono _ k _ _)

theorem below_cons {L : List Loc} {l : Loc} {d d' : Nat} (hb : Below L d) (hl : l.v < d') (hd : d ≤ d') :
    Below (l :: L) d' := by
  intro l' h'
  simp only [List.mem_cons] at h'
  rcases h' with rfl | h'
  · exact hl
  · have := hb l' h'; omega

set_option maxHeartbeats 1000000 in
/-- **Programs**: the code of `p` ends with the result represented at its location. -/
theorem Pg.comp_ok (L : List Loc) : ∀ {Γ : List Sl} {R : Sl} (p : Pg Γ R) (v : Vals Γ) (σ : MSt) (d wo : Nat)
    (W : List (BitVec 64)) (y : R.T), Rel Γ L v σ → Γ.length ≤ L.length → Below L d → LowLocs L wo →
    p.wf L d wo = true → p.Good v y → σ.wheap = [W] → (p.comp L d wo).2.2 ≤ W.length → W.length < 2 ^ 32 →
    ∃ σ' W', Mach.BExec (p.comp L d wo).1 σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧ SR σ' R (p.comp L d wo).2.1 y
  | _, .sc t, .ret e, v, σ, d, wo, W, y, hR, hl, hb, hlo, hwf, hg, hW, hcap, h32 => by
    simp only [Pg.wf] at hwf; simp only [Pg.Good] at hg
    simp only [Pg.comp]
    obtain ⟨σ1, e1, v1, k1, h1, w1⟩ := E.comp_ok L e v σ d hR hl hb hwf hg.2
    exact ⟨σ1, W, e1, h1, by rw [w1, hW], by rw [hg.1]; exact v1⟩
  | _, .ar k, .ret a, v, σ, d, wo, W, y, hR, hl, hb, hlo, hwf, hg, hW, hcap, h32 => by
    simp only [Pg.Good] at hg
    cases a with
    | var m =>
      simp only [Pg.comp]
      have hS := Rel.get m hR
      have hm := hb _ (Mem.loc_mem m L hl)
      refine ⟨_, W, .assign, rfl, hW, ?_⟩
      rw [hg]; exact SR.frame hS (set_ne (by omega)) rfl rfl
    | set _ _ _ | push _ _ | ite _ _ _ => simp [Pg.wf] at hwf
  | Γ, _, .let_ (s := s) x k, v, σ, d, wo, W, y, hR, hl, hb, hlo, hwf, hg, hW, hcap, h32 => by
    simp only [Pg.wf, Bool.and_eq_true] at hwf; simp only [Pg.Good] at hg
    simp only [Pg.comp] at hcap ⊢
    have hm := Pg.comp_mono ((Ini.comp L s x d wo).2.1 :: L) k (d + 1) (Ini.comp L s x d wo).2.2
    obtain ⟨σ1, W1, e1, h1, w1, k1, f1, s1, v1, o1, l1⟩ := Ini.comp_ok L s x v σ d wo W hR hl hb hlo hwf.1 hg.1 hW
      (by omega) h32
    have r1 : Rel Γ L v σ1 := Rel.wkeep hR (fun l hl' => f1 _ (hb l hl')) h1 (by rw [hW, w1]; exact k1) hlo hl
    have r1' : Rel (s :: Γ) ((Ini.comp L s x d wo).2.1 :: L) (Ini.den s x v, v) σ1 := ⟨s1, r1⟩
    obtain ⟨σ2, W2, e2, h2, w2, s2⟩ := Pg.comp_ok ((Ini.comp L s x d wo).2.1 :: L) k _ σ1 (d + 1) _ W1 y r1' (by simp; omega)
      (below_cons hb (by rw [v1]; omega) (by omega))
      (fun l' h' => by
        simp only [List.mem_cons] at h'
        rcases h' with rfl | h'
        · exact l1 _ (by simp)
        · exact (hlo l' h').elim .inl fun ⟨c, hc, hle⟩ => .inr ⟨c, hc, by omega⟩)
      hwf.2 hg.2 w1 (by rw [k1.1]; omega) (by rw [k1.1]; exact h32)
    exact ⟨σ2, W2, .seq e1 e2, h2.trans h1, w2, s2⟩
  | Γ, _, .loop (s := s) Δ b init k, v, σ, d, wo, W, y, hR, hl, hb, hlo, hwf, hg, hW, hcap, h32 => by
    simp only [Pg.wf, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hwf
    obtain ⟨⟨⟨⟨⟨hwi, hwb⟩, hrl⟩, hrf⟩, hrc⟩, hwk⟩ := hwf
    simp only [Pg.Good] at hg
    obtain ⟨hoi, r, P, hP0, hPok, hPs, hruns, hgk⟩ := hg
    simp only [Pg.comp] at hcap ⊢
    have hm := Pg.comp_mono (resLoc s (d + Δ.length) ((b.rl ((init.comp L d wo).2.1 ++ L) (d + Δ.length + 2)).getD default) :: L) k (d + Δ.length + 2) (init.comp L d wo).2.2
    obtain ⟨σ1, W1, e1, h1, w1, k1, f1, r1, v1, l1⟩ := Inis.comp_ok L init v σ d wo W hR hl hb hlo hwi hoi hW
      (by omega) h32
    have hmo := Inis.comp_mono L init d wo
    generalize hst : (init.comp L d wo).2.1 = st at *
    generalize hrl' : (b.rl (st ++ L) (d + Δ.length + 2)).getD default = rl at *
    have hlen : st.length = Δ.length := by
      have := congrArg List.length v1; simp only [vsOf, List.length_map, List.length_range'] at this; exact this
    have hin : ∀ l ∈ st, d ≤ l.v ∧ l.v < d + Δ.length := fun l h => by
      have : l.v ∈ vsOf st := List.mem_map_of_mem h
      rw [v1, List.mem_range'] at this; omega
    have hnin : ∀ j, (j < d ∨ d + Δ.length ≤ j) → j ∉ vsOf st := fun j hj h => by
      obtain ⟨l, hl', e⟩ := List.mem_map.1 h; have := hin l hl'; omega
    have hlay : LoopLay st (d + Δ.length) (d + Δ.length + 1) rl (d + Δ.length + 2) :=
      ⟨fun l h => by have := hin l h; omega, by omega, by omega, hrl, by rw [v1]; exact List.nodup_range',
        hnin _ (by omega), hnin _ (by omega), by omega, hrf⟩
    have rΓ1 : Rel Γ L v σ1 := Rel.wkeep hR (fun l hl' => f1 _ (hb l hl')) h1 (by rw [hW, w1]; exact k1) hlo hl
    have hR2 : Rel (Δ ++ Γ) (st ++ L) (Vals.app (init.den v) v) σ1 := by
      rw [Rel.app hlen]; exact ⟨r1, rΓ1⟩
    obtain ⟨σ3, e3, h3, w3, k3, rr3⟩ := T.loopCode_ok b v st L (d + Δ.length) (d + Δ.length + 1) rl
      (d + Δ.length + 2) hlay hlen hl (hb.mono (by omega))
      (fun l h => ⟨hnin _ (.inl (hb l h)), by have := hb l h; omega, by have := hb l h; omega⟩) hwb P hPok hPs
      (init.den v) r hruns hP0 σ1 hR2
    have rΓ3 : Rel Γ L v σ3 := Rel.frame rΓ1 (fun l h => by
        have := hb l h
        rw [k3 l.v (by omega) (hnin _ (.inl this)) (by omega) (by omega)])
      (by rw [h3]) (by rw [w3]) hl
    have rk : Rel (s :: Γ) (resLoc s (d + Δ.length) rl :: L) (r, v) σ3 := by
      refine ⟨?_, rΓ3⟩
      cases s with
      | sc t => exact rr3
      | ar k => exact rr3
    have hbk : Below (resLoc s (d + Δ.length) rl :: L) (d + Δ.length + 2) := by
      refine below_cons hb ?_ (by omega)
      cases s with
      | sc t => simp [resLoc, scLoc]
      | ar k => exact hrl
    have hlok : LowLocs (resLoc s (d + Δ.length) rl :: L) (init.comp L d wo).2.2 := by
      intro l h
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · cases s with
        | sc t => exact .inl rfl
        | ar k =>
          show rl.inp = true ∨ ∃ c, rl.cap = some c ∧ rl.off + c ≤ _
          simp only [Sl.isAr, Bool.not_true, Bool.false_or, List.contains_iff_mem, List.mem_append] at hrc
          rcases hrc with h | h
          · exact l1 _ h
          · exact (hlo _ h).elim .inl fun ⟨c, hc, hle⟩ => .inr ⟨c, hc, by omega⟩
      · exact (hlo _ h).elim .inl fun ⟨c, hc, hle⟩ => .inr ⟨c, hc, by omega⟩
    obtain ⟨σ4, W4, e4, h4, w4, s4⟩ := Pg.comp_ok _ k (r, v) σ3 (d + Δ.length + 2) _ W1 y rk (by simp; omega) hbk
      hlok hwk hgk (by rw [w3]; exact w1) (by rw [k1.1]; omega) (by rw [k1.1]; exact h32)
    exact ⟨σ4, W4, .seq e1 (.seq e3 e4), by rw [h4, h3]; exact h1, w4, s4⟩

end Proven.WA
