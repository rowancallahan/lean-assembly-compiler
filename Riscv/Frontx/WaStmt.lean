/- Word arrays (NOTES section 20), compiler part 3: loop bodies and loops.

A loop with state `Δ` (slot `j` in variable `st[j].v`; arrays keep their elements where their `Loc` says),
result variable `res`, flag `fl`, temporaries from `d`: `fl := 1; while fl { body }`.  A body `T` is a
decision tree: `ite` is two at-most-once loops, `let` a fresh variable, a `call` leaf first evaluates every
new scalar component into temporaries `d, d + 1, ...` (all in the old state) and then copies them into the
state variables; a `ret` leaf puts the result in `res` (a scalar) or leaves it in its slot (an array) and
clears `fl`. -/
import Riscv.Frontx.WaUpd

namespace Proven.WA
open Proven Proven.Frontx


/-! ## Call leaves -/

/-- evaluate the scalar components into `d + j` -/
def Args.pre (L : List Loc) {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → Nat → MS
  | _, .nil, d => skipAt d
  | _, @Args.cons _ (.sc _) _ e as, d => .seq (E.comp L e d) (as.pre L (d + 1))
  | _, @Args.cons _ (.ar _) _ _ as, d => .seq (skipAt d) (as.pre L (d + 1))

/-- copy them into the state variables -/
def Args.copy {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → List Loc → Nat → MS
  | _, .nil, _, d => skipAt d
  | _, @Args.cons _ (.sc _) _ _ as, st, d => .seq (.assign (st.headD default).v (.var d)) (as.copy st.tail (d + 1))
  | _, @Args.cons _ (.ar _) _ _ as, st, d => .seq (skipAt d) (as.copy st.tail (d + 1))

/-- static: the scalars' expressions are well formed, an array component is the array of its own slot, unchanged
or (at most one, `cw`) updated in place in the words of `w` -/
def Args.wf (L : List Loc) {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → List Loc → Loc → Bool → Bool
  | _, .nil, _, _, _ => true
  | _, @Args.cons _ (.sc _) _ e as, st, w, cw => E.wf L e && as.wf L st.tail w cw
  | _, @Args.cons _ (.ar _) _ a as, st, w, cw =>
    match a with
    | .var m => m.loc L == st.headD default && as.wf L st.tail w cw
    | _ => cw && A.wf L a && a.base.loc L == st.headD default && st.headD default == w && !w.inp &&
        as.wf L st.tail w false

def Args.ok {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → Vals Γ → Prop
  | _, .nil, _ => True
  | _, @Args.cons _ (.sc _) _ e as, v => E.ok e v ∧ as.ok v
  | _, @Args.cons _ (.ar _) _ a as, v => A.ok a v ∧ as.ok v

/-- the in-place update of the (one) array component that changes -/
def Args.upd (L : List Loc) {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → List Loc → Nat → MS
  | _, .nil, _, e => skipAt e
  | _, @Args.cons _ (.sc _) _ _ as, st, e => as.upd L st.tail e
  | _, @Args.cons _ (.ar _) _ a as, st, e =>
    match a with
    | .var _ => as.upd L st.tail e
    | _ => .seq (A.pre L a e) (A.st (st.headD default) (e + a.nt) a e)

/-! ## Bodies -/

def T.comp (st : List Loc) (res fl : Nat) : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → List Loc → Nat → MS
  | _, _, .sc _, .ret e, L, d => .seq (E.comp L e d) (.seq (.assign res (.var d)) (.assign fl (.const 0)))
  | _, _, .ar _, .ret _, _, _ => .assign fl (.const 0)
  | _, Δ, _, .call as, L, d => .seq (as.pre L d) (.seq (as.upd L st (d + Δ.length)) (as.copy st d))
  | _, _, _, .ite c a b, L, d =>
    .seq (E.comp L c d) (.seq (.assign (d + 1) (.bin .eq (.var d) (.const 0)))
      (.seq (when d (a.comp st res fl L (d + 2))) (when (d + 1) (b.comp st res fl L (d + 2)))))
  | _, _, _, .let_ e k, L, d => .seq (E.comp L e d) (k.comp st res fl (scLoc d :: L) (d + 1))

/-- static conditions; `rl` is where an array result lives -/
def T.wf (st : List Loc) (rl w : Loc) : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → List Loc → Nat → Bool
  | _, _, .sc _, .ret e, L, _ => e.wf L
  | _, _, .ar _, .ret a, L, _ => match a with | .var m => m.loc L == rl | _ => false
  | _, _, _, .call as, L, _ => as.wf L st w true
  | _, _, _, .ite c a b, L, d => c.wf L && a.wf st rl w L (d + 2) && b.wf st rl w L (d + 2)
  | _, _, _, .let_ e k, L, d => e.wf L && k.wf st rl w (scLoc d :: L) (d + 1)

def T.ok : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → Vals Γ → Prop
  | _, _, .sc _, .ret e, v => e.ok v
  | _, _, .ar _, .ret _, _ => True
  | _, _, _, .call as, v => as.ok v
  | _, _, _, .ite c a b, v => c.ok v ∧ if c.den v = true then a.ok v else b.ok v
  | _, _, _, .let_ e k, v => e.ok v ∧ k.ok (e.den v, v)

/-- the result is represented: a scalar in `res`, an array at `rl` -/
def RR (σ : MSt) : (R : Sl) → Nat → Loc → R.T → Prop
  | .sc t, res, _, r => σ.env res = t.rep r
  | .ar k, _, rl, r => SR σ (.ar k) rl r

/-! ## Correctness of a call leaf -/

/-- the temporaries hold the new scalar components -/
def Args.Tmps {Γ : List Sl} (σ : MSt) : {Δ : List Sl} → Args Γ Δ → Vals Γ → Nat → Prop
  | _, .nil, _, _ => True
  | _, @Args.cons _ (.sc t) _ e as, v, d => σ.env d = t.rep (E.den e v) ∧ as.Tmps σ v (d + 1)
  | _, @Args.cons _ (.ar _) _ _ as, v, d => as.Tmps σ v (d + 1)

theorem Args.Tmps.frame {Γ : List Sl} {σ σ' : MSt} : ∀ {Δ : List Sl} {as : Args Γ Δ} {v : Vals Γ} {d : Nat},
    as.Tmps σ v d → (∀ j, d ≤ j → j < d + Δ.length → σ'.env j = σ.env j) → as.Tmps σ' v d
  | _, .nil, _, _, _, _ => by simp only [Args.Tmps]
  | _, @Args.cons _ (.sc _) _ _ _, _, _, h, he => by
    simp only [Args.Tmps] at h ⊢
    exact ⟨by rw [he _ (by omega) (by simp)]; exact h.1,
      Args.Tmps.frame h.2 fun j h1 h2 => he j (by omega) (by simp at h2 ⊢; omega)⟩
  | _, @Args.cons _ (.ar _) _ _ _, _, _, h, he => by
    simp only [Args.Tmps] at h ⊢
    exact Args.Tmps.frame h fun j h1 h2 => he j (by omega) (by simp at h2 ⊢; omega)

theorem Args.wf_tail_ar {L : List Loc} {Γ Δ : List Sl} {k : AK} {a : A Γ k} {as : Args Γ Δ} {st : List Loc} {w : Loc}
    {cw : Bool} (h : (Args.cons (s := .ar k) a as).wf L st w cw = true) : ∃ cw', as.wf L st.tail w cw' = true := by
  simp only [Args.wf] at h
  split at h
  · simp only [Bool.and_eq_true] at h; exact ⟨cw, h.2⟩
  · simp only [Bool.and_eq_true] at h; exact ⟨false, h.2⟩

theorem Args.pre_ok (L : List Loc) {Γ : List Sl} (st : List Loc) (w : Loc) : ∀ {Δ : List Sl} (as : Args Γ Δ)
    (v : Vals Γ) (σ : MSt) (d : Nat) (cw : Bool), Rel Γ L v σ → Γ.length ≤ L.length → Below L d →
    as.wf L st w cw = true → as.ok v →
    ∃ σ', Mach.BExec (as.pre L d) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap ∧
      (∀ j, j < d → σ'.env j = σ.env j) ∧ as.Tmps σ' v d
  | _, .nil, v, σ, d, _, _, _, _, _, _ =>
    ⟨_, .assign, rfl, rfl, fun j hj => set_ne (by omega), by simp only [Args.Tmps]⟩
  | _, @Args.cons _ (.sc t) _ e as, v, σ, d, cw, hR, hl, hb, hwf, hok => by
    simp only [Args.wf, Bool.and_eq_true] at hwf; simp only [Args.ok] at hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.comp_ok L e v σ d hR hl hb hwf.1 hok.1).frame hR hb hl
    obtain ⟨σ2, e2, h2, w2, k2, t2⟩ :=
      Args.pre_ok L st.tail w as v σ1 (d + 1) cw r1 hl (hb.mono (by omega)) hwf.2 hok.2
    refine ⟨σ2, .seq e1 e2, h2.trans h1, w2.trans w1, fun j hj => by rw [k2 j (by omega), k1 j hj], ?_⟩
    simp only [Args.Tmps]
    exact ⟨by rw [k2 d (by omega)]; exact v1, t2⟩
  | _, @Args.cons _ (.ar _) _ a as, v, σ, d, cw, hR, hl, hb, hwf, hok => by
    obtain ⟨cw', hwf⟩ := Args.wf_tail_ar hwf; simp only [Args.ok] at hok
    have r1 : Rel Γ L v ⟨σ.env.set d 0, σ.heap, σ.wheap⟩ :=
      Rel.below hR hb hl (fun j hj => set_ne (by omega)) rfl rfl
    obtain ⟨σ2, e2, h2, w2, k2, t2⟩ :=
      Args.pre_ok L st.tail w as v _ (d + 1) cw' r1 hl (hb.mono (by omega)) hwf hok.2
    refine ⟨σ2, .seq .assign e2, h2, w2, fun j hj => by rw [k2 j (by omega)]; exact set_ne (by omega), ?_⟩
    simp only [Args.Tmps]; exact t2

/-- after the copies: the scalar slots hold the new values, the array slots' variables are kept -/
def Args.Res {Γ : List Sl} (σ σ' : MSt) : {Δ : List Sl} → Args Γ Δ → List Loc → Vals Γ → Prop
  | _, .nil, _, _ => True
  | _, @Args.cons _ (.sc t) _ e as, st, v => σ'.env (st.headD default).v = t.rep (E.den e v) ∧ as.Res σ σ' st.tail v
  | _, @Args.cons _ (.ar _) _ _ as, st, v =>
    σ'.env (st.headD default).v = σ.env (st.headD default).v ∧ as.Res σ σ' st.tail v

theorem Args.Res.frame {Γ : List Sl} {σ σ' σ'' : MSt} : ∀ {Δ : List Sl} {as : Args Γ Δ} {st : List Loc} {v : Vals Γ},
    as.Res σ σ' st v → (∀ l ∈ st, σ''.env l.v = σ'.env l.v) → st.length = Δ.length → as.Res σ σ'' st v
  | _, .nil, _, _, _, _, _ => by simp only [Args.Res]
  | _, .cons _ _, [], _, _, _, hl => by simp at hl
  | _, @Args.cons _ (.sc _) _ _ _, l :: st, _, h, he, hl => by
    simp only [Args.Res, List.headD_cons, List.tail_cons] at h ⊢
    exact ⟨by rw [he l (by simp)]; exact h.1,
      Args.Res.frame h.2 (fun l' h' => he l' (by simp [h'])) (by simpa using hl)⟩
  | _, @Args.cons _ (.ar _) _ _ _, l :: st, _, h, he, hl => by
    simp only [Args.Res, List.headD_cons, List.tail_cons] at h ⊢
    exact ⟨by rw [he l (by simp)]; exact h.1,
      Args.Res.frame h.2 (fun l' h' => he l' (by simp [h'])) (by simpa using hl)⟩

theorem Args.Res.base {Γ : List Sl} {σ σ1 σ' : MSt} : ∀ {Δ : List Sl} {as : Args Γ Δ} {st : List Loc} {v : Vals Γ},
    as.Res σ1 σ' st v → (∀ l ∈ st, σ1.env l.v = σ.env l.v) → st.length = Δ.length → as.Res σ σ' st v
  | _, .nil, _, _, _, _, _ => by simp only [Args.Res]
  | _, .cons _ _, [], _, _, _, hl => by simp at hl
  | _, @Args.cons _ (.sc _) _ _ _, l :: st, _, h, he, hl => by
    simp only [Args.Res, List.headD_cons, List.tail_cons] at h ⊢
    exact ⟨h.1, Args.Res.base h.2 (fun l' h' => he l' (by simp [h'])) (by simpa using hl)⟩
  | _, @Args.cons _ (.ar _) _ _ _, l :: st, _, h, he, hl => by
    simp only [Args.Res, List.headD_cons, List.tail_cons] at h ⊢
    exact ⟨by rw [h.1, he l (by simp)], Args.Res.base h.2 (fun l' h' => he l' (by simp [h'])) (by simpa using hl)⟩

theorem Args.copy_ok {Γ : List Sl} : ∀ {Δ : List Sl} (as : Args Γ Δ) (st : List Loc) (v : Vals Γ) (σ : MSt) (d : Nat),
    as.Tmps σ v d → Below st d → (vsOf st).Nodup → st.length = Δ.length →
    ∃ σ', Mach.BExec (as.copy st d) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap ∧
      (∀ j, j < d → j ∉ vsOf st → σ'.env j = σ.env j) ∧ as.Res σ σ' st v
  | _, .nil, st, v, σ, d, _, _, _, _ =>
    ⟨_, .assign, rfl, rfl, fun j hj _ => set_ne (by omega), by simp only [Args.Res]⟩
  | _, .cons _ _, [], _, _, _, _, _, _, hl => by simp at hl
  | _, @Args.cons _ (.sc t) _ e as, l :: st, v, σ, d, ht, hb, hn, hl => by
    simp only [Args.Tmps] at ht
    simp only [Args.copy, Args.Res, List.headD_cons, List.tail_cons]
    simp only [vsOf, List.map_cons, List.nodup_cons] at hn
    have hlv : l.v < d := hb l (by simp)
    have hbs : Below st (d + 1) := fun l' h' => Nat.lt_succ_of_lt (hb l' (by simp [h']))
    let σ1 : MSt := ⟨σ.env.set l.v (σ.env d), σ.heap, σ.wheap⟩
    have ht1 : as.Tmps σ1 v (d + 1) := Args.Tmps.frame ht.2 fun j h1 h2 => set_ne (by omega)
    obtain ⟨σ2, e2, h2, w2, k2, r2⟩ := Args.copy_ok as st v σ1 (d + 1) ht1 hbs hn.2 (by simpa using hl)
    refine ⟨σ2, .seq .assign e2, h2, w2, fun j hj hj' => ?_, ⟨?_, ?_⟩⟩
    · simp only [vsOf, List.map_cons, List.mem_cons, not_or] at hj'
      rw [k2 j (by omega) hj'.2]; exact set_ne hj'.1
    · rw [k2 l.v (by omega) hn.1]; simp only [σ1, set_eq]; exact ht.1
    · refine Args.Res.base r2 (fun l' h' => set_ne ?_) (by simpa using hl)
      intro e; apply hn.1; rw [← e]; exact List.mem_map_of_mem h'
  | _, @Args.cons _ (.ar _) _ _ as, l :: st, v, σ, d, ht, hb, hn, hl => by
    simp only [Args.Tmps] at ht
    simp only [Args.copy, Args.Res, List.headD_cons, List.tail_cons]
    simp only [vsOf, List.map_cons, List.nodup_cons] at hn
    have hlv : l.v < d := hb l (by simp)
    have hbs : Below st (d + 1) := fun l' h' => Nat.lt_succ_of_lt (hb l' (by simp [h']))
    let σ1 : MSt := ⟨σ.env.set d 0, σ.heap, σ.wheap⟩
    have ht1 : as.Tmps σ1 v (d + 1) := Args.Tmps.frame ht fun j h1 h2 => set_ne (by omega)
    obtain ⟨σ2, e2, h2, w2, k2, r2⟩ := Args.copy_ok as st v σ1 (d + 1) ht1 hbs hn.2 (by simpa using hl)
    refine ⟨σ2, .seq .assign e2, h2, w2, fun j hj hj' => ?_, ⟨?_, ?_⟩⟩
    · simp only [vsOf, List.map_cons, List.mem_cons, not_or] at hj'
      rw [k2 j (by omega) hj'.2]; exact set_ne (by omega)
    · rw [k2 l.v (by omega) hn.1]; exact set_ne (by omega)
    · exact Args.Res.base r2 (fun l' h' => set_ne (by have := hbs l' h'; have := hb l' (by simp [h']); omega))
        (by simpa using hl)

/-- the arrays of the new state are represented (after the update) -/
def Args.ArrOK {Γ : List Sl} (σ : MSt) : {Δ : List Sl} → Args Γ Δ → List Loc → Vals Γ → Prop
  | _, .nil, _, _ => True
  | _, @Args.cons _ (.sc _) _ _ as, st, v => as.ArrOK σ st.tail v
  | _, @Args.cons _ (.ar k) _ a as, st, v => SR σ (.ar k) (st.headD default) (A.den a v) ∧ as.ArrOK σ st.tail v

/-- after a call leaf the state slots represent the new state -/
theorem Args.rel {Γ : List Sl} : ∀ {Δ : List Sl} (as : Args Γ Δ) (st : List Loc) (v : Vals Γ) (σu σ' : MSt),
    as.Res σu σ' st v → as.ArrOK σu st v → σ'.heap = σu.heap → σ'.wheap = σu.wheap → st.length = Δ.length →
    Rel Δ st (as.den v) σ'
  | _, .nil, _, _, _, _, _, _, _, _, _ => trivial
  | _, .cons _ _, [], _, _, _, _, _, _, _, hl => by simp at hl
  | _, @Args.cons _ (.sc t) _ e as, l :: st, v, σu, σ', hres, ha, hh, hw, hlen => by
    simp only [Args.Res, List.headD_cons, List.tail_cons] at hres
    simp only [Args.ArrOK, List.tail_cons] at ha
    refine ⟨?_, Args.rel as st v σu σ' hres.2 ha hh hw (by simpa using hlen)⟩
    show σ'.env l.v = _
    rw [hres.1]; rfl
  | _, @Args.cons _ (.ar k) _ a as, l :: st, v, σu, σ', hres, ha, hh, hw, hlen => by
    simp only [Args.Res, List.headD_cons, List.tail_cons] at hres
    simp only [Args.ArrOK, List.headD_cons, List.tail_cons] at ha
    exact ⟨SR.frame ha.1 hres.1 hh hw, Args.rel as st v σu σ' hres.2 ha.2 hh hw (by simpa using hlen)⟩

/-- the in-place stores happen in `w` -/
def WO (w : Loc) (σ σ' : MSt) : Prop := ∀ W, σ.wheap = [W] → ∃ W', σ'.wheap = [W'] ∧ WOut w W W'

theorem WO.of_eq {w : Loc} {σ σ' : MSt} (h : σ'.wheap = σ.wheap) : WO w σ σ' := fun W hW => ⟨W, h.trans hW, WOut.refl w W⟩
theorem WO.trans {w : Loc} {σ σ1 σ2 : MSt} (h1 : WO w σ σ1) (h2 : WO w σ1 σ2) : WO w σ σ2 := fun W hW =>
  let ⟨W1, a, b⟩ := h1 W hW
  let ⟨W2, c, d⟩ := h2 W1 a
  ⟨W2, c, b.trans d⟩
theorem WO.ex {w : Loc} {σ σ' : MSt} (h : WO w σ σ') (hW : ∃ W, σ.wheap = [W]) : ∃ W, σ'.wheap = [W] :=
  let ⟨W, hW⟩ := hW; let ⟨W', h', _⟩ := h W hW; ⟨W', h'⟩

theorem SR.wo {σ σ' : MSt} {s : Sl} {l w : Loc} {x : s.T} (h : SR σ s l x) (hv : σ'.env l.v = σ.env l.v)
    (hh : σ'.heap = σ.heap) (hW : ∃ W, σ.wheap = [W]) (ho : WO w σ σ') (hs : Loc.sep l w = true) : SR σ' s l x := by
  obtain ⟨W, hW⟩ := hW
  obtain ⟨W', hW', ho'⟩ := ho W hW
  exact SR.wsep h hv hh hW hW' ho' hs

theorem Rel.wo : ∀ {Γ : List Sl} {L : List Loc} {v : Vals Γ} {σ σ' : MSt} {w : Loc}, Rel Γ L v σ →
    (∀ l ∈ L, σ'.env l.v = σ.env l.v) → σ'.heap = σ.heap → (∃ W, σ.wheap = [W]) → WO w σ σ' →
    (∀ l ∈ L, Loc.sep l w = true) → Γ.length ≤ L.length → Rel Γ L v σ'
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, hl => by simp at hl
  | _ :: _, l :: L, _, _, _, _, h, hv, hh, hW, ho, hs, hl =>
    ⟨SR.wo h.1 (hv l (by simp)) hh hW ho (hs l (by simp)),
      Rel.wo h.2 (fun l' h' => hv l' (List.mem_cons_of_mem _ h')) hh hW ho (fun l' h' => hs l' (List.mem_cons_of_mem _ h'))
        (by simp at hl ⊢; omega)⟩

/-- the unchanged arrays of a call leaf (after the update, all components are slots) -/
theorem Args.arrOK_vars {Γ : List Sl} (L : List Loc) (w : Loc) : ∀ {Δ : List Sl} (as : Args Γ Δ) (st : List Loc)
    (v : Vals Γ) (σ σ' : MSt), as.wf L st w false = true → Rel Γ L v σ → (∀ l ∈ st, σ'.env l.v = σ.env l.v) →
    σ'.heap = σ.heap → (∃ W, σ.wheap = [W]) → WO w σ σ' → (∀ l ∈ st, Loc.sep l w = true) → st.length = Δ.length →
    as.ArrOK σ' st v
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _, .cons _ _, [], _, _, _, _, _, _, _, _, _, _, hl => by simp at hl
  | _, @Args.cons _ (.sc t) _ e as, l :: st, v, σ, σ', hwf, hR, hv, hh, hW, ho, hs, hl => by
    simp only [Args.wf, Bool.and_eq_true] at hwf
    simp only [Args.ArrOK, List.tail_cons]
    exact Args.arrOK_vars L w as st v σ σ' hwf.2 hR (fun l' h' => hv l' (by simp [h'])) hh hW ho
      (fun l' h' => hs l' (by simp [h'])) (by simpa using hl)
  | _, @Args.cons _ (.ar k) _ a as, l :: st, v, σ, σ', hwf, hR, hv, hh, hW, ho, hs, hl => by
    simp only [Args.ArrOK, List.headD_cons, List.tail_cons]
    cases a with
    | var m =>
      simp only [Args.wf, Bool.and_eq_true, beq_iff_eq, List.headD_cons, List.tail_cons] at hwf
      have hS := Rel.get m hR
      rw [hwf.1] at hS
      exact ⟨SR.wo hS (hv l (by simp)) hh hW ho (hs l (by simp)),
        Args.arrOK_vars L w as st v σ σ' hwf.2 hR (fun l' h' => hv l' (by simp [h'])) hh hW ho
          (fun l' h' => hs l' (by simp [h'])) (by simpa using hl)⟩
    | set _ _ _ | push _ _ | ite _ _ _ => simp [Args.wf] at hwf

theorem count_le_one_tail {w l : Loc} {st : List Loc} (h : (l :: st).count w ≤ 1) (hm : w ∈ st) : l ≠ w := by
  intro e; subst e
  have := List.count_pos_iff.2 hm
  simp [List.count_cons] at h; omega

theorem Args.upd_written (L : List Loc) {Γ : List Sl} (w : Loc) {k : AK} {Δ : List Sl} (a : A Γ k) (as : Args Γ Δ)
    (st : List Loc) (v : Vals Γ) (σ : MSt) (e : Nat) (hR : Rel Γ L v σ) (hl : Γ.length ≤ L.length)
    (hb : Below L e) (hbs : Below (w :: st) e) (hwa : A.wf L a = true) (hbase : a.base.loc L = w)
    (hin : w.inp = false) (hwt : as.wf L st w false = true) (hok : A.ok a v) (hW : ∃ W, σ.wheap = [W])
    (hlen : st.length = Δ.length) (hsep : ∀ l' ∈ st, l'.v ≠ w.v ∧ Loc.sep l' w = true) :
    ∃ σ', Mach.BExec (.seq (A.pre L a e) (A.st w (e + a.nt) a e)) σ σ' ∧ σ'.heap = σ.heap ∧ WO w σ σ' ∧
      (∀ j, j < e → j ≠ w.v → σ'.env j = σ.env j) ∧ SR σ' (.ar k) w (A.den a v) ∧ as.ArrOK σ' st v := by
  obtain ⟨σ1, e1, h1, w1, k1, t1⟩ := A.pre_ok L a v σ e hR hl hb hwa hok
  obtain ⟨W, hW0⟩ := hW
  have hS := Rel.get a.base hR
  rw [hbase] at hS
  have hlv : w.v < e := hbs w (by simp)
  have hS1 : SR σ1 (.ar k) w (a.base.get v) := SR.frame hS (k1 _ hlv) h1 w1
  obtain ⟨σ2, W2, e2, h2, w2, l2, o2, k2, s2⟩ := A.st_ok L w (e + a.nt) a v σ1 e W hin hlv (Nat.le_refl _)
    (by rw [w1, hW0]) hwa t1 hok hS1
  have hWO : WO w σ σ2 := fun W' hW' => by
    rw [hW0] at hW'; cases hW'
    exact ⟨W2, w2, ⟨l2, o2⟩⟩
  have hk : ∀ j, j < e → j ≠ w.v → σ2.env j = σ.env j := fun j hj hjw => by
    rw [k2 j hjw (by omega) (.inl hj), k1 j hj]
  refine ⟨σ2, .seq e1 e2, by rw [h2, h1], hWO, hk, s2, ?_⟩
  exact Args.arrOK_vars L w as st v σ σ2 hwt hR (fun l' h' => hk _ (hbs l' (by simp [h'])) (hsep l' h').1)
    (by rw [h2, h1]) ⟨W, hW0⟩ hWO (fun l' h' => (hsep l' h').2) hlen

set_option maxHeartbeats 1000000 in
theorem Args.upd_ok (L : List Loc) {Γ : List Sl} (w : Loc) : ∀ {Δ : List Sl} (as : Args Γ Δ) (st : List Loc)
    (v : Vals Γ) (σ : MSt) (e : Nat) (cw : Bool), Rel Γ L v σ → Γ.length ≤ L.length → Below L e → Below st e →
    as.wf L st w cw = true → as.ok v → (∃ W, σ.wheap = [W]) → st.length = Δ.length →
    (∀ l ∈ st, l ≠ w → l.v ≠ w.v ∧ Loc.sep l w = true) → st.count w ≤ 1 →
    ∃ σ', Mach.BExec (as.upd L st e) σ σ' ∧ σ'.heap = σ.heap ∧ WO w σ σ' ∧
      (∀ j, j < e → j ≠ w.v → σ'.env j = σ.env j) ∧ as.ArrOK σ' st v ∧
      ((σ'.wheap = σ.wheap ∧ ∀ j, j < e → σ'.env j = σ.env j) ∨ w ∈ st)
  | _, .nil, _, v, σ, e, _, _, _, _, _, _, _, _, _, _, _ =>
    ⟨_, .assign, rfl, WO.of_eq rfl, fun j hj _ => set_ne (by omega), trivial, .inl ⟨rfl, fun j hj => set_ne (by omega)⟩⟩
  | _, .cons _ _, [], _, _, _, _, _, _, _, _, _, _, _, hl, _, _ => by simp at hl
  | _, @Args.cons _ (.sc t) _ x as, l :: st, v, σ, e, cw, hR, hl, hb, hbs, hwf, hok, hW, hlen, hsep, hc => by
    simp only [Args.wf, Bool.and_eq_true] at hwf; simp only [Args.ok] at hok
    simp only [Args.upd, List.tail_cons]
    obtain ⟨σ', e1, h1, o1, k1, a1, d1⟩ := Args.upd_ok L w as st v σ e cw hR hl hb
      (fun l' h' => hbs l' (by simp [h'])) hwf.2 hok.2 hW (by simpa using hlen) (fun l' h' => hsep l' (by simp [h']))
      (by simp [List.count_cons] at hc ⊢; omega)
    exact ⟨σ', e1, h1, o1, k1, a1, d1.elim .inl fun h => .inr (by simp [h])⟩
  | _, @Args.cons _ (.ar k) _ a as, l :: st, v, σ, e, cw, hR, hl, hb, hbs, hwf, hok, hW, hlen, hsep, hc => by
    simp only [Args.ok] at hok
    have hsep' : ∀ l' ∈ st, l' ≠ w → l'.v ≠ w.v ∧ Loc.sep l' w = true := fun l' h' => hsep l' (by simp [h'])
    have hc' : st.count w ≤ 1 := by simp [List.count_cons] at hc ⊢; omega
    cases a with
    | var m =>
      simp only [Args.wf, Bool.and_eq_true, beq_iff_eq, List.headD_cons, List.tail_cons] at hwf
      simp only [Args.upd, List.tail_cons]
      obtain ⟨σ', e1, h1, o1, k1, a1, d1⟩ := Args.upd_ok L w as st v σ e cw hR hl hb
        (fun l' h' => hbs l' (by simp [h'])) hwf.2 hok.2 hW (by simpa using hlen) hsep' hc'
      have hS := Rel.get m hR
      rw [hwf.1] at hS
      have hlv : l.v < e := hbs l (by simp)
      refine ⟨σ', e1, h1, o1, k1, ⟨?_, a1⟩, d1.elim .inl fun h => .inr (by simp [h])⟩
      simp only [List.headD_cons, A.den]
      rcases d1 with ⟨dw, de⟩ | hm
      · exact SR.frame hS (de _ hlv) h1 dw
      · have hne := count_le_one_tail hc hm
        obtain ⟨hv, hs⟩ := hsep l (by simp) hne
        exact SR.wo hS (k1 _ hlv hv) h1 hW o1 hs
    | set _ _ _ | push _ _ | ite _ _ _ =>
      simp only [Args.wf, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.headD_cons, List.tail_cons] at hwf
      obtain ⟨⟨⟨⟨⟨_, hwa⟩, hbase⟩, hlw⟩, hin⟩, hwt⟩ := hwf
      subst hlw
      simp only [Args.upd, List.headD_cons, Args.ArrOK]
      have hst : ∀ l' ∈ st, l'.v ≠ l.v ∧ Loc.sep l' l = true := fun l' h' => by
        have hne : l' ≠ l := fun e => by
          subst e; have := List.count_pos_iff.2 h'; simp [List.count_cons] at hc; omega
        exact hsep l' (by simp [h']) hne
      obtain ⟨σ', e1, h1, o1, k1, s1, a1⟩ := Args.upd_written L l _ as st v σ e hR hl hb hbs hwa hbase hin hwt hok.1 hW
        (by simpa using hlen) hst
      exact ⟨σ', e1, h1, o1, k1, ⟨s1, a1⟩, .inr (by simp)⟩
/-- the outcome of one iteration -/
def Outc (Δ : List Sl) (R : Sl) (st : List Loc) (res fl : Nat) (rl : Loc) (σ σ' : MSt) : Vals Δ ⊕ R.T → Prop
  | .inl s' => σ'.env fl = σ.env fl ∧ Rel Δ st s' σ'
  | .inr r => σ'.env fl = 0 ∧ RR σ' R res rl r

theorem RR.frame {σ σ' : MSt} {R : Sl} {res : Nat} {rl : Loc} {r : R.T} (h : RR σ R res rl r)
    (hres : σ'.env res = σ.env res) (hrl : σ'.env rl.v = σ.env rl.v) (hh : σ'.heap = σ.heap)
    (hw : σ'.wheap = σ.wheap) : RR σ' R res rl r := by
  cases R with
  | sc t => show σ'.env res = _; rw [hres]; exact h
  | ar k => exact SR.frame (show SR σ (.ar k) rl r from h) hrl hh hw

theorem Outc.frame {Δ : List Sl} {R : Sl} {st : List Loc} {res fl : Nat} {rl : Loc} {σ σ1 σ' : MSt}
    {o : Vals Δ ⊕ R.T} (h : Outc Δ R st res fl rl σ σ1 o) (hk : ∀ l ∈ st, σ'.env l.v = σ1.env l.v)
    (hres : σ'.env res = σ1.env res) (hfl : σ'.env fl = σ1.env fl) (hrl : σ'.env rl.v = σ1.env rl.v)
    (hh : σ'.heap = σ1.heap) (hw : σ'.wheap = σ1.wheap) (hlen : Δ.length ≤ st.length) :
    Outc Δ R st res fl rl σ σ' o := by
  cases o with
  | inl s' => exact ⟨hfl.trans h.1, Rel.frame h.2 hk hh hw hlen⟩
  | inr r => exact ⟨hfl.trans h.1, RR.frame h.2 hres hrl hh hw⟩

theorem Outc.base {Δ : List Sl} {R : Sl} {st : List Loc} {res fl : Nat} {rl : Loc} {σ σ0 σ' : MSt}
    {o : Vals Δ ⊕ R.T} (h : Outc Δ R st res fl rl σ σ' o) (hfl : σ.env fl = σ0.env fl) :
    Outc Δ R st res fl rl σ0 σ' o := by
  cases o with
  | inl s' => exact ⟨h.1.trans hfl, h.2⟩
  | inr r => exact h

/-- the layout of a loop: state variables, `res`, `fl` below `d`, distinct -/
structure LoopLay (st : List Loc) (res fl : Nat) (rl w : Loc) (d : Nat) : Prop where
  bst : Below st d
  hres : res < d
  hfl : fl < d
  hrl : rl.v < d
  nd : (vsOf st).Nodup
  rs : res ∉ vsOf st
  fs : fl ∉ vsOf st
  rf : res ≠ fl
  rlf : rl.v ≠ fl
  wsep : ∀ l ∈ st, l ≠ w → l.v ≠ w.v ∧ Loc.sep l w = true
  wc : st.count w ≤ 1
  hwv : w.v < d

theorem LoopLay.mono {st : List Loc} {res fl : Nat} {rl w : Loc} {d d' : Nat} (h : LoopLay st res fl rl w d)
    (h' : d ≤ d') : LoopLay st res fl rl w d' :=
  ⟨h.bst.mono h', by have := h.hres; omega, by have := h.hfl; omega, by have := h.hrl; omega, h.nd, h.rs, h.fs, h.rf,
    h.rlf, h.wsep, h.wc, by have := h.hwv; omega⟩

set_option maxHeartbeats 1000000 in
/-- **One iteration of a loop body.** -/
theorem T.comp_ok (st : List Loc) (res fl : Nat) (rl w : Loc) : ∀ {Γ Δ : List Sl} {R : Sl} (b : T Γ Δ R)
    (L : List Loc) (v : Vals Γ) (σ : MSt) (d : Nat), Rel Γ L v σ → Γ.length ≤ L.length → Below L d →
    LoopLay st res fl rl w d → st.length = Δ.length → b.wf st rl w L d = true → b.ok v → (∃ W, σ.wheap = [W]) →
    ∃ σ', Mach.BExec (b.comp st res fl L d) σ σ' ∧ σ'.heap = σ.heap ∧ WO w σ σ' ∧
      (∀ j, j < d → j ∉ vsOf st → j ≠ res → j ≠ fl → σ'.env j = σ.env j) ∧
      Outc Δ R st res fl rl σ σ' (b.out v)
  | _, _, .sc t, .ret e, L, v, σ, d, hR, hl, hb, hy, hlen, hwf, hok, hW => by
    simp only [T.wf] at hwf; simp only [T.ok] at hok
    simp only [T.comp, T.out]
    obtain ⟨σ1, e1, v1, k1, h1, w1⟩ := E.comp_ok L e v σ d hR hl hb hwf hok
    refine ⟨_, .seq e1 (.seq .assign .assign), h1, WO.of_eq w1, fun j hj h1 h2 h3 => ?_, ?_, ?_⟩
    · simp only [set_ne h3, set_ne h2, k1 j hj]
    · simp only [set_eq]; rfl
    · show _ = _
      simp only [set_ne hy.rf, Mach.BExp.denote, set_eq, Arg.den]; rw [v1]
  | _, _, .ar k, .ret a, L, v, σ, d, hR, hl, hb, hy, hlen, hwf, hok, hW => by
    simp only [T.comp, T.out]
    cases a with
    | var m =>
      simp only [T.wf, beq_iff_eq] at hwf
      have hS := Rel.get m hR
      rw [hwf] at hS
      refine ⟨_, .assign, rfl, WO.of_eq rfl, fun j hj h1 h2 h3 => set_ne h3, ?_, ?_⟩
      · simp only [set_eq]; rfl
      · show SR _ (.ar k) rl (m.get v)
        exact SR.frame hS (set_ne hy.rlf) rfl rfl
    | set _ _ _ => simp [T.wf] at hwf
    | push _ _ => simp [T.wf] at hwf
    | ite _ _ _ => simp [T.wf] at hwf
  | _, Δ, _, .call as, L, v, σ, d, hR, hl, hb, hy, hlen, hwf, hok, hW => by
    simp only [T.wf] at hwf; simp only [T.ok] at hok
    simp only [T.comp, T.out]
    obtain ⟨σ1, e1, h1, w1, k1, t1⟩ := Args.pre_ok L st w as v σ d true hR hl hb hwf hok
    have r1 := Rel.below hR hb hl k1 h1 w1
    obtain ⟨σu, eu, hu, ou, ku, au, du⟩ := Args.upd_ok L w as st v σ1 (d + Δ.length) true r1 hl
      (hb.mono (by omega)) (hy.bst.mono (by omega)) hwf hok (by rw [w1]; exact hW) hlen hy.wsep hy.wc
    have hwd : ∀ j, j < d → j ∉ vsOf st → σu.env j = σ1.env j := fun j hj hs => by
      rcases du with ⟨_, de⟩ | hm
      · exact de j (by omega)
      · exact ku j (by omega) (fun e => hs (e ▸ List.mem_map_of_mem hm))
    have tu : as.Tmps σu v d := Args.Tmps.frame t1 fun j h1' h2 => ku j h2 (by have := hy.hwv; omega)
    obtain ⟨σ2, e2, h2, w2, k2, r2⟩ := Args.copy_ok as st v σu d tu hy.bst hy.nd hlen
    refine ⟨σ2, .seq e1 (.seq eu e2), by rw [h2, hu, h1], (WO.of_eq w1).trans (ou.trans (WO.of_eq w2)),
      fun j hj hs _ _ => by rw [k2 j hj hs, hwd j hj hs, k1 j hj], ?_, ?_⟩
    · rw [k2 fl hy.hfl hy.fs, hwd fl hy.hfl hy.fs, k1 fl hy.hfl]
    · exact Args.rel as st v σu σ2 r2 au h2 w2 hlen
  | _, _, _, .ite c a b, L, v, σ, d, hR, hl, hb, hy, hlen, hwf, hok, hW => by
    simp only [T.wf, Bool.and_eq_true] at hwf; simp only [T.ok] at hok
    obtain ⟨⟨hwc, hwa⟩, hwb⟩ := hwf
    simp only [T.comp, T.out]
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.comp_ok L c v σ d hR hl hb hwc hok.1).frame hR hb hl
    let σ2 : MSt := ⟨σ1.env.set (d + 1) ((Mach.BExp.bin .eq (.var d) (.const 0)).denote σ1.env), σ1.heap, σ1.wheap⟩
    have r2 : Rel _ L v σ2 :=
      Rel.below r1 (hb.mono (show d ≤ d + 1 by omega)) hl (fun j hj => set_ne (show j ≠ d + 1 by omega)) rfl rfl
    have e2 : Mach.BExec (.assign (d + 1) (.bin .eq (.var d) (.const 0))) σ1 σ2 := .assign
    have hc1 : σ2.env d = rB (c.den v) := by simp only [σ2, set_ne (show d ≠ d + 1 by omega)]; exact v1
    have hc2 : σ2.env (d + 1) = rB (!c.den v) := by
      simp only [σ2, set_eq, Mach.BExp.denote, Op.eval, v1]; cases c.den v <;> rfl
    have hk2 : ∀ j, j < d → σ2.env j = σ.env j := fun j hj => by
      simp only [σ2, set_ne (show j ≠ d + 1 by omega)]; exact k1 j hj
    have hy2 := hy.mono (show d ≤ d + 2 by omega)
    have hW2 : ∃ W, σ2.wheap = [W] := by simp only [σ2]; rw [w1]; exact hW
    have hns : ∀ j, d ≤ j → j ∉ vsOf st := fun j hj h => by
      obtain ⟨l, hl', e⟩ := List.mem_map.1 h; have := hy.bst l hl'; omega
    have hrd : res < d := hy.hres
    have hfd : fl < d := hy.hfl
    have hrl : rl.v < d := hy.hrl
    cases hcv : c.den v with
    | true =>
      have hoa := hok.2; rw [hcv, if_pos rfl] at hoa
      obtain ⟨σ3, e3, h3, w3, k3, o3⟩ := T.comp_ok st res fl rl w a L v σ2 (d + 2) r2 hl (hb.mono (by omega)) hy2
        hlen hwa hoa hW2
      have hne : σ2.env d ≠ 0 := by rw [hc1, hcv]; decide
      have hw1 := when_true hne e3
      let σ4 : MSt := ⟨σ3.env.set d 0, σ3.heap, σ3.wheap⟩
      have hz : σ4.env (d + 1) = 0 := by
        simp only [σ4, set_ne (show d + 1 ≠ d by omega)]
        rw [k3 (d + 1) (by omega) (hns _ (by omega)) (by omega) (by omega), hc2, hcv]; rfl
      refine ⟨σ4, .seq e1 (.seq e2 (.seq hw1 (when_false hz))), h3.trans h1,
        (WO.of_eq (σ' := σ2) w1).trans (w3.trans (WO.of_eq rfl)),
        fun j hj hs h1 h2 => ?_, ?_⟩
      · simp only [σ4, set_ne (show j ≠ d by omega)]
        rw [k3 j (by omega) hs h1 h2, hk2 j hj]
      · rw [if_pos rfl]
        refine Outc.base (σ := σ2) (Outc.frame (σ1 := σ3) o3 (fun l hl' => set_ne (by have := hy.bst l hl'; omega))
          (set_ne (by omega)) (set_ne (by omega)) (set_ne (by omega)) rfl rfl (by omega)) ?_
        exact hk2 fl hfd
    | false =>
      have hob := hok.2; rw [hcv] at hob; simp only [Bool.false_eq_true, if_false] at hob
      have hz : σ2.env d = 0 := by rw [hc1, hcv]; rfl
      obtain ⟨σ3, e3, h3, w3, k3, o3⟩ := T.comp_ok st res fl rl w b L v σ2 (d + 2) r2 hl (hb.mono (by omega)) hy2
        hlen hwb hob hW2
      have hne : σ2.env (d + 1) ≠ 0 := by rw [hc2, hcv]; decide
      have hw2 := when_true hne e3
      refine ⟨_, .seq e1 (.seq e2 (.seq (when_false hz) hw2)), h3.trans h1,
        (WO.of_eq (σ' := σ2) w1).trans (w3.trans (WO.of_eq rfl)),
        fun j hj hs h1 h2 => ?_, ?_⟩
      · simp only [set_ne (show j ≠ d + 1 by omega)]
        rw [k3 j (by omega) hs h1 h2, hk2 j hj]
      · simp only [Bool.false_eq_true, if_false]
        refine Outc.base (σ := σ2) (Outc.frame (σ1 := σ3) o3 (fun l hl' => set_ne (by have := hy.bst l hl'; omega))
          (set_ne (by omega)) (set_ne (by omega)) (set_ne (by omega)) rfl rfl (by omega)) ?_
        exact hk2 fl hfd
  | _, _, _, .let_ e k, L, v, σ, d, hR, hl, hb, hy, hlen, hwf, hok, hW => by
    simp only [T.wf, Bool.and_eq_true] at hwf; simp only [T.ok] at hok
    simp only [T.comp, T.out]
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.comp_ok L e v σ d hR hl hb hwf.1 hok.1).frame hR hb hl
    have r1' : Rel (.sc _ :: _) (scLoc d :: L) (E.den e v, v) σ1 := ⟨v1, r1⟩
    have hb1 : Below (scLoc d :: L) (d + 1) := by
      intro l hl'
      simp only [List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · simp [scLoc]
      · have := hb l hl'; omega
    obtain ⟨σ2, e2, h2, w2, k2, o2⟩ := T.comp_ok st res fl rl w k (scLoc d :: L) (E.den e v, v) σ1 (d + 1) r1'
      (by simp; omega) hb1 (hy.mono (by omega)) hlen hwf.2 hok.2 (by rw [w1]; exact hW)
    refine ⟨σ2, .seq e1 e2, h2.trans h1, (WO.of_eq w1).trans w2, fun j hj hs h1 h2 => by rw [k2 j (by omega) hs h1 h2, k1 j hj], ?_⟩
    exact Outc.base o2 (k1 fl hy.hfl)

/-! ## Loops -/

theorem Rel.app {Γ : List Sl} {L : List Loc} {c : Vals Γ} {σ : MSt} : ∀ {Δ : List Sl} {st : List Loc} {s : Vals Δ},
    st.length = Δ.length → (Rel (Δ ++ Γ) (st ++ L) (Vals.app s c) σ ↔ Rel Δ st s σ ∧ Rel Γ L c σ)
  | [], [], _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: _, [], _, h => by simp at h
  | [], _ :: _, _, h => by simp at h
  | _ :: Δ, l :: st, s, h => by
    show SR σ _ l s.1 ∧ Rel (Δ ++ Γ) (st ++ L) (Vals.app s.2 c) σ ↔ (SR σ _ l s.1 ∧ Rel Δ st s.2 σ) ∧ Rel Γ L c σ
    rw [Rel.app (by simpa using h)]; exact and_assoc.symm

theorem T.comp_loop {Δ Γ : List Sl} {R : Sl} (b : T (Δ ++ Γ) Δ R) (c : Vals Γ) (st L : List Loc) (res fl : Nat)
    (rl w : Loc) (d : Nat) (hy : LoopLay st res fl rl w d) (hlen : st.length = Δ.length) (hl : Γ.length ≤ L.length)
    (hbL : Below L d) (hLd : ∀ l ∈ L, l.v ∉ vsOf st ∧ l.v ≠ res ∧ l.v ≠ fl ∧ Loc.sep l w = true)
    (hwf : b.wf st rl w (st ++ L) d = true) (P : Vals Δ → Prop) (hok : ∀ s, P s → b.ok (Vals.app s c))
    (hP : ∀ s s', P s → b.out (Vals.app s c) = .inl s' → P s') :
    ∀ s r, Runs b c s r → P s → ∀ σ, Rel (Δ ++ Γ) (st ++ L) (Vals.app s c) σ → σ.env fl ≠ 0 →
      (∃ W, σ.wheap = [W]) →
      ∃ σ', Mach.BExec (.loop (.var fl) (b.comp st res fl (st ++ L) d)) σ σ' ∧ σ'.heap = σ.heap ∧
        WO w σ σ' ∧ (∀ j, j < d → j ∉ vsOf st → j ≠ res → j ≠ fl → σ'.env j = σ.env j) ∧
        RR σ' R res rl r := by
  have hl2 : (Δ ++ Γ).length ≤ (st ++ L).length := by simp; omega
  have hb2 : Below (st ++ L) d := fun l h => by
    rcases List.mem_append.1 h with h | h
    · exact hy.bst l h
    · exact hbL l h
  intro s r hr
  induction hr with
  | @ret s r ho =>
    intro _ σ hR hfl hW
    obtain ⟨σ1, e1, h1, w1, k1, o1⟩ := T.comp_ok st res fl rl w b (st ++ L) (Vals.app s c) σ d hR hl2 hb2 hy hlen
      hwf (hok s ‹_›) hW
    rw [ho] at o1
    exact ⟨σ1, .loopT hfl e1 (.loopF o1.1), h1, w1, k1, o1.2⟩
  | @call s s' r ho _ ih =>
    intro hPs σ hR hfl hW
    obtain ⟨σ1, e1, h1, w1, k1, o1⟩ := T.comp_ok st res fl rl w b (st ++ L) (Vals.app s c) σ d hR hl2 hb2 hy hlen
      hwf (hok s hPs) hW
    rw [ho] at o1
    have hR1 : Rel (Δ ++ Γ) (st ++ L) (Vals.app s' c) σ1 := by
      rw [Rel.app hlen] at hR ⊢
      refine ⟨o1.2, Rel.wo hR.2 (fun l hl' => ?_) h1 hW w1 (fun l hl' => (hLd l hl').2.2.2) hl⟩
      obtain ⟨a1, a2, a3, _⟩ := hLd l hl'
      exact k1 l.v (hbL l hl') a1 a2 a3
    obtain ⟨σ2, e2, h2, w2, k2, o2⟩ := ih (hP s s' hPs ho) σ1 hR1 (by rw [o1.1]; exact hfl) (w1.ex hW)
    exact ⟨σ2, .loopT hfl e1 e2, h2.trans h1, w1.trans w2,
      fun j hj a1 a2 a3 => by rw [k2 j hj a1 a2 a3, k1 j hj a1 a2 a3], o2⟩

/-! ## Loops of the shape `if c then (calls) else (results)`: a plain `while` -/

def T.noRet : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → Bool
  | _, _, _, .ret _ => false
  | _, _, _, .call _ => true
  | _, _, _, .ite _ a b => a.noRet && b.noRet
  | _, _, _, .let_ _ k => k.noRet

def T.noCall : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → Bool
  | _, _, _, .ret _ => true
  | _, _, _, .call _ => false
  | _, _, _, .ite _ a b => a.noCall && b.noCall
  | _, _, _, .let_ _ k => k.noCall

theorem T.out_noRet : ∀ {Γ Δ : List Sl} {R : Sl} (b : T Γ Δ R) (v : Vals Γ), b.noRet = true → ∃ s', b.out v = .inl s'
  | _, _, _, .ret _, _, h => by simp [T.noRet] at h
  | _, _, _, .call _, _, _ => ⟨_, rfl⟩
  | _, _, _, .ite c a b, v, h => by
    simp only [T.noRet, Bool.and_eq_true] at h
    simp only [T.out]; split
    · exact T.out_noRet a v h.1
    · exact T.out_noRet b v h.2
  | _, _, _, .let_ e k, v, h => by simp only [T.noRet] at h; simp only [T.out]; exact T.out_noRet k _ h

theorem T.out_noCall : ∀ {Γ Δ : List Sl} {R : Sl} (b : T Γ Δ R) (v : Vals Γ), b.noCall = true → ∃ r, b.out v = .inr r
  | _, _, _, .ret _, _, _ => ⟨_, rfl⟩
  | _, _, _, .call _, _, h => by simp [T.noCall] at h
  | _, _, _, .ite c a b, v, h => by
    simp only [T.noCall, Bool.and_eq_true] at h
    simp only [T.out]; split
    · exact T.out_noCall a v h.1
    · exact T.out_noCall b v h.2
  | _, _, _, .let_ e k, v, h => by simp only [T.noCall] at h; simp only [T.out]; exact T.out_noCall k _ h

/-- the code of a loop: `t := c; while t { calls; t := c }; results` for the shape `if c then calls else results`,
else `fl := 1; while fl { body }` -/
def T.loopCode (st : List Loc) (res fl : Nat) {Γ Δ : List Sl} {R : Sl} (b : T Γ Δ R) (L : List Loc) (d : Nat) : MS :=
  match b with
  | .ite c A B =>
    if A.noRet && B.noCall then
      .seq (E.comp L c d) (.seq (.loop (.var d) (.seq (A.comp st res fl L (d + 2)) (E.comp L c d)))
        (B.comp st res fl L (d + 2)))
    else .seq (.assign fl (.const 1)) (.loop (.var fl) (b.comp st res fl L d))
  | _ => .seq (.assign fl (.const 1)) (.loop (.var fl) (b.comp st res fl L d))

set_option maxHeartbeats 1000000 in
theorem fast_loop {Δ Γ : List Sl} {R : Sl} (c : E (Δ ++ Γ) .bool) (A B : T (Δ ++ Γ) Δ R) (cv : Vals Γ)
    (st L : List Loc) (res fl : Nat) (rl w : Loc) (d : Nat) (hy : LoopLay st res fl rl w d) (hlen : st.length = Δ.length)
    (hl : Γ.length ≤ L.length) (hbL : Below L d) (hLd : ∀ l ∈ L, l.v ∉ vsOf st ∧ l.v ≠ res ∧ l.v ≠ fl ∧ Loc.sep l w = true)
    (hwf : (T.ite c A B).wf st rl w (st ++ L) d = true) (hA : A.noRet = true) (hB : B.noCall = true)
    (P : Vals Δ → Prop)
    (hok : ∀ s, P s → (T.ite c A B).ok (Vals.app s cv))
    (hP : ∀ s s', P s → (T.ite c A B).out (Vals.app s cv) = .inl s' → P s') :
    ∀ s r, Runs (T.ite c A B) cv s r → P s → ∀ σ, Rel (Δ ++ Γ) (st ++ L) (Vals.app s cv) σ →
      σ.env d = rB (c.den (Vals.app s cv)) → (∃ W, σ.wheap = [W]) →
      ∃ σ' sf, Mach.BExec (.loop (.var d) (.seq (A.comp st res fl (st ++ L) (d + 2)) (E.comp (st ++ L) c d))) σ σ' ∧
        σ'.heap = σ.heap ∧ WO w σ σ' ∧
        (∀ j, j < d → j ∉ vsOf st → j ≠ res → j ≠ fl → σ'.env j = σ.env j) ∧
        Rel (Δ ++ Γ) (st ++ L) (Vals.app sf cv) σ' ∧ c.den (Vals.app sf cv) = false ∧
        Runs (T.ite c A B) cv sf r ∧ P sf := by
  have hl2 : (Δ ++ Γ).length ≤ (st ++ L).length := by simp; omega
  have hb2 : Below (st ++ L) d := fun l h => by
    rcases List.mem_append.1 h with h | h
    · exact hy.bst l h
    · exact hbL l h
  simp only [T.wf, Bool.and_eq_true] at hwf
  obtain ⟨⟨hwc, hwa⟩, hwb⟩ := hwf
  intro s r hr
  induction hr with
  | @ret s r ho =>
    intro hPs σ hR hd hW
    -- `c` is false here: a true `c` would give a `call`
    have hcf : c.den (Vals.app s cv) = false := by
      cases hc : c.den (Vals.app s cv) with
      | false => rfl
      | true =>
        obtain ⟨s', hs'⟩ := T.out_noRet A (Vals.app s cv) hA
        simp only [T.out, hc, if_true, hs'] at ho; cases ho
    exact ⟨σ, s, .loopF (by show σ.env d = 0; rw [hd, hcf]; rfl), rfl, WO.of_eq rfl, fun _ _ _ _ _ => rfl, hR, hcf,
      .ret ho, hPs⟩
  | @call s s' r ho hr' ih =>
    intro hPs σ hR hd hW
    have hoks := hok s hPs
    simp only [T.ok] at hoks
    by_cases hc : c.den (Vals.app s cv) = true
    · rw [hc, if_pos rfl] at hoks
      have hoA : A.out (Vals.app s cv) = .inl s' := by simp only [T.out, hc, if_true] at ho; exact ho
      have hy2 := hy.mono (show d ≤ d + 2 by omega)
      obtain ⟨σ1, e1, h1, w1, k1, o1⟩ := T.comp_ok st res fl rl w A (st ++ L) (Vals.app s cv) σ (d + 2) hR hl2
        (hb2.mono (by omega)) hy2 hlen hwa hoks.2 hW
      rw [hoA] at o1
      have hR1 : Rel (Δ ++ Γ) (st ++ L) (Vals.app s' cv) σ1 := by
        rw [Rel.app hlen] at hR ⊢
        refine ⟨o1.2, Rel.wo hR.2 (fun l hl' => ?_) h1 hW w1 (fun l hl' => (hLd l hl').2.2.2) hl⟩
        obtain ⟨a1, a2, a3, _⟩ := hLd l hl'
        exact k1 l.v (by have := hbL l hl'; omega) a1 a2 a3
      have hPs' := hP s s' hPs ho
      have hoks' := hok s' hPs'
      simp only [T.ok] at hoks'
      replace hoks' := hoks'.1
      obtain ⟨σ2, e2, v2, k2, h2, w2, r2⟩ := (E.comp_ok (st ++ L) c (Vals.app s' cv) σ1 d hR1 hl2 hb2 hwc hoks').frame
        hR1 hb2 hl2
      obtain ⟨σ3, sf, e3, h3, w3, k3, r3, c3, u3, p3⟩ := ih hPs' σ2 r2 v2 (by rw [w2]; exact w1.ex hW)
      have hne : σ.env d ≠ 0 := by rw [hd, hc]; decide
      refine ⟨σ3, sf, .loopT hne (.seq e1 e2) e3, by rw [h3, h2, h1], w1.trans ((WO.of_eq w2).trans w3),
        fun j hj a1 a2 a3 => by rw [k3 j hj a1 a2 a3, k2 j hj, k1 j (by omega) a1 a2 a3], r3, c3, u3, p3⟩
    · simp only [Bool.not_eq_true] at hc
      obtain ⟨r', hr''⟩ := T.out_noCall B (Vals.app s cv) hB
      simp only [T.out, hc, Bool.false_eq_true, if_false, hr''] at ho; cases ho

theorem slow_loop {Δ Γ : List Sl} {R : Sl} (b : T (Δ ++ Γ) Δ R) (cv : Vals Γ) (st L : List Loc) (res fl : Nat)
    (rl w : Loc) (d : Nat) (hy : LoopLay st res fl rl w d) (hlen : st.length = Δ.length) (hl : Γ.length ≤ L.length)
    (hbL : Below L d) (hLd : ∀ l ∈ L, l.v ∉ vsOf st ∧ l.v ≠ res ∧ l.v ≠ fl ∧ Loc.sep l w = true)
    (hwf : b.wf st rl w (st ++ L) d = true) (P : Vals Δ → Prop) (hok : ∀ s, P s → b.ok (Vals.app s cv))
    (hP : ∀ s s', P s → b.out (Vals.app s cv) = .inl s' → P s') (s : Vals Δ) (r : R.T) (hr : Runs b cv s r)
    (hPs : P s) (σ : MSt) (hR : Rel (Δ ++ Γ) (st ++ L) (Vals.app s cv) σ) (hW : ∃ W, σ.wheap = [W]) :
    ∃ σ', Mach.BExec (.seq (.assign fl (.const 1)) (.loop (.var fl) (b.comp st res fl (st ++ L) d))) σ σ' ∧
      σ'.heap = σ.heap ∧ WO w σ σ' ∧ (∀ j, j < d → j ∉ vsOf st → j ≠ res → j ≠ fl → σ'.env j = σ.env j) ∧
      RR σ' R res rl r := by
  let σ1 : MSt := ⟨σ.env.set fl ((Mach.BExp.const 1).denote σ.env), σ.heap, σ.wheap⟩
  have hR1 : Rel (Δ ++ Γ) (st ++ L) (Vals.app s cv) σ1 := by
    refine Rel.frame hR (fun l h => set_ne ?_) rfl rfl (by simp; omega)
    rcases List.mem_append.1 h with h | h
    · intro e; apply hy.fs; rw [← e]; exact List.mem_map_of_mem h
    · exact (hLd l h).2.2.1
  obtain ⟨σ2, e2, h2, w2, k2, r2⟩ := T.comp_loop b cv st L res fl rl w d hy hlen hl hbL hLd hwf P hok hP s r hr hPs σ1
    hR1 (by simp only [σ1, set_eq, Mach.BExp.denote]; decide) hW
  exact ⟨σ2, .seq .assign e2, h2, (WO.of_eq (σ' := σ1) rfl).trans w2,
    fun j hj a1 a2 a3 => by rw [k2 j hj a1 a2 a3]; exact set_ne a3, r2⟩

theorem T.loopCode_ok {Δ Γ : List Sl} {R : Sl} (b : T (Δ ++ Γ) Δ R) (cv : Vals Γ) (st L : List Loc) (res fl : Nat)
    (rl w : Loc) (d : Nat) (hy : LoopLay st res fl rl w d) (hlen : st.length = Δ.length) (hl : Γ.length ≤ L.length)
    (hbL : Below L d) (hLd : ∀ l ∈ L, l.v ∉ vsOf st ∧ l.v ≠ res ∧ l.v ≠ fl ∧ Loc.sep l w = true)
    (hwf : b.wf st rl w (st ++ L) d = true) (P : Vals Δ → Prop) (hok : ∀ s, P s → b.ok (Vals.app s cv))
    (hP : ∀ s s', P s → b.out (Vals.app s cv) = .inl s' → P s') (s : Vals Δ) (r : R.T) (hr : Runs b cv s r)
    (hPs : P s) (σ : MSt) (hR : Rel (Δ ++ Γ) (st ++ L) (Vals.app s cv) σ) (hW : ∃ W, σ.wheap = [W]) :
    ∃ σ', Mach.BExec (b.loopCode st res fl (st ++ L) d) σ σ' ∧
      σ'.heap = σ.heap ∧ WO w σ σ' ∧ (∀ j, j < d → j ∉ vsOf st → j ≠ res → j ≠ fl → σ'.env j = σ.env j) ∧
      RR σ' R res rl r := by
  have hl2 : (Δ ++ Γ).length ≤ (st ++ L).length := by simp; omega
  have hb2 : Below (st ++ L) d := fun l h => by
    rcases List.mem_append.1 h with h | h
    · exact hy.bst l h
    · exact hbL l h
  unfold T.loopCode
  split
  · rename_i c A B
    split
    · rename_i hAB
      simp only [Bool.and_eq_true] at hAB
      have hw := hwf
      simp only [T.wf, Bool.and_eq_true] at hw
      obtain ⟨⟨hwc, hwa⟩, hwb⟩ := hw
      have hoks := hok s hPs
      simp only [T.ok] at hoks
      obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.comp_ok (st ++ L) c (Vals.app s cv) σ d hR hl2 hb2 hwc hoks.1).frame
        hR hb2 hl2
      obtain ⟨σ2, sf, e2, h2, w2, k2, r2, c2, u2, p2⟩ := fast_loop c A B cv st L res fl rl w d hy hlen hl hbL hLd hwf
        hAB.1 hAB.2 P hok hP s r hr hPs σ1 r1 v1 (by rw [w1]; exact hW)
      have hoB : B.out (Vals.app sf cv) = .inr r := by
        cases u2 with
        | ret ho => simp only [T.out, c2, Bool.false_eq_true, if_false] at ho; exact ho
        | call ho _ =>
          obtain ⟨r', hr'⟩ := T.out_noCall B (Vals.app sf cv) hAB.2
          simp only [T.out, c2, Bool.false_eq_true, if_false, hr'] at ho; cases ho
      have hoksf := hok sf p2
      simp only [T.ok, c2, Bool.false_eq_true, if_false] at hoksf
      obtain ⟨σ3, e3, h3, w3, k3, o3⟩ := T.comp_ok st res fl rl w B (st ++ L) (Vals.app sf cv) σ2 (d + 2) r2 hl2
        (hb2.mono (by omega)) (hy.mono (by omega)) hlen hwb hoksf.2 (w2.ex (by rw [w1]; exact hW))
      rw [hoB] at o3
      exact ⟨σ3, .seq e1 (.seq e2 e3), by rw [h3, h2, h1], (WO.of_eq w1).trans (w2.trans w3),
        fun j hj a1 a2 a3 => by rw [k3 j (by omega) a1 a2 a3, k2 j hj a1 a2 a3, k1 j hj], o3.2⟩
    · exact slow_loop _ cv st L res fl rl w d hy hlen hl hbL hLd hwf P hok hP s r hr hPs σ hR hW
  · exact slow_loop _ cv st L res fl rl w d hy hlen hl hbL hLd hwf P hok hP s r hr hPs σ hR hW

end Proven.WA
