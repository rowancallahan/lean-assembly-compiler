/- Word arrays (NOTES section 20), compiler part 3: loop bodies and loops.

A loop with state `Δ` (slot `j` in variable `st[j].v`; arrays keep their elements where their `Loc` says),
result variable `res`, flag `fl`, temporaries from `d`: `fl := 1; while fl { body }`.  A body `T` is a
decision tree: `ite` is two at-most-once loops, `let` a fresh variable, a `call` leaf first evaluates every
new scalar component into temporaries `d, d + 1, ...` (all in the old state) and then copies them into the
state variables; a `ret` leaf puts the result in `res` (a scalar) or leaves it in its slot (an array) and
clears `fl`. -/
import Riscv.Frontx.WaExp

namespace Proven.WA
open Proven Proven.Frontx

/-- a scalar's location (no memory) -/
def scLoc (v : Nat) : Loc := ⟨v, true, 0, none⟩

def skipAt (d : Nat) : MS := .assign d (.const 0)

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

/-- static: the scalars' expressions are well formed, an array component is the array of its own slot -/
def Args.wf (L : List Loc) {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → List Loc → Bool
  | _, .nil, _ => true
  | _, @Args.cons _ (.sc _) _ e as, st => E.wf L e && as.wf L st.tail
  | _, @Args.cons _ (.ar _) _ a as, st =>
    (match a with | .var m => m.loc L == st.headD default | _ => false) && as.wf L st.tail

def Args.ok {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → Vals Γ → Prop
  | _, .nil, _ => True
  | _, @Args.cons _ (.sc _) _ e as, v => E.ok e v ∧ as.ok v
  | _, @Args.cons _ (.ar _) _ _ as, v => as.ok v

/-! ## Bodies -/

def T.comp (st : List Loc) (res fl : Nat) : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → List Loc → Nat → MS
  | _, _, .sc _, .ret e, L, d => .seq (E.comp L e d) (.seq (.assign res (.var d)) (.assign fl (.const 0)))
  | _, _, .ar _, .ret _, _, _ => .assign fl (.const 0)
  | _, _, _, .call as, L, d => .seq (as.pre L d) (as.copy st d)
  | _, _, _, .ite c a b, L, d =>
    .seq (E.comp L c d) (.seq (.assign (d + 1) (.bin .eq (.var d) (.const 0)))
      (.seq (when d (a.comp st res fl L (d + 2))) (when (d + 1) (b.comp st res fl L (d + 2)))))
  | _, _, _, .let_ e k, L, d => .seq (E.comp L e d) (k.comp st res fl (scLoc d :: L) (d + 1))

/-- static conditions; `rl` is where an array result lives -/
def T.wf (st : List Loc) (rl : Loc) : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → List Loc → Nat → Bool
  | _, _, .sc _, .ret e, L, _ => e.wf L
  | _, _, .ar _, .ret a, L, _ => match a with | .var m => m.loc L == rl | _ => false
  | _, _, _, .call as, L, _ => as.wf L st
  | _, _, _, .ite c a b, L, d => c.wf L && a.wf st rl L (d + 2) && b.wf st rl L (d + 2)
  | _, _, _, .let_ e k, L, d => e.wf L && k.wf st rl (scLoc d :: L) (d + 1)

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

theorem Args.pre_ok (L : List Loc) {Γ : List Sl} (st : List Loc) : ∀ {Δ : List Sl} (as : Args Γ Δ) (v : Vals Γ)
    (σ : MSt) (d : Nat), Rel Γ L v σ → Γ.length ≤ L.length → Below L d → as.wf L st = true → as.ok v →
    ∃ σ', Mach.BExec (as.pre L d) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap ∧
      (∀ j, j < d → σ'.env j = σ.env j) ∧ as.Tmps σ' v d
  | _, .nil, v, σ, d, _, _, _, _, _ =>
    ⟨_, .assign, rfl, rfl, fun j hj => set_ne (by omega), by simp only [Args.Tmps]⟩
  | _, @Args.cons _ (.sc t) _ e as, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [Args.wf, Bool.and_eq_true] at hwf; simp only [Args.ok] at hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.comp_ok L e v σ d hR hl hb hwf.1 hok.1).frame hR hb hl
    obtain ⟨σ2, e2, h2, w2, k2, t2⟩ :=
      Args.pre_ok L st.tail as v σ1 (d + 1) r1 hl (hb.mono (by omega)) hwf.2 hok.2
    refine ⟨σ2, .seq e1 e2, h2.trans h1, w2.trans w1, fun j hj => by rw [k2 j (by omega), k1 j hj], ?_⟩
    simp only [Args.Tmps]
    exact ⟨by rw [k2 d (by omega)]; exact v1, t2⟩
  | _, @Args.cons _ (.ar _) _ a as, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [Args.wf, Bool.and_eq_true] at hwf; simp only [Args.ok] at hok
    have r1 : Rel Γ L v ⟨σ.env.set d 0, σ.heap, σ.wheap⟩ :=
      Rel.below hR hb hl (fun j hj => set_ne (by omega)) rfl rfl
    obtain ⟨σ2, e2, h2, w2, k2, t2⟩ :=
      Args.pre_ok L st.tail as v _ (d + 1) r1 hl (hb.mono (by omega)) hwf.2 hok
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

/-- after a call leaf the state slots represent the new state -/
theorem Args.rel {Γ : List Sl} (L : List Loc) : ∀ {Δ : List Sl} (as : Args Γ Δ) (st : List Loc) (v : Vals Γ)
    (σ0 σp σ' : MSt), Rel Γ L v σ0 → Γ.length ≤ L.length → as.wf L st = true → as.Res σp σ' st v →
    (∀ l ∈ st, σp.env l.v = σ0.env l.v) → σ'.heap = σ0.heap → σ'.wheap = σ0.wheap → st.length = Δ.length →
    Rel Δ st (as.den v) σ'
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _, .cons _ _, [], _, _, _, _, _, _, _, _, _, _, _, hl => by simp at hl
  | _, @Args.cons _ (.sc t) _ e as, l :: st, v, σ0, σp, σ', hR, hl, hwf, hres, hp, hh, hw, hlen => by
    simp only [Args.wf, Bool.and_eq_true] at hwf
    simp only [Args.Res, List.headD_cons, List.tail_cons] at hres
    refine ⟨?_, Args.rel L as st v σ0 σp σ' hR hl hwf.2 hres.2 (fun l' h' => hp l' (by simp [h'])) hh hw
      (by simpa using hlen)⟩
    show σ'.env l.v = _
    rw [hres.1]; rfl
  | _, @Args.cons _ (.ar k) _ a as, l :: st, v, σ0, σp, σ', hR, hl, hwf, hres, hp, hh, hw, hlen => by
    simp only [Args.wf, Bool.and_eq_true, List.headD_cons, List.tail_cons] at hwf
    simp only [Args.Res, List.headD_cons, List.tail_cons] at hres
    refine ⟨?_, Args.rel L as st v σ0 σp σ' hR hl hwf.2 hres.2 (fun l' h' => hp l' (by simp [h'])) hh hw
      (by simpa using hlen)⟩
    obtain ⟨hwa, -⟩ := hwf
    cases a with
    | var m =>
      simp only [beq_iff_eq] at hwa
      have hS := Rel.get m hR
      rw [hwa] at hS
      simp only [Args.den, Arg.den, A.den, List.headD_cons]
      exact SR.frame hS (by rw [hres.1, hp l (by simp)]) hh hw
    | set _ _ _ => simp at hwa
    | push _ _ => simp at hwa
    | ite _ _ _ => simp at hwa

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
structure LoopLay (st : List Loc) (res fl : Nat) (rl : Loc) (d : Nat) : Prop where
  bst : Below st d
  hres : res < d
  hfl : fl < d
  hrl : rl.v < d
  nd : (vsOf st).Nodup
  rs : res ∉ vsOf st
  fs : fl ∉ vsOf st
  rf : res ≠ fl
  rlf : rl.v ≠ fl

theorem LoopLay.mono {st : List Loc} {res fl : Nat} {rl : Loc} {d d' : Nat} (h : LoopLay st res fl rl d) (h' : d ≤ d') :
    LoopLay st res fl rl d' :=
  ⟨h.bst.mono h', by have := h.hres; omega, by have := h.hfl; omega, by have := h.hrl; omega, h.nd, h.rs, h.fs, h.rf,
    h.rlf⟩

set_option maxHeartbeats 1000000 in
/-- **One iteration of a loop body.** -/
theorem T.comp_ok (st : List Loc) (res fl : Nat) (rl : Loc) : ∀ {Γ Δ : List Sl} {R : Sl} (b : T Γ Δ R)
    (L : List Loc) (v : Vals Γ) (σ : MSt) (d : Nat), Rel Γ L v σ → Γ.length ≤ L.length → Below L d →
    LoopLay st res fl rl d → st.length = Δ.length → b.wf st rl L d = true → b.ok v →
    ∃ σ', Mach.BExec (b.comp st res fl L d) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap ∧
      (∀ j, j < d → j ∉ vsOf st → j ≠ res → j ≠ fl → σ'.env j = σ.env j) ∧
      Outc Δ R st res fl rl σ σ' (b.out v)
  | _, _, .sc t, .ret e, L, v, σ, d, hR, hl, hb, hy, hlen, hwf, hok => by
    simp only [T.wf] at hwf; simp only [T.ok] at hok
    simp only [T.comp, T.out]
    obtain ⟨σ1, e1, v1, k1, h1, w1⟩ := E.comp_ok L e v σ d hR hl hb hwf hok
    refine ⟨_, .seq e1 (.seq .assign .assign), h1, w1, fun j hj h1 h2 h3 => ?_, ?_, ?_⟩
    · simp only [set_ne h3, set_ne h2, k1 j hj]
    · simp only [set_eq]; rfl
    · show _ = _
      simp only [set_ne hy.rf, Mach.BExp.denote, set_eq, Arg.den]; rw [v1]
  | _, _, .ar k, .ret a, L, v, σ, d, hR, hl, hb, hy, hlen, hwf, hok => by
    simp only [T.comp, T.out]
    cases a with
    | var m =>
      simp only [T.wf, beq_iff_eq] at hwf
      have hS := Rel.get m hR
      rw [hwf] at hS
      refine ⟨_, .assign, rfl, rfl, fun j hj h1 h2 h3 => set_ne h3, ?_, ?_⟩
      · simp only [set_eq]; rfl
      · show SR _ (.ar k) rl (m.get v)
        exact SR.frame hS (set_ne hy.rlf) rfl rfl
    | set _ _ _ => simp [T.wf] at hwf
    | push _ _ => simp [T.wf] at hwf
    | ite _ _ _ => simp [T.wf] at hwf
  | _, _, _, .call as, L, v, σ, d, hR, hl, hb, hy, hlen, hwf, hok => by
    simp only [T.wf] at hwf; simp only [T.ok] at hok
    simp only [T.comp, T.out]
    obtain ⟨σ1, e1, h1, w1, k1, t1⟩ := Args.pre_ok L st as v σ d hR hl hb hwf hok
    obtain ⟨σ2, e2, h2, w2, k2, r2⟩ := Args.copy_ok as st v σ1 d t1 hy.bst hy.nd hlen
    refine ⟨σ2, .seq e1 e2, h2.trans h1, w2.trans w1, fun j hj hs _ _ => by rw [k2 j hj hs, k1 j hj], ?_, ?_⟩
    · rw [k2 fl hy.hfl hy.fs, k1 fl hy.hfl]
    · exact Args.rel L as st v σ σ1 σ2 hR hl hwf r2 (fun l hl' => k1 l.v (hy.bst l hl')) (h2.trans h1)
        (w2.trans w1) hlen
  | _, _, _, .ite c a b, L, v, σ, d, hR, hl, hb, hy, hlen, hwf, hok => by
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
    have hns : ∀ j, d ≤ j → j ∉ vsOf st := fun j hj h => by
      obtain ⟨l, hl', e⟩ := List.mem_map.1 h; have := hy.bst l hl'; omega
    have hrd : res < d := hy.hres
    have hfd : fl < d := hy.hfl
    have hrl : rl.v < d := hy.hrl
    cases hcv : c.den v with
    | true =>
      have hoa := hok.2; rw [hcv, if_pos rfl] at hoa
      obtain ⟨σ3, e3, h3, w3, k3, o3⟩ := T.comp_ok st res fl rl a L v σ2 (d + 2) r2 hl (hb.mono (by omega)) hy2
        hlen hwa hoa
      have hne : σ2.env d ≠ 0 := by rw [hc1, hcv]; decide
      have hw1 := when_true hne e3
      let σ4 : MSt := ⟨σ3.env.set d 0, σ3.heap, σ3.wheap⟩
      have hz : σ4.env (d + 1) = 0 := by
        simp only [σ4, set_ne (show d + 1 ≠ d by omega)]
        rw [k3 (d + 1) (by omega) (hns _ (by omega)) (by omega) (by omega), hc2, hcv]; rfl
      refine ⟨σ4, .seq e1 (.seq e2 (.seq hw1 (when_false hz))), h3.trans h1, w3.trans w1,
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
      obtain ⟨σ3, e3, h3, w3, k3, o3⟩ := T.comp_ok st res fl rl b L v σ2 (d + 2) r2 hl (hb.mono (by omega)) hy2
        hlen hwb hob
      have hne : σ2.env (d + 1) ≠ 0 := by rw [hc2, hcv]; decide
      have hw2 := when_true hne e3
      refine ⟨_, .seq e1 (.seq e2 (.seq (when_false hz) hw2)), h3.trans h1, w3.trans w1,
        fun j hj hs h1 h2 => ?_, ?_⟩
      · simp only [set_ne (show j ≠ d + 1 by omega)]
        rw [k3 j (by omega) hs h1 h2, hk2 j hj]
      · simp only [Bool.false_eq_true, if_false]
        refine Outc.base (σ := σ2) (Outc.frame (σ1 := σ3) o3 (fun l hl' => set_ne (by have := hy.bst l hl'; omega))
          (set_ne (by omega)) (set_ne (by omega)) (set_ne (by omega)) rfl rfl (by omega)) ?_
        exact hk2 fl hfd
  | _, _, _, .let_ e k, L, v, σ, d, hR, hl, hb, hy, hlen, hwf, hok => by
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
    obtain ⟨σ2, e2, h2, w2, k2, o2⟩ := T.comp_ok st res fl rl k (scLoc d :: L) (E.den e v, v) σ1 (d + 1) r1'
      (by simp; omega) hb1 (hy.mono (by omega)) hlen hwf.2 hok.2
    refine ⟨σ2, .seq e1 e2, h2.trans h1, w2.trans w1, fun j hj hs h1 h2 => by rw [k2 j (by omega) hs h1 h2, k1 j hj], ?_⟩
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
    (rl : Loc) (d : Nat) (hy : LoopLay st res fl rl d) (hlen : st.length = Δ.length) (hl : Γ.length ≤ L.length)
    (hbL : Below L d) (hLd : ∀ l ∈ L, l.v ∉ vsOf st ∧ l.v ≠ res ∧ l.v ≠ fl)
    (hwf : b.wf st rl (st ++ L) d = true) (P : Vals Δ → Prop) (hok : ∀ s, P s → b.ok (Vals.app s c))
    (hP : ∀ s s', P s → b.out (Vals.app s c) = .inl s' → P s') :
    ∀ s r, Runs b c s r → P s → ∀ σ, Rel (Δ ++ Γ) (st ++ L) (Vals.app s c) σ → σ.env fl ≠ 0 →
      ∃ σ', Mach.BExec (.loop (.var fl) (b.comp st res fl (st ++ L) d)) σ σ' ∧ σ'.heap = σ.heap ∧
        σ'.wheap = σ.wheap ∧ (∀ j, j < d → j ∉ vsOf st → j ≠ res → j ≠ fl → σ'.env j = σ.env j) ∧
        RR σ' R res rl r := by
  have hl2 : (Δ ++ Γ).length ≤ (st ++ L).length := by simp; omega
  have hb2 : Below (st ++ L) d := fun l h => by
    rcases List.mem_append.1 h with h | h
    · exact hy.bst l h
    · exact hbL l h
  intro s r hr
  induction hr with
  | @ret s r ho =>
    intro _ σ hR hfl
    obtain ⟨σ1, e1, h1, w1, k1, o1⟩ := T.comp_ok st res fl rl b (st ++ L) (Vals.app s c) σ d hR hl2 hb2 hy hlen hwf
      (hok s ‹_›)
    rw [ho] at o1
    exact ⟨σ1, .loopT hfl e1 (.loopF o1.1), h1, w1, k1, o1.2⟩
  | @call s s' r ho _ ih =>
    intro hPs σ hR hfl
    obtain ⟨σ1, e1, h1, w1, k1, o1⟩ := T.comp_ok st res fl rl b (st ++ L) (Vals.app s c) σ d hR hl2 hb2 hy hlen hwf
      (hok s hPs)
    rw [ho] at o1
    have hR1 : Rel (Δ ++ Γ) (st ++ L) (Vals.app s' c) σ1 := by
      rw [Rel.app hlen] at hR ⊢
      refine ⟨o1.2, Rel.frame hR.2 (fun l hl' => ?_) h1 w1 hl⟩
      obtain ⟨a1, a2, a3⟩ := hLd l hl'
      exact k1 l.v (hbL l hl') a1 a2 a3
    obtain ⟨σ2, e2, h2, w2, k2, o2⟩ := ih (hP s s' hPs ho) σ1 hR1 (by rw [o1.1]; exact hfl)
    exact ⟨σ2, .loopT hfl e1 e2, h2.trans h1, w2.trans w1,
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
    (st L : List Loc) (res fl : Nat) (rl : Loc) (d : Nat) (hy : LoopLay st res fl rl d) (hlen : st.length = Δ.length)
    (hl : Γ.length ≤ L.length) (hbL : Below L d) (hLd : ∀ l ∈ L, l.v ∉ vsOf st ∧ l.v ≠ res ∧ l.v ≠ fl)
    (hwf : (T.ite c A B).wf st rl (st ++ L) d = true) (hA : A.noRet = true) (hB : B.noCall = true)
    (P : Vals Δ → Prop)
    (hok : ∀ s, P s → (T.ite c A B).ok (Vals.app s cv))
    (hP : ∀ s s', P s → (T.ite c A B).out (Vals.app s cv) = .inl s' → P s') :
    ∀ s r, Runs (T.ite c A B) cv s r → P s → ∀ σ, Rel (Δ ++ Γ) (st ++ L) (Vals.app s cv) σ →
      σ.env d = rB (c.den (Vals.app s cv)) →
      ∃ σ' sf, Mach.BExec (.loop (.var d) (.seq (A.comp st res fl (st ++ L) (d + 2)) (E.comp (st ++ L) c d))) σ σ' ∧
        σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap ∧
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
    intro hPs σ hR hd
    -- `c` is false here: a true `c` would give a `call`
    have hcf : c.den (Vals.app s cv) = false := by
      cases hc : c.den (Vals.app s cv) with
      | false => rfl
      | true =>
        obtain ⟨s', hs'⟩ := T.out_noRet A (Vals.app s cv) hA
        simp only [T.out, hc, if_true, hs'] at ho; cases ho
    exact ⟨σ, s, .loopF (by show σ.env d = 0; rw [hd, hcf]; rfl), rfl, rfl, fun _ _ _ _ _ => rfl, hR, hcf, .ret ho, hPs⟩
  | @call s s' r ho hr' ih =>
    intro hPs σ hR hd
    have hoks := hok s hPs
    simp only [T.ok] at hoks
    by_cases hc : c.den (Vals.app s cv) = true
    · rw [hc, if_pos rfl] at hoks
      have hoA : A.out (Vals.app s cv) = .inl s' := by simp only [T.out, hc, if_true] at ho; exact ho
      have hy2 := hy.mono (show d ≤ d + 2 by omega)
      obtain ⟨σ1, e1, h1, w1, k1, o1⟩ := T.comp_ok st res fl rl A (st ++ L) (Vals.app s cv) σ (d + 2) hR hl2
        (hb2.mono (by omega)) hy2 hlen hwa hoks.2
      rw [hoA] at o1
      have hR1 : Rel (Δ ++ Γ) (st ++ L) (Vals.app s' cv) σ1 := by
        rw [Rel.app hlen] at hR ⊢
        refine ⟨o1.2, Rel.frame hR.2 (fun l hl' => ?_) h1 w1 hl⟩
        obtain ⟨a1, a2, a3⟩ := hLd l hl'
        exact k1 l.v (by have := hbL l hl'; omega) a1 a2 a3
      have hPs' := hP s s' hPs ho
      have hoks' := hok s' hPs'
      simp only [T.ok] at hoks'
      replace hoks' := hoks'.1
      obtain ⟨σ2, e2, v2, k2, h2, w2, r2⟩ := (E.comp_ok (st ++ L) c (Vals.app s' cv) σ1 d hR1 hl2 hb2 hwc hoks').frame
        hR1 hb2 hl2
      obtain ⟨σ3, sf, e3, h3, w3, k3, r3, c3, u3, p3⟩ := ih hPs' σ2 r2 v2
      have hne : σ.env d ≠ 0 := by rw [hd, hc]; decide
      refine ⟨σ3, sf, .loopT hne (.seq e1 e2) e3, by rw [h3, h2, h1], by rw [w3, w2, w1],
        fun j hj a1 a2 a3 => by rw [k3 j hj a1 a2 a3, k2 j hj, k1 j (by omega) a1 a2 a3], r3, c3, u3, p3⟩
    · simp only [Bool.not_eq_true] at hc
      obtain ⟨r', hr''⟩ := T.out_noCall B (Vals.app s cv) hB
      simp only [T.out, hc, Bool.false_eq_true, if_false, hr''] at ho; cases ho

theorem slow_loop {Δ Γ : List Sl} {R : Sl} (b : T (Δ ++ Γ) Δ R) (cv : Vals Γ) (st L : List Loc) (res fl : Nat)
    (rl : Loc) (d : Nat) (hy : LoopLay st res fl rl d) (hlen : st.length = Δ.length) (hl : Γ.length ≤ L.length)
    (hbL : Below L d) (hLd : ∀ l ∈ L, l.v ∉ vsOf st ∧ l.v ≠ res ∧ l.v ≠ fl)
    (hwf : b.wf st rl (st ++ L) d = true) (P : Vals Δ → Prop) (hok : ∀ s, P s → b.ok (Vals.app s cv))
    (hP : ∀ s s', P s → b.out (Vals.app s cv) = .inl s' → P s') (s : Vals Δ) (r : R.T) (hr : Runs b cv s r)
    (hPs : P s) (σ : MSt) (hR : Rel (Δ ++ Γ) (st ++ L) (Vals.app s cv) σ) :
    ∃ σ', Mach.BExec (.seq (.assign fl (.const 1)) (.loop (.var fl) (b.comp st res fl (st ++ L) d))) σ σ' ∧
      σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap ∧ (∀ j, j < d → j ∉ vsOf st → j ≠ res → j ≠ fl → σ'.env j = σ.env j) ∧
      RR σ' R res rl r := by
  let σ1 : MSt := ⟨σ.env.set fl ((Mach.BExp.const 1).denote σ.env), σ.heap, σ.wheap⟩
  have hR1 : Rel (Δ ++ Γ) (st ++ L) (Vals.app s cv) σ1 := by
    refine Rel.frame hR (fun l h => set_ne ?_) rfl rfl (by simp; omega)
    rcases List.mem_append.1 h with h | h
    · intro e; apply hy.fs; rw [← e]; exact List.mem_map_of_mem h
    · exact (hLd l h).2.2
  obtain ⟨σ2, e2, h2, w2, k2, r2⟩ := T.comp_loop b cv st L res fl rl d hy hlen hl hbL hLd hwf P hok hP s r hr hPs σ1
    hR1 (by simp only [σ1, set_eq, Mach.BExp.denote]; decide)
  exact ⟨σ2, .seq .assign e2, h2, w2, fun j hj a1 a2 a3 => by rw [k2 j hj a1 a2 a3]; exact set_ne a3, r2⟩

theorem T.loopCode_ok {Δ Γ : List Sl} {R : Sl} (b : T (Δ ++ Γ) Δ R) (cv : Vals Γ) (st L : List Loc) (res fl : Nat)
    (rl : Loc) (d : Nat) (hy : LoopLay st res fl rl d) (hlen : st.length = Δ.length) (hl : Γ.length ≤ L.length)
    (hbL : Below L d) (hLd : ∀ l ∈ L, l.v ∉ vsOf st ∧ l.v ≠ res ∧ l.v ≠ fl)
    (hwf : b.wf st rl (st ++ L) d = true) (P : Vals Δ → Prop) (hok : ∀ s, P s → b.ok (Vals.app s cv))
    (hP : ∀ s s', P s → b.out (Vals.app s cv) = .inl s' → P s') (s : Vals Δ) (r : R.T) (hr : Runs b cv s r)
    (hPs : P s) (σ : MSt) (hR : Rel (Δ ++ Γ) (st ++ L) (Vals.app s cv) σ) :
    ∃ σ', Mach.BExec (b.loopCode st res fl (st ++ L) d) σ σ' ∧
      σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap ∧ (∀ j, j < d → j ∉ vsOf st → j ≠ res → j ≠ fl → σ'.env j = σ.env j) ∧
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
      obtain ⟨σ2, sf, e2, h2, w2, k2, r2, c2, u2, p2⟩ := fast_loop c A B cv st L res fl rl d hy hlen hl hbL hLd hwf
        hAB.1 hAB.2 P hok hP s r hr hPs σ1 r1 v1
      have hoB : B.out (Vals.app sf cv) = .inr r := by
        cases u2 with
        | ret ho => simp only [T.out, c2, Bool.false_eq_true, if_false] at ho; exact ho
        | call ho _ =>
          obtain ⟨r', hr'⟩ := T.out_noCall B (Vals.app sf cv) hAB.2
          simp only [T.out, c2, Bool.false_eq_true, if_false, hr'] at ho; cases ho
      have hoksf := hok sf p2
      simp only [T.ok, c2, Bool.false_eq_true, if_false] at hoksf
      obtain ⟨σ3, e3, h3, w3, k3, o3⟩ := T.comp_ok st res fl rl B (st ++ L) (Vals.app sf cv) σ2 (d + 2) r2 hl2
        (hb2.mono (by omega)) (hy.mono (by omega)) hlen hwb hoksf.2
      rw [hoB] at o3
      exact ⟨σ3, .seq e1 (.seq e2 e3), by rw [h3, h2, h1], by rw [w3, w2, w1],
        fun j hj a1 a2 a3 => by rw [k3 j (by omega) a1 a2 a3, k2 j hj a1 a2 a3, k1 j hj], o3.2⟩
    · exact slow_loop _ cv st L res fl rl d hy hlen hl hbL hLd hwf P hok hP s r hr hPs σ hR
  · exact slow_loop _ cv st L res fl rl d hy hlen hl hbL hLd hwf P hok hP s r hr hPs σ hR

end Proven.WA
