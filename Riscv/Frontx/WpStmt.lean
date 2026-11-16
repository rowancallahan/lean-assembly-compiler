/- Paged dynamic arrays (NOTES section 30), part 6: loop bodies and loops.

A loop's state `Δ` holds at most one work (paged) array: the one its body updates in place (`w`); its other
array slots are views of the input.  So the store during a loop is `E0 ++ R0`: the state's work array (one entry
or none) and the enclosing arrays `R0`, which the loop does not change.

Code as in `WaStmt.lean`: a `call` leaf evaluates the scalar components into temporaries (`Args.preP`), updates
the written array (`Args.updP`: `A.preP` then `A.stP`), then copies the scalars (`Args.copyP`); a loop is
`fl := 1; while (fl &&& vOk) { body }`: after a push found no page (`vOk = 0`) the loop stops.

The page events of an iteration are those of its leaf (`T.evs`, the update's pushes); of a run, `RunsE`. -/
import Riscv.Frontx.WpUpd
import Riscv.Frontx.WaStmt

namespace Proven.WA
open Proven Proven.WP Proven.Top.Alloc
open Proven.Frontx (rN rN_toNat rN_lt rN_add rN_inj rB)

/-! ## Uniqueness of page tables in a store -/

theorem pairwise_of_mem {α : Type} {R : α → α → Prop} {l : List α} (h : l.Pairwise R) {a b : α} (ha : a ∈ l)
    (hb : b ∈ l) (hab : a ≠ b) : R a b ∨ R b a := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact .inl (h.1 b hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact .inr (h.1 a ha')
      · exact ih h.2 ha' hb'

theorem uniq_of_nodup {W : W64} : ∀ {arrs : List (Nat × W64)}, (owned W arrs).Nodup →
    ∀ {a b : Nat × W64}, a ∈ arrs → b ∈ arrs → a.1 = b.1 → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | x :: xs, hnd, a, b, ha, hb, he => by
    rw [owned_cons] at hnd
    have hd := List.nodup_append.1 hnd
    have hx : ∀ c ∈ xs, c.1 ≠ x.1 := fun c hc e =>
      hd.2.2 x.1 (by simp [pagesOf]) c.1 (List.mem_flatMap.2 ⟨c, hc, by simp [pagesOf]⟩) e.symm
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · rfl
      · exact absurd he.symm (hx b hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd he (hx a ha')
      · exact uniq_of_nodup hd.2.1 ha' hb' he

/-- two arrays of a store with the same page table are the same -/
theorem Store.uniq {C : Nat} {env : Mach.BEnv} {W : W64} {arrs : List (Nat × W64)} (h : Store C env W arrs)
    {a b : Nat × W64} (ha : a ∈ arrs) (hb : b ∈ arrs) (he : a.1 = b.1) : a = b :=
  uniq_of_nodup h.1.nodup ha hb he

theorem _root_.Proven.WP.Store.perm {C : Nat} {env : Mach.BEnv} {W : W64} {arrs arrs' : List (Nat × W64)}
    (h : Store C env W arrs) (hp : arrs.Perm arrs') : Store C env W arrs' :=
  ⟨h.1.perm (hp.flatMap_right _), fun a ha => h.2 a (hp.symm.subset ha)⟩

theorem arrsP_append {Γ : List Sl} {L : List PLoc} {c : Vals Γ} {env : Mach.BEnv} : ∀ {Δ : List Sl}
    {st : List PLoc} {s : Vals Δ}, st.length = Δ.length →
    arrsP (Δ ++ Γ) (st ++ L) (Vals.app s c) env = arrsP Δ st s env ++ arrsP Γ L c env
  | [], [], _, _ => rfl
  | _ :: _, [], _, h => by simp at h
  | [], _ :: _, _, h => by simp at h
  | .sc _ :: Δ, l :: st, s, h => by
    simp only [List.cons_append, arrsP, List.tail_cons, Vals.app]
    exact arrsP_append (by simpa using h)
  | .ar _ :: Δ, l :: st, s, h => by
    simp only [List.cons_append, arrsP, List.tail_cons, List.headD_cons, Vals.app]
    rw [arrsP_append (by simpa using h)]; split <;> rfl

theorem RelP.app {Γ : List Sl} {L : List PLoc} {c : Vals Γ} {σ : MSt} : ∀ {Δ : List Sl} {st : List PLoc}
    {s : Vals Δ}, st.length = Δ.length →
    (RelP (Δ ++ Γ) (st ++ L) (Vals.app s c) σ ↔ RelP Δ st s σ ∧ RelP Γ L c σ)
  | [], [], _, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: _, [], _, h => by simp at h
  | [], _ :: _, _, h => by simp at h
  | _ :: Δ, l :: st, s, h => by
    show SRP σ _ l s.1 ∧ RelP (Δ ++ Γ) (st ++ L) (Vals.app s.2 c) σ ↔ (SRP σ _ l s.1 ∧ RelP Δ st s.2 σ) ∧ RelP Γ L c σ
    rw [RelP.app (by simpa using h)]; exact and_assoc.symm

/-! ## Call leaves -/

/-- evaluate the scalar components into `d + j` -/
def Args.preP (L : List PLoc) {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → Nat → MS
  | _, .nil, d => skipAt d
  | _, @Args.cons _ (.sc _) _ e as, d => .seq (E.compP L e d) (as.preP L (d + 1))
  | _, @Args.cons _ (.ar _) _ _ as, d => .seq (skipAt d) (as.preP L (d + 1))

/-- copy them into the state variables -/
def Args.copyP {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → List PLoc → Nat → MS
  | _, .nil, _, d => skipAt d
  | _, @Args.cons _ (.sc _) _ _ as, st, d => .seq (.assign (st.headD default).v (.var d)) (as.copyP st.tail (d + 1))
  | _, @Args.cons _ (.ar _) _ _ as, st, d => .seq (skipAt d) (as.copyP st.tail (d + 1))

/-- static: scalars well formed; an array component is its own slot unchanged, or (at most one, `cw`) updated in
place in the work array `w` -/
def Args.wfP (L : List PLoc) {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → List PLoc → PLoc → Bool → Bool
  | _, .nil, _, _, _ => true
  | _, @Args.cons _ (.sc _) _ e as, st, w, cw => E.wfP L e && as.wfP L st.tail w cw
  | _, @Args.cons _ (.ar _) _ a as, st, w, cw =>
    match a with
    | .var m => m.locP L == st.headD default && as.wfP L st.tail w cw
    | _ => cw && A.wfP L a && a.base.locP L == st.headD default && st.headD default == w && !w.inp &&
        as.wfP L st.tail w false

def Args.okP {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → Vals Γ → Prop
  | _, .nil, _ => True
  | _, @Args.cons _ (.sc _) _ e as, v => E.ok e v ∧ as.okP v
  | _, @Args.cons _ (.ar _) _ a as, v => A.okP a v ∧ as.okP v

/-- the update of the (one) array component that changes -/
def Args.updP (L : List PLoc) {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → List PLoc → Nat → MS
  | _, .nil, _, e => skipAt e
  | _, @Args.cons _ (.sc _) _ _ as, st, e => as.updP L st.tail e
  | _, @Args.cons _ (.ar _) _ a as, st, e =>
    match a with
    | .var _ => as.updP L st.tail e
    | _ => .seq (A.preP L a e) (A.stP (st.headD default) (e + a.nt) a e)

/-- the page events of a call leaf: its update's -/
def Args.evs {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → Vals Γ → List MemEvent
  | _, .nil, _ => []
  | _, @Args.cons _ (.sc _) _ _ as, v => as.evs v
  | _, @Args.cons _ (.ar _) _ a as, v => A.evs a v ++ as.evs v

/-! ## Bodies -/

def T.compP (st : List PLoc) (res fl : Nat) : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → List PLoc → Nat → MS
  | _, _, .sc _, .ret e, L, d => .seq (E.compP L e d) (.seq (.assign res (.var d)) (.assign fl (.const 0)))
  | _, _, .ar _, .ret _, _, _ => .assign fl (.const 0)
  | _, Δ, _, .call as, L, d => .seq (as.preP L d) (.seq (as.updP L st (d + Δ.length)) (as.copyP st d))
  | _, _, _, .ite c a b, L, d =>
    .seq (E.compP L c d) (.seq (.assign (d + 1) (.bin .eq (.var d) (.const 0)))
      (.seq (when d (a.compP st res fl L (d + 2))) (when (d + 1) (b.compP st res fl L (d + 2)))))
  | _, _, _, .let_ e k, L, d => .seq (E.compP L e d) (k.compP st res fl (⟨d, false, 0⟩ :: L) (d + 1))

def T.wfP (st : List PLoc) (rl w : PLoc) : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → List PLoc → Nat → Bool
  | _, _, .sc _, .ret e, L, _ => E.wfP L e
  | _, _, .ar _, .ret a, L, _ => match a with | .var m => m.locP L == rl | _ => false
  | _, _, _, .call as, L, _ => as.wfP L st w true
  | _, _, _, .ite c a b, L, d => E.wfP L c && a.wfP st rl w L (d + 2) && b.wfP st rl w L (d + 2)
  | _, _, _, .let_ e k, L, d => E.wfP L e && k.wfP st rl w (⟨d, false, 0⟩ :: L) (d + 1)

def T.okP : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → Vals Γ → Prop
  | _, _, .sc _, .ret e, v => e.ok v
  | _, _, .ar _, .ret _, _ => True
  | _, _, _, .call as, v => as.okP v
  | _, _, _, .ite c a b, v => c.ok v ∧ if c.den v = true then a.okP v else b.okP v
  | _, _, _, .let_ e k, v => e.ok v ∧ k.okP (e.den v, v)

/-- the page events of the leaf a body reaches -/
def T.evs : {Γ Δ : List Sl} → {R : Sl} → T Γ Δ R → Vals Γ → List MemEvent
  | _, _, _, .ret _, _ => []
  | _, _, _, .call as, v => as.evs v
  | _, _, _, .ite c a b, v => if c.den v = true then a.evs v else b.evs v
  | _, _, _, .let_ e k, v => k.evs (e.den v, v)

/-- iterating a loop body, with the page events of the iterations (oldest first) -/
inductive RunsE {Δ Γ : List Sl} {R : Sl} (b : T (Δ ++ Γ) Δ R) (c : Vals Γ) : Vals Δ → R.T → List MemEvent → Prop
  | ret {s r} : b.out (Vals.app s c) = .inr r → RunsE b c s r []
  | call {s s' r E} : b.out (Vals.app s c) = .inl s' → RunsE b c s' r E →
      RunsE b c s r (b.evs (Vals.app s c) ++ E)

theorem RunsE.runs {Δ Γ : List Sl} {R : Sl} {b : T (Δ ++ Γ) Δ R} {c : Vals Γ} {s : Vals Δ} {r : R.T}
    {E : List MemEvent} (h : RunsE b c s r E) : Runs b c s r := by
  induction h with
  | ret ho => exact .ret ho
  | call ho _ ih => exact .call ho ih

theorem RunsE.det {Δ Γ : List Sl} {R : Sl} {b : T (Δ ++ Γ) Δ R} {c : Vals Γ} {s : Vals Δ} {r r' : R.T}
    {E E' : List MemEvent} (h : RunsE b c s r E) (h' : RunsE b c s r' E') : r = r' ∧ E = E' := by
  induction h generalizing r' E' with
  | ret ho =>
    cases h' with
    | ret ho' => rw [ho] at ho'; cases ho'; exact ⟨rfl, rfl⟩
    | call ho' _ => rw [ho] at ho'; cases ho'
  | call ho _ ih =>
    cases h' with
    | ret ho' => rw [ho] at ho'; cases ho'
    | call ho' hr' => rw [ho] at ho'; cases ho'; obtain ⟨e1, e2⟩ := ih hr'; exact ⟨e1, by rw [e2]⟩

/-- `runs_of` with events: a Lean function satisfying the body's equation runs to its value, with some events -/
theorem runsE_of {Δ Γ : List Sl} {R : Sl} {b : T (Δ ++ Γ) Δ R} {c : Vals Γ} {s : Vals Δ} {r : R.T}
    (h : Runs b c s r) : ∃ E, RunsE b c s r E := by
  induction h with
  | ret ho => exact ⟨[], .ret ho⟩
  | call ho _ ih => obtain ⟨E, hE⟩ := ih; exact ⟨_, .call ho hE⟩

/-- the variables of the slots -/
def vsOfP (L : List PLoc) : List Nat := L.map (·.v)

theorem Args.wfP_tail_ar {L : List PLoc} {Γ Δ : List Sl} {k : AK} {a : A Γ k} {as : Args Γ Δ} {st : List PLoc} {w : PLoc}
    {cw : Bool} (h : (Args.cons (s := .ar k) a as).wfP L st w cw = true) : ∃ cw', as.wfP L st.tail w cw' = true := by
  simp only [Args.wfP] at h
  split at h
  · simp only [Bool.and_eq_true] at h; exact ⟨cw, h.2⟩
  · simp only [Bool.and_eq_true] at h; exact ⟨false, h.2⟩

theorem Args.preP_ok (L : List PLoc) {Γ : List Sl} (st : List PLoc) (w : PLoc) : ∀ {Δ : List Sl} (as : Args Γ Δ)
    (v : Vals Γ) (σ : MSt) (d : Nat) (cw : Bool), EnvOK Γ L v σ → Γ.length ≤ L.length → BelowP L d →
    as.wfP L st w cw = true → as.okP v →
    ∃ σ', Mach.BExec (as.preP L d) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap ∧
      (∀ j, j < d → σ'.env j = σ.env j) ∧ as.Tmps σ' v d
  | _, .nil, v, σ, d, _, _, _, _, _, _ =>
    ⟨_, .assign, rfl, rfl, fun j hj => set_ne (by omega), by simp only [Args.Tmps]⟩
  | _, @Args.cons _ (.sc t) _ e as, v, σ, d, cw, hR, hl, hb, hwf, hok => by
    simp only [Args.wfP, Bool.and_eq_true] at hwf; simp only [Args.okP] at hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.compP_ok L e v σ d hR hl hb hwf.1 hok.1).frameP hR hb hl
    obtain ⟨σ2, e2, h2, w2, k2, t2⟩ :=
      Args.preP_ok L st.tail w as v σ1 (d + 1) cw r1 hl (hb.mono (by omega)) hwf.2 hok.2
    refine ⟨σ2, .seq e1 e2, h2.trans h1, w2.trans w1, fun j hj => by rw [k2 j (by omega), k1 j hj], ?_⟩
    simp only [Args.Tmps]
    exact ⟨by rw [k2 d (by omega)]; exact v1, t2⟩
  | _, @Args.cons _ (.ar _) _ a as, v, σ, d, cw, hR, hl, hb, hwf, hok => by
    obtain ⟨cw', hwf⟩ := Args.wfP_tail_ar hwf; simp only [Args.okP] at hok
    have r1 : EnvOK Γ L v ⟨σ.env.set d 0, σ.heap, σ.wheap⟩ :=
      hR.frame hb (fun j hj => set_ne (by omega)) rfl rfl
    obtain ⟨σ2, e2, h2, w2, k2, t2⟩ :=
      Args.preP_ok L st.tail w as v _ (d + 1) cw' r1 hl (hb.mono (by omega)) hwf hok.2
    refine ⟨σ2, .seq .assign e2, h2, w2, fun j hj => by rw [k2 j (by omega)]; exact set_ne (by omega), ?_⟩
    simp only [Args.Tmps]; exact t2

/-- after the copies: the scalar slots hold the new values, the array slots' variables are kept -/
def Args.ResP {Γ : List Sl} (σ σ' : MSt) : {Δ : List Sl} → Args Γ Δ → List PLoc → Vals Γ → Prop
  | _, .nil, _, _ => True
  | _, @Args.cons _ (.sc t) _ e as, st, v => σ'.env (st.headD default).v = t.rep (E.den e v) ∧ as.ResP σ σ' st.tail v
  | _, @Args.cons _ (.ar _) _ _ as, st, v =>
    σ'.env (st.headD default).v = σ.env (st.headD default).v ∧ as.ResP σ σ' st.tail v

theorem Args.ResP.frame {Γ : List Sl} {σ σ' σ'' : MSt} : ∀ {Δ : List Sl} {as : Args Γ Δ} {st : List PLoc} {v : Vals Γ},
    as.ResP σ σ' st v → (∀ l ∈ st, σ''.env l.v = σ'.env l.v) → st.length = Δ.length → as.ResP σ σ'' st v
  | _, .nil, _, _, _, _, _ => by simp only [Args.ResP]
  | _, .cons _ _, [], _, _, _, hl => by simp at hl
  | _, @Args.cons _ (.sc _) _ _ _, l :: st, _, h, he, hl => by
    simp only [Args.ResP, List.headD_cons, List.tail_cons] at h ⊢
    exact ⟨by rw [he l (by simp)]; exact h.1,
      Args.ResP.frame h.2 (fun l' h' => he l' (by simp [h'])) (by simpa using hl)⟩
  | _, @Args.cons _ (.ar _) _ _ _, l :: st, _, h, he, hl => by
    simp only [Args.ResP, List.headD_cons, List.tail_cons] at h ⊢
    exact ⟨by rw [he l (by simp)]; exact h.1,
      Args.ResP.frame h.2 (fun l' h' => he l' (by simp [h'])) (by simpa using hl)⟩

theorem Args.ResP.base {Γ : List Sl} {σ σ1 σ' : MSt} : ∀ {Δ : List Sl} {as : Args Γ Δ} {st : List PLoc} {v : Vals Γ},
    as.ResP σ1 σ' st v → (∀ l ∈ st, σ1.env l.v = σ.env l.v) → st.length = Δ.length → as.ResP σ σ' st v
  | _, .nil, _, _, _, _, _ => by simp only [Args.ResP]
  | _, .cons _ _, [], _, _, _, hl => by simp at hl
  | _, @Args.cons _ (.sc _) _ _ _, l :: st, _, h, he, hl => by
    simp only [Args.ResP, List.headD_cons, List.tail_cons] at h ⊢
    exact ⟨h.1, Args.ResP.base h.2 (fun l' h' => he l' (by simp [h'])) (by simpa using hl)⟩
  | _, @Args.cons _ (.ar _) _ _ _, l :: st, _, h, he, hl => by
    simp only [Args.ResP, List.headD_cons, List.tail_cons] at h ⊢
    exact ⟨by rw [h.1, he l (by simp)], Args.ResP.base h.2 (fun l' h' => he l' (by simp [h'])) (by simpa using hl)⟩

theorem Args.copyP_ok {Γ : List Sl} : ∀ {Δ : List Sl} (as : Args Γ Δ) (st : List PLoc) (v : Vals Γ) (σ : MSt) (d : Nat),
    as.Tmps σ v d → BelowP st d → (vsOfP st).Nodup → st.length = Δ.length →
    ∃ σ', Mach.BExec (as.copyP st d) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap ∧
      (∀ j, j < d → j ∉ vsOfP st → σ'.env j = σ.env j) ∧ as.ResP σ σ' st v
  | _, .nil, st, v, σ, d, _, _, _, _ =>
    ⟨_, .assign, rfl, rfl, fun j hj _ => set_ne (by omega), by simp only [Args.ResP]⟩
  | _, .cons _ _, [], _, _, _, _, _, _, hl => by simp at hl
  | _, @Args.cons _ (.sc t) _ e as, l :: st, v, σ, d, ht, hb, hn, hl => by
    simp only [Args.Tmps] at ht
    simp only [Args.copyP, Args.Res, List.headD_cons, List.tail_cons]
    simp only [vsOfP, List.map_cons, List.nodup_cons] at hn
    have hlv : l.v < d := (hb l (by simp)).1
    have hbs : BelowP st (d + 1) := BelowP.mono (fun l' (h' : l' ∈ st) => hb l' (by simp [h'])) (by omega)
    let σ1 : MSt := ⟨σ.env.set l.v (σ.env d), σ.heap, σ.wheap⟩
    have ht1 : as.Tmps σ1 v (d + 1) := Args.Tmps.frame ht.2 fun j h1 h2 => set_ne (by omega)
    obtain ⟨σ2, e2, h2, w2, k2, r2⟩ := Args.copyP_ok as st v σ1 (d + 1) ht1 hbs hn.2 (by simpa using hl)
    refine ⟨σ2, .seq .assign e2, h2, w2, fun j hj hj' => ?_, ⟨?_, ?_⟩⟩
    · simp only [vsOfP, List.map_cons, List.mem_cons, not_or] at hj'
      rw [k2 j (by omega) hj'.2]; exact set_ne hj'.1
    · show σ2.env l.v = _; rw [k2 l.v (by omega) hn.1]; simp only [σ1, set_eq]; exact ht.1
    · refine Args.ResP.base r2 (fun l' h' => set_ne ?_) (by simpa using hl)
      intro e; apply hn.1; rw [← e]; exact List.mem_map_of_mem h'
  | _, @Args.cons _ (.ar _) _ _ as, l :: st, v, σ, d, ht, hb, hn, hl => by
    simp only [Args.Tmps] at ht
    simp only [Args.copyP, Args.Res, List.headD_cons, List.tail_cons]
    simp only [vsOfP, List.map_cons, List.nodup_cons] at hn
    have hlv : l.v < d := (hb l (by simp)).1
    have hbs : BelowP st (d + 1) := BelowP.mono (fun l' (h' : l' ∈ st) => hb l' (by simp [h'])) (by omega)
    let σ1 : MSt := ⟨σ.env.set d 0, σ.heap, σ.wheap⟩
    have ht1 : as.Tmps σ1 v (d + 1) := Args.Tmps.frame ht fun j h1 h2 => set_ne (by omega)
    obtain ⟨σ2, e2, h2, w2, k2, r2⟩ := Args.copyP_ok as st v σ1 (d + 1) ht1 hbs hn.2 (by simpa using hl)
    refine ⟨σ2, .seq .assign e2, h2, w2, fun j hj hj' => ?_, ⟨?_, ?_⟩⟩
    · simp only [vsOfP, List.map_cons, List.mem_cons, not_or] at hj'
      rw [k2 j (by omega) hj'.2]; exact set_ne (by omega)
    · show σ2.env l.v = _; rw [k2 l.v (by omega) hn.1]; exact set_ne (by omega)
    · exact Args.ResP.base r2 (fun l' h' => set_ne (by
        have := (hb l' (List.mem_cons_of_mem _ (by simpa using h'))).1; omega)) (by simpa using hl)


/-! ## The work array of a loop state -/

/-- the locations of the work arrays of a state -/
def workLocs : (Δ : List Sl) → List PLoc → List PLoc
  | [], _ => []
  | .sc _ :: Δ, st => workLocs Δ st.tail
  | .ar _ :: Δ, st => (if (st.headD default).inp then [] else [st.headD default]) ++ workLocs Δ st.tail

/-- the work arrays of the new state of a call leaf -/
def Args.arrs {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → List PLoc → Vals Γ → Mach.BEnv → List (Nat × W64)
  | _, .nil, _, _, _ => []
  | _, @Args.cons _ (.sc _) _ _ as, st, v, env => as.arrs st.tail v env
  | _, @Args.cons _ (.ar k) _ a as, st, v, env =>
    if (st.headD default).inp then as.arrs st.tail v env
    else ((env (st.headD default).pt).toNat, words k (A.den a v)) :: as.arrs st.tail v env

/-- the words of the new value of the component at `w` -/
def Args.wwords {Γ : List Sl} : {Δ : List Sl} → Args Γ Δ → List PLoc → PLoc → Vals Γ → W64
  | _, .nil, _, _, _ => []
  | _, @Args.cons _ (.sc _) _ _ as, st, w, v => as.wwords st.tail w v
  | _, @Args.cons _ (.ar k) _ a as, st, w, v =>
    if st.headD default = w then words k (A.den a v) else as.wwords st.tail w v

theorem arrsP_args {Γ : List Sl} {v : Vals Γ} {env : Mach.BEnv} : ∀ {Δ : List Sl} (as : Args Γ Δ) (st : List PLoc),
    arrsP Δ st (as.den v) env = as.arrs st v env
  | _, .nil, _ => rfl
  | _, @Args.cons _ (.sc _) _ _ as, st => by simp only [Args.den, arrsP, Args.arrs]; exact arrsP_args as st.tail
  | _, @Args.cons _ (.ar _) _ _ as, st => by
    simp only [Args.den, arrsP, Args.arrs, Arg.den]; rw [arrsP_args as st.tail]

theorem workLocs_inp : ∀ {Δ : List Sl} {st : List PLoc} {l : PLoc}, l ∈ workLocs Δ st → l.inp = false
  | [], _, _, h => by simp [workLocs] at h
  | .sc _ :: _, st, _, h => by simp only [workLocs] at h; exact workLocs_inp h
  | .ar _ :: _, st, l, h => by
    simp only [workLocs, List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp at h
      · rename_i hi; simp only [List.mem_singleton] at h; subst h; simpa using hi
    · exact workLocs_inp h

theorem args_arrs_nil {Γ : List Sl} {v : Vals Γ} {env : Mach.BEnv} : ∀ {Δ : List Sl} (as : Args Γ Δ)
    (st : List PLoc), workLocs Δ st = [] → as.arrs st v env = []
  | _, .nil, _, _ => rfl
  | _, @Args.cons _ (.sc _) _ _ as, st, h => by
    simp only [workLocs] at h; simp only [Args.arrs]; exact args_arrs_nil as st.tail h
  | _, @Args.cons _ (.ar _) _ _ as, st, h => by
    simp only [workLocs] at h
    simp only [Args.arrs]
    by_cases hi : (st.headD default).inp = true
    · rw [if_pos hi] at h ⊢; exact args_arrs_nil as st.tail (by simpa using h)
    · rw [if_neg hi] at h; simp at h

theorem args_arrs_one {Γ : List Sl} {v : Vals Γ} {env : Mach.BEnv} {w : PLoc} : ∀ {Δ : List Sl} (as : Args Γ Δ)
    (st : List PLoc), workLocs Δ st = [w] → as.arrs st v env = [((env w.pt).toNat, as.wwords st w v)]
  | _, .nil, _, h => by simp [workLocs] at h
  | _, @Args.cons _ (.sc _) _ _ as, st, h => by
    simp only [workLocs] at h; simp only [Args.arrs, Args.wwords]; exact args_arrs_one as st.tail h
  | _, @Args.cons _ (.ar _) _ _ as, st, h => by
    simp only [workLocs] at h
    simp only [Args.arrs, Args.wwords]
    by_cases hi : (st.headD default).inp = true
    · rw [if_pos hi] at h ⊢; simp only [List.nil_append] at h
      have hw : w.inp = false := workLocs_inp (by rw [h]; simp)
      rw [if_neg (fun e => by rw [e] at hi; rw [hw] at hi; cases hi)]
      exact args_arrs_one as st.tail h
    · rw [if_neg hi] at h ⊢
      simp only [List.singleton_append, List.cons.injEq] at h
      rw [if_pos h.1, h.1, args_arrs_nil as st.tail h.2]

/-- the array component at `w` (the first one) is represented -/
def Args.WOK {Γ : List Sl} (σ : MSt) (w : PLoc) : {Δ : List Sl} → Args Γ Δ → List PLoc → Vals Γ → Prop
  | _, .nil, _, _ => True
  | _, @Args.cons _ (.sc _) _ _ as, st, v => as.WOK σ w st.tail v
  | _, @Args.cons _ (.ar k) _ a as, st, v =>
    if st.headD default = w then SRP σ (.ar k) w (A.den a v) else as.WOK σ w st.tail v

theorem workLocs_mem_of {Δ : List Sl} {st : List PLoc} {w : PLoc} (h : workLocs Δ st = []) (hw : w ∈ workLocs Δ st) :
    False := by rw [h] at hw; simp at hw

/-- the update of a call leaf is no code or exactly one update; the words of the new value at `w` -/
theorem Args.updP_shape (L : List PLoc) {Γ : List Sl} (w : PLoc) (v : Vals Γ) (e : Nat) :
    ∀ {Δ : List Sl} (as : Args Γ Δ) (st : List PLoc) (cw : Bool), as.wfP L st w cw = true →
    (workLocs Δ st = [w] ∨ workLocs Δ st = []) →
    (as.updP L st e = skipAt e ∧ as.evs v = [] ∧
      (workLocs Δ st = [w] → ∀ ws, (∀ k (m : Mem Γ (.ar k)), m.locP L = w → words k (m.get v) = ws) →
        as.wwords st w v = ws) ∧
      (∀ σ', (∀ k (m : Mem Γ (.ar k)), m.locP L = w → SRP σ' (.ar k) w (m.get v)) → as.WOK σ' w st v)) ∨
    (∃ (k : AK) (a : A Γ k), cw = true ∧ as.updP L st e = .seq (A.preP L a e) (A.stP w (e + a.nt) a e) ∧
      as.evs v = A.evs a v ∧ a.base.locP L = w ∧ w.inp = false ∧ a.wfP L = true ∧ (as.okP v → a.okP v) ∧
      workLocs Δ st = [w] ∧ as.wwords st w v = words k (A.den a v) ∧
      (∀ σ', SRP σ' (.ar k) w (A.den a v) → as.WOK σ' w st v))
  | _, .nil, _, _, _, hwl => .inl ⟨rfl, rfl, fun h => by simp [workLocs] at h, fun _ _ => trivial⟩
  | _, @Args.cons _ (.sc _) _ _ as, st, cw, h, hwl => by
    simp only [Args.wfP, Bool.and_eq_true] at h
    simp only [workLocs] at hwl
    simp only [Args.updP, Args.evs, Args.okP, Args.wwords, workLocs, Args.WOK]
    rcases Args.updP_shape L w v e as st.tail cw h.2 hwl with h' | ⟨k, a, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    · exact .inl h'
    · exact .inr ⟨k, a, h1, h2, h3, h4, h5, h6, fun ho => h7 ho.2, h8, h9, h10⟩
  | _, @Args.cons _ (.ar _) Δt a as, st, cw, h, hwl => by
    simp only [workLocs] at hwl
    cases a with
    | var m =>
      simp only [Args.wfP, Bool.and_eq_true, beq_iff_eq] at h
      simp only [Args.updP, Args.evs, Args.okP, A.evs, List.nil_append, Args.wwords, workLocs, Arg.den, A.den,
        Args.WOK]
      by_cases hi : (st.headD default).inp = true
      · rw [if_pos hi] at hwl ⊢; simp only [List.nil_append] at hwl ⊢
        have hne : (st.headD default = w) → workLocs Δt st.tail = [w] → False := fun e hw' => by
          have := workLocs_inp (show w ∈ workLocs Δt st.tail by rw [hw']; simp); rw [← e, hi] at this; cases this
        rcases Args.updP_shape L w v e as st.tail cw h.2 hwl with ⟨c1, c2, c3, c4⟩ | ⟨k, a, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
        · refine .inl ⟨c1, c2, fun hw ws hm => ?_, fun σ' hs => ?_⟩
          · rw [if_neg (fun e => hne e hw)]; exact c3 hw ws hm
          · by_cases hl : st.headD default = w
            · rw [if_pos hl]; exact hs _ m (h.1.trans hl)
            · rw [if_neg hl]; exact c4 σ' hs
        · exact .inr ⟨k, a, h1, h2, h3, h4, h5, h6, fun ho => h7 ho.2, h8,
            by rw [if_neg (fun e => hne e h8)]; exact h9, fun σ' hs => by rw [if_neg (fun e => hne e h8)]; exact h10 σ' hs⟩
      · rw [if_neg hi] at hwl ⊢
        simp only [List.singleton_append] at hwl ⊢
        rcases hwl with hwl | hwl
        · simp only [List.cons.injEq] at hwl
          obtain ⟨hl, ht⟩ := hwl
          rcases Args.updP_shape L w v e as st.tail cw h.2 (.inr ht) with ⟨c1, c2, c3, c4⟩ | ⟨k, a, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
          · refine .inl ⟨c1, c2, fun _ ws hm => ?_, fun σ' hs => ?_⟩
            · rw [if_pos hl]; exact hm _ m (h.1.trans hl)
            · rw [if_pos hl]; exact hs _ m (h.1.trans hl)
          · rw [ht] at h8; simp at h8
        · simp at hwl
    | set a' i x | push a' x | ite c a' b' =>
      simp only [Args.wfP, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
      obtain ⟨⟨⟨⟨⟨hcw, hwa⟩, hbase⟩, hlw⟩, hin⟩, hwt⟩ := h
      have hhd : (st.headD default).inp = false := by rw [hlw]; exact hin
      rw [if_neg (by rw [hhd]; decide)] at hwl
      simp only [List.singleton_append] at hwl
      have hwl' : workLocs Δt st.tail = [] := by
        rcases hwl with hwl | hwl
        · simp only [List.cons.injEq] at hwl; exact hwl.2
        · simp at hwl
      refine .inr ⟨_, _, hcw, ?_, ?_, ?_, hin, hwa, fun ho => ho.1, ?_, ?_, fun σ' hs => ?_⟩
      · simp only [Args.updP]; rw [hlw]
      · simp only [Args.evs]
        rcases Args.updP_shape L w v e as st.tail false hwt (.inr hwl') with h' | ⟨_, _, h1, _⟩
        · rw [h'.2.1, List.append_nil]
        · cases h1
      · simp only [A.base] at hbase ⊢; rw [hbase, hlw]
      · simp only [workLocs, hwl', List.append_nil]; rw [if_neg (by rw [hhd]; decide), hlw]
      · simp only [Args.wwords, hlw, if_true, Arg.den]
      · simp only [Args.WOK, hlw, if_true, Arg.den]; exact hs

/-! ## The new state of a call leaf is represented -/

/-- the array components are represented at their slots -/
def Args.ArrOKP {Γ : List Sl} (σ : MSt) : {Δ : List Sl} → Args Γ Δ → List PLoc → Vals Γ → Prop
  | _, .nil, _, _ => True
  | _, @Args.cons _ (.sc _) _ _ as, st, v => as.ArrOKP σ st.tail v
  | _, @Args.cons _ (.ar k) _ a as, st, v => SRP σ (.ar k) (st.headD default) (A.den a v) ∧ as.ArrOKP σ st.tail v

theorem Args.relP {Γ : List Sl} : ∀ {Δ : List Sl} (as : Args Γ Δ) (st : List PLoc) (v : Vals Γ) (σu σ' : MSt),
    as.ResP σu σ' st v → as.ArrOKP σu st v → σ'.heap = σu.heap → st.length = Δ.length →
    RelP Δ st (as.den v) σ'
  | _, .nil, _, _, _, _, _, _, _, _ => trivial
  | _, .cons _ _, [], _, _, _, _, _, _, hl => by simp at hl
  | _, @Args.cons _ (.sc t) _ e as, l :: st, v, σu, σ', hres, ha, hh, hlen => by
    simp only [Args.ResP, List.headD_cons, List.tail_cons] at hres
    simp only [Args.ArrOKP, List.tail_cons] at ha
    refine ⟨?_, Args.relP as st v σu σ' hres.2 ha hh (by simpa using hlen)⟩
    show σ'.env l.v = _
    rw [hres.1]; rfl
  | _, @Args.cons _ (.ar k) _ a as, l :: st, v, σu, σ', hres, ha, hh, hlen => by
    simp only [Args.ResP, List.headD_cons, List.tail_cons] at hres
    simp only [Args.ArrOKP, List.headD_cons, List.tail_cons] at ha
    exact ⟨SRP.frame ha.1 hres.1 hh, Args.relP as st v σu σ' hres.2 ha.2 hh (by simpa using hlen)⟩

/-- the array components are represented: those at slots other than `w` by the old state (they are views
or unchanged), the one at `w` by `WOK` -/
theorem Args.arrOKP (L : List PLoc) {Γ : List Sl} (w : PLoc) (v : Vals Γ) (σu : MSt)
    (hvar : ∀ k (m : Mem Γ (.ar k)), m.locP L ≠ w → SRP σu (.ar k) (m.locP L) (m.get v)) :
    ∀ {Δ : List Sl} (as : Args Γ Δ) (st : List PLoc) (cw : Bool), as.wfP L st w cw = true →
      (vsOfP st).Nodup → st.length = Δ.length → (w ∈ st → as.WOK σu w st v) → as.ArrOKP σu st v
  | _, .nil, _, _, _, _, _, _ => trivial
  | _, .cons _ _, [], _, _, _, hl, _ => by simp at hl
  | _, @Args.cons _ (.sc _) _ _ as, l :: st, cw, h, hnd, hl, hw => by
    simp only [Args.wfP, Bool.and_eq_true, List.tail_cons] at h
    simp only [Args.WOK, List.tail_cons] at hw; simp only [Args.ArrOKP, List.tail_cons]
    simp only [vsOfP, List.map_cons, List.nodup_cons] at hnd
    exact Args.arrOKP L w v σu hvar as st cw h.2 hnd.2 (by simpa using hl) (fun hm => hw (List.mem_cons_of_mem _ hm))
  | _, @Args.cons _ (.ar k) _ a as, l :: st, cw, h, hnd, hl, hw => by
    simp only [Args.WOK, List.headD_cons, List.tail_cons] at hw; simp only [Args.ArrOKP, List.headD_cons, List.tail_cons]
    simp only [vsOfP, List.map_cons, List.nodup_cons] at hnd
    have hwf : ∃ cw', as.wfP L st w cw' = true := by
      simp only [Args.wfP] at h; split at h <;> simp only [Bool.and_eq_true, List.tail_cons] at h
      · exact ⟨_, h.2⟩
      · exact ⟨_, h.2⟩
    obtain ⟨cw', hwf⟩ := hwf
    by_cases hlw : l = w
    · subst hlw
      have hnot : l ∉ st := fun hm => hnd.1 (List.mem_map_of_mem hm)
      refine ⟨?_, Args.arrOKP L l v σu hvar as st cw' hwf hnd.2 (by simpa using hl) (fun hm => absurd hm hnot)⟩
      have := hw (List.mem_cons_self ..); rw [if_pos rfl] at this; exact this
    · rw [if_neg hlw] at hw
      refine ⟨?_, Args.arrOKP L w v σu hvar as st cw' hwf hnd.2 (by simpa using hl) (fun hm => hw (List.mem_cons_of_mem _ hm))⟩
      cases a with
      | var m =>
        simp only [Args.wfP, Bool.and_eq_true, beq_iff_eq, List.headD_cons] at h
        simp only [A.den]; rw [← h.1]; exact hvar _ m (by rw [h.1]; exact hlw)
      | set _ _ _ | push _ _ | ite _ _ _ =>
        simp only [Args.wfP, Bool.and_eq_true, beq_iff_eq, List.headD_cons] at h
        exact absurd h.1.1.2 hlw

end Proven.WA
