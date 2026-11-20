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
    rw [arrsP_append (by simpa using h)]; by_cases hi : l.inp = true <;> simp [hi]

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
      have := hw (List.mem_cons_self ..); simp only [↓reduceIte] at this; exact this
    · simp only [hlw, ↓reduceIte] at hw
      refine ⟨?_, Args.arrOKP L w v σu hvar as st cw' hwf hnd.2 (by simpa using hl) (fun hm => hw (List.mem_cons_of_mem _ hm))⟩
      cases a with
      | var m =>
        simp only [Args.wfP, Bool.and_eq_true, beq_iff_eq, List.headD_cons] at h
        simp only [A.den]; rw [← h.1]; exact hvar _ m (by rw [h.1]; exact hlw)
      | set _ _ _ | push _ _ | ite _ _ _ =>
        simp only [Args.wfP, Bool.and_eq_true, beq_iff_eq, List.headD_cons] at h
        exact absurd h.1.1.2 hlw

/-! ## One iteration -/

/-- the variables a loop leaves alone -/
def NP (j : Nat) : Prop := j ≠ vFh ∧ j ≠ vBump ∧ j ≠ vOk

/-- the layout of a loop: state variables (sizes and page tables), `res`, `fl` below `d`, distinct, none of the pool's -/
structure LoopLayP (st : List PLoc) (res fl : Nat) (rl w : PLoc) (d : Nat) : Prop where
  bst : BelowP st d
  hres : res < d
  hfl : fl < d
  hrl : rl.v < d ∧ rl.pt < d
  nd : (vsOfP st).Nodup
  rs : res ∉ vsOfP st
  fs : fl ∉ vsOfP st
  rf : res ≠ fl
  rlf : rl.v ≠ fl
  p8 : 8 ≤ res ∧ 8 ≤ fl ∧ ∀ l ∈ st, 8 ≤ l.v ∧ 8 ≤ l.pt
  ptn : ∀ l ∈ st, l.pt ∉ vsOfP st ∧ l.pt ≠ res ∧ l.pt ≠ fl
  w8 : 8 ≤ w.v ∧ 8 ≤ w.pt ∧ w.v ≠ w.pt ∧ w.v < d ∧ w.pt < d

theorem LoopLayP.mono {st : List PLoc} {res fl : Nat} {rl w : PLoc} {d d' : Nat} (h : LoopLayP st res fl rl w d)
    (h' : d ≤ d') : LoopLayP st res fl rl w d' :=
  ⟨h.bst.mono h', by have := h.hres; omega, by have := h.hfl; omega, by have := h.hrl; omega, h.nd, h.rs, h.fs, h.rf,
    h.rlf, h.p8, h.ptn, by have := h.w8; omega⟩

/-- the work array of the state before an iteration: none, or the one at `w` with words `ws` -/
def WPre (Δ : List Sl) (st : List PLoc) (w : PLoc) {Γ : List Sl} (L : List PLoc) (v : Vals Γ) (env : Mach.BEnv)
    (E0 : List (Nat × W64)) : Prop :=
  (workLocs Δ st = [] ∧ E0 = []) ∨
    (workLocs Δ st = [w] ∧ ∃ ws, E0 = [((env w.pt).toNat, ws)] ∧
      ∀ k (m : Mem Γ (.ar k)), m.locP L = w → words k (m.get v) = ws)

theorem rN_toNat_toNat (x : BitVec 64) : rN x.toNat = x := by simp [rN]

theorem workLocs_sub : ∀ {Δ : List Sl} {st : List PLoc} {l : PLoc}, st.length = Δ.length → l ∈ workLocs Δ st → l ∈ st
  | [], _, _, _, h => by simp [workLocs] at h
  | _ :: _, [], _, hl, _ => by simp at hl
  | .sc _ :: _, x :: st, _, hl, h => by
    simp only [workLocs, List.tail_cons] at h; exact List.mem_cons_of_mem _ (workLocs_sub (by simpa using hl) h)
  | .ar _ :: _, x :: st, l, hl, h => by
    simp only [workLocs, List.mem_append, List.headD_cons, List.tail_cons] at h
    rcases h with h | h
    · cases hx : x.inp <;> simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
      · simp only [List.mem_singleton] at h; subst h; exact List.mem_cons_self ..
      · simp at h
    · exact List.mem_cons_of_mem _ (workLocs_sub (by simpa using hl) h)

set_option maxHeartbeats 8000000 in
/-- **a call leaf**: the new state is represented (its work array in the store), or a push found no page -/
theorem Args.leaf_ok (st : List PLoc) (res fl : Nat) (rl w : PLoc) (C : Nat) (R0 E0 : List (Nat × W64))
    {Γ Δ : List Sl} (as : Args Γ Δ) (L : List PLoc) (v : Vals Γ) (σ : MSt) (d : Nat) (W : W64)
    (hE : EnvOK Γ L v σ) (hb : BelowP L d) (hy : LoopLayP st res fl rl w d) (hlen : st.length = Δ.length)
    (hwf : as.wfP L st w true = true) (hok : as.okP v) (hW : σ.wheap = [W]) (hok1 : σ.env vOk = 1)
    (hS : Store C σ.env W (E0 ++ R0)) (hpre : WPre Δ st w L v σ.env E0) (hst : ∀ l ∈ st, l ∈ L)
    (hLw : ∀ l ∈ L, l.v = w.v → l = w) (hLnp : ∀ l ∈ L, NP l.v) :
    ∃ σ' W', Mach.BExec (.seq (as.preP L d) (.seq (as.updP L st (d + Δ.length)) (as.copyP st d))) σ σ' ∧
      σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧ (∀ j, j < d → j ∉ vsOfP st → NP j → σ'.env j = σ.env j) ∧
      ((σ'.env vOk = 1 ∧ RelP Δ st (as.den v) σ' ∧
          Store C σ'.env W' (arrsP Δ st (as.den v) σ'.env ++ R0) ∧
          finE (pageCount (E0 ++ R0)) (as.evs v) = pageCount (arrsP Δ st (as.den v) σ'.env ++ R0) ∧
          pk (pageCount (E0 ++ R0)) (as.evs v) ≤ C) ∨
        (σ'.env vOk = 0 ∧ C < pk (pageCount (E0 ++ R0)) (as.evs v))) := by
  have hd8 : 8 ≤ d := by have := hy.p8.1; have := hy.hres; omega
  -- 1. scalar components into the temporaries
  obtain ⟨σ1, e1, h1, w1, k1, t1⟩ := Args.preP_ok L st w as v σ d true hE hE.len hb hwf hok
  have hE1 := hE.frame hb k1 h1 w1
  have hS1 : Store C σ1.env W (E0 ++ R0) := hS.env fun j hj => k1 j (by have := pool_vars hj; omega)
  have hW1 : σ1.wheap = [W] := by rw [w1, hW]
  have hok1' : σ1.env vOk = 1 := by rw [k1 _ (by simp only [vOk]; omega)]; exact hok1
  -- 2. the update
  have hwl : workLocs Δ st = [w] ∨ workLocs Δ st = [] := by
    rcases hpre with ⟨h, -⟩ | ⟨h, -⟩
    · exact .inr h
    · exact .inl h
  have hv8 : ∀ l ∈ st, 8 ≤ l.v ∧ 8 ≤ l.pt := hy.p8.2.2
  have hnpst : ∀ j, j ∈ vsOfP st → NP j := fun j hj => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hj; have := (hv8 l hl).1; simp only [NP, vFh, vBump, vOk]; omega
  -- the old state's slots, after any change of variables at or above `d`
  have hfr : ∀ (σx : MSt), σx.heap = σ.heap → (∀ j, j < d → j ≠ w.v → NP j → σx.env j = σ.env j) →
      ∀ k (m : Mem Γ (.ar k)), m.locP L ≠ w → SRP σx (.ar k) (m.locP L) (m.get v) := by
    intro σx hh hk k m hm
    have hmL := Mem.locP_mem m L hE.len
    refine SRP.frame (hE.rel.get m) (hk _ (hb _ hmL).1 (fun e => hm (hLw _ hmL e)) (hLnp _ hmL)) hh
  have hcopy : ∀ (σu : MSt), as.Tmps σu v d → ∃ σ', Mach.BExec (as.copyP st d) σu σ' ∧ σ'.heap = σu.heap ∧
      σ'.wheap = σu.wheap ∧ (∀ j, j < d → j ∉ vsOfP st → σ'.env j = σu.env j) ∧ as.ResP σu σ' st v :=
    fun σu tu => Args.copyP_ok as st v σu d tu hy.bst hy.nd hlen
  rcases Args.updP_shape L w v (d + Δ.length) as st true hwf hwl with ⟨c1, c2, c3, c4⟩ |
      ⟨k, a, -, hcode, hev, hbase, hwinp, hawf, haok, hwl1, hww, hwok⟩
  · -- no update
    let σu : MSt := ⟨σ1.env.set (d + Δ.length) 0, σ1.heap, σ1.wheap⟩
    have eu : Mach.BExec (as.updP L st (d + Δ.length)) σ1 σu := by rw [c1]; exact .assign
    have tu : as.Tmps σu v d := Args.Tmps.frame t1 fun j h1 h2 => by
      simp only [σu]; rw [set_ne (by omega)]
    obtain ⟨σ', e3, h3, w3, k3, r3⟩ := hcopy σu tu
    have hku : ∀ j, j < d → σu.env j = σ.env j := fun j hj => by
      simp only [σu]; rw [set_ne (by omega), k1 j hj]
    have hk' : ∀ j, j < d → j ∉ vsOfP st → σ'.env j = σ.env j := fun j hj hs => by rw [k3 j hj hs, hku j hj]
    have hrel : RelP Δ st (as.den v) σ' := by
      refine Args.relP as st v σu σ' r3 ?_ h3 hlen
      refine Args.arrOKP L w v σu (hfr σu (by simp [σu, h1]) fun j hj _ _ => hku j hj) as st true hwf hy.nd hlen
        (fun _ => c4 σu fun k m hm => ?_)
      have hmL := Mem.locP_mem m L hE.len
      rw [← hm]; exact SRP.frame (hE.rel.get m) (hku _ (hb _ hmL).1) (by simp [σu, h1])
    have hlow : ∀ j, j < 8 → σ'.env j = σ.env j := fun j hj => hk' j (by omega) (fun hm => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hm; have := (hv8 l hl).1; omega)
    have hE0eq : arrsP Δ st (as.den v) σ'.env = E0 := by
      rw [arrsP_args]
      rcases hpre with ⟨hw0, rfl⟩ | ⟨hw1, ws, rfl, hm⟩
      · exact args_arrs_nil as st hw0
      · rw [args_arrs_one as st hw1, c3 hw1 ws hm]
        have hwst : w ∈ st := workLocs_sub hlen (by rw [hw1]; simp)
        rw [hk' w.pt hy.w8.2.2.2.2 (hy.ptn w hwst).1]
    refine ⟨σ', W, .seq e1 (.seq eu e3), by rw [h3]; simp [σu, h1], by rw [w3]; simp [σu, hW1],
      fun j hj hs _ => hk' j hj hs, .inl ⟨?_, hrel, ?_, ?_, ?_⟩⟩
    · rw [hlow vOk (by decide)]; exact hok1
    · rw [hE0eq]; exact hS.env fun j hj => hlow j (by have := pool_vars hj; omega)
    · rw [c2, hE0eq]; rfl
    · rw [c2]; exact hS.count_le
  · -- the update `a` of the work array at `w`
    rcases hpre with ⟨hw0, -⟩ | ⟨-, ws, hE0, hm⟩
    · rw [hw0] at hwl1; cases hwl1
    have hwst : w ∈ st := workLocs_sub hlen (by rw [hwl1]; simp)
    have hwL : w ∈ L := hst w hwst
    generalize he : d + Δ.length = e at hcode t1
    have hde : d ≤ e := by omega
    obtain ⟨σ2, e2, h2, w2, k2, t2⟩ := A.preP_ok L a v σ1 e hE1 hE.len (hb.mono hde) hawf (haok hok)
    have hk21 : ∀ j, j < d → σ2.env j = σ.env j := fun j hj => by rw [k2 j (by omega), k1 j hj]
    have hW2 : σ2.wheap = [W] := by rw [w2, hW1]
    have hS2 : Store C σ2.env W (((σ.env w.pt).toNat, words k (a.base.get v)) :: R0) := by
      have := hS.env (env' := σ2.env) fun j hj => hk21 j (by have := pool_vars hj; omega)
      rw [hE0, ← hm k a.base hbase] at this; exact this
    have hpt2 : σ2.env w.pt = rN (σ.env w.pt).toNat := by rw [rN_toNat_toNat, hk21 _ hy.w8.2.2.2.2]
    have hsz2 : σ2.env w.v = rN (AK.size k (a.base.get v)) := by
      have := (hE.rel.get a.base).1; rw [hbase] at this; rw [hk21 _ hy.w8.2.2.2.1]; exact this
    obtain ⟨σu, Wu, eu, hu, wu, ku, ru⟩ := A.stP_ok w (e + a.nt) C _ R0 a v σ2 e W hW2 hS2 hpt2 hsz2 t2 (haok hok)
      (A.baseOK_of_wf L a hawf) (by rw [hk21 _ (by simp only [vOk]; omega)]; exact hok1) hy.w8.1 hy.w8.2.1
      hy.w8.2.2.1 (by have := hy.w8.2.2.2.1; omega) (by have := hy.w8.2.2.2.2; omega) (Nat.le_refl _)
    have hkuσ : ∀ j, j < d → j ≠ w.v → NP j → σu.env j = σ.env j := fun j hj hw hn => by
      rw [ku j (.inl (by omega)) hw hn.1 hn.2.1 hn.2.2, hk21 j hj]
    have tu : as.Tmps σu v d := Args.Tmps.frame t1 fun j h1 h2 => by
      rw [ku j (.inl (by omega)) (by have := hy.w8.2.2.2.1; omega) (by simp only [vFh]; omega)
        (by simp only [vBump]; omega) (by simp only [vOk]; omega), k2 j (by omega)]
    obtain ⟨σ', e3, h3, w3, k3, r3⟩ := hcopy σu tu
    have hk' : ∀ j, j < d → j ∉ vsOfP st → NP j → σ'.env j = σ.env j := fun j hj hs hn => by
      rw [k3 j hj hs, hkuσ j hj (fun e => hs (e ▸ List.mem_map_of_mem hwst)) hn]
    have hlow : ∀ j, j < 8 → j ≠ vFh → j ≠ vBump → j ≠ vOk → σ'.env j = σ.env j := fun j hj a b c =>
      hk' j (by omega) (fun hm => by obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hm; have := (hv8 l hl).1; omega) ⟨a, b, c⟩
    have hcode' : Mach.BExec (as.updP L st e) σ1 σu := by rw [hcode]; exact .seq e2 eu
    have hfr' : ∀ j, j = vCap ∨ j = vBump ∨ j = vFh → σ'.env j = σu.env j := fun j hj => by
      have := pool_vars hj
      exact k3 j (by omega) (fun hm => by obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hm; have := (hv8 l hl).1; omega)
    have hokσ' : σ'.env vOk = σu.env vOk := by
      refine k3 vOk (by simp only [vOk]; omega) (fun hm => ?_)
      obtain ⟨l, hl, he'⟩ := List.mem_map.1 hm
      have := (hv8 l hl).1; simp only [vOk] at he'; omega
    have hu0 : pageCount (E0 ++ R0) = pageCount (((σ.env w.pt).toNat, words k (a.base.get v)) :: R0) := by
      rw [hE0, ← hm k a.base hbase]; rfl
    refine ⟨σ', Wu, .seq e1 (.seq hcode' e3), by rw [h3, hu, h2, h1], by rw [w3, wu], fun j hj hs hn => hk' j hj hs hn,
      ?_⟩
    rw [hev, hu0]
    rcases ru with ⟨o, sz, Su, fu, pu⟩ | ⟨o, pu⟩
    · refine .inl ⟨by rw [hokσ']; exact o, ?_, ?_, ?_, pu⟩
      · refine Args.relP as st v σu σ' r3 ?_ h3 hlen
        refine Args.arrOKP L w v σu ?_ as st true hwf hy.nd hlen (fun _ => hwok σu ?_)
        · exact hfr σu (by rw [hu, h2, h1]) hkuσ
        · have hA := Su.2 _ (List.mem_cons_self ..)
          have hlen' := hA.len
          rw [words_length] at hlen'
          refine ⟨sz, by rw [P] at hlen'; omega, fun h => absurd h (by rw [hwinp]; decide), fun _ => hlen'⟩
      · rw [arrsP_args, args_arrs_one as st hwl1, hww]
        have : σ'.env w.pt = σ.env w.pt := hk' w.pt hy.w8.2.2.2.2 (hy.ptn w hwst).1 (hLnp w hwL |> fun _ => by
          simp only [NP, vFh, vBump, vOk]; have := hy.w8.2.1; omega)
        rw [this]; exact Su.env hfr'
      · rw [fu, arrsP_args, args_arrs_one as st hwl1, hww]
        have : σ'.env w.pt = σ.env w.pt := hk' w.pt hy.w8.2.2.2.2 (hy.ptn w hwst).1 (by
          simp only [NP, vFh, vBump, vOk]; have := hy.w8.2.1; omega)
        rw [this]; rfl
    · exact .inr ⟨by rw [hokσ']; exact o, pu⟩

/-- the result of a loop: a scalar in `res`, an array at `rl` (a work array: the state's) -/
def RRP (σ : MSt) (E0 : List (Nat × W64)) : (R : Sl) → Nat → PLoc → R.T → Prop
  | .sc t, res, _, r => σ.env res = t.rep r
  | .ar k, _, rl, r => SRP σ (.ar k) rl r ∧ (rl.inp = false → E0 = [((σ.env rl.pt).toNat, words k r)])

/-- the outcome of one iteration -/
def OutP (Δ : List Sl) (R : Sl) (st : List PLoc) (res fl : Nat) (rl : PLoc) (C : Nat) (R0 E0 : List (Nat × W64))
    (σ σ' : MSt) (W W' : W64) (E : List MemEvent) : Vals Δ ⊕ R.T → Prop
  | .inl s' => σ'.env fl = σ.env fl ∧
      ((σ'.env vOk = 1 ∧ RelP Δ st s' σ' ∧ Store C σ'.env W' (arrsP Δ st s' σ'.env ++ R0) ∧
          finE (pageCount (E0 ++ R0)) E = pageCount (arrsP Δ st s' σ'.env ++ R0) ∧ pk (pageCount (E0 ++ R0)) E ≤ C) ∨
        (σ'.env vOk = 0 ∧ C < pk (pageCount (E0 ++ R0)) E))
  | .inr r => σ'.env fl = 0 ∧ σ'.env vOk = 1 ∧ W' = W ∧ E = [] ∧ RRP σ' E0 R res rl r ∧
      (∀ j ∈ vsOfP st, σ'.env j = σ.env j) ∧ Store C σ'.env W' (E0 ++ R0)

theorem RRP.frame {σ σ' : MSt} {E0 : List (Nat × W64)} {R : Sl} {res : Nat} {rl : PLoc} {r : R.T}
    (h : RRP σ E0 R res rl r) (hres : σ'.env res = σ.env res) (hv : σ'.env rl.v = σ.env rl.v)
    (hp : σ'.env rl.pt = σ.env rl.pt) (hh : σ'.heap = σ.heap) : RRP σ' E0 R res rl r := by
  cases R with
  | sc t => show σ'.env res = _; rw [hres]; exact h
  | ar k => exact ⟨SRP.frame h.1 hv hh, fun hi => by rw [hp]; exact h.2 hi⟩

theorem RelP.frameL : ∀ {Γ : List Sl} {L : List PLoc} {v : Vals Γ} {σ σ' : MSt}, RelP Γ L v σ →
    (∀ l ∈ L, σ'.env l.v = σ.env l.v) → σ'.heap = σ.heap → Γ.length ≤ L.length → RelP Γ L v σ' := RelP.frame

/-- the outcome survives changes of variables that are not the state's, `res`, `fl`, the pool's -/
theorem OutP.frame {Δ : List Sl} {R : Sl} {st : List PLoc} {res fl : Nat} {rl : PLoc} {C : Nat}
    {R0 E0 : List (Nat × W64)} {σ σ1 σ' : MSt} {W W' : W64} {E : List MemEvent} {o : Vals Δ ⊕ R.T}
    (h : OutP Δ R st res fl rl C R0 E0 σ σ1 W W' E o) (hlen : st.length = Δ.length)
    (hk : ∀ j, (j ∈ vsOfP st ∨ (∃ l ∈ st, j = l.pt) ∨ j = res ∨ j = fl ∨ j = rl.v ∨ j = rl.pt ∨ j < 8) →
      σ'.env j = σ1.env j)
    (hh : σ'.heap = σ1.heap) (hw : σ'.wheap = σ1.wheap) :
    OutP Δ R st res fl rl C R0 E0 σ σ' W W' E o := by
  cases o with
  | inl s' =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨by rw [hk fl (.inr (.inr (.inr (.inl rfl))))]; exact h1, ?_⟩
    rcases h2 with ⟨o1, r1, S1, f1, p1⟩ | ⟨o1, p1⟩
    · have harr : arrsP Δ st s' σ'.env = arrsP Δ st s' σ1.env :=
        arrsP_congr (fun l hl => hk _ (.inr (.inl ⟨l, hl, rfl⟩))) (by omega)
      refine .inl ⟨by rw [hk vOk (.inr (.inr (.inr (.inr (.inr (.inr (by decide)))))))]; exact o1,
        r1.frameL (fun l hl => hk _ (.inl (List.mem_map_of_mem hl))) hh (by omega), ?_, by rw [harr]; exact f1, p1⟩
      rw [harr]; exact S1.env fun j hj => hk j (.inr (.inr (.inr (.inr (.inr (.inr (pool_vars hj)))))))
    · exact .inr ⟨by rw [hk vOk (.inr (.inr (.inr (.inr (.inr (.inr (by decide)))))))]; exact o1, p1⟩
  | inr r =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
    refine ⟨by rw [hk fl (.inr (.inr (.inr (.inl rfl))))]; exact h1,
      by rw [hk vOk (.inr (.inr (.inr (.inr (.inr (.inr (by decide)))))))]; exact h2, h3, h4,
      RRP.frame h5 (hk _ (.inr (.inr (.inl rfl)))) (hk _ (.inr (.inr (.inr (.inr (.inl rfl))))))
        (hk _ (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))) hh, fun j hj => by rw [hk j (.inl hj)]; exact h6 j hj,
      h7.env fun j hj => hk j (.inr (.inr (.inr (.inr (.inr (.inr (pool_vars hj)))))))⟩

theorem OutP.base {Δ : List Sl} {R : Sl} {st : List PLoc} {res fl : Nat} {rl : PLoc} {C : Nat}
    {R0 E0 : List (Nat × W64)} {σ σ0 σ' : MSt} {W W' : W64} {E : List MemEvent} {o : Vals Δ ⊕ R.T}
    (h : OutP Δ R st res fl rl C R0 E0 σ σ' W W' E o) (hfl : σ.env fl = σ0.env fl)
    (hs : ∀ j ∈ vsOfP st, σ.env j = σ0.env j) :
    OutP Δ R st res fl rl C R0 E0 σ0 σ' W W' E o := by
  cases o with
  | inl s' => exact ⟨h.1.trans hfl, h.2⟩
  | inr r => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun j hj => (h.2.2.2.2.2.1 j hj).trans (hs j hj),
      h.2.2.2.2.2.2⟩

theorem WPre.env {Δ : List Sl} {st : List PLoc} {w : PLoc} {Γ : List Sl} {L : List PLoc} {v : Vals Γ}
    {env env' : Mach.BEnv} {E0 : List (Nat × W64)} (h : WPre Δ st w L v env E0) (he : env' w.pt = env w.pt) :
    WPre Δ st w L v env' E0 := by
  rcases h with h | ⟨h1, ws, h2, h3⟩
  · exact .inl h
  · exact .inr ⟨h1, ws, by rw [he]; exact h2, h3⟩

theorem WPre.let_ {Δ : List Sl} {st : List PLoc} {w : PLoc} {Γ : List Sl} {L : List PLoc} {v : Vals Γ}
    {env : Mach.BEnv} {E0 : List (Nat × W64)} {t : Ty} (x : t.T) (l : PLoc) (h : WPre Δ st w L v env E0) :
    WPre Δ st w (Γ := .sc t :: Γ) (l :: L) ((x, v) : Vals (.sc t :: Γ)) env E0 := by
  rcases h with h | ⟨h1, ws, h2, h3⟩
  · exact .inl h
  · refine .inr ⟨h1, ws, h2, fun k m hm => ?_⟩
    cases m with
    | tl m' => rw [Mem.locP_tl] at hm; exact h3 k m' hm

set_option maxHeartbeats 8000000 in
/-- **One iteration of a loop body.** -/
theorem T.compP_ok (st : List PLoc) (res fl : Nat) (rl w : PLoc) (C : Nat) (R0 : List (Nat × W64)) :
    ∀ {Γ Δ : List Sl} {R : Sl} (b : T Γ Δ R) (L : List PLoc) (v : Vals Γ) (σ : MSt) (d : Nat) (W : W64)
    (E0 : List (Nat × W64)), EnvOK Γ L v σ → BelowP L d → LoopLayP st res fl rl w d → st.length = Δ.length →
    b.wfP st rl w L d = true → b.okP v → σ.wheap = [W] → σ.env vOk = 1 → Store C σ.env W (E0 ++ R0) →
    WPre Δ st w L v σ.env E0 → (∀ l ∈ st, l ∈ L) → (∀ l ∈ L, l.v = w.v → l = w) → (∀ l ∈ L, NP l.v) →
    (rl.inp = false → rl = w ∧ workLocs Δ st = [w]) →
    ∃ σ' W', Mach.BExec (b.compP st res fl L d) σ σ' ∧ σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧
      (∀ j, j < d → j ∉ vsOfP st → j ≠ res → j ≠ fl → NP j → σ'.env j = σ.env j) ∧
      OutP Δ R st res fl rl C R0 E0 σ σ' W W' (b.evs v) (b.out v)
  | _, _, .sc t, .ret e, L, v, σ, d, W, E0, hE, hb, hy, hlen, hwf, hok, hW, hok1, hS, hpre, hst, hLw, hLnp, hrl => by
    simp only [T.wfP] at hwf; simp only [T.okP] at hok
    simp only [T.compP, T.out, T.evs]
    obtain ⟨σ1, e1, v1, k1, h1, w1⟩ := E.compP_ok L e v σ d hE hE.len hb hwf hok
    refine ⟨_, W, .seq e1 (.seq .assign .assign), h1, by rw [w1, hW], fun j hj _ h2 h3 _ => ?_, ?_, ?_, rfl, rfl, ?_,
      fun j hj => ?_, ?_⟩
    · simp only [set_ne h3, set_ne h2, k1 j hj]
    · simp only [set_eq]; rfl
    · simp only [set_ne (show vOk ≠ fl by have := hy.p8.2.1; simp only [vOk]; omega),
        set_ne (show vOk ≠ res by have := hy.p8.1; simp only [vOk]; omega), k1 _ (show vOk < d by
          have := hy.p8.1; have := hy.hres; simp only [vOk]; omega)]; exact hok1
    · show _ = _
      simp only [set_ne hy.rf, Mach.BExp.denote, set_eq, Arg.den]; rw [v1]
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hj
      have := (hy.bst l hl).1
      simp only [set_ne (show l.v ≠ fl by intro e; exact hy.fs (e ▸ hj)),
        set_ne (show l.v ≠ res by intro e; exact hy.rs (e ▸ hj))]
      exact k1 _ this
    · refine hS.env fun j hj => ?_
      have := pool_vars hj
      simp only [set_ne (show j ≠ fl by have := hy.p8.2.1; omega), set_ne (show j ≠ res by have := hy.p8.1; omega)]
      exact k1 _ (by have := hy.p8.1; have := hy.hres; omega)
  | _, _, .ar k, .ret a, L, v, σ, d, W, E0, hE, hb, hy, hlen, hwf, hok, hW, hok1, hS, hpre, hst, hLw, hLnp, hrl => by
    simp only [T.compP, T.out, T.evs]
    cases a with
    | var m =>
      simp only [T.wfP, beq_iff_eq] at hwf
      have hS' := hE.rel.get m
      rw [hwf] at hS'
      refine ⟨_, W, .assign, rfl, hW, fun j hj _ _ h3 _ => set_ne h3, ?_, ?_, rfl, rfl, ⟨?_, ?_⟩, fun j hj => ?_, ?_⟩
      · simp only [set_eq]; rfl
      · show (σ.env.set fl _) vOk = 1
        rw [set_ne (show vOk ≠ fl by have := hy.p8.2.1; simp only [vOk]; omega)]; exact hok1
      · exact SRP.frame hS' (set_ne hy.rlf) rfl
      · intro hi
        obtain ⟨hrw, hwl⟩ := hrl hi
        rcases hpre with ⟨hw0, -⟩ | ⟨hw1, ws, hE0, hm⟩
        · rw [hw0] at hwl; cases hwl
        · have hwst : w ∈ st := workLocs_sub hlen (by rw [hw1]; simp)
          show E0 = [(((σ.env.set fl _) rl.pt).toNat, words k (m.get v))]
          rw [hE0, set_ne (by rw [hrw]; exact (hy.ptn w hwst).2.2), hrw, hm k m (hwf.trans hrw)]
      · show (σ.env.set fl _) j = σ.env j
        exact set_ne (fun e => hy.fs (e ▸ hj))
      · exact hS.env fun j hj => set_ne (by have := pool_vars hj; have := hy.p8.2.1; omega)
    | set _ _ _ | push _ _ | ite _ _ _ => simp [T.wfP] at hwf
  | _, Δ, _, .call as, L, v, σ, d, W, E0, hE, hb, hy, hlen, hwf, hok, hW, hok1, hS, hpre, hst, hLw, hLnp, hrl => by
    simp only [T.wfP] at hwf; simp only [T.okP] at hok
    simp only [T.compP, T.out, T.evs]
    obtain ⟨σ', W', e1, h1, w1, k1, r1⟩ := Args.leaf_ok st res fl rl w C R0 E0 as L v σ d W hE hb hy hlen hwf hok
      hW hok1 hS hpre hst hLw hLnp
    refine ⟨σ', W', e1, h1, w1, fun j hj hs _ _ hn => k1 j hj hs hn, ?_, r1⟩
    exact k1 fl hy.hfl hy.fs (by have := hy.p8.2.1; simp only [NP, vFh, vBump, vOk]; omega)
  | _, _, _, .ite c a b, L, v, σ, d, W, E0, hE, hb, hy, hlen, hwf, hok, hW, hok1, hS, hpre, hst, hLw, hLnp, hrl => by
    simp only [T.wfP, Bool.and_eq_true] at hwf; simp only [T.okP] at hok
    obtain ⟨⟨hwc, hwa⟩, hwb⟩ := hwf
    simp only [T.compP, T.out, T.evs]
    have hd8 : 8 ≤ d := by have := hy.p8.1; have := hy.hres; omega
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.compP_ok L c v σ d hE hE.len hb hwc hok.1).frameP hE hb hE.len
    let σ2 : MSt := ⟨σ1.env.set (d + 1) ((Mach.BExp.bin .eq (.var d) (.const 0)).denote σ1.env), σ1.heap, σ1.wheap⟩
    have hk2 : ∀ j, j < d → σ2.env j = σ.env j := fun j hj => by
      simp only [σ2, set_ne (show j ≠ d + 1 by omega)]; exact k1 j hj
    have r2 : EnvOK _ L v σ2 := hE.frame hb hk2 (by simp [σ2, h1]) (by simp [σ2, w1])
    have e2 : Mach.BExec (.assign (d + 1) (.bin .eq (.var d) (.const 0))) σ1 σ2 := .assign
    have hc1 : σ2.env d = rB (c.den v) := by simp only [σ2, set_ne (show d ≠ d + 1 by omega)]; exact v1
    have hc2 : σ2.env (d + 1) = rB (!c.den v) := by
      simp only [σ2, set_eq, Mach.BExp.denote, Op.eval, v1]; cases c.den v <;> rfl
    have hW2 : σ2.wheap = [W] := by simp only [σ2]; rw [w1, hW]
    have hok2 : σ2.env vOk = 1 := by rw [hk2 _ (by simp only [vOk]; omega)]; exact hok1
    have hS2 : Store C σ2.env W (E0 ++ R0) := hS.env fun j hj => hk2 j (by have := pool_vars hj; omega)
    have hpre2 := hpre.env (hk2 _ hy.w8.2.2.2.2)
    have hy2 := hy.mono (show d ≤ d + 2 by omega)
    have hns : ∀ j, d ≤ j → j ∉ vsOfP st := fun j hj h => by
      obtain ⟨l, hl', e⟩ := List.mem_map.1 h; have := (hy.bst l hl').1; omega
    have hprot : ∀ j, (j ∈ vsOfP st ∨ (∃ l ∈ st, j = l.pt) ∨ j = res ∨ j = fl ∨ j = rl.v ∨ j = rl.pt ∨ j < 8) →
        j < d := by
      intro j hj
      rcases hj with h | ⟨l, hl, rfl⟩ | rfl | rfl | rfl | rfl | h
      · obtain ⟨l, hl', rfl⟩ := List.mem_map.1 h; exact (hy.bst l hl').1
      · exact (hy.bst l hl).2
      · exact hy.hres
      · exact hy.hfl
      · exact hy.hrl.1
      · exact hy.hrl.2
      · omega
    cases hcv : c.den v with
    | true =>
      have hoa := hok.2; rw [hcv, if_pos rfl] at hoa
      obtain ⟨σ3, W3, e3, h3, w3, k3, o3⟩ := T.compP_ok st res fl rl w C R0 a L v σ2 (d + 2) W E0 r2
        (hb.mono (by omega)) hy2 hlen hwa hoa hW2 hok2 hS2 hpre2 hst hLw hLnp hrl
      have hne : σ2.env d ≠ 0 := by rw [hc1, hcv]; decide
      have hw1 := when_true hne e3
      let σ4 : MSt := ⟨σ3.env.set d 0, σ3.heap, σ3.wheap⟩
      have hz : σ4.env (d + 1) = 0 := by
        simp only [σ4, set_ne (show d + 1 ≠ d by omega)]
        rw [k3 (d + 1) (by omega) (hns _ (by omega)) (by have := hy.hres; omega) (by have := hy.hfl; omega)
          (by simp only [NP, vFh, vBump, vOk]; omega), hc2, hcv]; rfl
      refine ⟨σ4, W3, .seq e1 (.seq e2 (.seq hw1 (when_false hz))), by simp [σ4, h3, σ2, h1], by simp [σ4, w3],
        fun j hj hs hr hf hn => ?_, ?_⟩
      · simp only [σ4, set_ne (show j ≠ d by omega)]
        rw [k3 j (by omega) hs hr hf hn, hk2 j hj]
      · rw [if_pos rfl, if_pos rfl]
        refine OutP.base (σ := σ2) (OutP.frame o3 hlen (fun j hj => ?_) rfl rfl) (hk2 fl hy.hfl)
          (fun j hj => hk2 j (by obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hj; exact (hy.bst l hl).1))
        simp only [σ4]; rw [set_ne (by have := hprot j hj; omega)]
    | false =>
      have hob := hok.2; rw [hcv] at hob; simp only [Bool.false_eq_true, if_false] at hob
      have hz : σ2.env d = 0 := by rw [hc1, hcv]; rfl
      obtain ⟨σ3, W3, e3, h3, w3, k3, o3⟩ := T.compP_ok st res fl rl w C R0 b L v σ2 (d + 2) W E0 r2
        (hb.mono (by omega)) hy2 hlen hwb hob hW2 hok2 hS2 hpre2 hst hLw hLnp hrl
      have hne : σ2.env (d + 1) ≠ 0 := by rw [hc2, hcv]; decide
      have hw2 := when_true hne e3
      refine ⟨_, W3, .seq e1 (.seq e2 (.seq (when_false hz) hw2)), by simp [h3, σ2, h1], by simp [w3],
        fun j hj hs hr hf hn => ?_, ?_⟩
      · simp only [set_ne (show j ≠ d + 1 by omega)]
        rw [k3 j (by omega) hs hr hf hn, hk2 j hj]
      · simp only [Bool.false_eq_true, if_false]
        refine OutP.base (σ := σ2) (OutP.frame o3 hlen (fun j hj => ?_) rfl rfl) (hk2 fl hy.hfl)
          (fun j hj => hk2 j (by obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hj; exact (hy.bst l hl).1))
        show (σ3.env.set (d + 1) 0) j = σ3.env j
        rw [set_ne (by have := hprot j hj; omega)]
  | _, _, _, .let_ e k, L, v, σ, d, W, E0, hE, hb, hy, hlen, hwf, hok, hW, hok1, hS, hpre, hst, hLw, hLnp, hrl => by
    simp only [T.wfP, Bool.and_eq_true] at hwf; simp only [T.okP] at hok
    simp only [T.compP, T.out, T.evs]
    have hd8 : 8 ≤ d := by have := hy.p8.1; have := hy.hres; omega
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.compP_ok L e v σ d hE hE.len hb hwf.1 hok.1).frameP hE hb hE.len
    have r1' : EnvOK (.sc _ :: _) (⟨d, false, 0⟩ :: L) (E.den e v, v) σ1 := by
      refine ⟨⟨v1, r1.rel⟩, by simp; exact hE.len, ?_⟩
      obtain ⟨W1, hW1, h32, hall⟩ := r1.at_
      exact ⟨W1, hW1, h32, by unfold AllAt; simp only [arrsP, List.tail_cons]; exact hall⟩
    have hb1 : BelowP (⟨d, false, 0⟩ :: L) (d + 1) := by
      intro l hl'
      simp only [List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · simp only; omega
      · have := hb l hl'; omega
    have hW1 : σ1.wheap = [W] := by rw [w1, hW]
    have hpool : ∀ j, j < 8 → σ1.env j = σ.env j := fun j hj => k1 j (by omega)
    obtain ⟨σ2, W2, e2, h2, w2, k2, o2⟩ := T.compP_ok st res fl rl w C R0 k (⟨d, false, 0⟩ :: L) (E.den e v, v) σ1
      (d + 1) W E0 r1' hb1 (hy.mono (by omega)) hlen hwf.2 hok.2 hW1 (by rw [hpool _ (by decide)]; exact hok1)
      (hS.env fun j hj => hpool j (pool_vars hj))
      (WPre.let_ _ _ (hpre.env (k1 _ hy.w8.2.2.2.2))) (fun l hl => List.mem_cons_of_mem _ (hst l hl))
      (fun l hl e' => by
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · simp only at e'; have := hy.w8.2.2.2.1; omega
        · exact hLw l hl e')
      (fun l hl => by
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · simp only [NP, vFh, vBump, vOk]; omega
        · exact hLnp l hl) hrl
    refine ⟨σ2, W2, .seq e1 e2, h2.trans h1, w2, fun j hj hs hr hf hn => by rw [k2 j (by omega) hs hr hf hn, k1 j hj],
      ?_⟩
    exact OutP.base o2 (k1 fl hy.hfl)
      (fun j hj => k1 j (by obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hj; exact (hy.bst l hl).1))

/-! ## Loops -/

/-- the words of the state's slot at `w` -/
def wordsAt : (Δ : List Sl) → List PLoc → PLoc → Vals Δ → W64
  | [], _, _, _ => []
  | .sc _ :: Δ, st, w, s => wordsAt Δ st.tail w s.2
  | .ar k :: Δ, st, w, s => if st.headD default = w then words k s.1 else wordsAt Δ st.tail w s.2

theorem arrsP_nil {env : Mach.BEnv} : ∀ {Δ : List Sl} {st : List PLoc} (s : Vals Δ), workLocs Δ st = [] →
    arrsP Δ st s env = []
  | [], _, _, _ => rfl
  | .sc _ :: _, st, s, h => by simp only [workLocs] at h; simp only [arrsP]; exact arrsP_nil s.2 h
  | .ar _ :: _, st, s, h => by
    simp only [workLocs] at h; simp only [arrsP]
    by_cases hi : (st.headD default).inp = true
    · rw [if_pos hi] at h ⊢; exact arrsP_nil s.2 (by simpa using h)
    · rw [if_neg hi] at h; simp at h

theorem arrsP_one {env : Mach.BEnv} {w : PLoc} : ∀ {Δ : List Sl} {st : List PLoc} (s : Vals Δ),
    workLocs Δ st = [w] → arrsP Δ st s env = [((env w.pt).toNat, wordsAt Δ st w s)]
  | [], _, _, h => by simp [workLocs] at h
  | .sc _ :: _, st, s, h => by simp only [workLocs] at h; simp only [arrsP, wordsAt]; exact arrsP_one s.2 h
  | .ar _ :: _, st, s, h => by
    simp only [workLocs] at h; simp only [arrsP, wordsAt]
    by_cases hi : (st.headD default).inp = true
    · rw [if_pos hi] at h ⊢; simp only [List.nil_append] at h
      have hw : w.inp = false := workLocs_inp (by rw [h]; simp)
      rw [if_neg (fun e => by rw [e] at hi; rw [hw] at hi; cases hi)]
      exact arrsP_one s.2 h
    · rw [if_neg hi] at h ⊢
      simp only [List.singleton_append, List.cons.injEq] at h
      rw [if_pos h.1, h.1, arrsP_nil s.2 h.2]

/-- before an iteration: the state's work array, as the body needs it -/
theorem wpre_of {C : Nat} {W : W64} {Δ Γ : List Sl} {st L : List PLoc} {w : PLoc} {s : Vals Δ} {c : Vals Γ}
    {env : Mach.BEnv} {X : List (Nat × W64)} (hwl : workLocs Δ st = [w] ∨ workLocs Δ st = [])
    (hlen : st.length = Δ.length) (hS : Store C env W (arrsP Δ st s env ++ (arrsP Γ L c env ++ X))) :
    WPre Δ st w (st ++ L) (Vals.app s c) env (arrsP Δ st s env) := by
  rcases hwl with h | h
  · refine .inr ⟨h, wordsAt Δ st w s, arrsP_one s h, fun k m hm => ?_⟩
    have hwi : w.inp = false := workLocs_inp (by rw [h]; simp)
    have h1 := arrsP_mem (v := Vals.app s c) env m (by rw [hm]; exact hwi)
    rw [arrsP_append hlen, hm] at h1
    have h2 : ((env w.pt).toNat, wordsAt Δ st w s) ∈ arrsP Δ st s env ++ arrsP Γ L c env := by
      rw [arrsP_one s h]; simp
    rw [← List.append_assoc] at hS
    have := Store.uniq hS (List.mem_append_left _ h1) (List.mem_append_left _ h2) rfl
    exact (Prod.mk.inj this).2
  · exact .inl ⟨h, arrsP_nil s h⟩

/-- the code of a loop: `fl := 1; while (fl &&& vOk) { body }` -/
def T.loopP (st : List PLoc) (res fl : Nat) {Γ Δ : List Sl} {R : Sl} (b : T Γ Δ R) (L : List PLoc) (d : Nat) : MS :=
  .seq (.assign fl (.const 1)) (.loop (.bin .and (.var fl) (.var vOk)) (b.compP st res fl L d))

theorem and_flag {x y : BitVec 64} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) : (x &&& y ≠ 0) ↔ (x ≠ 0 ∧ y ≠ 0) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

set_option maxHeartbeats 8000000 in
/-- **A loop runs to its result**, or stops once a push found no page (exactly when the run's page events
exceed `C`) -/
theorem T.runP_ok {Δ Γ : List Sl} {R : Sl} (b : T (Δ ++ Γ) Δ R) (c : Vals Γ) (st L : List PLoc) (res fl : Nat)
    (rl w : PLoc) (d C : Nat) (X : List (Nat × W64)) (hy : LoopLayP st res fl rl w d) (hlen : st.length = Δ.length)
    (hl : Γ.length ≤ L.length) (hbL : BelowP L d)
    (hLd : ∀ l ∈ L, (l.v ∉ vsOfP st ∧ l.v ≠ res ∧ l.v ≠ fl ∧ NP l.v) ∧ (l.pt ∉ vsOfP st ∧ l.pt ≠ res ∧ l.pt ≠ fl ∧
      NP l.pt))
    (hwf : b.wfP st rl w (st ++ L) d = true) (hwl : workLocs Δ st = [w] ∨ workLocs Δ st = [])
    (hLw : ∀ l ∈ st ++ L, l.v = w.v → l = w) (hrl : rl.inp = false → rl = w ∧ workLocs Δ st = [w])
    (P : Vals Δ → Prop) (hok : ∀ s, P s → b.okP (Vals.app s c))
    (hP : ∀ s s', P s → b.out (Vals.app s c) = .inl s' → P s') :
    ∀ s r E, RunsE b c s r E → P s → ∀ σ W, EnvOK (Δ ++ Γ) (st ++ L) (Vals.app s c) σ → σ.env fl ≠ 0 →
      (σ.env fl = 0 ∨ σ.env fl = 1) → σ.env vOk = 1 → σ.wheap = [W] →
      Store C σ.env W (arrsP Δ st s σ.env ++ (arrsP Γ L c σ.env ++ X)) →
      ∃ σ' W', Mach.BExec (.loop (.bin .and (.var fl) (.var vOk)) (b.compP st res fl (st ++ L) d)) σ σ' ∧
        σ'.heap = σ.heap ∧ σ'.wheap = [W'] ∧
        (∀ j, j < d → j ∉ vsOfP st → j ≠ res → j ≠ fl → NP j → σ'.env j = σ.env j) ∧
        ((σ'.env vOk = 1 ∧ ∃ sf, RelP Δ st sf σ' ∧ RRP σ' (arrsP Δ st sf σ'.env) R res rl r ∧
            Store C σ'.env W' (arrsP Δ st sf σ'.env ++ (arrsP Γ L c σ.env ++ X)) ∧
            finE (pageCount (arrsP Δ st s σ.env ++ (arrsP Γ L c σ.env ++ X))) E =
              pageCount (arrsP Δ st sf σ'.env ++ (arrsP Γ L c σ.env ++ X)) ∧
            pk (pageCount (arrsP Δ st s σ.env ++ (arrsP Γ L c σ.env ++ X))) E ≤ C) ∨
          (σ'.env vOk = 0 ∧ C < pk (pageCount (arrsP Δ st s σ.env ++ (arrsP Γ L c σ.env ++ X))) E)) := by
  have hl2 : (Δ ++ Γ).length ≤ (st ++ L).length := by simp; omega
  have hb2 : BelowP (st ++ L) d := fun l h => by
    rcases List.mem_append.1 h with h | h
    · exact hy.bst l h
    · exact hbL l h
  have hnp2 : ∀ l ∈ st ++ L, NP l.v := fun l h => by
    rcases List.mem_append.1 h with h | h
    · have := (hy.p8.2.2 l h).1; simp only [NP, vFh, vBump, vOk]; omega
    · exact (hLd l h).1.2.2.2
  intro s r E hr
  induction hr with
  | @ret s r ho =>
    intro hPs σ W hE hfl hfl01 hok1 hW hS
    obtain ⟨σ1, W1, e1, h1, w1, k1, o1⟩ := T.compP_ok st res fl rl w C ((arrsP Γ L c σ.env ++ X)) b (st ++ L)
      (Vals.app s c) σ d W (arrsP Δ st s σ.env) hE hb2 hy hlen hwf (hok s hPs) hW hok1 hS
      (wpre_of hwl hlen hS) (fun l h => List.mem_append_left _ h) hLw hnp2 hrl
    rw [ho] at o1
    obtain ⟨f1, ok1, hWW, ev1, rr1, hst1, hS1⟩ := o1
    subst hWW
    have hc : (Mach.BExp.bin .and (.var fl) (.var vOk)).denote σ1.env = 0 := by
      simp only [Mach.BExp.denote, Op.eval, f1]; simp
    have hc0 : (Mach.BExp.bin .and (.var fl) (.var vOk)).denote σ.env ≠ 0 := by
      simp only [Mach.BExp.denote, Op.eval, hok1]
      rcases hfl01 with h | h
      · exact absurd h hfl
      · rw [h]; decide
    have hpt1 : ∀ l ∈ st, σ1.env l.pt = σ.env l.pt := fun l hl => k1 _ (hy.bst l hl).2 (hy.ptn l hl).1
      (hy.ptn l hl).2.1 (hy.ptn l hl).2.2 (by have := (hy.p8.2.2 l hl).2; simp only [NP, vFh, vBump, vOk]; omega)
    have harr : arrsP Δ st s σ1.env = arrsP Δ st s σ.env := arrsP_congr hpt1 (by omega)
    refine ⟨σ1, _, .loopT hc0 e1 (.loopF hc), h1, w1, k1, .inl ⟨ok1, s, ?_, by rw [harr]; exact rr1,
      by rw [harr]; exact hS1, by rw [harr]; rfl, hS.count_le⟩⟩
    have := ((RelP.app hlen).1 hE.rel).1
    exact this.frame (fun l hl => hst1 _ (List.mem_map_of_mem hl)) h1 (by omega)
  | @call s s' r E ho hr' ih =>
    intro hPs σ W hE hfl hfl01 hok1 hW hS
    obtain ⟨σ1, W1, e1, h1, w1, k1, o1⟩ := T.compP_ok st res fl rl w C ((arrsP Γ L c σ.env ++ X)) b (st ++ L)
      (Vals.app s c) σ d W (arrsP Δ st s σ.env) hE hb2 hy hlen hwf (hok s hPs) hW hok1 hS
      (wpre_of hwl hlen hS) (fun l h => List.mem_append_left _ h) hLw hnp2 hrl
    rw [ho] at o1
    obtain ⟨f1, o1⟩ := o1
    have hc0 : (Mach.BExp.bin .and (.var fl) (.var vOk)).denote σ.env ≠ 0 := by
      simp only [Mach.BExp.denote, Op.eval, hok1]
      rcases hfl01 with h | h
      · exact absurd h hfl
      · rw [h]; decide
    -- the enclosing slots are untouched
    have hLk : ∀ l ∈ L, σ1.env l.v = σ.env l.v ∧ σ1.env l.pt = σ.env l.pt := fun l hl =>
      ⟨k1 _ (hbL l hl).1 (hLd l hl).1.1 (hLd l hl).1.2.1 (hLd l hl).1.2.2.1 (hLd l hl).1.2.2.2,
        k1 _ (hbL l hl).2 (hLd l hl).2.1 (hLd l hl).2.2.1 (hLd l hl).2.2.2.1 (hLd l hl).2.2.2.2⟩
    have hR0 : arrsP Γ L c σ1.env = arrsP Γ L c σ.env := arrsP_congr (fun l hl => (hLk l hl).2) hl
    rcases o1 with ⟨ok1, rel1, S1, fin1, pk1⟩ | ⟨ok1, pk1⟩
    · have hE1 : EnvOK (Δ ++ Γ) (st ++ L) (Vals.app s' c) σ1 := by
        refine ⟨(RelP.app hlen).2 ⟨rel1, ((RelP.app hlen).1 hE.rel).2.frame (fun l hl => (hLk l hl).1) h1 hl⟩,
          hl2, W1, w1, S1.1.wlen.2, ?_⟩
        unfold AllAt; rw [arrsP_append hlen, hR0]
        intro a ha; exact S1.2 a (by rw [← List.append_assoc]; exact List.mem_append_left _ ha)
      obtain ⟨σ2, W2, e2, h2, w2, k2, r2⟩ := ih (hP s s' hPs ho) σ1 W1 hE1 (by rw [f1]; exact hfl)
        (by rw [f1]; exact hfl01) ok1 w1 (by rw [hR0]; exact S1)
      refine ⟨σ2, W2, .loopT hc0 e1 e2, h2.trans h1, w2, fun j hj a1 a2 a3 a4 => by
        rw [k2 j hj a1 a2 a3 a4, k1 j hj a1 a2 a3 a4], ?_⟩
      rw [hR0] at r2
      rw [pk_append, finE_append, fin1]
      rcases r2 with ⟨o2, sf, r2a, r2b, r2c, r2d, r2e⟩ | ⟨o2, p2⟩
      · exact .inl ⟨o2, sf, r2a, r2b, r2c, r2d, Nat.max_le.2 ⟨pk1, r2e⟩⟩
      · exact .inr ⟨o2, Nat.lt_of_lt_of_le p2 (Nat.le_max_right _ _)⟩
    · have hc1 : (Mach.BExp.bin .and (.var fl) (.var vOk)).denote σ1.env = 0 := by
        simp only [Mach.BExp.denote, Op.eval, ok1]; simp
      exact ⟨σ1, W1, .loopT hc0 e1 (.loopF hc1), h1, w1, k1,
        .inr ⟨ok1, Nat.lt_of_lt_of_le pk1 (pk_mono_left _ _ _)⟩⟩

end Proven.WA
