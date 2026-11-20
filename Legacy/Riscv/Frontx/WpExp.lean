/- Paged dynamic arrays (NOTES section 30), part 3: locations, the representation relation, expressions.

The source language is `WA` (`WaLang.lean`, unchanged).  A slot's location `PLoc`: its variable `v` (a scalar's
value, an array's size) and, for an array, either the input block (`inp`, bytes, read only) or a work array:
the variable `pt` holding its page table (`WpRep.lean`).  Every work array is owned by exactly one slot (views of
work arrays are copies), so the arrays of the store are the work-array slots' (`arrsP`).

`RelP` says only what the variables and the input block hold; the work arrays' elements are in the store
(`Store C env W (arrsP …)`).  An expression reads arrays only: `E.compP_ok` needs `AllAt` (every work array at
its page table) and changes no memory. -/
import Legacy.Riscv.Frontx.WpRep

namespace Proven.WA
open Proven Proven.WP
open Proven.Frontx (rN rN_toNat rN_lt rN_add rN_inj rB r8)

structure PLoc where
  v : Nat
  inp : Bool := false
  pt : Nat := 0
  deriving DecidableEq, Repr

instance : Inhabited PLoc := ⟨⟨0, false, 0⟩⟩

/-- the words of an array's elements -/
def words (k : AK) (a : k.T) : W64 := (List.range (AK.size k a)).map (AK.w k a)

theorem words_length (k : AK) (a : k.T) : (words k a).length = AK.size k a := by simp [words]

theorem words_get (k : AK) (a : k.T) {j : Nat} (h : j < AK.size k a) : (words k a)[j]? = some (AK.w k a j) := by
  simp [words, h]

/-- the input bytes `I` hold array `a` -/
def InpAt (I : List (BitVec 8)) (k : AK) (a : k.T) : Prop :=
  AK.size k a ≤ I.length ∧ ∀ j, j < AK.size k a → (I[j]?).map (·.setWidth 64) = some (AK.w k a j)

def SRP (σ : MSt) : (s : Sl) → PLoc → s.T → Prop
  | .sc t, l, x => σ.env l.v = t.rep x
  | .ar k, l, a => σ.env l.v = rN (AK.size k a) ∧ AK.size k a < 2 ^ 32 ∧
      (l.inp = true → InpAt (σ.heap.getD 0 []) k a) ∧ (l.inp = false → AK.size k a ≤ P * P)

def RelP : (Γ : List Sl) → List PLoc → Vals Γ → MSt → Prop
  | [], _, _, _ => True
  | s :: Γ, L, v, σ => SRP σ s (L.headD default) v.1 ∧ RelP Γ L.tail v.2 σ

/-- the work arrays of an environment: page table and words -/
def arrsP : (Γ : List Sl) → List PLoc → Vals Γ → Mach.BEnv → List (Nat × W64)
  | [], _, _, _ => []
  | .sc _ :: Γ, L, v, env => arrsP Γ L.tail v.2 env
  | .ar k :: Γ, L, v, env =>
    if (L.headD default).inp then arrsP Γ L.tail v.2 env
    else ((env (L.headD default).pt).toNat, words k v.1) :: arrsP Γ L.tail v.2 env

def Mem.locP {Γ : List Sl} {s : Sl} (m : Mem Γ s) (L : List PLoc) : PLoc := L.getD m.idx default

theorem RelP.get : ∀ {Γ : List Sl} {L : List PLoc} {v : Vals Γ} {σ : MSt} {s : Sl} (m : Mem Γ s),
    RelP Γ L v σ → SRP σ s (m.locP L) (m.get v)
  | _ :: _, L, _, _, _, .hd, h => by cases L <;> exact h.1
  | _ :: _, L, _, _, _, .tl m, h => by
    cases L with
    | nil => have := RelP.get m h.2; cases m <;> exact this
    | cons l L => exact RelP.get m h.2

theorem Mem.locP_tl {Γ : List Sl} {s s' : Sl} (m : Mem Γ s) (L : List PLoc) :
    (Mem.tl (s' := s') m).locP L = m.locP L.tail := by
  cases L <;> simp [Mem.locP, Mem.idx]

theorem Mem.locP_hd {Γ : List Sl} {s : Sl} (L : List PLoc) : (Mem.hd (s := s) (Γ := Γ)).locP L = L.headD default := by
  cases L <;> simp [Mem.locP, Mem.idx]

/-- a work array of the environment is one of the store's arrays -/
theorem arrsP_mem : ∀ {Γ : List Sl} {L : List PLoc} {v : Vals Γ} (env : Mach.BEnv) {k : AK}
    (m : Mem Γ (.ar k)), (m.locP L).inp = false →
    ((env (m.locP L).pt).toNat, words k (m.get v)) ∈ arrsP Γ L v env
  | _ :: _, L, _, env, _, .hd, h => by
    rw [Mem.locP_hd] at h ⊢; simp only [arrsP, h, Mem.get]; simp
  | .sc _ :: _, L, v, env, _, .tl m, h => by
    rw [Mem.locP_tl] at h ⊢; exact arrsP_mem (L := L.tail) (v := v.2) env m h
  | .ar _ :: _, L, v, env, _, .tl m, h => by
    rw [Mem.locP_tl] at h ⊢
    have := arrsP_mem (L := L.tail) (v := v.2) env m h
    simp only [arrsP]; split
    · exact this
    · exact List.mem_cons_of_mem _ this

/-- every work array of the environment is at its page table -/
def AllAt (W : W64) (Γ : List Sl) (L : List PLoc) (v : Vals Γ) (env : Mach.BEnv) : Prop :=
  ∀ a ∈ arrsP Γ L v env, ArrAt W a.1 a.2

theorem SRP.frame {σ σ' : MSt} {s : Sl} {l : PLoc} {x : s.T} (h : SRP σ s l x) (hv : σ'.env l.v = σ.env l.v)
    (hh : σ'.heap = σ.heap) : SRP σ' s l x := by
  cases s with
  | sc t => show σ'.env l.v = _; rw [hv]; exact h
  | ar k => obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨by rw [hv]; exact h1, h2, by rw [hh]; exact h3, h4⟩

theorem RelP.frame : ∀ {Γ : List Sl} {L : List PLoc} {v : Vals Γ} {σ σ' : MSt}, RelP Γ L v σ →
    (∀ l ∈ L, σ'.env l.v = σ.env l.v) → σ'.heap = σ.heap → Γ.length ≤ L.length → RelP Γ L v σ'
  | [], _, _, _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _, _, _, hl => by simp at hl
  | _ :: _, l :: L, _, _, _, h, hv, hh, hl =>
    ⟨SRP.frame h.1 (hv l (List.mem_cons_self ..)) hh,
      RelP.frame h.2 (fun l' h' => hv l' (List.mem_cons_of_mem _ h')) hh (by simp at hl ⊢; omega)⟩

/-- the arrays depend only on the page-table variables -/
theorem arrsP_congr : ∀ {Γ : List Sl} {L : List PLoc} {v : Vals Γ} {env env' : Mach.BEnv},
    (∀ l ∈ L, env' l.pt = env l.pt) → Γ.length ≤ L.length → arrsP Γ L v env' = arrsP Γ L v env
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _, hl => by simp at hl
  | .sc _ :: _, l :: L, _, _, _, h, hl => by
    simp only [arrsP, List.tail_cons]
    exact arrsP_congr (fun l' h' => h l' (List.mem_cons_of_mem _ h')) (by simp at hl ⊢; omega)
  | .ar _ :: _, l :: L, _, _, _, h, hl => by
    simp only [arrsP, List.tail_cons, List.headD_cons]
    rw [arrsP_congr (fun l' h' => h l' (List.mem_cons_of_mem _ h')) (by simp at hl ⊢; omega),
      h l (List.mem_cons_self ..)]

/-- the variables of the slots (sizes and page tables) are below `d` -/
def BelowP (L : List PLoc) (d : Nat) : Prop := ∀ l ∈ L, l.v < d ∧ l.pt < d

theorem BelowP.mono {L : List PLoc} {d d' : Nat} (h : BelowP L d) (h' : d ≤ d') : BelowP L d' :=
  fun l hl => ⟨Nat.lt_of_lt_of_le (h l hl).1 h', Nat.lt_of_lt_of_le (h l hl).2 h'⟩

theorem Mem.locP_mem {Γ : List Sl} {s : Sl} (m : Mem Γ s) (L : List PLoc) (hl : Γ.length ≤ L.length) :
    m.locP L ∈ L := by
  have := Mem.idx_lt m
  unfold Mem.locP
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m.idx < L.length by omega), Option.getD_some]
  exact List.getElem_mem _

/-- the state an expression runs in: the slots are represented, the work arrays at their page tables -/
structure EnvOK (Γ : List Sl) (L : List PLoc) (v : Vals Γ) (σ : MSt) : Prop where
  rel : RelP Γ L v σ
  len : Γ.length ≤ L.length
  at_ : ∃ W, σ.wheap = [W] ∧ W.length < 2 ^ 32 ∧ AllAt W Γ L v σ.env

theorem EnvOK.frame {Γ : List Sl} {L : List PLoc} {v : Vals Γ} {σ σ' : MSt} {d : Nat} (h : EnvOK Γ L v σ)
    (hb : BelowP L d) (he : ∀ j, j < d → σ'.env j = σ.env j) (hh : σ'.heap = σ.heap) (hw : σ'.wheap = σ.wheap) :
    EnvOK Γ L v σ' := by
  refine ⟨h.rel.frame (fun l hl => he _ (hb l hl).1) hh h.len, h.len, ?_⟩
  obtain ⟨W, h1, h2, h3⟩ := h.at_
  refine ⟨W, by rw [hw, h1], h2, ?_⟩
  unfold AllAt; rw [arrsP_congr (fun l hl => he _ (hb l hl).2) h.len]; exact h3

/-! ## Loads -/

/-- `d := a[var d]` (or `0` when out of range, `chk`) for an array at `l` (temporaries `d + 1 ..`) -/
def ldP (l : PLoc) (d : Nat) : MS := if l.inp then .load d 0 (.var d) else getEl l.pt d

def getCodeP (l : PLoc) (chk : Bool) (d : Nat) : MS :=
  if chk then
    .seq (.assign (d + 2) (.const 0)) (.seq (.assign (d + 1) (.bin .ult (.var d) (.var l.v)))
      (.seq (when (d + 1) (.seq (.assign (d + 2) (.var d)) (ldP l (d + 2)))) (.assign d (.var (d + 2)))))
  else ldP l d

/-- a load of element `i` in range: `d` gets the word, only `d` and `d + 1` change -/
theorem ldP_ok {Γ : List Sl} {L : List PLoc} {v : Vals Γ} {σ : MSt} {k : AK} (hE : EnvOK Γ L v σ)
    (m : Mem Γ (.ar k)) (d : Nat) (hb : BelowP L d) (i : Nat) (hd : σ.env d = rN i) (hi : i < AK.size k (m.get v)) :
    ∃ σ', Mach.BExec (ldP (m.locP L) d) σ σ' ∧ σ'.env d = AK.w k (m.get v) i ∧
      (∀ j, j ≠ d → j ≠ d + 1 → σ'.env j = σ.env j) ∧ σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap := by
  have hS := hE.rel.get m
  obtain ⟨hv, h32, hinp, hwk⟩ := hS
  have hm := hb _ (Mem.locP_mem m L hE.len)
  obtain ⟨W, hW, hW32, hall⟩ := hE.at_
  obtain ⟨env, Hp, Ws⟩ := σ
  simp only at hW hd hinp hall hv ⊢; subst hW
  unfold ldP
  split
  · rename_i hin
    obtain ⟨hl, hj⟩ := hinp hin
    have h := hj i hi
    cases Hp with
    | nil => simp at h
    | cons B Hs =>
      simp only [List.getD_cons_zero] at h
      have hiB : i < B.length := by
        rcases Nat.lt_or_ge i B.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at h; simp at h
      rw [List.getElem?_eq_getElem hiB] at h
      have e := Option.some.inj h
      have hdi : ((Mach.BExp.var d).denote env).toNat = i := by
        simp only [Mach.BExp.denote, hd]; exact rN_toNat (by omega)
      have := Mach.BExec.load (v := d) (b := 0) (i := .var d) (σ := ⟨env, B :: Hs, [W]⟩) (by simp)
        (by simp only [List.getElem_cons_zero, hdi]; exact hiB)
      simp only [List.getElem_cons_zero, hdi, e] at this
      exact ⟨_, this, set_eq, fun j h1 _ => set_ne h1, rfl, rfl⟩
  · rename_i hin
    have hin' : (m.locP L).inp = false := by simpa using hin
    have hA := hall _ (arrsP_mem env m hin')
    simp only at hA
    have hpt : env (m.locP L).pt = rN (env (m.locP L).pt).toNat := by simp [rN]
    have hsz : i < (words k (m.get v)).length := by rw [words_length]; exact hi
    obtain ⟨x, hx, e⟩ := getEl_ok hA Hp env (m.locP L).pt d ⟨by omega, by omega⟩ hpt i hd hsz hW32
    rw [words_get k _ hi] at hx
    refine ⟨_, e, by simp only [set_eq]; exact (Option.some.inj hx).symm, fun j h1 h2 => ?_, rfl, rfl⟩
    simp only [set_ne h1, set_ne h2]


/-! ## Expressions -/

theorem ERun.frameP {S : MS} {σ : MSt} {d : Nat} {x : BitVec 64} {Γ : List Sl} {L : List PLoc} {v : Vals Γ}
    (h : ERun S σ d x) (hR : EnvOK Γ L v σ) (hb : BelowP L d) (hl : Γ.length ≤ L.length) :
    ∃ σ', Mach.BExec S σ σ' ∧ σ'.env d = x ∧ (∀ j, j < d → σ'.env j = σ.env j) ∧ σ'.heap = σ.heap ∧
      σ'.wheap = σ.wheap ∧ EnvOK Γ L v σ' := by
  obtain ⟨σ', h1, h2, h3, h4, h5⟩ := h
  exact ⟨σ', h1, h2, h3, h4, h5, hR.frame hb h3 h4 h5⟩

theorem getCodeP_ok {Γ : List Sl} {L : List PLoc} {v : Vals Γ} {σ : MSt} {k : AK} (hE : EnvOK Γ L v σ)
    (m : Mem Γ (.ar k)) (chk : Bool) (d : Nat) (hb : BelowP L d) (i : Nat) (hd : σ.env d = rN i)
    (h64 : i < 2 ^ 64) (hin : chk = false → i < AK.size k (m.get v)) :
    ERun (getCodeP (m.locP L) chk d) σ d (AK.w k (m.get v) i) := by
  have hS := hE.rel.get m
  obtain ⟨hv, h32, -, -⟩ := hS
  have hm := hb _ (Mem.locP_mem m L hE.len)
  cases chk with
  | false =>
    obtain ⟨σ', e, h1, h2, h3, h4⟩ := ldP_ok hE m d hb i hd (hin rfl)
    exact ⟨σ', e, h1, fun j hj => h2 j (by omega) (by omega), h3, h4⟩
  | true =>
    simp only [getCodeP, if_true]
    let σ1 : MSt := ⟨σ.env.set (d + 2) 0, σ.heap, σ.wheap⟩
    let c := (Mach.BExp.bin .ult (.var d) (.var (m.locP L).v)).denote σ1.env
    let σ2 : MSt := ⟨σ1.env.set (d + 1) c, σ1.heap, σ1.wheap⟩
    have hc : c = if i < AK.size k (m.get v) then 1#64 else 0#64 := by
      simp only [c, σ1, Mach.BExp.denote, Op.eval, set_ne (show d ≠ d + 2 by omega),
        set_ne (show (m.locP L).v ≠ d + 2 by omega), hd, hv]
      simp only [rN_lt h64 (by omega : AK.size k (m.get v) < 2 ^ 64)]; rfl
    by_cases hi : i < AK.size k (m.get v)
    · have hc1 : σ2.env (d + 1) ≠ 0 := by simp only [σ2, set_eq, hc, if_pos hi]; decide
      let σ3 : MSt := ⟨σ2.env.set (d + 2) (σ2.env d), σ2.heap, σ2.wheap⟩
      have hd3 : σ3.env (d + 2) = rN i := by
        simp only [σ3, σ2, σ1, set_eq, set_ne (show d ≠ d + 1 by omega), set_ne (show d ≠ d + 2 by omega), hd]
      have hE3 : EnvOK Γ L v σ3 := hE.frame hb (fun j hj => by
        simp only [σ3, σ2, σ1, set_ne (show j ≠ d + 2 by omega), set_ne (show j ≠ d + 1 by omega)]) rfl rfl
      obtain ⟨σ4, e4, v4, k4, h4, w4⟩ := ldP_ok hE3 m (d + 2) (hb.mono (by omega)) i hd3 hi
      have hw := when_true hc1 (.seq (Mach.BExec.assign (v := d + 2) (e := .var d)) e4)
      refine ⟨_, .seq .assign (.seq .assign (.seq hw .assign)), ?_, ?_, ?_, ?_⟩
      · simp only [Mach.BExp.denote, set_eq, set_ne (show d + 2 ≠ d + 1 by omega)]; exact v4
      · intro j hj
        simp only [set_ne (show j ≠ d by omega), set_ne (show j ≠ d + 1 by omega)]
        rw [k4 j (by omega) (by omega)]
        simp only [σ3, σ2, σ1, set_ne (show j ≠ d + 2 by omega), set_ne (show j ≠ d + 1 by omega)]
      · exact h4
      · exact w4
    · have hc0 : σ2.env (d + 1) = 0 := by simp only [σ2, set_eq, hc, if_neg hi]; rfl
      refine ⟨_, .seq .assign (.seq .assign (.seq (when_false hc0) .assign)), ?_, ?_, rfl, rfl⟩
      · simp only [σ2, σ1, Mach.BExp.denote, set_eq, set_ne (show d + 2 ≠ d + 1 by omega)]
        rw [AK.w_oob k _ i (by omega)]
      · intro j hj
        simp only [σ2, σ1, set_ne (show j ≠ d by omega), set_ne (show j ≠ d + 1 by omega),
          set_ne (show j ≠ d + 2 by omega)]

/-- a pure expression as one machine expression (no loads, no `if`) -/
def E.toBP (L : List PLoc) {Γ : List Sl} : {t : Ty} → E Γ t → Option MB
  | _, .var m => some (.var (m.locP L).v)
  | t, .lit _ c => some (.const (t.rep c))
  | t, .bin o a b => if o.sup t && !o.isM then (match a.toBP L, b.toBP L with
      | some x, some y => some (mop o t x y) | _, _ => none) else none
  | _, @E.cmp _ t o a b => if o.sup t then (match a.toBP L, b.toBP L with
      | some x, some y => some (mcmp t o x y) | _, _ => none) else none
  | t, @E.cast _ s _ a => if cast.sup s t then (match a.toBP L with | some x => some (mcast s t x) | none => none)
      else none
  | _, .size m => some (.var (m.locP L).v)
  | _, _ => none

/-- `d := e` in one assignment when `e` is pure and shallow, else `S` -/
def pureOrP (L : List PLoc) {Γ : List Sl} {t : Ty} (e : E Γ t) (d : Nat) (S : MS) : MS :=
  match e.toBP L with
  | some b => if b.depth < 6 then .assign d b else S
  | none => S

def E.compP (L : List PLoc) {Γ : List Sl} : {t : Ty} → E Γ t → Nat → MS
  | _, .var m, d => .assign d (.var (m.locP L).v)
  | t, .lit _ c, d => .assign d (.const (t.rep c))
  | t, .bin o a b, d => pureOrP L (.bin o a b) d
    (.seq (a.compP L d) (.seq (b.compP L (d + 1)) (binS o t d)))
  | _, @E.cmp _ t o a b, d => pureOrP L (.cmp o a b) d
    (.seq (a.compP L d) (.seq (b.compP L (d + 1)) (.assign d (mcmp t o (.var d) (.var (d + 1))))))
  | t, @E.cast _ s _ a, d => pureOrP L (.cast t a) d (.seq (a.compP L d) (.assign d (mcast s t (.var d))))
  | _, .ite c a b, d =>
    .seq (c.compP L (d + 1)) (.seq (.assign (d + 2) (.bin .eq (.var (d + 1)) (.const 0)))
      (.seq (when (d + 1) (.seq (a.compP L (d + 3)) (.assign d (.var (d + 3)))))
        (when (d + 2) (.seq (b.compP L (d + 3)) (.assign d (.var (d + 3)))))))
  | _, .getA m i chk, d => .seq (i.compP L d) (getCodeP (m.locP L) chk d)
  | _, .getB m i chk, d => .seq (i.compP L d) (getCodeP (m.locP L) chk d)
  | _, .size m, d => .assign d (.var (m.locP L).v)

/-- static conditions: supported operations, byte arrays of the input read as bytes -/
def E.wfP (L : List PLoc) {Γ : List Sl} : {t : Ty} → E Γ t → Bool
  | _, .var _ | _, .lit _ _ | _, .size _ => true
  | t, .bin o a b => o.sup t && a.wfP L && b.wfP L
  | _, @E.cmp _ t o a b => o.sup t && a.wfP L && b.wfP L
  | t, @E.cast _ s _ a => cast.sup s t && a.wfP L
  | _, .ite c a b => c.wfP L && a.wfP L && b.wfP L
  | t, .getA m i _ => (!(m.locP L).inp || t == .u8) && i.wfP L
  | _, .getB _ i _ => i.wfP L

theorem E.toBP_ok (L : List PLoc) {Γ : List Sl} (v : Vals Γ) (σ : MSt) (hR : EnvOK Γ L v σ) :
    ∀ {t : Ty} (e : E Γ t) (b : MB), e.ok v → e.toBP L = some b → b.denote σ.env = t.rep (e.den v)
  | _, .var m, b, _, h => by
    simp only [E.toBP, Option.some.injEq] at h; subst h; exact hR.rel.get m
  | _, .lit _ c, b, _, h => by simp only [E.toBP, Option.some.injEq] at h; subst h; rfl
  | t, .bin o a c, b, hok, h => by
    simp only [E.ok] at hok
    simp only [E.toBP] at h
    split at h
    · rename_i hs
      split at h
      · rename_i x y hx hy
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
        exact mop_ok o t _ _ _ _ _ (E.toBP_ok L v σ hR a x hok.1 hx) (E.toBP_ok L v σ hR c y hok.2.1 hy) hs.1 hs.2
          hok.2.2.1 hok.2.2.2
      · cases h
    · cases h
  | _, @E.cmp _ t o a c, b, hok, h => by
    simp only [E.ok] at hok
    simp only [E.toBP] at h
    split at h
    · rename_i hs
      split at h
      · rename_i x y hx hy
        simp only [Option.some.injEq] at h; subst h
        exact mcmp_ok o t _ _ _ _ _ (E.toBP_ok L v σ hR a x hok.1 hx) (E.toBP_ok L v σ hR c y hok.2.1 hy) hs hok.2.2
      · cases h
    · cases h
  | t, @E.cast _ s _ a, b, hok, h => by
    simp only [E.ok] at hok
    simp only [E.toBP] at h
    split at h
    · rename_i hs
      split at h
      · rename_i x hx
        simp only [Option.some.injEq] at h; subst h
        exact mcast_ok s t _ _ _ (E.toBP_ok L v σ hR a x hok.1 hx) hs hok.2
      · cases h
    · cases h
  | _, .size m, b, _, h => by
    simp only [E.toBP, Option.some.injEq] at h; subst h; exact (hR.rel.get m).1
  | _, .ite _ _ _, _, _, h | _, .getA _ _ _, _, _, h | _, .getB _ _ _, _, _, h => by simp [E.toBP] at h

theorem pureOrP_ok (L : List PLoc) {Γ : List Sl} {t : Ty} (e : E Γ t) (v : Vals Γ) (σ : MSt) (d : Nat) (S : MS)
    (hR : EnvOK Γ L v σ) (hok : e.ok v) (hS : ERun S σ d (t.rep (e.den v))) :
    ERun (pureOrP L e d S) σ d (t.rep (e.den v)) := by
  unfold pureOrP
  split
  · rename_i b hb
    split
    · exact ⟨_, .assign, by simp only [set_eq]; exact E.toBP_ok L v σ hR e b hok hb, fun j hj => set_ne (by omega),
        rfl, rfl⟩
    · exact hS
  · exact hS

set_option maxHeartbeats 1000000 in
/-- **Expressions**: the code of `e` leaves the word of its value in `d`. -/
theorem E.compP_ok (L : List PLoc) : ∀ {Γ : List Sl} {t : Ty} (e : E Γ t) (v : Vals Γ) (σ : MSt) (d : Nat),
    EnvOK Γ L v σ → Γ.length ≤ L.length → BelowP L d → e.wfP L = true → e.ok v →
    ERun (e.compP L d) σ d (t.rep (e.den v))
  | _, _, .var m, v, σ, d, hR, hl, hb, _, _ => by
    simp only [E.compP, E.den]
    have hS := hR.rel.get m
    have hlt := (hb _ (Mem.locP_mem m L hl)).1
    exact ⟨_, .assign, by simp only [Mach.BExp.denote, set_eq]; exact hS, fun j hj => set_ne (by omega), rfl, rfl⟩
  | _, _, .lit _ c, v, σ, d, _, _, _, _, _ => by
    simp only [E.compP, E.den]
    exact ⟨_, .assign, by simp only [Mach.BExp.denote, set_eq]; try rfl, fun j hj => set_ne (by omega), rfl, rfl⟩
  | _, t, .bin o a b, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [E.compP]
    refine pureOrP_ok L (.bin o a b) v σ d _ hR hok ?_
    simp only [E.den]; simp only [E.ok] at hok
    simp only [E.wfP, Bool.and_eq_true] at hwf
    obtain ⟨⟨hs, hwa⟩, hwb⟩ := hwf
    obtain ⟨hoa, hob, hx, hsd⟩ := hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.compP_ok L a v σ d hR hl hb hwa hoa).frameP hR hb hl
    obtain ⟨σ2, e2, v2, k2, h2, w2, r2⟩ :=
      (E.compP_ok L b v σ1 (d + 1) r1 hl (hb.mono (by omega)) hwb hob).frameP r1 (hb.mono (by omega)) hl
    obtain ⟨σ3, e3, v3, k3, h3, w3⟩ := binS_ok o t d σ2 (by rw [k2 d (by omega), v1]) v2 hs hx hsd
    refine ⟨_, .seq e1 (.seq e2 e3), v3, fun j hj => ?_, h3.trans (h2.trans h1), w3.trans (w2.trans w1)⟩
    rw [k3 j hj, k2 j (by omega), k1 j hj]
  | _, _, @E.cmp _ t o a b, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [E.compP]
    refine pureOrP_ok L (.cmp o a b) v σ d _ hR hok ?_
    simp only [E.den]; simp only [E.ok] at hok
    simp only [E.wfP, Bool.and_eq_true] at hwf
    obtain ⟨⟨hs, hwa⟩, hwb⟩ := hwf
    obtain ⟨hoa, hob, hx⟩ := hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.compP_ok L a v σ d hR hl hb hwa hoa).frameP hR hb hl
    obtain ⟨σ2, e2, v2, k2, h2, w2, r2⟩ :=
      (E.compP_ok L b v σ1 (d + 1) r1 hl (hb.mono (by omega)) hwb hob).frameP r1 (hb.mono (by omega)) hl
    refine ⟨_, .seq e1 (.seq e2 .assign), ?_, fun j hj => ?_, h2.trans h1, w2.trans w1⟩
    · simp only [set_eq]
      exact mcmp_ok o t _ _ _ _ _ (by simp only [Mach.BExp.denote]; rw [k2 d (by omega), v1]) v2 hs hx
    · simp only [set_ne (show j ≠ d by omega)]; rw [k2 j (by omega), k1 j hj]
  | _, t, @E.cast _ s _ a, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [E.compP]
    refine pureOrP_ok L (.cast t a) v σ d _ hR hok ?_
    simp only [E.den]; simp only [E.ok] at hok
    simp only [E.wfP, Bool.and_eq_true] at hwf
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.compP_ok L a v σ d hR hl hb hwf.2 hok.1).frameP hR hb hl
    refine ⟨_, .seq e1 .assign, ?_, fun j hj => ?_, h1, w1⟩
    · simp only [set_eq]; exact mcast_ok s t _ _ _ (by simp only [Mach.BExp.denote]; exact v1) hwf.1 hok.2
    · simp only [set_ne (show j ≠ d by omega)]; rw [k1 j hj]
  | _, t, .ite c a b, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [E.compP, E.den]; simp only [E.ok] at hok
    simp only [E.wfP, Bool.and_eq_true] at hwf
    obtain ⟨⟨hwc, hwa⟩, hwb⟩ := hwf
    obtain ⟨hoc, hob⟩ := hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ :=
      (E.compP_ok L c v σ (d + 1) hR hl (hb.mono (by omega)) hwc hoc).frameP hR (hb.mono (by omega)) hl
    let σ2 : MSt := ⟨σ1.env.set (d + 2) ((Mach.BExp.bin .eq (.var (d + 1)) (.const 0)).denote σ1.env), σ1.heap,
      σ1.wheap⟩
    have r2 : EnvOK _ L v σ2 :=
      r1.frame (hb.mono (show d ≤ d + 2 by omega)) (fun j hj => set_ne (show j ≠ d + 2 by omega)) rfl rfl
    have e2 : Mach.BExec (.assign (d + 2) (.bin .eq (.var (d + 1)) (.const 0))) σ1 σ2 := .assign
    have hc1 : σ2.env (d + 1) = rB (c.den v) := by simp only [σ2, set_ne (show d + 1 ≠ d + 2 by omega)]; exact v1
    have hc2 : σ2.env (d + 2) = rB (!c.den v) := by
      simp only [σ2, set_eq, Mach.BExp.denote, Op.eval, v1]; cases c.den v <;> rfl
    cases hcv : c.den v with
    | true =>
      rw [hcv, if_pos rfl] at hob
      obtain ⟨σ3, e3, v3, k3, h3, w3, r3⟩ :=
        (E.compP_ok L a v σ2 (d + 3) r2 hl (hb.mono (by omega)) hwa hob).frameP r2 (hb.mono (by omega)) hl
      have hne : σ2.env (d + 1) ≠ 0 := by rw [hc1, hcv]; decide
      have hw1 := when_true hne (.seq e3 (.assign (v := d) (e := .var (d + 3))))
      let σ4 : MSt := ⟨(σ3.env.set d (σ3.env (d + 3))).set (d + 1) 0, σ3.heap, σ3.wheap⟩
      have hz : σ4.env (d + 2) = 0 := by
        simp only [σ4, set_ne (show d + 2 ≠ d + 1 by omega), set_ne (show d + 2 ≠ d by omega)]
        rw [k3 (d + 2) (by omega), hc2, hcv]; rfl
      refine ⟨σ4, .seq e1 (.seq e2 (.seq hw1 (when_false hz))), ?_, fun j hj => ?_, h3.trans h1, w3.trans w1⟩
      · simp only [σ4, set_ne (show d ≠ d + 1 by omega), set_eq, v3, if_true]
      · simp only [σ4, set_ne (show j ≠ d + 1 by omega), set_ne (show j ≠ d by omega), k3 j (by omega), σ2,
          set_ne (show j ≠ d + 2 by omega), k1 j (by omega)]
    | false =>
      rw [hcv] at hob; simp only [Bool.false_eq_true, if_false] at hob
      have hz : σ2.env (d + 1) = 0 := by rw [hc1, hcv]; rfl
      obtain ⟨σ3, e3, v3, k3, h3, w3, r3⟩ :=
        (E.compP_ok L b v σ2 (d + 3) r2 hl (hb.mono (by omega)) hwb hob).frameP r2 (hb.mono (by omega)) hl
      have hne : σ2.env (d + 2) ≠ 0 := by rw [hc2, hcv]; decide
      have hw2 := when_true hne (.seq e3 (.assign (v := d) (e := .var (d + 3))))
      refine ⟨_, .seq e1 (.seq e2 (.seq (when_false hz) hw2)), ?_, fun j hj => ?_, h3.trans h1, w3.trans w1⟩
      · simp only [set_ne (show d ≠ d + 2 by omega), set_eq, Mach.BExp.denote, v3, Bool.false_eq_true, if_false]
      · simp only [set_ne (show j ≠ d + 2 by omega), set_ne (show j ≠ d by omega), k3 j (by omega), σ2,
          k1 j (by omega)]
  | _, _, .getA m i chk, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [E.compP, E.den]; simp only [E.ok] at hok
    simp only [E.wfP, Bool.and_eq_true] at hwf
    obtain ⟨hoi, h64, hin⟩ := hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.compP_ok L i v σ d hR hl hb hwf.2 hoi).frameP hR hb hl
    obtain ⟨σ2, e2, v2, k2, h2, w2⟩ := getCodeP_ok r1 m chk d hb (i.den v) v1 h64 hin
    exact ⟨σ2, .seq e1 e2, v2, fun j hj => by rw [k2 j hj, k1 j hj], h2.trans h1, w2.trans w1⟩
  | _, _, .getB m i chk, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [E.compP, E.den]; simp only [E.ok] at hok
    simp only [E.wfP] at hwf
    obtain ⟨hoi, h64, hin⟩ := hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.compP_ok L i v σ d hR hl hb hwf hoi).frameP hR hb hl
    obtain ⟨σ2, e2, v2, k2, h2, w2⟩ := getCodeP_ok r1 m chk d hb (i.den v) v1 h64 hin
    exact ⟨σ2, .seq e1 e2, v2, fun j hj => by rw [k2 j hj, k1 j hj], h2.trans h1, w2.trans w1⟩
  | _, _, .size m, v, σ, d, hR, hl, hb, _, _ => by
    simp only [E.compP, E.den]
    have hS := (hR.rel.get m)
    have hlt := (hb _ (Mem.locP_mem m L hl)).1
    exact ⟨_, .assign, by simp only [Mach.BExp.denote, set_eq]; exact hS.1, fun j hj => set_ne (by omega), rfl, rfl⟩

end Proven.WA
