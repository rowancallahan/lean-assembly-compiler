/- Word arrays (NOTES section 20), compiler part 2: expressions to three-address statements and
`E.comp_ok` (the value lands in the target variable; nothing below it and no memory is written). -/
import Legacy.Riscv.Frontx.WaComp

namespace Proven.WA
open Proven Proven.Frontx

/-! ## At-most-once loops -/

/-- `while c { S; c := 0 }` -/
def when (c : Nat) (S : MS) : MS := .loop (.var c) (.seq S (.assign c (.const 0)))

theorem when_false {c : Nat} {S : MS} {σ : MSt} (h : σ.env c = 0) : Mach.BExec (when c S) σ σ := .loopF h

theorem when_true {c : Nat} {S : MS} {σ σ₁ : MSt} (h : σ.env c ≠ 0) (hS : Mach.BExec S σ σ₁) :
    Mach.BExec (when c S) σ ⟨σ₁.env.set c 0, σ₁.heap, σ₁.wheap⟩ :=
  .loopT h (.seq hS .assign) (.loopF (by simp [Mach.BEnv.set, Mach.BExp.denote]))

theorem set_ne {env : Mach.BEnv} {v j : Nat} {x : BitVec 64} (h : j ≠ v) : env.set v x j = env j := by
  simp [Mach.BEnv.set, h]
theorem set_eq {env : Mach.BEnv} {v : Nat} {x : BitVec 64} : env.set v x v = x := by simp [Mach.BEnv.set]

/-- a scalar's location (no memory) -/
def scLoc (v : Nat) : Loc := ⟨v, true, 0, none⟩

def skipAt (d : Nat) : MS := .assign d (.const 0)

/-! ## Loads -/

/-- `d := a[var d]` (or `0` when out of range, `chk`) for an array at `l` -/
def getCode (l : Loc) (chk : Bool) (d : Nat) : MS :=
  let ld (v : Nat) : MS := if l.inp then .load v 0 (.var d) else .load64 v 0 (.bin .add (.var d) (.const (BitVec.ofNat 64 l.off)))
  if chk then
    .seq (.assign (d + 2) (.const 0)) (.seq (.assign (d + 1) (.bin .ult (.var d) (.var l.v)))
      (.seq (when (d + 1) (ld (d + 2))) (.assign d (.var (d + 2)))))
  else ld d

/-! ## Multiply / divide / remainder: `BStmt.mop` -/

/-- `Int` `/` (`Int.ediv`): the machine's signed remainder (`d + 2`) and quotient (`d + 3`), adjusted when the
remainder is negative (`edivB`, `IntRep.lean`) -/
def iDivS (d : Nat) : MS :=
  .seq (.mop .rem (d + 2) (.var d) (.var (d + 1))) (.seq (.mop .div (d + 3) (.var d) (.var (d + 1)))
    (.assign d (.ite (.bin .slt (.var (d + 2)) (.const 0))
      (.ite (.bin .slt (.const 0) (.var (d + 1))) (.bin .sub (.var (d + 3)) (.const 1)) (.bin .add (.var (d + 3)) (.const 1)))
      (.ite (.bin .eq (.var (d + 1)) (.const 0)) (.const 0) (.var (d + 3))))))

/-- `Int` `%` (`Int.emod`): the signed remainder, plus `|d + 1|` when negative (`emodB`) -/
def iModS (d : Nat) : MS :=
  .seq (.mop .rem (d + 2) (.var d) (.var (d + 1)))
    (.assign d (.ite (.bin .slt (.var (d + 2)) (.const 0))
      (.ite (.bin .slt (.var (d + 1)) (.const 0)) (.bin .sub (.var (d + 2)) (.var (d + 1))) (.bin .add (.var (d + 2)) (.var (d + 1))))
      (.var (d + 2))))

/-- `d := d o (d + 1)` with the M extension (temporary `d + 2`): `*` then the type's mask; `/` guarded (the
machine's `divu` by zero is all ones, Lean's `/` is `0`); `%` unguarded (`remu` by zero is the dividend, as `%`) -/
def mStmt (o : Op2) (t : Ty) (d : Nat) : MS :=
  match o with
  | .div => if t = .int then iDivS d else .seq (.mop .divu (d + 2) (.var d) (.var (d + 1)))
      (.assign d (.ite (.bin .eq (.var (d + 1)) (.const 0)) (.const 0) (.var (d + 2))))
  | .mod => if t = .int then iModS d else .mop .remu d (.var d) (.var (d + 1))
  | _ => .seq (.mop .mul d (.var d) (.var (d + 1))) (.assign d (mkMask t (.var d)))

/-- `d := d o (d + 1)` -/
def binS (o : Op2) (t : Ty) (d : Nat) : MS :=
  if o.isM then mStmt o t d else .assign d (mop o t (.var d) (.var (d + 1)))

/-! ## The compiler -/

/-- a pure expression as one machine expression (no loads, no `if`) -/
def E.toB (L : List Loc) {Γ : List Sl} : {t : Ty} → E Γ t → Option MB
  | _, .var m => some (.var (m.loc L).v)
  | t, .lit _ c => some (.const (t.rep c))
  | t, .bin o a b => if o.sup t && !o.isM then (match a.toB L, b.toB L with
      | some x, some y => some (mop o t x y) | _, _ => none) else none
  | _, @E.cmp _ t o a b => if o.sup t then (match a.toB L, b.toB L with
      | some x, some y => some (mcmp t o x y) | _, _ => none) else none
  | t, @E.cast _ s _ a => if cast.sup s t then (match a.toB L with | some x => some (mcast s t x) | none => none)
      else none
  | _, .size m => some (.var (m.loc L).v)
  | _, _ => none

/-- `d := e` in one assignment when `e` is pure and shallow, else `S` -/
def pureOr (L : List Loc) {Γ : List Sl} {t : Ty} (e : E Γ t) (d : Nat) (S : MS) : MS :=
  match e.toB L with
  | some b => if b.depth < 6 then .assign d b else S
  | none => S

def E.comp (L : List Loc) {Γ : List Sl} : {t : Ty} → E Γ t → Nat → MS
  | _, .var m, d => .assign d (.var (m.loc L).v)
  | t, .lit _ c, d => .assign d (.const (t.rep c))
  | t, .bin o a b, d => pureOr L (.bin o a b) d
    (.seq (a.comp L d) (.seq (b.comp L (d + 1)) (binS o t d)))
  | _, @E.cmp _ t o a b, d => pureOr L (.cmp o a b) d
    (.seq (a.comp L d) (.seq (b.comp L (d + 1)) (.assign d (mcmp t o (.var d) (.var (d + 1))))))
  | t, @E.cast _ s _ a, d => pureOr L (.cast t a) d (.seq (a.comp L d) (.assign d (mcast s t (.var d))))
  | _, .ite c a b, d =>
    .seq (c.comp L (d + 1)) (.seq (.assign (d + 2) (.bin .eq (.var (d + 1)) (.const 0)))
      (.seq (when (d + 1) (.seq (a.comp L (d + 3)) (.assign d (.var (d + 3)))))
        (when (d + 2) (.seq (b.comp L (d + 3)) (.assign d (.var (d + 3)))))))
  | _, .getA m i chk, d => .seq (i.comp L d) (getCode (m.loc L) chk d)
  | _, .getB m i chk, d => .seq (i.comp L d) (getCode (m.loc L) chk d)
  | _, .size m, d => .assign d (.var (m.loc L).v)

/-- static conditions: supported operations, byte arrays of the input read as bytes -/
def E.wf (L : List Loc) {Γ : List Sl} : {t : Ty} → E Γ t → Bool
  | _, .var _ | _, .lit _ _ | _, .size _ => true
  | t, .bin o a b => o.sup t && a.wf L && b.wf L
  | _, @E.cmp _ t o a b => o.sup t && a.wf L && b.wf L
  | t, @E.cast _ s _ a => cast.sup s t && a.wf L
  | _, .ite c a b => c.wf L && a.wf L && b.wf L
  | t, .getA m i _ => (!(m.loc L).inp || t == .u8) && i.wf L
  | _, .getB _ i _ => i.wf L

/-- run-time conditions: exact `Nat` operands, in-range plain loads -/
def E.ok {Γ : List Sl} : {t : Ty} → E Γ t → Vals Γ → Prop
  | _, .var _, _ | _, .lit _ _, _ | _, .size _, _ => True
  | t, .bin o a b, v => a.ok v ∧ b.ok v ∧ (o.exact t = true → t.small (a.den v) ∧ t.small (b.den v)) ∧
      o.side t (a.den v) (b.den v)
  | _, @E.cmp _ t _ a b, v => a.ok v ∧ b.ok v ∧ t.small (a.den v) ∧ t.small (b.den v)
  | t, @E.cast _ s _ a, v => a.ok v ∧ cast.side s t (a.den v)
  | _, .ite c a b, v => c.ok v ∧ (if c.den v = true then a.ok v else b.ok v)
  | _, .getA m i chk, v => i.ok v ∧ @LT.lt Nat _ (i.den v) (2 ^ 64) ∧
      (chk = false → @LT.lt Nat _ (i.den v) (AK.size (.arr _) (m.get v)))
  | _, .getB m i chk, v => i.ok v ∧ @LT.lt Nat _ (i.den v) (2 ^ 64) ∧
      (chk = false → @LT.lt Nat _ (i.den v) (AK.size .ba (m.get v)))

/-! ## Correctness -/

/-- `S` leaves `x` in `d`, keeps the variables below `d` and the memory -/
def ERun (S : MS) (σ : MSt) (d : Nat) (x : BitVec 64) : Prop :=
  ∃ σ', Mach.BExec S σ σ' ∧ σ'.env d = x ∧ (∀ j, j < d → σ'.env j = σ.env j) ∧ σ'.heap = σ.heap ∧ σ'.wheap = σ.wheap

/-- the slot variables are below `d` -/
def Below (L : List Loc) (d : Nat) : Prop := ∀ l ∈ L, l.v < d

theorem Below.mono {L : List Loc} {d d' : Nat} (h : Below L d) (h' : d ≤ d') : Below L d' :=
  fun l hl => Nat.lt_of_lt_of_le (h l hl) h'

theorem Rel.below {Γ : List Sl} {L : List Loc} {v : Vals Γ} {σ σ' : MSt} {d : Nat} (hR : Rel Γ L v σ)
    (hb : Below L d) (hl : Γ.length ≤ L.length) (he : ∀ j, j < d → σ'.env j = σ.env j)
    (hh : σ'.heap = σ.heap) (hw : σ'.wheap = σ.wheap) : Rel Γ L v σ' :=
  Rel.frame hR (fun l hl' => he _ (hb l hl')) hh hw hl

theorem Mem.idx_lt : ∀ {Γ : List Sl} {s : Sl} (m : Mem Γ s), m.idx < Γ.length
  | _, _, .hd => by simp [Mem.idx]
  | _, _, .tl m => by have := Mem.idx_lt m; simp only [Mem.idx, List.length_cons]; omega

theorem Mem.loc_mem {Γ : List Sl} {s : Sl} (m : Mem Γ s) (L : List Loc) (hl : Γ.length ≤ L.length) :
    m.loc L ∈ L := by
  have := Mem.idx_lt m
  unfold Mem.loc
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m.idx < L.length by omega), Option.getD_some]
  exact List.getElem_mem _

/-- a load of element `i` of an array in range -/
theorem load_ok {k : AK} {l : Loc} {a : k.T} {σ : MSt} (hA : AR (σ.heap.getD 0 []) (σ.wheap.getD 0 []) k l a)
    (d v : Nat) (i : Nat) (hi : i < AK.size k a) (hd : σ.env d = rN i)
    (h64 : i < 2 ^ 64) :
    Mach.BExec (if l.inp then .load v 0 (.var d) else .load64 v 0 (.bin .add (.var d) (.const (BitVec.ofNat 64 l.off))))
      σ ⟨σ.env.set v (AK.w k a i), σ.heap, σ.wheap⟩ := by
  unfold AR at hA
  split
  · rename_i hin
    rw [if_pos hin] at hA
    obtain ⟨_, hj⟩ := hA
    have h := hj i hi
    cases hH : σ.heap with
    | nil => rw [hH] at h; simp at h
    | cons B H =>
      rw [hH] at h
      simp only [List.getD_cons_zero] at h
      have hiB : i < B.length := by
        rcases Nat.lt_or_ge i B.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at h; simp at h
      rw [List.getElem?_eq_getElem hiB] at h
      have e := Option.some.inj h
      have hdi : ((Mach.BExp.var d).denote σ.env).toNat = i := by
        simp only [Mach.BExp.denote, hd, rN, BitVec.toNat_ofNat]; omega
      have := Mach.BExec.load (v := v) (b := 0) (i := .var d) (σ := σ) (by rw [hH]; simp)
        (by simp only [hH, List.getElem_cons_zero, hdi]; exact hiB)
      simp only [hH, List.getElem_cons_zero, hdi, e] at this
      exact hH ▸ this
  · rename_i hin
    rw [if_neg hin] at hA
    obtain ⟨hoff, hW32, _, hj⟩ := hA
    have h := hj i hi
    cases hW : σ.wheap with
    | nil => rw [hW] at h; simp at h
    | cons W WS =>
      rw [hW] at h
      simp only [List.getD_cons_zero] at h
      have hiW : l.off + i < W.length := by
        rcases Nat.lt_or_ge (l.off + i) W.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at h; simp at h
      rw [List.getElem?_eq_getElem hiW] at h
      have e := Option.some.inj h
      rw [hW] at hW32; simp only [List.getD_cons_zero] at hW32
      have hdi : ((Mach.BExp.bin .add (.var d) (.const (BitVec.ofNat 64 l.off))).denote σ.env).toNat = l.off + i := by
        simp only [Mach.BExp.denote, Op.eval, hd, rN, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      have := Mach.BExec.load64 (v := v) (b := 0) (i := .bin .add (.var d) (.const (BitVec.ofNat 64 l.off))) (σ := σ)
        (by rw [hW]; simp) (by simp only [hW, List.getElem_cons_zero, hdi]; exact hiW)
      simp only [hW, List.getElem_cons_zero, hdi, e] at this
      exact hW ▸ this

theorem AK.w_oob : ∀ (k : AK) (a : k.T) (i : Nat), AK.size k a ≤ i → AK.w k a i = 0
  | .ba, a, i, h => by
    simp only [AK.w, AK.get, AK.el, Ty.rep]
    rw [getElem!_neg a i (by simp only [AK.size] at h; omega)]; rfl
  | .arr .u8, a, i, h | .arr .u16, a, i, h | .arr .u32, a, i, h | .arr .u64, a, i, h | .arr .nat, a, i, h
  | .arr .bool, a, i, h | .arr .int, a, i, h => by
    simp only [AK.w, AK.get, AK.el, Ty.rep]
    rw [getElem!_neg a i (by simp only [AK.size] at h; omega)]; rfl

theorem SR.ar {σ : MSt} {k : AK} {l : Loc} {a : k.T} (h : SR σ (.ar k) l a) :
    σ.env l.v = rN (AK.size k a) ∧ AK.size k a < 2 ^ 32 ∧ AR (σ.heap.getD 0 []) (σ.wheap.getD 0 []) k l a := h

/-- the load of `getCode`, in range or not -/
theorem getCode_ok {k : AK} {l : Loc} {a : k.T} {σ : MSt} (hS : SR σ (.ar k) l a) (chk : Bool) (d : Nat)
    (hl : l.v < d) (i : Nat) (hd : σ.env d = rN i) (h64 : i < 2 ^ 64) (hin : chk = false → i < AK.size k a) :
    ERun (getCode l chk d) σ d (AK.w k a i) := by
  obtain ⟨hv, h32, hA⟩ := hS.ar
  cases chk with
  | false =>
    exact ⟨_, load_ok hA d d i (hin rfl) hd h64, set_eq, fun j hj => set_ne (by omega), rfl, rfl⟩
  | true =>
    simp only [getCode, if_true]
    have hlt : (Mach.BExp.bin .ult (.var d) (.var l.v)).denote ((σ.env.set (d + 2) 0).set (d + 1) 0) = 0 ∨ True := .inr trivial
    clear hlt
    let σ1 : MSt := ⟨σ.env.set (d + 2) 0, σ.heap, σ.wheap⟩
    let c := (Mach.BExp.bin .ult (.var d) (.var l.v)).denote σ1.env
    let σ2 : MSt := ⟨σ1.env.set (d + 1) c, σ1.heap, σ1.wheap⟩
    have hc : c = if i < AK.size k a then 1#64 else 0#64 := by
      simp only [c, σ1, Mach.BExp.denote, Op.eval, set_ne (show d ≠ d + 2 by omega),
        set_ne (show l.v ≠ d + 2 by omega), hd, hv]
      simp only [rN_lt h64 (by omega : AK.size k a < 2 ^ 64)]; rfl
    by_cases hi : i < AK.size k a
    · have hc1 : σ2.env (d + 1) ≠ 0 := by simp only [σ2, set_eq, hc, if_pos hi]; decide
      have hd2 : σ2.env d = rN i := by
        simp only [σ2, σ1, set_ne (show d ≠ d + 1 by omega), set_ne (show d ≠ d + 2 by omega), hd]
      have hA2 : AR (σ2.heap.getD 0 []) (σ2.wheap.getD 0 []) k l a := hA
      have hw := when_true hc1 (load_ok hA2 d (d + 2) i hi hd2 h64)
      refine ⟨_, .seq .assign (.seq .assign (.seq hw .assign)), ?_, ?_, rfl, rfl⟩
      · simp only [Mach.BExp.denote, set_eq, set_ne (show d + 2 ≠ d + 1 by omega)]
      · intro j hj
        simp only [σ2, σ1, set_ne (show j ≠ d by omega), set_ne (show j ≠ d + 1 by omega),
          set_ne (show j ≠ d + 2 by omega)]
    · have hc0 : σ2.env (d + 1) = 0 := by simp only [σ2, set_eq, hc, if_neg hi]; rfl
      refine ⟨_, .seq .assign (.seq .assign (.seq (when_false hc0) .assign)), ?_, ?_, rfl, rfl⟩
      · simp only [σ2, σ1, Mach.BExp.denote, set_eq, set_ne (show d + 2 ≠ d + 1 by omega)]
        rw [AK.w_oob k a i (by omega)]
      · intro j hj
        simp only [σ2, σ1, set_ne (show j ≠ d by omega), set_ne (show j ≠ d + 1 by omega),
          set_ne (show j ≠ d + 2 by omega)]

theorem ERun.frame {S : MS} {σ : MSt} {d : Nat} {x : BitVec 64} {Γ : List Sl} {L : List Loc} {v : Vals Γ}
    (h : ERun S σ d x) (hR : Rel Γ L v σ) (hb : Below L d) (hl : Γ.length ≤ L.length) :
    ∃ σ', Mach.BExec S σ σ' ∧ σ'.env d = x ∧ (∀ j, j < d → σ'.env j = σ.env j) ∧ σ'.heap = σ.heap ∧
      σ'.wheap = σ.wheap ∧ Rel Γ L v σ' := by
  obtain ⟨σ', h1, h2, h3, h4, h5⟩ := h
  exact ⟨σ', h1, h2, h3, h4, h5, Rel.below hR hb hl h3 h4 h5⟩

theorem E.toB_ok (L : List Loc) {Γ : List Sl} (v : Vals Γ) (σ : MSt) (hR : Rel Γ L v σ) :
    ∀ {t : Ty} (e : E Γ t) (b : MB), e.ok v → e.toB L = some b → b.denote σ.env = t.rep (e.den v)
  | _, .var m, b, _, h => by
    simp only [E.toB, Option.some.injEq] at h; subst h; exact Rel.get m hR
  | _, .lit _ c, b, _, h => by simp only [E.toB, Option.some.injEq] at h; subst h; rfl
  | t, .bin o a c, b, hok, h => by
    simp only [E.ok] at hok
    simp only [E.toB] at h
    split at h
    · rename_i hs
      split at h
      · rename_i x y hx hy
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
        exact mop_ok o t _ _ _ _ _ (E.toB_ok L v σ hR a x hok.1 hx) (E.toB_ok L v σ hR c y hok.2.1 hy) hs.1 hs.2
          hok.2.2.1 hok.2.2.2
      · cases h
    · cases h
  | _, @E.cmp _ t o a c, b, hok, h => by
    simp only [E.ok] at hok
    simp only [E.toB] at h
    split at h
    · rename_i hs
      split at h
      · rename_i x y hx hy
        simp only [Option.some.injEq] at h; subst h
        exact mcmp_ok o t _ _ _ _ _ (E.toB_ok L v σ hR a x hok.1 hx) (E.toB_ok L v σ hR c y hok.2.1 hy) hs hok.2.2
      · cases h
    · cases h
  | t, @E.cast _ s _ a, b, hok, h => by
    simp only [E.ok] at hok
    simp only [E.toB] at h
    split at h
    · rename_i hs
      split at h
      · rename_i x hx
        simp only [Option.some.injEq] at h; subst h
        exact mcast_ok s t _ _ _ (E.toB_ok L v σ hR a x hok.1 hx) hs hok.2
      · cases h
    · cases h
  | _, .size m, b, _, h => by
    simp only [E.toB, Option.some.injEq] at h; subst h; exact (Rel.get m hR).ar.1
  | _, .ite _ _ _, _, _, h | _, .getA _ _ _, _, _, h | _, .getB _ _ _, _, _, h => by simp [E.toB] at h

theorem pureOr_ok (L : List Loc) {Γ : List Sl} {t : Ty} (e : E Γ t) (v : Vals Γ) (σ : MSt) (d : Nat) (S : MS)
    (hR : Rel Γ L v σ) (hok : e.ok v) (hS : ERun S σ d (t.rep (e.den v))) :
    ERun (pureOr L e d S) σ d (t.rep (e.den v)) := by
  unfold pureOr
  split
  · rename_i b hb
    split
    · exact ⟨_, .assign, by simp only [set_eq]; exact E.toB_ok L v σ hR e b hok hb, fun j hj => set_ne (by omega),
        rfl, rfl⟩
    · exact hS
  · exact hS

theorem divu_ne {X Y : BitVec 64} (h : Y ≠ 0) : Mach.MOp.eval .divu X Y = X / Y := by simp only [Mach.MOp.eval, if_neg h]


theorem r8_divM (x y : UInt8) : (if r8 y = 0 then 0 else if r8 y = 0 then BitVec.allOnes 64 else r8 x / r8 y) = r8 (x / y) := by
  by_cases h : r8 y = 0
  · have : y = 0 := UInt8.toNat_inj.1 (by have := congrArg BitVec.toNat h; rw [r8_nat] at this; simpa using this)
    subst this; rw [if_pos h]; simp [r8]
  · rw [if_neg h, if_neg h]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_udiv, r8_nat, r8_nat, r8_nat, UInt8.toNat_div]
theorem r8_modM (x y : UInt8) : r8 x % r8 y = r8 (x % y) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod, r8_nat, r8_nat, r8_nat, UInt8.toNat_mod]
theorem r16_divM (x y : UInt16) : (if r16 y = 0 then 0 else if r16 y = 0 then BitVec.allOnes 64 else r16 x / r16 y) = r16 (x / y) := by
  by_cases h : r16 y = 0
  · have : y = 0 := UInt16.toNat_inj.1 (by have := congrArg BitVec.toNat h; rw [r16_nat] at this; simpa using this)
    subst this; rw [if_pos h]; simp [r16]
  · rw [if_neg h, if_neg h]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_udiv, r16_nat, r16_nat, r16_nat, UInt16.toNat_div]
theorem r16_modM (x y : UInt16) : r16 x % r16 y = r16 (x % y) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod, r16_nat, r16_nat, r16_nat, UInt16.toNat_mod]
theorem r32_divM (x y : UInt32) : (if r32 y = 0 then 0 else if r32 y = 0 then BitVec.allOnes 64 else r32 x / r32 y) = r32 (x / y) := by
  by_cases h : r32 y = 0
  · have : y = 0 := UInt32.toNat_inj.1 (by have := congrArg BitVec.toNat h; rw [r32_nat] at this; simpa using this)
    subst this; rw [if_pos h]; simp [r32]
  · rw [if_neg h, if_neg h]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_udiv, r32_nat, r32_nat, r32_nat, UInt32.toNat_div]
theorem r32_modM (x y : UInt32) : r32 x % r32 y = r32 (x % y) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod, r32_nat, r32_nat, r32_nat, UInt32.toNat_mod]
theorem r64_divM (x y : UInt64) : (if r64 y = 0 then 0 else if r64 y = 0 then BitVec.allOnes 64 else r64 x / r64 y) = r64 (x / y) := by
  by_cases h : r64 y = 0
  · have : y = 0 := UInt64.toNat_inj.1 (by have := congrArg BitVec.toNat h; rw [r64_nat] at this; simpa using this)
    subst this; rw [if_pos h]; simp [r64]
  · rw [if_neg h, if_neg h]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_udiv, r64_nat, r64_nat, r64_nat, UInt64.toNat_div]
theorem r64_modM (x y : UInt64) : r64 x % r64 y = r64 (x % y) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod, r64_nat, r64_nat, r64_nat, UInt64.toNat_mod]
theorem rN_divM {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (if rN y = 0 then 0 else if rN y = 0 then BitVec.allOnes 64 else rN x / rN y) = rN (x / y) := by
  by_cases h : rN y = 0
  · have : y = 0 := by have := congrArg BitVec.toNat h; rw [rN_toNat hy] at this; simpa using this
    subst this; rw [if_pos h]; simp [rN]
  · rw [if_neg h, if_neg h]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, rN_toNat hx, rN_toNat hy, rN_toNat (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]
theorem rN_modM {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : rN x % rN y = rN (x % y) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, rN_toNat hx, rN_toNat hy, rN_toNat (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx)]

/-- the machine word of `x o y` from the words of `x` and `y`, as `mStmt` computes it -/
theorem mword_ok (o : Op2) (t : Ty) (x y : t.T) (hs : o.sup t = true) (hm : o.isM = true)
    (hx : o.exact t = true → t.small x ∧ t.small y) (hi : t = .int → o = .mul) :
    (match o with
      | .div => if t.rep y = 0 then 0 else Mach.MOp.eval .divu (t.rep x) (t.rep y)
      | .mod => Mach.MOp.eval .remu (t.rep x) (t.rep y)
      | _ => (match t.mask with | some m => Mach.MOp.eval .mul (t.rep x) (t.rep y) &&& m | none => Mach.MOp.eval .mul (t.rep x) (t.rep y)))
      = t.rep (o.den t x y) := by
  cases o <;> (try (exfalso; revert hm; decide)) <;> cases t <;> (try (exfalso; revert hs; decide)) <;>
    (try (exfalso; exact absurd (hi rfl) (by decide))) <;>
    simp only [Op2.exact, Ty.small, forall_const, true_implies] at hx <;>
    simp only [Ty.mask, Ty.rep, Op2.den, Mach.MOp.eval]
  · apply BitVec.eq_of_toNat_eq; rw [and_mask8, BitVec.toNat_mul, r8_nat, r8_nat, r8_nat, UInt8.toNat_mul,
      Nat.mod_mod_of_dvd _ (by decide)]
  · apply BitVec.eq_of_toNat_eq; rw [and_mask16, BitVec.toNat_mul, r16_nat, r16_nat, r16_nat, UInt16.toNat_mul,
      Nat.mod_mod_of_dvd _ (by decide)]
  · apply BitVec.eq_of_toNat_eq; rw [and_mask32, BitVec.toNat_mul, r32_nat, r32_nat, r32_nat, UInt32.toNat_mul,
      Nat.mod_mod_of_dvd _ (by decide)]
  · apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_mul, r64_nat, r64_nat, r64_nat, UInt64.toNat_mul]
  · apply BitVec.eq_of_toNat_eq; simp [rN, BitVec.toNat_mul, Nat.mul_mod]
  all_goals first
    | exact r8_divM x y | exact r16_divM x y | exact r32_divM x y | exact r64_divM x y
    | exact r8_modM x y | exact r16_modM x y | exact r32_modM x y | exact r64_modM x y
    | exact rN_divM hx.1 hx.2 | exact rN_modM hx.1 hx.2 | exact (rI_mul x y).symm

/-- **`binS`**: the word of `x o y` lands in `d` -/
theorem binS_ok (o : Op2) (t : Ty) (d : Nat) (σ : MSt) {x y : t.T} (ha : σ.env d = t.rep x)
    (hb : σ.env (d + 1) = t.rep y) (hs : o.sup t = true) (hx : o.exact t = true → t.small x ∧ t.small y)
    (hsd : o.side t x y) : ERun (binS o t d) σ d (t.rep (o.den t x y)) := by
  unfold binS
  cases hm : o.isM
  · rw [if_neg (by simp)]
    refine ⟨_, .assign, ?_, fun j hj => set_ne (by omega), rfl, rfl⟩
    dsimp only; rw [set_eq]; exact mop_ok o t _ _ _ _ _ (by simp only [Mach.BExp.denote]; exact ha)
      (by simp only [Mach.BExp.denote]; exact hb) hs hm hx hsd
  · rw [if_pos rfl]
    cases o <;> (try exact absurd hm (by decide))
    · -- mul
      have hw := mword_ok .mul t x y hs hm hx (fun _ => rfl)
      simp only [mStmt]
      refine ⟨_, .seq .mop .assign, ?_, fun j hj => ?_, rfl, rfl⟩
      · dsimp only; rw [set_eq, ← hw]
        simp only [Mach.BExp.denote, set_eq]
        unfold mkMask; split <;> simp_all [Mach.BExp.denote, Op.eval, set_eq]
      · dsimp only; rw [set_ne (show j ≠ d by omega), set_ne (show j ≠ d by omega)]
    · -- div
      by_cases ht : t = .int
      · subst ht
        have ⟨⟨x1, x2⟩, y1, y2⟩ := hx rfl
        simp only [mStmt, if_pos rfl, iDivS]
        refine ⟨_, .seq .mop (.seq .mop .assign), ?_, fun j hj => ?_, rfl, rfl⟩
        · dsimp only
          simp only [set_eq, Mach.BExp.denote, Op.eval, set_ne (show d ≠ d + 2 by omega), set_ne (show d ≠ d + 3 by omega),
            set_ne (show d + 1 ≠ d + 2 by omega), set_ne (show d + 1 ≠ d + 3 by omega),
            set_ne (show d + 2 ≠ d + 3 by omega), ha, hb, Op2.den, Ty.rep]
          rw [rI_ediv x1 x2 y1 y2]
          simp only [edivB, sdivH, sremH]
          by_cases h1 : (Mach.MOp.eval .rem (rI x) (rI y)).slt 0#64 = true <;>
            by_cases h2 : (0#64).slt (rI y) = true <;> by_cases h3 : rI y = 0#64 <;>
            first | exact absurd (h3 ▸ h2) (by decide) | (simp [h1, h2, h3]; done) |
              (simp [h1, h2, h3] <;> split <;> split <;> simp_all)
        · dsimp only
          rw [set_ne (show j ≠ d by omega), set_ne (show j ≠ d + 3 by omega), set_ne (show j ≠ d + 2 by omega)]
      have hw := mword_ok .div t x y hs hm hx (fun h => absurd h ht)
      simp only [mStmt, if_neg ht]
      refine ⟨_, .seq .mop .assign, ?_, fun j hj => ?_, rfl, rfl⟩
      · dsimp only; rw [set_eq, ← hw]
        simp only [Mach.BExp.denote, Op.eval, set_eq, set_ne (show d ≠ d + 2 by omega),
          set_ne (show d + 1 ≠ d + 2 by omega), ha, hb]
        by_cases h0 : t.rep y = 0 <;> simp [h0]
      · dsimp only; rw [set_ne (show j ≠ d by omega), set_ne (show j ≠ d + 2 by omega)]
    · -- mod
      by_cases ht : t = .int
      · subst ht
        have ⟨⟨x1, x2⟩, y1, y2⟩ := hx rfl
        simp only [mStmt, if_pos rfl, iModS]
        refine ⟨_, .seq .mop .assign, ?_, fun j hj => ?_, rfl, rfl⟩
        · dsimp only
          simp only [set_eq, Mach.BExp.denote, Op.eval, set_ne (show d ≠ d + 2 by omega),
            set_ne (show d + 1 ≠ d + 2 by omega), ha, hb, Op2.den, Ty.rep]
          rw [rI_emod x1 x2 y1 y2]
          simp only [emodB, sremH]
          by_cases h1 : (Mach.MOp.eval .rem (rI x) (rI y)).slt 0#64 = true <;>
            by_cases h2 : (rI y).slt 0#64 = true <;> simp [h1, h2]
        · dsimp only; rw [set_ne (show j ≠ d by omega), set_ne (show j ≠ d + 2 by omega)]
      have hw := mword_ok .mod t x y hs hm hx (fun h => absurd h ht)
      simp only [mStmt, if_neg ht]
      refine ⟨_, .mop, ?_, fun j hj => ?_, rfl, rfl⟩
      · dsimp only; rw [set_eq, ← hw]; simp only [Mach.BExp.denote, ha, hb]
      · dsimp only; rw [set_ne (show j ≠ d by omega)]

set_option maxHeartbeats 1000000 in
/-- **Expressions**: the code of `e` leaves the word of its value in `d`. -/
theorem E.comp_ok (L : List Loc) : ∀ {Γ : List Sl} {t : Ty} (e : E Γ t) (v : Vals Γ) (σ : MSt) (d : Nat),
    Rel Γ L v σ → Γ.length ≤ L.length → Below L d → e.wf L = true → e.ok v →
    ERun (e.comp L d) σ d (t.rep (e.den v))
  | _, _, .var m, v, σ, d, hR, hl, hb, _, _ => by
    simp only [E.comp, E.den]
    have hS := Rel.get m hR
    have hlt := hb _ (Mem.loc_mem m L hl)
    exact ⟨_, .assign, by simp only [Mach.BExp.denote, set_eq]; exact hS, fun j hj => set_ne (by omega), rfl, rfl⟩
  | _, _, .lit _ c, v, σ, d, _, _, _, _, _ => by
    simp only [E.comp, E.den]
    exact ⟨_, .assign, by simp only [Mach.BExp.denote, set_eq]; try rfl, fun j hj => set_ne (by omega), rfl, rfl⟩
  | _, t, .bin o a b, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [E.comp]
    refine pureOr_ok L (.bin o a b) v σ d _ hR hok ?_
    simp only [E.den]; simp only [E.ok] at hok
    simp only [E.wf, Bool.and_eq_true] at hwf
    obtain ⟨⟨hs, hwa⟩, hwb⟩ := hwf
    obtain ⟨hoa, hob, hx, hsd⟩ := hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.comp_ok L a v σ d hR hl hb hwa hoa).frame hR hb hl
    obtain ⟨σ2, e2, v2, k2, h2, w2, r2⟩ :=
      (E.comp_ok L b v σ1 (d + 1) r1 hl (hb.mono (by omega)) hwb hob).frame r1 (hb.mono (by omega)) hl
    obtain ⟨σ3, e3, v3, k3, h3, w3⟩ := binS_ok o t d σ2 (by rw [k2 d (by omega), v1]) v2 hs hx hsd
    refine ⟨_, .seq e1 (.seq e2 e3), v3, fun j hj => ?_, h3.trans (h2.trans h1), w3.trans (w2.trans w1)⟩
    rw [k3 j hj, k2 j (by omega), k1 j hj]
  | _, _, @E.cmp _ t o a b, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [E.comp]
    refine pureOr_ok L (.cmp o a b) v σ d _ hR hok ?_
    simp only [E.den]; simp only [E.ok] at hok
    simp only [E.wf, Bool.and_eq_true] at hwf
    obtain ⟨⟨hs, hwa⟩, hwb⟩ := hwf
    obtain ⟨hoa, hob, hx⟩ := hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.comp_ok L a v σ d hR hl hb hwa hoa).frame hR hb hl
    obtain ⟨σ2, e2, v2, k2, h2, w2, r2⟩ :=
      (E.comp_ok L b v σ1 (d + 1) r1 hl (hb.mono (by omega)) hwb hob).frame r1 (hb.mono (by omega)) hl
    refine ⟨_, .seq e1 (.seq e2 .assign), ?_, fun j hj => ?_, h2.trans h1, w2.trans w1⟩
    · simp only [set_eq]
      exact mcmp_ok o t _ _ _ _ _ (by simp only [Mach.BExp.denote]; rw [k2 d (by omega), v1]) v2 hs hx
    · simp only [set_ne (show j ≠ d by omega)]; rw [k2 j (by omega), k1 j hj]
  | _, t, @E.cast _ s _ a, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [E.comp]
    refine pureOr_ok L (.cast t a) v σ d _ hR hok ?_
    simp only [E.den]; simp only [E.ok] at hok
    simp only [E.wf, Bool.and_eq_true] at hwf
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.comp_ok L a v σ d hR hl hb hwf.2 hok.1).frame hR hb hl
    refine ⟨_, .seq e1 .assign, ?_, fun j hj => ?_, h1, w1⟩
    · simp only [set_eq]; exact mcast_ok s t _ _ _ (by simp only [Mach.BExp.denote]; exact v1) hwf.1 hok.2
    · simp only [set_ne (show j ≠ d by omega)]; rw [k1 j hj]
  | _, t, .ite c a b, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [E.comp, E.den]; simp only [E.ok] at hok
    simp only [E.wf, Bool.and_eq_true] at hwf
    obtain ⟨⟨hwc, hwa⟩, hwb⟩ := hwf
    obtain ⟨hoc, hob⟩ := hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ :=
      (E.comp_ok L c v σ (d + 1) hR hl (hb.mono (by omega)) hwc hoc).frame hR (hb.mono (by omega)) hl
    let σ2 : MSt := ⟨σ1.env.set (d + 2) ((Mach.BExp.bin .eq (.var (d + 1)) (.const 0)).denote σ1.env), σ1.heap,
      σ1.wheap⟩
    have r2 : Rel _ L v σ2 :=
      Rel.below r1 (hb.mono (show d ≤ d + 2 by omega)) hl (fun j hj => set_ne (show j ≠ d + 2 by omega)) rfl rfl
    have e2 : Mach.BExec (.assign (d + 2) (.bin .eq (.var (d + 1)) (.const 0))) σ1 σ2 := .assign
    have hc1 : σ2.env (d + 1) = rB (c.den v) := by simp only [σ2, set_ne (show d + 1 ≠ d + 2 by omega)]; exact v1
    have hc2 : σ2.env (d + 2) = rB (!c.den v) := by
      simp only [σ2, set_eq, Mach.BExp.denote, Op.eval, v1]; cases c.den v <;> rfl
    cases hcv : c.den v with
    | true =>
      rw [hcv, if_pos rfl] at hob
      obtain ⟨σ3, e3, v3, k3, h3, w3, r3⟩ :=
        (E.comp_ok L a v σ2 (d + 3) r2 hl (hb.mono (by omega)) hwa hob).frame r2 (hb.mono (by omega)) hl
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
        (E.comp_ok L b v σ2 (d + 3) r2 hl (hb.mono (by omega)) hwb hob).frame r2 (hb.mono (by omega)) hl
      have hne : σ2.env (d + 2) ≠ 0 := by rw [hc2, hcv]; decide
      have hw2 := when_true hne (.seq e3 (.assign (v := d) (e := .var (d + 3))))
      refine ⟨_, .seq e1 (.seq e2 (.seq (when_false hz) hw2)), ?_, fun j hj => ?_, h3.trans h1, w3.trans w1⟩
      · simp only [set_ne (show d ≠ d + 2 by omega), set_eq, Mach.BExp.denote, v3, Bool.false_eq_true, if_false]
      · simp only [set_ne (show j ≠ d + 2 by omega), set_ne (show j ≠ d by omega), k3 j (by omega), σ2,
          k1 j (by omega)]
  | _, _, .getA m i chk, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [E.comp, E.den]; simp only [E.ok] at hok
    simp only [E.wf, Bool.and_eq_true] at hwf
    obtain ⟨hoi, h64, hin⟩ := hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.comp_ok L i v σ d hR hl hb hwf.2 hoi).frame hR hb hl
    obtain ⟨σ2, e2, v2, k2, h2, w2⟩ := getCode_ok (Rel.get m r1) chk d (hb _ (Mem.loc_mem m L hl)) (i.den v) v1 h64 hin
    exact ⟨σ2, .seq e1 e2, v2, fun j hj => by rw [k2 j hj, k1 j hj], h2.trans h1, w2.trans w1⟩
  | _, _, .getB m i chk, v, σ, d, hR, hl, hb, hwf, hok => by
    simp only [E.comp, E.den]; simp only [E.ok] at hok
    simp only [E.wf] at hwf
    obtain ⟨hoi, h64, hin⟩ := hok
    obtain ⟨σ1, e1, v1, k1, h1, w1, r1⟩ := (E.comp_ok L i v σ d hR hl hb hwf hoi).frame hR hb hl
    obtain ⟨σ2, e2, v2, k2, h2, w2⟩ := getCode_ok (Rel.get m r1) chk d (hb _ (Mem.loc_mem m L hl)) (i.den v) v1 h64 hin
    exact ⟨σ2, .seq e1 e2, v2, fun j hj => by rw [k2 j hj, k1 j hj], h2.trans h1, w2.trans w1⟩
  | _, _, .size m, v, σ, d, hR, hl, hb, _, _ => by
    simp only [E.comp, E.den]
    have hS := (Rel.get m hR).ar
    have hlt := hb _ (Mem.loc_mem m L hl)
    exact ⟨_, .assign, by simp only [Mach.BExp.denote, set_eq]; exact hS.1, fun j hj => set_ne (by omega), rfl, rfl⟩

end Proven.WA
