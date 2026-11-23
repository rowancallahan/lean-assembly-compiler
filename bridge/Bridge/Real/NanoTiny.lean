/- Bridge.Real.NanoTiny: the tiny NANO program, nano side.

Source text `srcM` = "def m (x : List UInt8) : List UInt8 :=\n  put [] 1\n".  nano's emitter turns it into `oM`
(`#eval emitXs srcM`, Testing/denotes_real/CheckNano.lean; the emitter does not reduce in the kernel).  `ev_main`: the big-step meaning `Ev` of the emitted Expr `m x` (`mainX`,
the form `expr_rv` states the machine result in) is `[1]`, for every input. -/
import Bridge.Real.Tr
import Nano.Expr.Correct

namespace Bridge.Real.NanoTiny
open ExprSpec

def srcM : List UInt8 := "def m (x : List UInt8) : List UInt8 :=\n  put [] 1\n".toUTF8.toList

def LU8 : X := .app (.c "List" [0]) (.c "UInt8" [])
def nilX : X := .app (.c "List.nil" [0]) (.c "UInt8" [])
def oneX : X := apps (.c "OfNat.ofNat" [0]) [.c "UInt64" [], .nat 1, .app (.c "UInt64.instOfNat" []) (.nat 1)]
def bodyX : X := apps (.c "put" []) [nilX, oneX]
def oM : List (String × X × X) := [("m", .pi LU8 LU8, .lam LU8 bodyX)]


/-- `m`'s emitted Expr applied to the input: COPIED verbatim from `ExprSpec.mainX` (Nano/Expr/MachExpr.lean on
keep_round1_armfix, the term `expr_rv` states the machine result about); not on this branch. -/
abbrev mainX : X := .app (.c "m" []) (.bv 0)

/-! ## inverting `Ev` on the three emitted terms -/

theorem spine_apps : ∀ (f : X) (as : List X), spine (apps f as) = ((spine f).1, (spine f).2 ++ as)
  | f, [] => by simp [apps]
  | f, a :: as => by
    have := spine_apps (.app f a) as
    simp only [apps, List.foldl_cons] at this ⊢
    rw [this]; simp [spine]

theorem spine_c (n : String) (ls : List Nat) (as : List X) : spine (apps (.c n ls) as) = (.c n ls, as) := by
  rw [spine_apps]; simp [spine]

/-- equal spines with constant heads -/
theorem apps_c_inj {n n' : String} {ls ls' : List Nat} {as as' : List X}
    (h : apps (.c n ls) as = apps (.c n' ls') as') : n = n' ∧ ls = ls' ∧ as = as' := by
  have := congrArg spine h
  rw [spine_c, spine_c] at this
  simp only [Prod.mk.injEq, X.c.injEq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem nilX_eq : nilX = apps (.c "List.nil" [0]) [.c "UInt8" []] := rfl
theorem oneX_eq : oneX = apps (.c "OfNat.ofNat" [0]) [.c "UInt64" [], .nat 1, .app (.c "UInt64.instOfNat" []) (.nat 1)] := rfl

theorem ev_nil {P : Prog} {env : List V} {r : V} (h : Ev P env nilX r) : r = .l [] := by
  generalize he : nilX = e at h
  cases h with
  | nil => rfl
  | bv => cases he
  | lt => cases he
  | litU => rw [nilX_eq] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | litN => rw [nilX_eq] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | bin => rw [nilX_eq] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | iteT => rw [nilX_eq] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | iteF => rw [nilX_eq] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | mk => rw [nilX_eq] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | cases => rw [nilX_eq] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | natZ => rw [nilX_eq] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | natS => rw [nilX_eq] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | prim => rw [nilX_eq] at he; exact absurd (apps_c_inj he).2.1 (by simp)
  | call => rw [nilX_eq] at he; exact absurd (apps_c_inj he).2.1 (by simp)

theorem ev_one {P : Prog} {env : List V} {r : V} (h : Ev P env oneX r) : r = .w 1 := by
  generalize he : oneX = e at h
  cases h with
  | litU => rw [oneX_eq] at he; obtain ⟨-, -, h3⟩ := apps_c_inj he; simp at h3; obtain ⟨h31, -⟩ := h3; subst h31; rfl
  | nil => cases he
  | bv => cases he
  | lt => cases he
  | litN => rw [oneX_eq] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | bin => rw [oneX_eq] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | iteT => rw [oneX_eq] at he; exact absurd (apps_c_inj he).1 (by simp)
  | iteF => rw [oneX_eq] at he; exact absurd (apps_c_inj he).1 (by simp)
  | mk => rw [oneX_eq] at he; exact absurd (apps_c_inj he).1 (by simp)
  | cases => rw [oneX_eq] at he; exact absurd (apps_c_inj he).1 (by simp)
  | natZ => rw [oneX_eq] at he; exact absurd (apps_c_inj he).1 (by simp)
  | natS => rw [oneX_eq] at he; exact absurd (apps_c_inj he).1 (by simp)
  | prim => rw [oneX_eq] at he; exact absurd (apps_c_inj he).2.1 (by simp)
  | call => rw [oneX_eq] at he; exact absurd (apps_c_inj he).2.1 (by simp)

theorem evl_args {P : Prog} {env : List V} {vs : List V} (h : EvL P env [nilX, oneX] vs) :
    vs = [.l [], .w 1] := by
  cases h with
  | cons h1 h2 =>
    cases h2 with
    | cons h3 h4 => cases h4; rw [ev_nil h1, ev_one h3]

theorem ev_body {env : List V} {r : V} (h : Ev (progOf oM) env bodyX r) : r = .l [1] := by
  generalize he : bodyX = e at h
  cases h with
  | prim ha hp =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    rw [evl_args ha] at hp
    simp [prim] at hp; rw [← hp]
  | call ha hl =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have : ("put" == "m") = false := by decide
    simp [progOf, oM, List.lookup, this] at hl
  | nil => cases he
  | bv => cases he
  | lt => cases he
  | litU => exact absurd (apps_c_inj he).1 (by simp)
  | litN => exact absurd (apps_c_inj he).1 (by simp)
  | bin => exact absurd (apps_c_inj he).2.2 (by simp)
  | iteT => exact absurd (apps_c_inj he).1 (by simp)
  | iteF => exact absurd (apps_c_inj he).1 (by simp)
  | mk => exact absurd (apps_c_inj he).1 (by simp)
  | cases => exact absurd (apps_c_inj he).1 (by simp)
  | natZ => exact absurd (apps_c_inj he).1 (by simp)
  | natS => exact absurd (apps_c_inj he).1 (by simp)

/-- **The meaning of the emitted `m` on any input is `[1]`.** -/
theorem ev_main {inp : List UInt8} {r : V} (h : Ev (progOf oM) [.l inp] mainX r) : r = .l [1] := by
  generalize he : mainX = e at h
  have hm : mainX = apps (.c "m" []) [.bv 0] := rfl
  cases h with
  | call ha hl hs hb =>
    rw [hm] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    simp [progOf, oM] at hl; subst hl
    cases ha with
    | cons h1 h2 =>
      cases h2
      simp [strip] at hs; subst hs
      exact ev_body hb
  | prim ha hp =>
    rw [hm] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 => cases h2; simp [prim] at hp
  | nil => simp [mainX] at he
  | bv => cases he
  | lt => cases he
  | litU => rw [hm] at he; exact absurd (apps_c_inj he).1 (by simp)
  | litN => rw [hm] at he; exact absurd (apps_c_inj he).1 (by simp)
  | bin => rw [hm] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | iteT => rw [hm] at he; exact absurd (apps_c_inj he).1 (by simp)
  | iteF => rw [hm] at he; exact absurd (apps_c_inj he).1 (by simp)
  | mk => rw [hm] at he; exact absurd (apps_c_inj he).1 (by simp)
  | cases => rw [hm] at he; exact absurd (apps_c_inj he).1 (by simp)
  | natZ => rw [hm] at he; exact absurd (apps_c_inj he).1 (by simp)
  | natS => rw [hm] at he; exact absurd (apps_c_inj he).1 (by simp)

end Bridge.Real.NanoTiny
