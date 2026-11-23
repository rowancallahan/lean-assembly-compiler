/- Bridge.Real.NanoLet: growth step `let`, nano side.
Source `srcT` = "def m (x : List UInt8) : List UInt8 := let y := rd x 0; put [] (y * 3 + y)\n"; emitted `oT`
(`#eval`, CheckNano): the body is nano's `.lt` (a `let`) over the `rd`.  `ev_mainT`: on input `inp`, `Ev` gives
`[outT inp]`, `outT inp = (y * 3 + y).toUInt8` with `y = (inp.getD 0 0).toUInt64`. -/
import Bridge.Real.NanoA

namespace Bridge.Real.NanoLet
open ExprSpec Bridge.Real.NanoTiny Bridge.Real.NanoR Bridge.Real.NanoL Bridge.Real.NanoA

def srcT : List UInt8 := "def m (x : List UInt8) : List UInt8 := let y := rd x 0; put [] (y * 3 + y)\n".toUTF8.toList
def mulT : X := apps (.c "HMul.hMul" [0, 0, 0]) [ExprSpec.U, ExprSpec.U, ExprSpec.U, instMulX, .bv 0, litUX 3]
def addT : X := apps (.c "HAdd.hAdd" [0, 0, 0]) [ExprSpec.U, ExprSpec.U, ExprSpec.U, instAddX, mulT, .bv 0]
def inT : X := apps (.c "put" []) [nilX, addT]
def bodyT : X := .lt true ExprSpec.U rdX inT
def oT : List (String × X × X) := [("m", .pi LU8 LU8, .lam LU8 bodyT)]

def outT (inp : List UInt8) : UInt8 := ((inp.getD 0 0).toUInt64 * 3 + (inp.getD 0 0).toUInt64).toUInt8

theorem apps_ne_lt {n : String} {ls : List Nat} {as : List X} {nd : Bool} {t v b : X} : apps (.c n ls) as ≠ .lt nd t v b := by
  intro h
  have := congrArg spine h
  rw [spine_c] at this; simp [spine] at this

theorem lookup_rd : (progOf oT).lookup "rd" = none := by
  have : ("rd" == "m") = false := by decide
  simp [progOf, oT, List.lookup, this]

theorem ev_addT {inp : List UInt8} {y : UInt64} {r : V} (h : Ev (progOf oT) [.w y, .l inp] addT r) :
    r = .w (y * 3 + y) := by
  obtain ⟨x, y1, z, hb, ha, hc, rfl⟩ := ev_bin6 (by simp) h
  obtain ⟨x', y', z', hb', ha', hc', hx⟩ := ev_bin6 (by simp) ha
  have e1 := ev_bv0 ha'; have e2 := ev_litU 3 hc'; have e3 := ev_bv0 hc
  simp only [V.w.injEq] at e1 e2 e3 hx; subst e1 e2 e3 hx
  simp [binV] at hb hb'; rw [← hb, ← hb']

theorem ev_inT {inp : List UInt8} {y : UInt64} {r : V} (h : Ev (progOf oT) [.w y, .l inp] inT r) :
    r = .l [(y * 3 + y).toUInt8] := by
  generalize he : inT = e at h
  have hk : inT = apps (.c "put" []) [nilX, addT] := rfl
  cases h with
  | prim ha hp =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 =>
      cases h2 with
      | cons h3 h4 =>
        cases h4
        rw [ev_nil h1, ev_addT h3] at hp
        simp [prim] at hp; rw [← hp]; simp
  | call ha hl =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have : ("put" == "m") = false := by decide
    simp [progOf, oT, List.lookup, this] at hl
  | nil => cases he
  | bv => cases he
  | lt => cases he
  | litU => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | litN => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | bin => rw [hk] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | iteT => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | iteF => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | mk => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | cases => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | natZ => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | natS => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)

theorem ev_bodyT {inp : List UInt8} {r : V} (h : Ev (progOf oT) [.l inp] bodyT r) : r = .l [outT inp] := by
  generalize he : bodyT = e at h
  cases h with
  | lt hv hb =>
    cases he
    rw [ev_rdG lookup_rd hv] at hb
    exact ev_inT hb
  | nil => cases he
  | bv => cases he
  | prim => exact absurd he.symm apps_ne_lt
  | call => exact absurd he.symm apps_ne_lt
  | litU => exact absurd he.symm apps_ne_lt
  | litN => exact absurd he.symm apps_ne_lt
  | bin => exact absurd he.symm apps_ne_lt
  | iteT => exact absurd he.symm apps_ne_lt
  | iteF => exact absurd he.symm apps_ne_lt
  | mk => exact absurd he.symm apps_ne_lt
  | cases => exact absurd he.symm apps_ne_lt
  | natZ => exact absurd he.symm apps_ne_lt
  | natS => exact absurd he.symm apps_ne_lt

theorem ev_mainT {inp : List UInt8} {r : V} (h : Ev (progOf oT) [.l inp] mainX r) : r = .l [outT inp] := by
  generalize he : mainX = e at h
  have hm : mainX = apps (.c "m" []) [.bv 0] := rfl
  cases h with
  | call ha hl hs hb =>
    rw [hm] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    simp [progOf, oT] at hl; subst hl
    cases ha with
    | cons h1 h2 =>
      cases h2
      rw [ev_bv0 h1] at hb
      simp [strip] at hs; subst hs
      exact ev_bodyT hb
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

theorem outT_toNat (inp : List UInt8) : (outT inp).toNat = ((inp.getD 0 0).toNat * 3 + (inp.getD 0 0).toNat) % 256 := by
  unfold outT
  generalize inp.getD 0 0 = b
  have hb := b.toNat_lt
  simp

end Bridge.Real.NanoLet
