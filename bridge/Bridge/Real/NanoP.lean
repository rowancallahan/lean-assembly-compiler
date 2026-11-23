/- Bridge.Real.NanoP: growth step `pairs`, nano side.
Source `srcP` = "def m (x : List UInt8) : List UInt8 := let (u, v) := (rd x 0, 3); put [] (u * v + u)\n"; emitted `oP`
(`#eval`, CheckNano): nano's `Prod.mk` and `Prod.casesOn` (two-binder λ minor).  `ev_mainP`: `Ev` gives
`[NanoLet.outT inp]` (the same value as the `let` step: `(y * 3 + y).toUInt8`, `y = (inp.getD 0 0).toUInt64`). -/
import Bridge.Real.NanoF
import Bridge.Real.NanoLet

namespace Bridge.Real.NanoP
open ExprSpec Bridge.Real.NanoTiny Bridge.Real.NanoR Bridge.Real.NanoL Bridge.Real.NanoA Bridge.Real.NanoF

def srcP : List UInt8 := "def m (x : List UInt8) : List UInt8 := let (u, v) := (rd x 0, 3); put [] (u * v + u)\n".toUTF8.toList

def mkX : X := apps (.c "Prod.mk" [0, 0]) [ExprSpec.U, ExprSpec.U, rdX, litUX 3]
def mulP : X := apps (.c "HMul.hMul" [0, 0, 0]) [ExprSpec.U, ExprSpec.U, ExprSpec.U, instMulX, .bv 1, .bv 0]
def addP : X := apps (.c "HAdd.hAdd" [0, 0, 0]) [ExprSpec.U, ExprSpec.U, ExprSpec.U, instAddX, mulP, .bv 1]
def inP : X := apps (.c "put" []) [nilX, addP]
def motP : X := .lam (.app (.app (.c "Prod" [0, 0]) ExprSpec.U) ExprSpec.U) LU8
def bodyP : X := apps (.c "Prod.casesOn" [1, 0, 0]) [ExprSpec.U, ExprSpec.U, motP, mkX, .lam ExprSpec.U (.lam ExprSpec.U inP)]
def oP : List (String × X × X) := [("m", .pi LU8 LU8, .lam LU8 bodyP)]

theorem lookup_rdP : (progOf oP).lookup "rd" = none := by
  have : ("rd" == "m") = false := by decide
  simp [progOf, oP, List.lookup, this]

theorem ev_mkP {inp : List UInt8} {r : V} (h : Ev (progOf oP) [.l inp] mkX r) :
    r = .p (.w (inp.getD 0 0).toUInt64) (.w 3) := by
  generalize he : mkX = e at h
  have hk : mkX = apps (.c "Prod.mk" [0, 0]) [ExprSpec.U, ExprSpec.U, rdX, litUX 3] := rfl
  rw [hk] at he
  cases h with
  | mk ha hb =>
    obtain ⟨-, -, h3⟩ := apps_c_inj he; simp only [List.cons.injEq] at h3
    obtain ⟨-, -, rfl, rfl, -⟩ := h3
    rw [ev_rdG lookup_rdP ha, ev_litU 3 hb]; rfl
  | _ => spine_absurd he

theorem ev_addP {inp : List UInt8} {y : UInt64} {r : V} (h : Ev (progOf oP) [.w 3, .w y, .l inp] addP r) :
    r = .w (y * 3 + y) := by
  obtain ⟨x, y1, z, hb, ha, hc, rfl⟩ := ev_bin6 (by simp) h
  obtain ⟨x', y', z', hb', ha', hc', hx⟩ := ev_bin6 (by simp) ha
  have e1 := ev_bv ha'; have e2 := ev_bv hc'; have e3 := ev_bv hc
  simp at e1 e2 e3 hx; subst e1 e2 e3 hx
  simp [binV] at hb hb'; rw [← hb, ← hb']

theorem ev_inP {inp : List UInt8} {y : UInt64} {r : V} (h : Ev (progOf oP) [.w 3, .w y, .l inp] inP r) :
    r = .l [(y * 3 + y).toUInt8] := by
  generalize he : inP = e at h
  have hk : inP = apps (.c "put" []) [nilX, addP] := rfl
  rw [hk] at he
  cases h with
  | prim ha hp =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 =>
      cases h2 with
      | cons h3 h4 =>
        cases h4
        rw [ev_nil h1, ev_addP h3] at hp
        simp [prim] at hp; rw [← hp]; simp
  | call ha hl =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have : ("put" == "m") = false := by decide
    simp [progOf, oP, List.lookup, this] at hl
  | _ => spine_absurd he

theorem ev_bodyP {inp : List UInt8} {r : V} (h : Ev (progOf oP) [.l inp] bodyP r) : r = .l [NanoLet.outT inp] := by
  generalize he : bodyP = e at h
  have hk : bodyP = apps (.c "Prod.casesOn" [1, 0, 0])
      [ExprSpec.U, ExprSpec.U, motP, mkX, .lam ExprSpec.U (.lam ExprSpec.U inP)] := rfl
  rw [hk] at he
  cases h with
  | cases hv hb =>
    obtain ⟨-, -, h3⟩ := apps_c_inj he; simp only [List.cons.injEq, X.lam.injEq, and_true] at h3
    obtain ⟨-, -, -, hv', -, -, hb'⟩ := h3
    subst hv' hb'
    have := ev_mkP hv; simp only [V.p.injEq] at this; obtain ⟨rfl, rfl⟩ := this
    rw [ev_inP hb]; rfl
  | _ => spine_absurd he

theorem ev_mainP {inp : List UInt8} {r : V} (h : Ev (progOf oP) [.l inp] mainX r) : r = .l [NanoLet.outT inp] := by
  generalize he : mainX = e at h
  have hm : mainX = apps (.c "m" []) [.bv 0] := rfl
  rw [hm] at he
  cases h with
  | call ha hl hs hb =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    simp [progOf, oP] at hl; subst hl
    cases ha with
    | cons h1 h2 =>
      cases h2
      rw [ev_bv0 h1] at hb
      simp [strip] at hs; subst hs
      exact ev_bodyP hb
  | prim ha hp =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 => cases h2; simp [prim] at hp
  | _ => spine_absurd he

end Bridge.Real.NanoP
