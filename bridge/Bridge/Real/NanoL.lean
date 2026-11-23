/- Bridge.Real.NanoL: growth step `ite`, nano side.

Source `srcL` = "def m (x : List UInt8) : List UInt8 :=\n  put [] (if rd x 0 < 5 then 1 else 2)\n"; emitted `oL`
(`#eval`, Testing/denotes_real/CheckNano.lean).  `ev_mainL`: on input `inp`, `Ev` gives `[outL inp]`,
`outL inp = (if (inp.getD 0 0).toUInt64 < 5 then 1 else 2).toUInt8`. -/
import Bridge.Real.NanoR

namespace Bridge.Real.NanoL
open ExprSpec Bridge.Real.NanoTiny Bridge.Real.NanoR

def srcL : List UInt8 := "def m (x : List UInt8) : List UInt8 :=\n  put [] (if rd x 0 < 5 then 1 else 2)\n".toUTF8.toList

def U : X := .c "UInt64" []
def condX : X := apps (.c "LT.lt" [0]) [U, .c "instLTUInt64" [], rdX, litUX 5]
def decX : X := apps (.c "UInt64.decLt" []) [rdX, litUX 5]
def iteX' : X := apps (.c "ite" [1]) [U, condX, decX, litUX 1, litUX 2]
def bodyL : X := apps (.c "put" []) [nilX, iteX']
def oL : List (String × X × X) := [("m", .pi LU8 LU8, .lam LU8 bodyL)]

def outL (inp : List UInt8) : UInt8 := (if (inp.getD 0 0).toUInt64 < 5 then (1 : UInt64) else 2).toUInt8

/-- `rd x 0` on the input (any program not defining `rd`) -/
theorem ev_rdG {P : Prog} (hP : P.lookup "rd" = none) {inp : List UInt8} {r : V}
    (h : Ev P [.l inp] rdX r) : r = .w (inp.getD 0 0).toUInt64 := by
  generalize he : rdX = e at h
  have hk : rdX = apps (.c "rd" []) [.bv 0, litUX 0] := rfl
  cases h with
  | prim ha hp =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 =>
      cases h2 with
      | cons h3 h4 =>
        cases h4
        rw [ev_bv0 h1, ev_litU 0 h3] at hp
        simp [prim] at hp; rw [← hp]; rfl
  | call ha hl => rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he; rw [hP] at hl; cases hl
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

theorem evb_cond {P : Prog} (hP : P.lookup "rd" = none) {inp : List UInt8} {bb : Bool}
    (h : EvB P [.l inp] condX bb) : bb = decide ((inp.getD 0 0).toUInt64 < 5) := by
  generalize he : condX = e at h
  have hk : condX = apps (.c "LT.lt" [0]) [U, .c "instLTUInt64" [], rdX, litUX 5] := rfl
  cases h with
  | lt ha hb =>
    rw [hk] at he; obtain ⟨-, -, h3⟩ := apps_c_inj he
    simp only [List.cons.injEq] at h3
    obtain ⟨-, -, rfl, rfl, -⟩ := h3
    have e1 := ev_rdG hP ha; have e2 := ev_litU 5 hb
    simp only [V.w.injEq] at e1 e2; subst e1; subst e2; rfl
  | ltN ha hb =>
    rw [hk] at he; obtain ⟨-, -, h3⟩ := apps_c_inj he
    simp only [List.cons.injEq] at h3
    obtain ⟨-, -, rfl, rfl, -⟩ := h3
    have := ev_rdG hP ha; cases this
  | eq => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | eqN => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)

theorem ev_ite {P : Prog} (hP : P.lookup "rd" = none) {inp : List UInt8} {r : V}
    (h : Ev P [.l inp] iteX' r) : r = .w (if (inp.getD 0 0).toUInt64 < 5 then 1 else 2) := by
  generalize he : iteX' = e at h
  have hk : iteX' = apps (.c "ite" [1]) [U, condX, decX, litUX 1, litUX 2] := rfl
  cases h with
  | iteT hc ht =>
    rw [hk] at he; obtain ⟨-, -, h3⟩ := apps_c_inj he
    simp only [List.cons.injEq] at h3
    obtain ⟨-, rfl, -, rfl, -, -⟩ := h3
    have hb := evb_cond hP hc
    rw [ev_litU 1 ht]
    have : (inp.getD 0 0).toUInt64 < 5 := by simpa using hb.symm
    rw [if_pos this]; rfl
  | iteF hc ht =>
    rw [hk] at he; obtain ⟨-, -, h3⟩ := apps_c_inj he
    simp only [List.cons.injEq] at h3
    obtain ⟨-, rfl, -, -, rfl, -⟩ := h3
    have hb := evb_cond hP hc
    rw [ev_litU 2 ht]
    have : ¬ (inp.getD 0 0).toUInt64 < 5 := by simpa using hb.symm
    rw [if_neg this]; rfl
  | prim => rw [hk] at he; exact absurd (apps_c_inj he).2.1 (by simp)
  | call => rw [hk] at he; exact absurd (apps_c_inj he).2.1 (by simp)
  | nil => cases he
  | bv => cases he
  | lt => cases he
  | litU => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | litN => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | bin => rw [hk] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | mk => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | cases => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | natZ => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | natS => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)

theorem lookup_rd : (progOf oL).lookup "rd" = none := by
  have : ("rd" == "m") = false := by decide
  simp [progOf, oL, List.lookup, this]

theorem ev_bodyL {inp : List UInt8} {r : V} (h : Ev (progOf oL) [.l inp] bodyL r) : r = .l [outL inp] := by
  generalize he : bodyL = e at h
  have hk : bodyL = apps (.c "put" []) [nilX, iteX'] := rfl
  cases h with
  | prim ha hp =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 =>
      cases h2 with
      | cons h3 h4 =>
        cases h4
        rw [ev_nil h1, ev_ite lookup_rd h3] at hp
        simp [prim] at hp; rw [← hp]; simp [outL]
  | call ha hl =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have : ("put" == "m") = false := by decide
    simp [progOf, oL, List.lookup, this] at hl
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

/-- **The meaning of the emitted `m` on input `inp` is `[outL inp]`.** -/
theorem ev_mainL {inp : List UInt8} {r : V} (h : Ev (progOf oL) [.l inp] mainX r) : r = .l [outL inp] := by
  generalize he : mainX = e at h
  have hm : mainX = apps (.c "m" []) [.bv 0] := rfl
  cases h with
  | call ha hl hs hb =>
    rw [hm] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    simp [progOf, oL] at hl; subst hl
    cases ha with
    | cons h1 h2 =>
      cases h2
      rw [ev_bv0 h1] at hb
      simp [strip] at hs; subst hs
      exact ev_bodyL hb
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

end Bridge.Real.NanoL
