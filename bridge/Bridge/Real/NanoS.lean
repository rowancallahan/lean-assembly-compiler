/- Bridge.Real.NanoS: growth step `-` (UInt64 subtraction), nano side.
Source `srcS` = "def m (x : List UInt8) : List UInt8 :=\n  put [] (rd x 0 - 3)\n"; emitted `oS` (`#eval`, CheckNano).
`ev_mainS`: on input `inp`, `Ev` gives `[outS inp]`, `outS inp = ((inp.getD 0 0).toUInt64 - 3).toUInt8`. -/
import Bridge.Real.NanoA

namespace Bridge.Real.NanoS
open ExprSpec Bridge.Real.NanoTiny Bridge.Real.NanoR Bridge.Real.NanoL Bridge.Real.NanoA (ev_bin6)

def srcS : List UInt8 := "def m (x : List UInt8) : List UInt8 :=\n  put [] (rd x 0 - 3)\n".toUTF8.toList
def instSubX : X := apps (.c "instHSub" [0]) [ExprSpec.U, .c "instSubUInt64" []]
def subX : X := apps (.c "HSub.hSub" [0, 0, 0]) [ExprSpec.U, ExprSpec.U, ExprSpec.U, instSubX, rdX, litUX 3]
def bodyS : X := apps (.c "put" []) [nilX, subX]
def oS : List (String × X × X) := [("m", .pi LU8 LU8, .lam LU8 bodyS)]

def outS (inp : List UInt8) : UInt8 := ((inp.getD 0 0).toUInt64 - 3).toUInt8

theorem lookup_rd : (progOf oS).lookup "rd" = none := by
  have : ("rd" == "m") = false := by decide
  simp [progOf, oS, List.lookup, this]

theorem ev_sub {inp : List UInt8} {r : V} (h : Ev (progOf oS) [.l inp] subX r) :
    r = .w ((inp.getD 0 0).toUInt64 - 3) := by
  obtain ⟨x, y, z, hb, ha, hc, rfl⟩ := ev_bin6 (by simp) h
  have e1 := ev_rdG lookup_rd ha; have e2 := ev_litU 3 hc
  simp only [V.w.injEq] at e1 e2; subst e1 e2
  simp [binV] at hb; rw [← hb]

theorem ev_bodyS {inp : List UInt8} {r : V} (h : Ev (progOf oS) [.l inp] bodyS r) : r = .l [outS inp] := by
  generalize he : bodyS = e at h
  have hk : bodyS = apps (.c "put" []) [nilX, subX] := rfl
  cases h with
  | prim ha hp =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 =>
      cases h2 with
      | cons h3 h4 =>
        cases h4
        rw [ev_nil h1, ev_sub h3] at hp
        simp [prim] at hp; rw [← hp]; simp [outS]
  | call ha hl =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have : ("put" == "m") = false := by decide
    simp [progOf, oS, List.lookup, this] at hl
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

theorem ev_mainS {inp : List UInt8} {r : V} (h : Ev (progOf oS) [.l inp] mainX r) : r = .l [outS inp] := by
  generalize he : mainX = e at h
  have hm : mainX = apps (.c "m" []) [.bv 0] := rfl
  cases h with
  | call ha hl hs hb =>
    rw [hm] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    simp [progOf, oS] at hl; subst hl
    cases ha with
    | cons h1 h2 =>
      cases h2
      rw [ev_bv0 h1] at hb
      simp [strip] at hs; subst hs
      exact ev_bodyS hb
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

theorem outS_toNat (inp : List UInt8) :
    (outS inp).toNat = ((inp.getD 0 0).toNat + (18446744073709551616 - 3)) % 256 := by
  unfold outS
  generalize inp.getD 0 0 = b
  have hb := b.toNat_lt
  simp [UInt64.toNat_sub]
  omega

end Bridge.Real.NanoS
