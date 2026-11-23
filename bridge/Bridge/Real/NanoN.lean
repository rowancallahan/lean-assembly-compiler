/- Bridge.Real.NanoN: growth step `len` (a prelude op recursing over the input), nano side.
Source `srcN` = "def m (x : List UInt8) : List UInt8 :=\n  put [] (len x)\n"; `ev_mainN`: `Ev` gives `[outN inp]`,
`outN inp = inp.length.toUInt64.toUInt8`. -/
import Bridge.Real.NanoC

namespace Bridge.Real.NanoN
open ExprSpec Bridge.Real.NanoTiny Bridge.Real.NanoR Bridge.Real.NanoL Bridge.Real.NanoA

def srcN : List UInt8 := "def m (x : List UInt8) : List UInt8 :=\n  put [] (len x)\n".toUTF8.toList
def lenX : X := apps (.c "len" []) [.bv 0]
def bodyNX : X := apps (.c "put" []) [nilX, lenX]
def oN : List (String × X × X) := [("m", .pi LU8 LU8, .lam LU8 bodyNX)]

def outN (inp : List UInt8) : UInt8 := inp.length.toUInt64.toUInt8

theorem ev_len {inp : List UInt8} {r : V} (h : Ev (progOf oN) [.l inp] lenX r) : r = .w inp.length.toUInt64 := by
  generalize he : lenX = e at h
  have hk : lenX = apps (.c "len" []) [.bv 0] := rfl
  cases h with
  | prim ha hp =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 => cases h2; rw [ev_bv0 h1] at hp; simp [prim] at hp; rw [← hp]
  | call ha hl =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have : ("len" == "m") = false := by decide
    simp [progOf, oN, List.lookup, this] at hl
  | nil => rw [hk] at he; simp [apps] at he
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

theorem ev_bodyN {inp : List UInt8} {r : V} (h : Ev (progOf oN) [.l inp] bodyNX r) : r = .l [outN inp] := by
  generalize he : bodyNX = e at h
  have hk : bodyNX = apps (.c "put" []) [nilX, lenX] := rfl
  cases h with
  | prim ha hp =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 =>
      cases h2 with
      | cons h3 h4 =>
        cases h4
        rw [ev_nil h1, ev_len h3] at hp
        simp [prim] at hp; rw [← hp]; simp [outN]
  | call ha hl =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have h2 : ("put" == "m") = false := by decide
    simp [progOf, oN, List.lookup, h2] at hl
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

theorem ev_mainN {inp : List UInt8} {r : V} (h : Ev (progOf oN) [.l inp] mainX r) : r = .l [outN inp] := by
  generalize he : mainX = e at h
  have hm : mainX = apps (.c "m" []) [.bv 0] := rfl
  cases h with
  | call ha hl hs hb =>
    rw [hm] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    simp [progOf, oN] at hl; subst hl
    cases ha with
    | cons h1 h2 =>
      cases h2
      rw [ev_bv0 h1] at hb
      simp [strip] at hs; subst hs
      exact ev_bodyN hb
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

theorem outN_toNat (inp : List UInt8) : (outN inp).toNat = inp.length % 256 := by
  unfold outN; simp

end Bridge.Real.NanoN
