/- Bridge.Real.NanoC: growth step `calls`, nano side.
Source `srcC` = "def f (a : UInt64) : UInt64 :=\n  a + 1\ndef m (x : List UInt8) : List UInt8 :=\n  put [] (f (rd x 0) * 2)\n";
emitted `oC` (`#eval`, CheckNano).  `ev_mainC`: `Ev` gives `[outC inp]`,
`outC inp = (((inp.getD 0 0).toUInt64 + 1) * 2).toUInt8` — through nano's `call` rule into `f`'s emitted body. -/
import Bridge.Real.NanoA

namespace Bridge.Real.NanoC
open ExprSpec Bridge.Real.NanoTiny Bridge.Real.NanoR Bridge.Real.NanoL Bridge.Real.NanoA

def srcC : List UInt8 :=
  "def f (a : UInt64) : UInt64 :=\n  a + 1\ndef m (x : List UInt8) : List UInt8 :=\n  put [] (f (rd x 0) * 2)\n".toUTF8.toList
def fBodyX : X := apps (.c "HAdd.hAdd" [0, 0, 0]) [ExprSpec.U, ExprSpec.U, ExprSpec.U, instAddX, .bv 0, litUX 1]
def callX : X := apps (.c "f" []) [rdX]
def mulCX : X := apps (.c "HMul.hMul" [0, 0, 0]) [ExprSpec.U, ExprSpec.U, ExprSpec.U, instMulX, callX, litUX 2]
def bodyCX : X := apps (.c "put" []) [nilX, mulCX]
def oC : List (String × X × X) :=
  [("f", .pi ExprSpec.U ExprSpec.U, .lam ExprSpec.U fBodyX), ("m", .pi LU8 LU8, .lam LU8 bodyCX)]

def outC (inp : List UInt8) : UInt8 := (((inp.getD 0 0).toUInt64 + 1) * 2).toUInt8

theorem lookup_rd : (progOf oC).lookup "rd" = none := by
  have h1 : ("rd" == "f") = false := by decide
  have h2 : ("rd" == "m") = false := by decide
  simp [progOf, oC, List.lookup, h1, h2]

/-- the call: nano's `call` rule runs `f`'s emitted body at the argument -/
theorem ev_call {inp : List UInt8} {r : V} (h : Ev (progOf oC) [.l inp] callX r) :
    r = .w ((inp.getD 0 0).toUInt64 + 1) := by
  generalize he : callX = e at h
  have hk : callX = apps (.c "f" []) [rdX] := rfl
  cases h with
  | call ha hl hs hb =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    simp [progOf, oC, List.lookup] at hl; subst hl
    cases ha with
    | cons h1 h2 =>
      cases h2
      rw [ev_rdG lookup_rd h1] at hb
      simp [strip] at hs; subst hs
      obtain ⟨x, y, z, hbn, ha', hc, rfl⟩ := ev_bin6 (by simp) hb
      have e1 := ev_bv0 ha'; have e2 := ev_litU 1 hc
      simp only [V.w.injEq] at e1 e2; subst e1 e2
      simp [binV] at hbn; rw [← hbn]; rfl
  | prim ha hp =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 => cases h2; simp [prim] at hp
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

theorem ev_bodyC {inp : List UInt8} {r : V} (h : Ev (progOf oC) [.l inp] bodyCX r) : r = .l [outC inp] := by
  generalize he : bodyCX = e at h
  have hk : bodyCX = apps (.c "put" []) [nilX, mulCX] := rfl
  cases h with
  | prim ha hp =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 =>
      cases h2 with
      | cons h3 h4 =>
        cases h4
        obtain ⟨x, y, z, hb, ha', hc, rfl⟩ := ev_bin6 (by simp) h3
        have e1 := ev_call ha'; have e2 := ev_litU 2 hc
        simp only [V.w.injEq] at e1 e2; subst e1 e2
        simp [binV] at hb
        rw [ev_nil h1, ← hb] at hp
        simp [prim] at hp; rw [← hp]; simp [outC]
  | call ha hl =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have h1 : ("put" == "f") = false := by decide
    have h2 : ("put" == "m") = false := by decide
    simp [progOf, oC, List.lookup, h1, h2] at hl
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

theorem ev_mainC {inp : List UInt8} {r : V} (h : Ev (progOf oC) [.l inp] mainX r) : r = .l [outC inp] := by
  generalize he : mainX = e at h
  have hm : mainX = apps (.c "m" []) [.bv 0] := rfl
  cases h with
  | call ha hl hs hb =>
    rw [hm] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have h1 : ("m" == "f") = false := by decide
    simp [progOf, oC, List.lookup, h1] at hl; subst hl
    cases ha with
    | cons h1 h2 =>
      cases h2
      rw [ev_bv0 h1] at hb
      simp [strip] at hs; subst hs
      exact ev_bodyC hb
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

theorem outC_toNat (inp : List UInt8) : (outC inp).toNat = ((inp.getD 0 0).toNat + 1) * 2 % 256 := by
  unfold outC
  generalize inp.getD 0 0 = b
  have hb := b.toNat_lt
  simp

end Bridge.Real.NanoC
