/- Bridge.Real.NanoR: an INPUT-DEPENDENT nano program, nano side.

Source `srcR` = "def m (x : List UInt8) : List UInt8 :=\n  put [] (rd x 0 + 1)\n"; nano's emitter gives `oR`
(`#eval`, Testing/denotes_real/CheckNano.lean).  `ev_mainR`: the meaning `Ev` of the emitted `m` on input `inp`
is `[outR inp]`, `outR inp = ((inp.getD 0 0).toUInt64 + 1).toUInt8` (the first byte plus one, wrapping; `1` on
the empty input). -/
import Bridge.Real.NanoTiny

namespace Bridge.Real.NanoR
open ExprSpec Bridge.Real.NanoTiny

def srcR : List UInt8 := "def m (x : List UInt8) : List UInt8 :=\n  put [] (rd x 0 + 1)\n".toUTF8.toList

def litUX (k : Nat) : X := apps (.c "OfNat.ofNat" [0]) [.c "UInt64" [], .nat k, .app (.c "UInt64.instOfNat" []) (.nat k)]
def rdX : X := apps (.c "rd" []) [.bv 0, litUX 0]
def instX : X := apps (.c "instHAdd" [0]) [.c "UInt64" [], .c "instAddUInt64" []]
def plusX : X := apps (.c "HAdd.hAdd" [0, 0, 0]) [.c "UInt64" [], .c "UInt64" [], .c "UInt64" [], instX, rdX, litUX 1]
def bodyR : X := apps (.c "put" []) [nilX, plusX]
def oR : List (String × X × X) := [("m", .pi LU8 LU8, .lam LU8 bodyR)]

def outR (inp : List UInt8) : UInt8 := ((inp.getD 0 0).toUInt64 + 1).toUInt8

theorem apps_ne_bv {n : String} {ls : List Nat} {as : List X} {i : Nat} : apps (.c n ls) as ≠ .bv i := by
  intro h
  have := congrArg spine h
  rw [spine_c] at this; simp [spine] at this

theorem ev_bv0 {P : Prog} {v : V} {env : List V} {r : V} (h : Ev P (v :: env) (.bv 0) r) : r = v := by
  generalize he : X.bv 0 = e at h
  cases h with
  | bv h => cases he; simpa using h.symm
  | lt => cases he
  | nil => cases he
  | litU => exact absurd he.symm apps_ne_bv
  | litN => exact absurd he.symm apps_ne_bv
  | bin => exact absurd he.symm apps_ne_bv
  | iteT => exact absurd he.symm apps_ne_bv
  | iteF => exact absurd he.symm apps_ne_bv
  | mk => exact absurd he.symm apps_ne_bv
  | cases => exact absurd he.symm apps_ne_bv
  | natZ => exact absurd he.symm apps_ne_bv
  | natS => exact absurd he.symm apps_ne_bv
  | prim => exact absurd he.symm apps_ne_bv
  | call => exact absurd he.symm apps_ne_bv

theorem ev_litU {P : Prog} {env : List V} {r : V} (k : Nat) (h : Ev P env (litUX k) r) :
    r = .w (UInt64.ofNat k) := by
  generalize he : litUX k = e at h
  have hk : litUX k = apps (.c "OfNat.ofNat" [0]) [.c "UInt64" [], .nat k, .app (.c "UInt64.instOfNat" []) (.nat k)] := rfl
  cases h with
  | litU => rw [hk] at he; obtain ⟨-, -, h3⟩ := apps_c_inj he; simp at h3; obtain ⟨h31, -⟩ := h3; subst h31; rfl
  | nil => cases he
  | bv => cases he
  | lt => cases he
  | litN => rw [hk] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | bin => rw [hk] at he; exact absurd (apps_c_inj he).2.2 (by simp)
  | iteT => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | iteF => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | mk => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | cases => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | natZ => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | natS => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | prim => rw [hk] at he; exact absurd (apps_c_inj he).2.1 (by simp)
  | call => rw [hk] at he; exact absurd (apps_c_inj he).2.1 (by simp)

theorem ev_rd {inp : List UInt8} {r : V} (h : Ev (progOf oR) [.l inp] rdX r) :
    r = .w (inp.getD 0 0).toUInt64 := by
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
  | call ha hl =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have : ("rd" == "m") = false := by decide
    simp [progOf, oR, List.lookup, this] at hl
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

theorem ev_plus {inp : List UInt8} {r : V} (h : Ev (progOf oR) [.l inp] plusX r) :
    r = .w ((inp.getD 0 0).toUInt64 + 1) := by
  generalize he : plusX = e at h
  have hk : plusX = apps (.c "HAdd.hAdd" [0, 0, 0]) [.c "UInt64" [], .c "UInt64" [], .c "UInt64" [], instX, rdX, litUX 1] := rfl
  cases h with
  | bin hb ha hc =>
    rw [hk] at he; obtain ⟨rfl, -, h3⟩ := apps_c_inj he
    simp only [List.cons.injEq] at h3
    obtain ⟨-, -, -, -, rfl, rfl, -⟩ := h3
    have e1 := ev_rd ha; have e2 := ev_litU 1 hc
    simp only [V.w.injEq] at e1 e2; subst e1; subst e2
    simp [binV] at hb; rw [← hb]; rfl
  | prim => rw [hk] at he; exact absurd (apps_c_inj he).2.1 (by simp)
  | call => rw [hk] at he; exact absurd (apps_c_inj he).2.1 (by simp)
  | nil => cases he
  | bv => cases he
  | lt => cases he
  | litU => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | litN => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | iteT => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | iteF => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | mk => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | cases => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | natZ => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)
  | natS => rw [hk] at he; exact absurd (apps_c_inj he).1 (by simp)

theorem ev_bodyR {inp : List UInt8} {r : V} (h : Ev (progOf oR) [.l inp] bodyR r) : r = .l [outR inp] := by
  generalize he : bodyR = e at h
  have hk : bodyR = apps (.c "put" []) [nilX, plusX] := rfl
  cases h with
  | prim ha hp =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 =>
      cases h2 with
      | cons h3 h4 =>
        cases h4
        rw [ev_nil h1, ev_plus h3] at hp
        simp [prim] at hp; rw [← hp]; simp [outR]
  | call ha hl =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have : ("put" == "m") = false := by decide
    simp [progOf, oR, List.lookup, this] at hl
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

/-- **The meaning of the emitted `m` on input `inp` is `[outR inp]`.** -/
theorem ev_mainR {inp : List UInt8} {r : V} (h : Ev (progOf oR) [.l inp] mainX r) : r = .l [outR inp] := by
  generalize he : mainX = e at h
  have hm : mainX = apps (.c "m" []) [.bv 0] := rfl
  cases h with
  | call ha hl hs hb =>
    rw [hm] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    simp [progOf, oR] at hl; subst hl
    cases ha with
    | cons h1 h2 =>
      cases h2
      rw [ev_bv0 h1] at hb
      simp [strip] at hs; subst hs
      exact ev_bodyR hb
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

/-- the output byte, as a number -/
theorem outR_toNat (inp : List UInt8) :
    (outR inp).toNat = if (inp.getD 0 0).toNat < 255 then (inp.getD 0 0).toNat + 1 else 0 := by
  unfold outR
  generalize inp.getD 0 0 = b
  have hb := b.toNat_lt
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_add, UInt8.toNat_toUInt64]
  split <;> simp <;> omega

end Bridge.Real.NanoR
