/- Bridge.Real.NanoA: growth step `u64 ops`, nano side.
Source `srcA` = "def m (x : List UInt8) : List UInt8 :=\n  put [] (rd x 0 * 3 + 7)\n"; emitted `oA`
(`#eval`, CheckNano).  `ev_mainA`: on input `inp`, `Ev` gives `[outA inp]`, `outA inp = ((inp.getD 0 0).toUInt64 * 3 + 7).toUInt8`. -/
import Bridge.Real.NanoL

namespace Bridge.Real.NanoA
open ExprSpec Bridge.Real.NanoTiny Bridge.Real.NanoR Bridge.Real.NanoL

def srcA : List UInt8 := "def m (x : List UInt8) : List UInt8 :=\n  put [] (rd x 0 * 3 + 7)\n".toUTF8.toList
def instAddX : X := apps (.c "instHAdd" [0]) [ExprSpec.U, .c "instAddUInt64" []]
def instMulX : X := apps (.c "instHMul" [0]) [ExprSpec.U, .c "instMulUInt64" []]
def mulX : X := apps (.c "HMul.hMul" [0, 0, 0]) [ExprSpec.U, ExprSpec.U, ExprSpec.U, instMulX, rdX, litUX 3]
def addX : X := apps (.c "HAdd.hAdd" [0, 0, 0]) [ExprSpec.U, ExprSpec.U, ExprSpec.U, instAddX, mulX, litUX 7]
def bodyA : X := apps (.c "put" []) [nilX, addX]
def oA : List (String × X × X) := [("m", .pi LU8 LU8, .lam LU8 bodyA)]

def outA (inp : List UInt8) : UInt8 := ((inp.getD 0 0).toUInt64 * 3 + 7).toUInt8

/-- a six-argument spine at a level-polymorphic head can only be a `bin` -/
theorem ev_bin6 {P : Prog} {env : List V} {n : String} {ls : List Nat} (hls : ls ≠ []) {t1 t2 t3 i a b : X} {r : V}
    (h : Ev P env (apps (.c n ls) [t1, t2, t3, i, a, b]) r) :
    ∃ x y z, binV n x y = some z ∧ Ev P env a (.w x) ∧ Ev P env b (.w y) ∧ r = .w z := by
  generalize he : apps (.c n ls) [t1, t2, t3, i, a, b] = e at h
  cases h with
  | bin hb ha hc =>
    obtain ⟨rfl, -, h3⟩ := apps_c_inj he
    simp only [List.cons.injEq] at h3
    obtain ⟨-, -, -, -, rfl, rfl, -⟩ := h3
    exact ⟨_, _, _, hb, ha, hc, rfl⟩
  | prim => exact absurd (apps_c_inj he).2.1 hls
  | call => exact absurd (apps_c_inj he).2.1 hls
  | nil => cases he
  | bv => cases he
  | lt => cases he
  | litU => exact absurd (apps_c_inj he).2.2 (by simp)
  | litN => exact absurd (apps_c_inj he).2.2 (by simp)
  | iteT => exact absurd (apps_c_inj he).2.2 (by simp)
  | iteF => exact absurd (apps_c_inj he).2.2 (by simp)
  | mk => exact absurd (apps_c_inj he).2.2 (by simp)
  | cases => exact absurd (apps_c_inj he).2.2 (by simp)
  | natZ => exact absurd (apps_c_inj he).2.2 (by simp)
  | natS => exact absurd (apps_c_inj he).2.2 (by simp)

theorem lookup_rd : (progOf oA).lookup "rd" = none := by
  have : ("rd" == "m") = false := by decide
  simp [progOf, oA, List.lookup, this]

theorem ev_add {inp : List UInt8} {r : V} (h : Ev (progOf oA) [.l inp] addX r) :
    r = .w ((inp.getD 0 0).toUInt64 * 3 + 7) := by
  obtain ⟨x, y, z, hb, ha, hc, rfl⟩ := ev_bin6 (by simp) h
  obtain ⟨x', y', z', hb', ha', hc', hx⟩ := ev_bin6 (by simp) ha
  have e1 := ev_rdG lookup_rd ha'; have e2 := ev_litU 3 hc'; have e3 := ev_litU 7 hc
  simp only [V.w.injEq] at e1 e2 e3 hx; subst e1 e2 e3 hx
  simp [binV] at hb hb'; rw [← hb, ← hb']; rfl

theorem ev_bodyA {inp : List UInt8} {r : V} (h : Ev (progOf oA) [.l inp] bodyA r) : r = .l [outA inp] := by
  generalize he : bodyA = e at h
  have hk : bodyA = apps (.c "put" []) [nilX, addX] := rfl
  cases h with
  | prim ha hp =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 =>
      cases h2 with
      | cons h3 h4 =>
        cases h4
        rw [ev_nil h1, ev_add h3] at hp
        simp [prim] at hp; rw [← hp]; simp [outA]
  | call ha hl =>
    rw [hk] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have : ("put" == "m") = false := by decide
    simp [progOf, oA, List.lookup, this] at hl
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

theorem ev_mainA {inp : List UInt8} {r : V} (h : Ev (progOf oA) [.l inp] mainX r) : r = .l [outA inp] := by
  generalize he : mainX = e at h
  have hm : mainX = apps (.c "m" []) [.bv 0] := rfl
  cases h with
  | call ha hl hs hb =>
    rw [hm] at he; obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    simp [progOf, oA] at hl; subst hl
    cases ha with
    | cons h1 h2 =>
      cases h2
      rw [ev_bv0 h1] at hb
      simp [strip] at hs; subst hs
      exact ev_bodyA hb
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

theorem outA_toNat (inp : List UInt8) : (outA inp).toNat = ((inp.getD 0 0).toNat * 3 + 7) % 256 := by
  unfold outA
  generalize inp.getD 0 0 = b
  have hb := b.toNat_lt
  simp

end Bridge.Real.NanoA
