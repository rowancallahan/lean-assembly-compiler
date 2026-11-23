/- Bridge.Real.NanoF: growth step `fuel loop`, nano side.
Source `srcF` (below): a structural fuel loop `lp` (nano's `Nat.casesOn` with the fuel as discriminant) and
`def m (x : List UInt8) : List UInt8 := put [] (lp 3 x (rd x 0))`; emitted `oF` (`#eval`, CheckNano).
`ev_lp`: by induction on the fuel, `lp k x a` evaluates to `a + k`; `ev_mainF`: `Ev` gives `[outF inp]`. -/
import Bridge.Real.NanoA

namespace Bridge.Real.NanoF
open ExprSpec Bridge.Real.NanoTiny Bridge.Real.NanoR Bridge.Real.NanoL Bridge.Real.NanoA

def srcF : List UInt8 := ("def lp : Nat → List UInt8 → UInt64 → UInt64\n  | 0, x, a => a\n  | n + 1, x, a => lp n x (a + 1)\n" ++
  "def m (x : List UInt8) : List UInt8 := put [] (lp 3 x (rd x 0))\n").toUTF8.toList

def NX : X := .c "Nat" []
def litNX (k : Nat) : X := apps (.c "OfNat.ofNat" [0]) [NX, .nat k, .app (.c "instOfNatNat" []) (.nat k)]
def addS : X := apps (.c "HAdd.hAdd" [0, 0, 0]) [ExprSpec.U, ExprSpec.U, ExprSpec.U, instAddX, .bv 1, litUX 1]
def stepX : X := apps (.c "lp" []) [.bv 0, .bv 2, addS]
def lpBody : X := apps (.c "Nat.casesOn" [1]) [.lam NX ExprSpec.U, .bv 2, .bv 0, .lam NX stepX]
def lpTy : X := .pi NX (.pi LU8 (.pi ExprSpec.U ExprSpec.U))
def lpVal : X := .lam NX (.lam LU8 (.lam ExprSpec.U lpBody))
def callF : X := apps (.c "lp" []) [litNX 3, .bv 0, rdX]
def bodyF : X := apps (.c "put" []) [nilX, callF]
def oF : List (String × X × X) := [("lp", lpTy, lpVal), ("m", .pi LU8 LU8, .lam LU8 bodyF)]

def outF (inp : List UInt8) : UInt8 := ((inp.getD 0 0).toUInt64 + 3).toUInt8

/-- closes the spine-mismatch cases of an `Ev` inversion -/
macro "spine_absurd" he:ident : tactic =>
  `(tactic| first
    | (cases $he:ident; done)
    | (simp [apps] at $he:ident; done)
    | exact absurd (apps_c_inj $he).1 (by simp)
    | exact absurd (apps_c_inj $he).2.1 (by simp)
    | exact absurd (apps_c_inj $he).2.2 (by simp)
    | exact absurd ($he).symm apps_ne_bv)

theorem ev_bv {P : Prog} {env : List V} {i : Nat} {r : V} (h : Ev P env (.bv i) r) : env[i]? = some r := by
  generalize he : X.bv i = e at h
  cases h with
  | bv h => cases he; exact h
  | _ => spine_absurd he

theorem ev_litN {P : Prog} {env : List V} {r : V} (k : Nat) (h : Ev P env (litNX k) r) : r = .n k := by
  generalize he : litNX k = e at h
  have hk : litNX k = apps (.c "OfNat.ofNat" [0]) [NX, .nat k, .app (.c "instOfNatNat" []) (.nat k)] := rfl
  rw [hk] at he
  cases h with
  | litN => obtain ⟨-, -, h3⟩ := apps_c_inj he; simp [NX] at h3; obtain ⟨h31, -⟩ := h3; subst h31; rfl
  | litU => exact absurd (apps_c_inj he).2.2 (by simp [NX])
  | _ => spine_absurd he

theorem ev_natCases {P : Prog} {env : List V} {M d z T s : X} {r : V}
    (h : Ev P env (apps (.c "Nat.casesOn" [1]) [M, d, z, .lam T s]) r) :
    (Ev P env d (.n 0) ∧ Ev P env z r) ∨ ∃ k, Ev P env d (.n (k + 1)) ∧ Ev P (.n k :: env) s r := by
  generalize he : apps (.c "Nat.casesOn" [1]) [M, d, z, .lam T s] = e at h
  cases h with
  | natZ hd hz =>
    obtain ⟨-, -, h3⟩ := apps_c_inj he; simp only [List.cons.injEq, X.lam.injEq] at h3
    obtain ⟨-, rfl, rfl, -, -, -⟩ := h3; exact .inl ⟨hd, hz⟩
  | natS hd hs =>
    obtain ⟨-, -, h3⟩ := apps_c_inj he; simp only [List.cons.injEq, X.lam.injEq] at h3
    obtain ⟨-, rfl, -, ⟨-, rfl⟩, -⟩ := h3; exact .inr ⟨_, hd, hs⟩
  | _ => spine_absurd he

theorem lookup_rdF : (progOf oF).lookup "rd" = none := by
  have h1 : ("rd" == "lp") = false := by decide
  have h2 : ("rd" == "m") = false := by decide
  simp [progOf, oF, List.lookup, h1, h2]

theorem lookup_lp : (progOf oF).lookup "lp" = some lpVal := by simp [progOf, oF, List.lookup]

/-- one loop step: the recursive call, with the accumulator advanced -/
theorem ev_step {inp : List UInt8} {a : UInt64} {k : Nat} {r : V}
    (h : Ev (progOf oF) [.n k, .w a, .l inp, .n (k + 1)] stepX r) :
    Ev (progOf oF) [.w (a + 1), .l inp, .n k] lpBody r := by
  generalize he : stepX = e at h
  have hk : stepX = apps (.c "lp" []) [.bv 0, .bv 2, addS] := rfl
  rw [hk] at he
  cases h with
  | call ha hl hs hb =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    rw [lookup_lp] at hl; cases hl
    cases ha with
    | cons h1 h2 =>
      cases h2 with
      | cons h3 h4 =>
        cases h4 with
        | cons h5 h6 =>
          cases h6
          have e1 := ev_bv h1; have e3 := ev_bv h3
          simp at e1 e3; subst e1 e3
          obtain ⟨x, y, z, hbn, ha', hc, rfl⟩ := ev_bin6 (by simp) h5
          have e5 := ev_bv ha'; have e6 := ev_litU 1 hc
          simp at e5 e6; subst e5 e6
          simp [binV] at hbn; subst hbn
          simp [strip, lpVal] at hs; subst hs
          exact hb
  | prim ha hp =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons _ h2 => cases h2 with
      | cons _ h4 => cases h4 with
        | cons _ h6 => cases h6; simp [prim] at hp
  | _ => spine_absurd he

/-- **the fuel loop**: `lp k x a` evaluates to `a + k` -/
theorem ev_lp {inp : List UInt8} (k : Nat) : ∀ (a : UInt64) {r : V},
    Ev (progOf oF) [.w a, .l inp, .n k] lpBody r → r = .w (a + UInt64.ofNat k) := by
  induction k with
  | zero =>
    intro a r h
    rcases ev_natCases h with ⟨-, hz⟩ | ⟨j, hd, -⟩
    · have e2 := ev_bv hz; simp at e2; subst e2; simp
    · have e1 := ev_bv hd; simp at e1
  | succ k ih =>
    intro a r h
    rcases ev_natCases h with ⟨hd, -⟩ | ⟨j, hd, hs⟩
    · have e1 := ev_bv hd; simp at e1
    · have e1 := ev_bv hd; simp at e1; subst e1
      rw [ih (a + 1) (ev_step hs)]
      congr 1; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_add]; omega

theorem ev_callF {inp : List UInt8} {r : V} (h : Ev (progOf oF) [.l inp] callF r) :
    r = .w ((inp.getD 0 0).toUInt64 + 3) := by
  generalize he : callF = e at h
  have hk : callF = apps (.c "lp" []) [litNX 3, .bv 0, rdX] := rfl
  rw [hk] at he
  cases h with
  | call ha hl hs hb =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    rw [lookup_lp] at hl; cases hl
    cases ha with
    | cons h1 h2 =>
      cases h2 with
      | cons h3 h4 =>
        cases h4 with
        | cons h5 h6 =>
          cases h6
          rw [ev_litN 3 h1, ev_bv0 h3, ev_rdG lookup_rdF h5] at hb
          simp [strip, lpVal] at hs; subst hs
          rw [ev_lp 3 _ hb]; rfl
  | prim ha hp =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons _ h2 => cases h2 with
      | cons _ h4 => cases h4 with
        | cons _ h6 => cases h6; simp [prim] at hp
  | _ => spine_absurd he

theorem ev_bodyF {inp : List UInt8} {r : V} (h : Ev (progOf oF) [.l inp] bodyF r) : r = .l [outF inp] := by
  generalize he : bodyF = e at h
  have hk : bodyF = apps (.c "put" []) [nilX, callF] := rfl
  rw [hk] at he
  cases h with
  | prim ha hp =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 =>
      cases h2 with
      | cons h3 h4 =>
        cases h4
        rw [ev_nil h1, ev_callF h3] at hp
        simp [prim] at hp; rw [← hp]; simp [outF]
  | call ha hl =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have h1 : ("put" == "lp") = false := by decide
    have h2 : ("put" == "m") = false := by decide
    simp [progOf, oF, List.lookup, h1, h2] at hl
  | _ => spine_absurd he

theorem ev_mainF {inp : List UInt8} {r : V} (h : Ev (progOf oF) [.l inp] mainX r) : r = .l [outF inp] := by
  generalize he : mainX = e at h
  have hm : mainX = apps (.c "m" []) [.bv 0] := rfl
  rw [hm] at he
  cases h with
  | call ha hl hs hb =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    have h1 : ("m" == "lp") = false := by decide
    simp [progOf, oF, List.lookup, h1] at hl; subst hl
    cases ha with
    | cons h1 h2 =>
      cases h2
      rw [ev_bv0 h1] at hb
      simp [strip] at hs; subst hs
      exact ev_bodyF hb
  | prim ha hp =>
    obtain ⟨rfl, -, rfl⟩ := apps_c_inj he
    cases ha with
    | cons h1 h2 => cases h2; simp [prim] at hp
  | _ => spine_absurd he

theorem outF_toNat (inp : List UInt8) : (outF inp).toNat = ((inp.getD 0 0).toNat + 3) % 256 := by
  unfold outF
  generalize inp.getD 0 0 = b
  have hb := b.toNat_lt
  simp

end Bridge.Real.NanoF
