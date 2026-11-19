/- Nano/V2Self/Proof/ParInvPrim: Layer 3, the PRIM tables and shape codes (box G).
* `ShapeCode.det`: a code decodes to at most one shape (code equality in the machine ⇒ shape equality in Layer 2);
* Par1's prim tables on machine words = Layer 2's: `v91_eq` (arity), `v92_code` (result code), `v90_code` (parameter code). -/
import Nano.V2Self.Proof.ParInvExpr
import Nano.V2Self.Proof.ParRunPrim
namespace ParInv
open C BufL ParSpec ParRun

theorem ShapeCode.det {h : Buf} {c : UInt64} {s s' : Sh} (r : ShapeCode h c s) (r' : ShapeCode h c s') : s = s' := by
  induction r generalizing s' with
  | uw => cases r' with
    | uw => rfl
    | pr h5 => simp at h5
  | bf => cases r' with
    | bf => rfl
    | pr h5 => simp at h5
  | ls => cases r' with
    | ls => rfl
    | pr h5 => simp at h5
  | nt => cases r' with
    | nt => rfl
    | pr h5 => simp at h5
  | pr h5 _ el er _ _ iha ihb =>
    cases r' with
    | uw => simp at h5
    | bf => simp at h5
    | ls => simp at h5
    | nt => simp at h5
    | pr _ _ el' er' ra rb =>
      subst el er el' er'
      rw [iha ra, ihb rb]

theorem ShOpt.det {h : Buf} {c : UInt64} {o o' : Option Sh} (r : ShOpt h c o) (r' : ShOpt h c o') (hs : o.isSome) (hs' : o'.isSome) :
    o = o' := by
  match o, o', hs, hs' with
  | some s, some s', _, _ => exact congrArg some (ShapeCode.det r r')

/-- a small Nat as a machine word compares like the Nat -/
theorem u_beq {p : Nat} (hp : p < 2 ^ 64) (c : Nat) (hc : c < 2 ^ 64) : (p.toUInt64 == c.toUInt64) = decide (p = c) := by
  by_cases e : p = c
  · subst e; simp
  · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro q; apply e
    have := congrArg UInt64.toNat q
    simpa [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hc] using this

theorem u_lt {p : Nat} (hp : p < 2 ^ 64) (c : Nat) (hc : c < 2 ^ 64) : (p.toUInt64 < c.toUInt64) ↔ p < c := by
  rw [UInt64.lt_iff_toNat_lt]; simp [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hc]

/-- v91 = `primAr` -/
theorem v91_eq {p : Nat} (hp : p < 2 ^ 64) : v91 p.toUInt64 = (primAr p).toUInt64 := by
  have e := fun c hc => u_beq hp c hc
  have e5 := e 5 (by decide); have e8 := e 8 (by decide); have e2 := e 2 (by decide); have e4 := e 4 (by decide)
  have e7 := e 7 (by decide); have e9 := e 9 (by decide)
  simp only [show (5 : Nat).toUInt64 = 5 from rfl, show (8 : Nat).toUInt64 = 8 from rfl, show (2 : Nat).toUInt64 = 2 from rfl,
    show (4 : Nat).toUInt64 = 4 from rfl, show (7 : Nat).toUInt64 = 7 from rfl, show (9 : Nat).toUInt64 = 9 from rfl] at e5 e8 e2 e4 e7 e9
  unfold v91 primAr
  simp only [e5, e8, e2, e4, e7, e9, decide_eq_true_eq]
  by_cases h5 : p = 5 <;> by_cases h8 : p = 8 <;> by_cases h2 : p = 2 <;> by_cases h4 : p = 4 <;> by_cases h7 : p = 7 <;>
    by_cases h9 : p = 9 <;> simp [h5, h8, h2, h4, h7, h9] <;> omega

/-- v92 = the code of `primRes` -/
theorem v92_code (h : Buf) {p : Nat} (hp : p < 2 ^ 64) : ShapeCode h (v92 p.toUInt64) (primRes p) := by
  have e := fun c hc => u_beq hp c hc
  have e1 := e 1 (by decide); have e4 := e 4 (by decide); have e5 := e 5 (by decide); have e8 := e 8 (by decide); have e9 := e 9 (by decide)
  simp only [show (5 : Nat).toUInt64 = 5 from rfl, show (8 : Nat).toUInt64 = 8 from rfl, show (1 : Nat).toUInt64 = 1 from rfl,
    show (4 : Nat).toUInt64 = 4 from rfl, show (9 : Nat).toUInt64 = 9 from rfl] at e1 e4 e5 e8 e9
  unfold v92 primRes
  simp only [e1, e4, e5, e8, e9, decide_eq_true_eq]
  by_cases h1 : p = 1 <;> by_cases h4 : p = 4 <;> by_cases h5 : p = 5 <;> by_cases h8 : p = 8 <;> by_cases h9 : p = 9 <;>
    simp [h1, h4, h5, h8, h9] <;> first | exact .uw | exact .bf | exact .ls | exact .nt | omega

/-- v90 = the code of `primPar` -/
theorem v90_code (h : Buf) {p j : Nat} (hp : p < 2 ^ 64) (hj : j < 2 ^ 64) : ShapeCode h (v90 p.toUInt64 j.toUInt64) (primPar p j) := by
  have e0 := u_beq hj 0 (by decide)
  have l5 := u_lt hp 5 (by decide)
  simp only [show (0 : Nat).toUInt64 = 0 from rfl, show (5 : Nat).toUInt64 = 5 from rfl] at e0 l5
  unfold v90 primPar
  simp only [e0, decide_eq_true_eq, l5]
  by_cases h0 : j = 0 <;> by_cases h5 : p < 5 <;> simp [h0, h5] <;> first | exact .uw | exact .bf | exact .ls

end ParInv
