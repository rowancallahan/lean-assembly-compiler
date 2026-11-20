/- `Int` scalars in the front ends (NOTES section 26): a value is its two's complement word `rI x =
BitVec.ofInt 64 x` (`x mod 2^64`).  `+ - * -x` and `Int.ofNat` commute with `rI` unconditionally; comparisons,
`Int.toNat`, `Int.natAbs`, `/` and `%` need the operands in range, `-2^63 ≤ x < 2^63` (side conditions,
discharged by `omega` from the hypotheses).  Lean's `/` and `%` on `Int` are `Int.ediv` / `Int.emod` (rounding
so that `0 ≤ x % y < |y|`; `x / 0 = 0`, `x % 0 = x`): built from the machine's signed `div` / `rem`
(`Int.tdiv` / `Int.tmod`, `Mach.MOp`) by one adjustment when the remainder is negative (`edivB`, `emodB`). -/
import Lean
import Legacy.Riscv.Frontx.Rep

namespace Proven.Frontx
open Proven

/-- an `Int` in a word: two's complement (`x mod 2^64`) -/
def rI (x : Int) : BitVec 64 := BitVec.ofInt 64 x

theorem rI_toInt {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) : (rI x).toInt = x := by
  rw [rI, BitVec.toInt_ofInt]; rw [Int.bmod_eq_of_le] <;> omega

theorem rI_add (a b : Int) : rI (a + b) = rI a + rI b := BitVec.ofInt_add a b
theorem rI_sub (a b : Int) : rI (a - b) = rI a - rI b := by simp [rI, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
theorem rI_mul (a b : Int) : rI (a * b) = rI a * rI b := BitVec.ofInt_mul a b
theorem rI_neg (a : Int) : rI (-a) = 0#64 - rI a := by simp [rI, BitVec.ofInt_neg]
theorem rI_ofNat (n : Nat) : rI (n : Int) = rN n := by simp [rI, rN]
theorem rI_intOfNat (n : Nat) : rI (Int.ofNat n) = rN n := rI_ofNat n
theorem rI_lit (n : Nat) : rI (no_index (OfNat.ofNat n : Int)) = BitVec.ofNat 64 n := by
  show rI (n : Int) = _; simp [rI]
theorem rI_slt {a b : Int} (ha1 : -2 ^ 63 ≤ a) (ha2 : a < 2 ^ 63) (hb1 : -2 ^ 63 ≤ b) (hb2 : b < 2 ^ 63) :
    (rI a).slt (rI b) = decide (a < b) := by
  rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, rI_toInt ha1 ha2, rI_toInt hb1 hb2]; simp
theorem rI_inj {a b : Int} (ha1 : -2 ^ 63 ≤ a) (ha2 : a < 2 ^ 63) (hb1 : -2 ^ 63 ≤ b) (hb2 : b < 2 ^ 63) :
    (rI a = rI b) = (a = b) := by
  apply propext; constructor
  · intro h; rw [← rI_toInt ha1 ha2, ← rI_toInt hb1 hb2, h]
  · intro h; rw [h]
/-- the value of a word literal as an `Int` (two's complement) -/
def litI (n : Nat) : Int := if n % 2 ^ 64 < 2 ^ 63 then ((n % 2 ^ 64 : Nat) : Int) else ((n % 2 ^ 64 : Nat) : Int) - 2 ^ 64
theorem lit_rI (n : Nat) : BitVec.ofNat 64 n = rI (litI n) := by
  unfold litI rI; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, BitVec.toNat_ofInt]; split <;> omega
theorem litI_range (n : Nat) : -2 ^ 63 ≤ litI n ∧ litI n < 2 ^ 63 := by unfold litI; split <;> omega
theorem rI_slt_litR {a : Int} (n : Nat) (ha1 : -2 ^ 63 ≤ a) (ha2 : a < 2 ^ 63) :
    (rI a).slt (BitVec.ofNat 64 n) = decide (a < litI n) := by
  rw [lit_rI, rI_slt ha1 ha2 (litI_range n).1 (litI_range n).2]
theorem rI_slt_litL {b : Int} (n : Nat) (hb1 : -2 ^ 63 ≤ b) (hb2 : b < 2 ^ 63) :
    (BitVec.ofNat 64 n).slt (rI b) = decide (litI n < b) := by
  rw [lit_rI, rI_slt (litI_range n).1 (litI_range n).2 hb1 hb2]
theorem rI_eq_litR {a : Int} (n : Nat) (ha1 : -2 ^ 63 ≤ a) (ha2 : a < 2 ^ 63) :
    (rI a = BitVec.ofNat 64 n) = (a = litI n) := by
  rw [lit_rI, rI_inj ha1 ha2 (litI_range n).1 (litI_range n).2]
theorem rI_eq_litL {b : Int} (n : Nat) (hb1 : -2 ^ 63 ≤ b) (hb2 : b < 2 ^ 63) :
    (BitVec.ofNat 64 n = rI b) = (litI n = b) := by
  rw [lit_rI, rI_inj (litI_range n).1 (litI_range n).2 hb1 hb2]
theorem rI_ite (p : Prop) [Decidable p] (a b : Int) : rI (if p then a else b) = if p then rI a else rI b := by
  split <;> rfl

/-- `Int.toNat`: `0` below zero -/
theorem rN_toNatI {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) :
    rN x.toNat = if (rI x).slt 0#64 = true then 0#64 else rI x := by
  have : (0#64) = rI 0 := rfl
  rw [this, rI_slt h1 h2 (by omega) (by omega)]
  by_cases h : x < 0
  · simp only [h, decide_true, if_true]; rw [Int.toNat_of_nonpos (by omega)]; rfl
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    conv => rhs; rw [show x = ((x.toNat : Nat) : Int) by omega]
    rw [rI_ofNat]
theorem rN_natAbs {x : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) :
    rN x.natAbs = if (rI x).slt 0#64 = true then 0#64 - rI x else rI x := by
  have : (0#64) = rI 0 := rfl
  rw [this, rI_slt h1 h2 (by omega) (by omega), ← this]
  by_cases h : x < 0
  · simp only [h, decide_true, if_true]
    rw [← rI_neg, show -x = ((x.natAbs : Nat) : Int) by omega, rI_ofNat]
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    rw [show x = ((x.natAbs : Nat) : Int) by omega, rI_ofNat]; simp

/-- the machine's signed quotient / remainder (`div` / `rem`: zero divisor gives all ones / the dividend) -/
def sdivH (a b : BitVec 64) : BitVec 64 := Mach.MOp.eval .div a b
def sremH (a b : BitVec 64) : BitVec 64 := Mach.MOp.eval .rem a b
theorem mopV_div (x y : BitVec 64) : mopV .div x y = sdivH x y := rfl
theorem mopV_rem (x y : BitVec 64) : mopV .rem x y = sremH x y := rfl

/-- Lean's `/` and `%` on `Int` from the machine's: an adjustment when the remainder is negative -/
def edivB (a b : BitVec 64) : BitVec 64 :=
  let q := sdivH a b
  let r := sremH a b
  if r.slt 0#64 = true then (if (0#64).slt b = true then q - 1#64 else q + 1#64) else if b = 0#64 then 0#64 else q
def emodB (a b : BitVec 64) : BitVec 64 :=
  let r := sremH a b
  if r.slt 0#64 = true then (if b.slt 0#64 = true then r - b else r + b) else r


theorem tmod_range {x y : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) :
    -2 ^ 63 ≤ x.tmod y ∧ x.tmod y < 2 ^ 63 := by
  have := Int.natAbs_tmod x y
  have := Nat.mod_le x.natAbs y.natAbs
  by_cases hx : 0 ≤ x
  · have := Int.tmod_nonneg y hx; omega
  · have h := Int.tmod_nonneg y (a := -x) (by omega)
    rw [Int.neg_tmod] at h; omega

theorem sremH_rI {x y : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) (hy1 : -2 ^ 63 ≤ y) (hy2 : y < 2 ^ 63) :
    sremH (rI x) (rI y) = rI (x.tmod y) := by
  simp only [sremH, Mach.MOp.eval, rI_toInt h1 h2, rI_toInt hy1 hy2]; rfl

theorem sdivH_rI {x y : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) (hy1 : -2 ^ 63 ≤ y) (hy2 : y < 2 ^ 63) :
    sdivH (rI x) (rI y) = if y = 0 then rI (-1) else rI (x.tdiv y) := by
  have e0 : (0 : BitVec 64) = rI 0 := rfl
  simp only [sdivH, Mach.MOp.eval, rI_toInt h1 h2, rI_toInt hy1 hy2, e0, rI_inj (b := 0) hy1 hy2 (by decide) (by decide)]; rfl

theorem rI_emod {x y : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) (hy1 : -2 ^ 63 ≤ y) (hy2 : y < 2 ^ 63) :
    rI (x % y) = emodB (rI x) (rI y) := by
  have e0 : (0#64) = rI 0 := rfl
  have ⟨t1, t2⟩ := tmod_range (y := y) h1 h2
  simp only [emodB, sremH_rI h1 h2 hy1 hy2, e0, rI_slt (b := 0) t1 t2 (by decide) (by decide), rI_slt (b := 0) hy1 hy2 (by decide) (by decide),
    ← rI_sub, ← rI_add, decide_eq_true_eq]
  have ht := @Int.tmod_eq_emod x y
  have hm := Int.emod_nonneg x (b := y)
  have hl := Int.emod_lt x (b := y)
  rcases Int.lt_trichotomy y 0 with hy | hy | hy
  · have hm := hm (by omega); have hl := hl (by omega)
    split at ht <;> (repeat' split) <;> first | omega | (congr 1; omega)
  · subst hy; simp
  · have hm := hm (by omega); have hl := hl (by omega)
    split at ht <;> (repeat' split) <;> first | omega | (congr 1; omega)

theorem rI_ediv {x y : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) (hy1 : -2 ^ 63 ≤ y) (hy2 : y < 2 ^ 63) :
    rI (x / y) = edivB (rI x) (rI y) := by
  have e0 : (0#64) = rI 0 := rfl
  have e1 : (1#64) = rI 1 := rfl
  have ⟨t1, t2⟩ := tmod_range (y := y) h1 h2
  simp only [edivB, sremH_rI h1 h2 hy1 hy2, sdivH_rI h1 h2 hy1 hy2, e0, e1, rI_slt (b := 0) t1 t2 (by decide) (by decide),
    rI_slt (a := 0) (by decide) (by decide) hy1 hy2, rI_inj (b := 0) hy1 hy2 (by decide) (by decide), decide_eq_true_eq]
  have ht := @Int.tmod_eq_emod x y
  have hq := @Int.tdiv_eq_ediv x y
  rcases Int.lt_trichotomy y 0 with hy | hy | hy
  · have hm := Int.emod_nonneg x (b := y) (by omega); have hl := Int.emod_lt x (b := y) (by omega)
    rw [Int.sign_eq_neg_one_of_neg hy] at hq
    split at ht <;> split at hq <;> (repeat' split) <;>
      first | omega | (rw [← rI_add]; congr 1; omega) | (congr 1; omega)
  · subst hy; simp; intro; rfl
  · have hm := Int.emod_nonneg x (b := y) (by omega); have hl := Int.emod_lt x (b := y) (by omega)
    rw [Int.sign_eq_one_of_pos hy] at hq
    split at ht <;> split at hq <;> (repeat' split) <;>
      first | omega | (rw [← rI_sub]; congr 1; omega) | (congr 1; omega)

/-- the same with `Int.ediv` / `Int.emod` written out (lean-svg writes `Int.ediv a 256`) -/
theorem rI_ediv' {x y : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) (hy1 : -2 ^ 63 ≤ y) (hy2 : y < 2 ^ 63) :
    rI (Int.ediv x y) = edivB (rI x) (rI y) := rI_ediv h1 h2 hy1 hy2
theorem rI_emod' {x y : Int} (h1 : -2 ^ 63 ≤ x) (h2 : x < 2 ^ 63) (hy1 : -2 ^ 63 ≤ y) (hy2 : y < 2 ^ 63) :
    rI (Int.emod x y) = emodB (rI x) (rI y) := rI_emod h1 h2 hy1 hy2

/-- what `omega` is told about an `Int` temporary defined by an `if` (with its condition) -/
theorem ite_eq_orI {c : Prop} [Decidable c] {a b x : Int} (h : (if c then a else b) = x) : (c ∧ x = a) ∨ (¬c ∧ x = b) := by
  split at h <;> simp_all
theorem ite_eq_orI' {c : Prop} [Decidable c] {a b x : Int} (h : x = if c then a else b) : (c ∧ x = a) ∨ (¬c ∧ x = b) :=
  ite_eq_orI h.symm

/-- a product is bounded by the product of bounds of its factors (for `omega`, which does not multiply variables) -/
theorem mul_bound {x y A B : Int} (hx1 : -A ≤ x) (hx2 : x ≤ A) (hy1 : -B ≤ y) (hy2 : y ≤ B) :
    -(A * B) ≤ x * y ∧ x * y ≤ A * B := by
  have ha : x.natAbs ≤ A.toNat := by omega
  have hb : y.natAbs ≤ B.toNat := by omega
  have h := Nat.mul_le_mul ha hb
  have e := Int.natAbs_mul x y
  have hA : (0:Int) ≤ A := by omega
  have hB : (0:Int) ≤ B := by omega
  have : ((A.toNat * B.toNat : Nat) : Int) = A * B := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg hA, Int.toNat_of_nonneg hB]
  have : (((x*y).natAbs : Nat) : Int) ≤ A * B := by rw [← this]; exact_mod_cast (e ▸ h)
  omega

theorem ediv_hdiv (a b : Int) : Int.ediv a b = a / b := rfl
theorem emod_hmod (a b : Int) : Int.emod a b = a % b := rfl

open Lean Meta Elab Tactic in
/-- unfold the abbreviations of `Int` (lean-svg's `Fx`) in the goal and the hypotheses, so that `omega` and the
representation lemmas see `Int`; `Int.ediv` / `Int.emod` as `/` / `%` (the forms `omega` reads) -/
elab "frontx_int_abbrev" : tactic => withMainContext do
  let mut es : Array Expr := #[← getMainTarget]
  for d in ← getLCtx do
    if !d.isImplementationDetail then es := es.push (← instantiateMVars d.type) |>.push d.type
  let mut cs : Array Name := #[]
  for e in es do
    for c in e.getUsedConstants do
      if cs.contains c then continue
      let some (.defnInfo di) := (← getEnv).find? c | continue
      if di.levelParams.isEmpty && di.value.isConstOf ``Int then cs := cs.push c
  let ids := (cs.map mkIdent) ++ #[mkIdent ``ediv_hdiv, mkIdent ``emod_hmod]
  evalTactic (← `(tactic| dsimp only [$[$ids:ident],*] at *))

open Lean Meta Elab Tactic in
/-- bounds of the `Int` products `x * y` (neither a literal) in the goal and the hypotheses: a bound `|x| ≤ 2 ^ k`
of each factor is searched by `omega` (innermost products first, two rounds), then `mul_bound` / `Nat.mul_le_mul` -/
elab "frontx_int_facts" : tactic => withMainContext do
  let mut es : Array Expr := #[← getMainTarget]
  for d in ← getLCtx do
    if !d.isImplementationDetail then es := es.push (← instantiateMVars d.type)
  let mut muls : Array Expr := #[]
  let isLit (e : Expr) : Bool := e.isAppOfArity ``OfNat.ofNat 3 || (e.isAppOfArity ``Neg.neg 3 && e.appArg!.isAppOfArity ``OfNat.ofNat 3)
  for e in es do
    let mut todo := #[e]
    while h : todo.size > 0 do
      let x := todo.back
      todo := todo.pop
      match x with
      | .app f a => todo := todo.push f |>.push a
      | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
      | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
      | .mdata _ b => todo := todo.push b
      | _ => pure ()
      if x.hasLooseBVars then continue
      if x.isAppOfArity ``HMul.hMul 6 && ((x.getArg! 0).isConstOf ``Int || (x.getArg! 0).isConstOf ``Nat) &&
          !isLit (x.getArg! 4) && !isLit (x.getArg! 5) then
        unless muls.contains x do muls := muls.push x
  if muls.isEmpty then throwError "frontx_int_facts: no product"
  let sorted := muls.qsort fun a b => a.approxDepth < b.approxDepth
  let ks : List Nat := [1, 2 ^ 8, 2 ^ 15, 2 ^ 16, 2 ^ 24, 2 ^ 31, 2 ^ 32, 2 ^ 40, 2 ^ 47, 2 ^ 48, 2 ^ 56, 2 ^ 62, 2 ^ 63]
  let mut n := 0
  -- twice: a factor's bound may need the bound of a product found later (a temporary defined by it)
  for m in sorted ++ sorted do
    let isNat := (m.getArg! 0).isConstOf ``Nat
    let mut hs : Array Ident := #[]
    for x in [m.getArg! 4, m.getArg! 5] do
      let xs ← Term.exprToSyntax x
      let hn := mkIdent (Name.mkSimple s!"hib{n}"); n := n + 1
      for k in ks do
        let st ← saveState
        try
          if isNat then
            Tactic.withoutRecover <| evalTactic (← `(tactic| have $hn : $xs ≤ $(Lean.quote k) := by omega))
          else
            Tactic.withoutRecover <| evalTactic (← `(tactic| have $hn : -($(Lean.quote k) : Int) ≤ $xs ∧ $xs ≤ ($(Lean.quote k) : Int) := by omega))
          hs := hs.push hn
          break
        catch _ => st.restore
    if let #[a, b] := hs then
      if isNat then evalTactic (← `(tactic| have := Nat.mul_le_mul $a $b))
      else evalTactic (← `(tactic| have := mul_bound $a.1 $a.2 $b.1 $b.2))

end Proven.Frontx
