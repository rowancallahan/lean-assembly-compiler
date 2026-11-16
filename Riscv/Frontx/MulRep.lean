/- Multiply / divide / remainder by a variable for the list front end (NOTES section 22): the representation
lemmas the obligations of `Translate.lean` are closed with (the words `mopS` leaves, `Sub.lean`). -/
import Lean
import Riscv.Frontx.Rep
import Riscv.Frontx.Exc

namespace Proven.Frontx

theorem rN_mul (a b : Nat) : rN (a * b) = rN a * rN b := by
  apply BitVec.eq_of_toNat_eq; simp [rN, BitVec.toNat_mul, Nat.mul_mod]
theorem rN_div {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : rN (a / b) = rN a / rN b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, rN_toNat ha, rN_toNat hb, rN_toNat (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]
theorem rN_mod {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : rN (a % b) = rN a % rN b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, rN_toNat ha, rN_toNat hb, rN_toNat (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha)]

theorem r64_mul (a b : UInt64) : r64 (a * b) = r64 a * r64 b := rfl
theorem r64_div (a b : UInt64) : r64 (a / b) = r64 a / r64 b := rfl
theorem r64_mod (a b : UInt64) : r64 (a % b) = r64 a % r64 b := rfl

theorem r32_mul (a b : UInt32) : r32 (a * b) = (r32 a * r32 b) &&& 0xffffffff#64 := by
  apply BitVec.eq_of_toNat_eq; rw [and_mask32, BitVec.toNat_mul, r32_nat, r32_nat, r32_nat, UInt32.toNat_mul,
    Nat.mod_mod_of_dvd _ (by decide)]
theorem r32_div (a b : UInt32) : r32 (a / b) = r32 a / r32 b := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_udiv, r32_nat, r32_nat, r32_nat, UInt32.toNat_div]
theorem r32_mod (a b : UInt32) : r32 (a % b) = r32 a % r32 b := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod, r32_nat, r32_nat, r32_nat, UInt32.toNat_mod]

theorem r16_mul (a b : UInt16) : r16 (a * b) = (r16 a * r16 b) &&& 0xffff#64 := by
  apply BitVec.eq_of_toNat_eq; rw [and_mask16, BitVec.toNat_mul, r16_nat, r16_nat, r16_nat, UInt16.toNat_mul,
    Nat.mod_mod_of_dvd _ (by decide)]
theorem r16_div (a b : UInt16) : r16 (a / b) = r16 a / r16 b := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_udiv, r16_nat, r16_nat, r16_nat, UInt16.toNat_div]
theorem r16_mod (a b : UInt16) : r16 (a % b) = r16 a % r16 b := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod, r16_nat, r16_nat, r16_nat, UInt16.toNat_mod]

theorem r8_mul (a b : UInt8) : r8 (a * b) = (r8 a * r8 b) &&& 0xff#64 := by
  apply BitVec.eq_of_toNat_eq; rw [and_mask8, BitVec.toNat_mul, r8_nat, r8_nat, r8_nat, UInt8.toNat_mul,
    Nat.mod_mod_of_dvd _ (by decide)]
theorem r8_div (a b : UInt8) : r8 (a / b) = r8 a / r8 b := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_udiv, r8_nat, r8_nat, r8_nat, UInt8.toNat_div]
theorem r8_mod (a b : UInt8) : r8 (a % b) = r8 a % r8 b := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod, r8_nat, r8_nat, r8_nat, UInt8.toNat_mod]

/-- `Nat` shift left by a variable below 64 (`sll` takes the amount mod 64) -/
theorem rN_shlV {a b : Nat} (hb : b < 64) : rN (a <<< b) = rN a <<< ((rN b).toNat % 64) := by
  rw [rN_toNat (by omega), Nat.mod_eq_of_lt hb]
  apply BitVec.eq_of_toNat_eq; simp [rN, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]

/-- the amount of a `Nat` shift by `b % 64` (a mask) -/
theorem rN_and63_mod (b : Nat) : (rN b &&& 63#64).toNat % 64 = b % 64 := by
  rw [BitVec.toNat_and]
  simp only [rN, BitVec.toNat_ofNat]
  rw [show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem rN_xor' (a b : Nat) : rN (a ^^^ b) = rN a ^^^ rN b := by
  apply BitVec.eq_of_toNat_eq; simp [rN, Nat.xor_mod_two_pow]
theorem nat_and63_mod (y : Nat) : (y &&& 63) % 64 = y % 64 := by
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem bv_and63_mod (x : BitVec 64) : (x &&& 63#64).toNat % 64 = x.toNat % 64 := by
  rw [BitVec.toNat_and, show (63#64).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

/-- a `Nat` right shift by a variable, guarded (`0` from 64 on) -/
theorem shr_guard (x : BitVec 64) {y : Nat} (hy : y < 2 ^ 64) :
    (if (if rN y < 64#64 then 1#64 else 0#64) = 0#64 then 0#64 else x >>> ((rN y).toNat % 64)) = x >>> y := by
  rw [rN_toNat hy]
  have e : (rN y < 64#64) ↔ y < 64 := by
    rw [show (64#64) = BitVec.ofNat 64 64 from rfl, rN_lt_lit hy (by decide)]
  by_cases h : y < 64
  · rw [if_pos (e.2 h), if_neg (by decide), Nat.mod_eq_of_lt h]
  · rw [if_neg (fun h' => h (e.1 h')), if_pos rfl]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod]
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt]
    exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))

/-- the guarded shift as `simp` leaves it -/
theorem shr_guardB (x y : BitVec 64) : (if y < 64#64 then x >>> (y.toNat % 64) else 0#64) = x >>> y.toNat := by
  by_cases h : y < 64#64
  · have : y.toNat < 64 := h
    rw [if_pos h, Nat.mod_eq_of_lt this]
  · have : 64 ≤ y.toNat := by have := BitVec.not_lt.1 h; exact this
    rw [if_neg h]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod]
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt]
    exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) this)
theorem shr_guardN (x : BitVec 64) (y : Nat) : (if y < 64 then x >>> (y % 64) else 0#64) = x >>> y := by
  by_cases h : y < 64
  · rw [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.zero_mod]
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt]
    exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega))
theorem shr_guardU (x : BitVec 64) (y : UInt64) :
    (if r64 y < 64#64 then x >>> (y.toNat % 64) else 0#64) = x >>> y.toNat := shr_guardB x (r64 y)
theorem r64_toNat_eq (a : UInt64) : (r64 a).toNat = a.toNat := rfl

open Lean Meta Elab Tactic in
/-- bounds `omega` cannot find by itself: `a % b ≤ a`, `0 < b → a % b < b`, `a / b ≤ a`, `a &&& b ≤ a, b` for every
`Nat` `%` / `/` / `&&&`
in the goal and the hypotheses -/
elab "frontx_md_facts" : tactic => withMainContext do
  let mut es : Array Expr := #[← getMainTarget]
  for d in ← getLCtx do
    if !d.isImplementationDetail then es := es.push (← instantiateMVars d.type)
  let mut mods : Array (Expr × Expr) := #[]
  let mut divs : Array (Expr × Expr) := #[]
  let mut ands : Array (Expr × Expr) := #[]
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
      if x.isAppOfArity ``HMod.hMod 6 && (x.getArg! 0).isConstOf ``Nat then
        unless mods.contains (x.getArg! 4, x.getArg! 5) do mods := mods.push (x.getArg! 4, x.getArg! 5)
      if x.isAppOfArity ``HDiv.hDiv 6 && (x.getArg! 0).isConstOf ``Nat then
        unless divs.contains (x.getArg! 4, x.getArg! 5) do divs := divs.push (x.getArg! 4, x.getArg! 5)
      if x.isAppOfArity ``HAnd.hAnd 6 && (x.getArg! 0).isConstOf ``Nat then
        unless ands.contains (x.getArg! 4, x.getArg! 5) do ands := ands.push (x.getArg! 4, x.getArg! 5)
  if mods.isEmpty && divs.isEmpty && ands.isEmpty then throwError "frontx_md_facts: no `%` / `/` / `&&&`"
  for (a, b) in mods do
    let (a, b) := (← Term.exprToSyntax a, ← Term.exprToSyntax b)
    evalTactic (← `(tactic| have := Nat.mod_le $a $b))
    evalTactic (← `(tactic| have := fun h : 0 < $b => Nat.mod_lt $a h))
  for (a, b) in divs do
    let (a, b) := (← Term.exprToSyntax a, ← Term.exprToSyntax b)
    evalTactic (← `(tactic| have := Nat.div_le_self $a $b))
  for (a, b) in ands do
    let (a, b) := (← Term.exprToSyntax a, ← Term.exprToSyntax b)
    evalTactic (← `(tactic| have := Nat.and_le_left (n := $a) (m := $b)))
    evalTactic (← `(tactic| have := Nat.and_le_right (n := $a) (m := $b)))

end Proven.Frontx
