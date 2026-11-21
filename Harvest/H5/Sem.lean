/- Harvest/H5/Sem: parser-behaviour WITNESSES and macro shapes. Each `example`/theorem is checked by Lean's own parser +
elaborator when this file is compiled, so the statement fixes which parse Lean chose (the distinguishing value is in the comment). -/
namespace Harvest.H5

-- left assoc: right grouping would give 9 / 50 / 6
theorem sub_left : (10 - 3 - 2 : Nat) = 5 := by decide
theorem div_left : (100 / 10 / 5 : Nat) = 2 := by decide
theorem mul_mod_left : (2 * 3 % 4 : Nat) = 2 := by decide
-- right assoc `^`: (2^3)^2 = 64
theorem pow_right : (2 ^ 3 ^ 2 : Nat) = 512 := by decide
-- `*` over `+`; `<<<` over `+`; `+` over `&&&`
theorem mul_over_add : (1 + 2 * 3 : Nat) = 7 := by decide
theorem shl_over_add : (1 <<< 2 + 1 : Nat) = 5 := by decide
theorem add_over_and : (6 &&& 3 + 1 : Nat) = 4 := by decide
theorem add_over_cons : (1 + 1 :: [] : List Nat) = [2] := by decide
-- prefix `-` (75) is below `^` (80): -(2^2)
theorem neg_pow : (-2 ^ 2 : Int) = -4 := by decide
-- Bool: `!` binds its operand at 40, above `&&` (35); `&&` over `||`, `||` over nothing; `^^` (33) below `&&`
theorem not_and : (!false && false) = false := by decide
theorem and_over_or : (true || false && false) = true := by decide
-- pipes
theorem pipe_l : (Nat.succ <| Nat.succ <| 1) = 3 := rfl
theorem pipe_r : (1 |> Nat.succ |> Nat.succ) = 3 := rfl
theorem pipe_arith : (Nat.succ <| 1 + 2) = 4 := rfl

-- macro shapes (all by `rfl`): the operators are abbreviations for the instance functions
theorem pipe_app (f : α → β) (x : α) : (f <| x) = f x := rfl
theorem pipe2_app (f : α → β) (x : α) : (x |> f) = f x := rfl
theorem comp_app (f : β → γ) (g : α → β) (x : α) : (f ∘ g) x = f (g x) := rfl
theorem cons_def (a : α) (l : List α) : (a :: l) = List.cons a l := rfl
theorem append_def (a b : List α) : (a ++ b) = List.append a b := rfl
theorem bne_def (a b : UInt64) : (a != b) = !(a == b) := rfl
theorem and_true : ∀ b : Bool, (true && b) = b := fun _ => rfl
theorem and_false : ∀ b : Bool, (false && b) = false := fun _ => rfl
theorem or_true : ∀ b : Bool, (true || b) = true := fun _ => rfl
theorem or_false : ∀ b : Bool, (false || b) = b := fun _ => rfl
theorem u64_and (a b : UInt64) : (a &&& b) = UInt64.land a b := rfl
theorem u64_or (a b : UInt64) : (a ||| b) = UInt64.lor a b := rfl
theorem u64_xor (a b : UInt64) : (a ^^^ b) = UInt64.xor a b := rfl
theorem u64_add (a b : UInt64) : (a + b) = UInt64.add a b := rfl
theorem u64_sub (a b : UInt64) : (a - b) = UInt64.sub a b := rfl
theorem u64_mul (a b : UInt64) : (a * b) = UInt64.mul a b := rfl
theorem u64_div (a b : UInt64) : (a / b) = UInt64.div a b := rfl
theorem u64_mod (a b : UInt64) : (a % b) = UInt64.mod a b := rfl
theorem u64_shl (a b : UInt64) : (a <<< b) = UInt64.shiftLeft a b := rfl
theorem u64_shr (a b : UInt64) : (a >>> b) = UInt64.shiftRight a b := rfl
theorem u64_beq_iff (a b : UInt64) : (a == b) = true ↔ a = b := by simp
theorem u64_lt_iff (a b : UInt64) : decide (a < b) = true ↔ a.toNat < b.toNat := by simp [UInt64.lt_iff_toNat_lt]
theorem u64_le_iff (a b : UInt64) : decide (a ≤ b) = true ↔ a.toNat ≤ b.toNat := by simp [UInt64.le_iff_toNat_le]

end Harvest.H5
