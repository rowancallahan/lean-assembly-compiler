/- Harvest/H5/Wide: UInt64 totality facts nano's evaluator relies on (division by zero, shift counts), ∀-quantified. DRAFT. -/
namespace Harvest.H5
theorem u64_div_zero (x : UInt64) : x / 0 = 0 := by simp
theorem u64_mod_zero (x : UInt64) : x % 0 = x := by simp
end Harvest.H5
