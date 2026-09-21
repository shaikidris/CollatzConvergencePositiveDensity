/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.Fan

/-! # Table-free maximum and mean bounds for the actual fan -/

namespace WordCertDensity.Reference

/-- Positive summation of the elementary marker cap gives the fan maximum bound. -/
theorem fan_le_two_pow (m : ℕ) (x : ZMod (3^m)) : fan m x ≤ (8/9 : ℝ)*2^m := by
  calc
    _ ≤ ∑' j : ℕ, (4 : ℝ)^(-(j : ℤ))*((2/3 : ℝ)*2^m) :=
      (fan_summable m x).tsum_le_tsum
        (fun j => mul_le_mul_of_nonneg_left (marker_le_two_pow m _) (by positivity))
        (fanCoefficient_hasSum.summable.mul_right _)
    _ = _ := by rw [tsum_mul_right, fanCoefficient_hasSum.tsum_eq]; ring

/-- The prepared elementary fan handoff, requiring no finite moment table. -/
theorem fanElementary (m : ℕ) : mean m (fan m) = 8/9 ∧
    ∀ x, 0 ≤ fan m x ∧ fan m x ≤ (8/9 : ℝ)*2^m :=
  ⟨mean_fan m, fun x => ⟨fan_nonneg m x, fan_le_two_pow m x⟩⟩

end WordCertDensity.Reference
