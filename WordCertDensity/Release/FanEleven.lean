/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Release.BlockEleven
import WordCertDensity.Reference.FanMaximum

/-! # The second-moment fan ceiling for the analytic first release -/

namespace WordCertDensity.Reference

/-- The exact fan prefactor times the separately named depth-eleven ceiling. -/
noncomputable def fanEnergyElevenCeiling (m : ℕ) : ℝ :=
  (64 / 135) * energyElevenCeiling (m + 1)

/-- The actual fan at every level obeys the explicit first-release energy ceiling. -/
theorem fan_second_le_elevenCeiling (m : ℕ) :
    mean m (fun x => fan m x ^ 2) ≤ fanEnergyElevenCeiling m := by
  have h := mul_le_mul_of_nonneg_left (moment_two_le_energyElevenCeiling (m + 1))
    (by norm_num : (0 : ℝ) ≤ 64 / 135)
  rw [← fan_second_moment m] at h
  simpa only [Real.rpow_two, fanEnergyElevenCeiling] using h

/-- The explicit energy denominator is strictly positive at every level. -/
theorem fanEnergyElevenCeiling_pos (m : ℕ) : 0 < fanEnergyElevenCeiling m := by
  unfold fanEnergyElevenCeiling energyElevenCeiling
  positivity

end WordCertDensity.Reference
