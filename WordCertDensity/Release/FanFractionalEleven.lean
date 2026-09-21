/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Release.BlockEleven
import WordCertDensity.Reference.FanCoset

/-! # Fractional fan ceiling from the accepted depth-eleven certificate -/

namespace WordCertDensity.Reference

/-- The exact fan prefactor times the accepted propagated order-three-halves ceiling. -/
noncomputable def fanFractionalElevenCeiling (m : ℕ) : ℝ :=
  (3 * (8 / 9 : ℝ) ^ (3 / 2 : ℝ) / (1 + (2 : ℝ) ^ (3 / 2 : ℝ))) *
    fractionalElevenCeiling (m + 1)

/-- The actual fractional fan moment obeys the depth-eleven ceiling at every level. -/
theorem fan_fractional_le_elevenCeiling (m : ℕ) :
    mean m (fun x => fan m x ^ (3 / 2 : ℝ)) ≤ fanFractionalElevenCeiling m := by
  rw [fan_moment_identity (3 / 2) (by norm_num) m]
  exact mul_le_mul_of_nonneg_left
    (moment_fractional_le_fractionalElevenCeiling (m + 1)) (by positivity)

/-- The explicit fractional fan ceiling is positive. -/
theorem fanFractionalElevenCeiling_pos (m : ℕ) : 0 < fanFractionalElevenCeiling m := by
  unfold fanFractionalElevenCeiling fractionalElevenCeiling
  positivity

end WordCertDensity.Reference
