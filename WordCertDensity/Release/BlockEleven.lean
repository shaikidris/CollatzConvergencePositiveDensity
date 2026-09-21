/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.BlockCeilings
import WordCertDensity.Certificates.LevelElevenMoments
import WordCertDensity.Certificates.InitialFractionalBounds

/-! # All-level moment ceilings from accepted depth-eleven certificates -/

namespace WordCertDensity.Reference

/-- Fully numerical depth-eleven second-moment ceiling, with a coarse short remainder. -/
noncomputable def energyElevenCeiling (n : ℕ) : ℝ := (3167 / 500) ^ (n / 11) * (5 / 3) ^ (n % 11)

/-- Fully numerical fractional ceiling; separate from the manuscript's twelve-step formula. -/
noncomputable def fractionalElevenCeiling (n : ℕ) : ℝ :=
  (259093 / 125000) ^ (n / 11) * (1276143 / 1000000) ^ (n % 11)

/-- The accepted second-moment certificate propagates to every natural level. -/
theorem moment_two_le_energyElevenCeiling (n : ℕ) : moment 2 n ≤ energyElevenCeiling n := by
  apply (moment_block_ceiling 2 (by norm_num) 11 (3167 / 500) (by positivity)
    Certificates.energy_eleven n).trans
  exact mul_le_mul_of_nonneg_left
    (moment_single_ceiling 2 (by norm_num) (5 / 3) (by positivity)
      Certificates.energy_one.le (n % 11)) (by positivity)

/-- The accepted fractional certificate propagates to every natural level. -/
theorem moment_fractional_le_fractionalElevenCeiling (n : ℕ) :
    moment (3 / 2) n ≤ fractionalElevenCeiling n := by
  apply (moment_block_ceiling (3 / 2) (by norm_num) 11 (259093 / 125000) (by positivity)
    Certificates.fractional_eleven n).trans
  exact mul_le_mul_of_nonneg_left
    (moment_single_ceiling (3 / 2) (by norm_num) (1276143 / 1000000) (by positivity)
      Certificates.fractional_one (n % 11)) (by positivity)

end WordCertDensity.Reference
