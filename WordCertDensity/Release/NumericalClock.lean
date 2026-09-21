/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Release.Analytic
import WordCertDensity.Construction.ClockCheckpoint

/-! # The accepted density constant at the printed numerical clock

The reference threshold is strictly below the rational clock `10431/1000`, so
every accepted common-clock bound specialises to that single printed value.

This is the Phase 1 variant. It uses the accepted depth-eleven formula, not the
manuscript's optimised `fmDensity` recipe, so it does not close the blueprint's
`numericalClock` contract.
-/

namespace WordCertDensity.Release

/-- The reference threshold is strictly below the printed rational clock. -/
theorem criticalClock_lt_numerical : criticalClock < 10431 / 1000 := by
  have hlow := Construction.clock_log_four_thirds_lower
  have hpos : (0 : ℝ) < Real.log (4 / 3) := lt_trans (by norm_num) hlow
  have hdef : criticalClock = 3 / Real.log (4 / 3 : ℝ) := rfl
  rw [hdef, div_lt_iff₀ hpos]
  linarith

/-- The accepted depth-eleven density constant holds at the printed clock. -/
theorem depthEleven_numericalClock :
    ∃ m : ℕ, 2 ≤ m ∧
      Density.kappa * Analytic.mixingError m < Construction.persistentRootScore / 2 ∧
      0 < Density.secondElevenDensity Construction.persistentRootScore m ∧
      Density.secondElevenDensity Construction.persistentRootScore m ≤
        lowerNaturalDensity (good (10431 / 1000)) := by
  obtain ⟨m, hm, hpaid, hd⟩ := depthEleven_common_density
  exact ⟨m, hm, hpaid, hd.1, hd.2 _ criticalClock_lt_numerical⟩

/-- The classical common constant also holds at the printed clock. -/
theorem common_numericalClock :
    ∃ d : ℝ, 0 < d ∧ d ≤ lowerNaturalDensity (good (10431 / 1000)) := by
  obtain ⟨d, hd, hclock⟩ := common_positive_density
  exact ⟨d, hd, hclock _ criticalClock_lt_numerical⟩

end WordCertDensity.Release
