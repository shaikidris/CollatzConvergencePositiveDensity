/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.DyadicBasin
import WordCertDensity.Release.TargetDensity

/-! # Exact positive-density criterion for a fixed target

The finite-hitting basin of a positive multiple of three is dyadic and has
zero natural density. The accepted actual-source theorem supplies positive
lower density for every other positive target at each clock above the threshold.
-/

namespace WordCertDensity.Density

/-- A positive fixed target has positive lower density at any admitted clock
exactly when it is not divisible by three. -/
theorem targetCriterion (target : ℕ) (htarget : 0 < target) (c : ℝ)
    (hc : criticalClock < c) :
    0 < lowerNaturalDensity (goodTarget target c) ↔ ¬ 3 ∣ target := by
  constructor
  · intro hpositive hdiv
    have hzero := lowerNaturalDensity_goodTarget_eq_zero_of_three_dvd hdiv htarget c
    rw [hzero] at hpositive
    exact (lt_irrefl (0 : ℝ) hpositive)
  · intro hdiv
    obtain ⟨d, hd, hbound⟩ := Release.admissibleTarget_elementaryDensity htarget hdiv
    exact lt_of_lt_of_le hd (hbound.2 c hc)

end WordCertDensity.Density
