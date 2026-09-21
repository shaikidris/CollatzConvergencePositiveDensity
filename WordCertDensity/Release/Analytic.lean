/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Release.SecondDensity

/-! # Analytic release with a depth-eleven density formula

This entry point uses the classical source construction. It does not assert an
effective cutoff, an endpoint clock, or any of the manuscript's optimized constants.
-/

namespace WordCertDensity.Release

/-- The classical common positive-density theorem for every strictly larger clock. -/
theorem common_positive_density : CommonClockDensity := collatz_common_positive_density

/-- One canonical paid level supplies the depth-eleven formula for every larger clock. -/
theorem depthEleven_common_density :
    ∃ m : ℕ, 2 ≤ m ∧
      Density.kappa * Analytic.mixingError m < Construction.persistentRootScore / 2 ∧
      EveryClockDensityBound (Density.secondElevenDensity Construction.persistentRootScore m) :=
  Density.exists_canonicalSecondDensity

end WordCertDensity.Release
