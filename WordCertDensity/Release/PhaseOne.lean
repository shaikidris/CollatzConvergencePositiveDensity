/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Density.TargetCriterion
import WordCertDensity.Release.FractionalDensity
import WordCertDensity.Release.NumericalClock
import WordCertDensity.Release.RootCorollary
import WordCertDensity.Review.DiagonalClock

/-! # The Phase 1 entry point

Every theorem of the adopted Phase 1 scope, restated once in a single place so
that the literal statements can be read against the release notes. Each is a
re-statement of an already accepted root; nothing new is proved here.

## What is in scope

* PH1-01 common-clock density, and PH1-03 the depth-eleven formula.
* PH1-06 every admissible fixed target, the exact multiple-of-three criterion,
  and the positive individual-root corollary.
* PH1-07 vanishing clock loss, for convergence to one and for each target.
* PH1-08 the numerical clock and the fixed-level fractional density.

## What is NOT in scope

* PH1-04 is only partly covered: E03a (entropy increments, the monotone limit
  with its tail bound, and `rate 1 = 0`) is still outstanding, and E03b, E01,
  E02 and E04 are deferred.
* PH1-05 is deferred in full: neither the profile specialisation nor the
  complementary capacity chain is Phase 1.
* No optimised recipe appears anywhere below. `fmDensity`, `cFM`, `cFM16` and
  `ccomp` are Phase 2, and no comparison against them is claimed.
* Every density constant below is existential, not evaluated. No effective
  cutoff and no decay rate is asserted.
-/

namespace WordCertDensity.Release.PhaseOne

open Filter Construction
open scoped Topology

/-! ### PH1-01 and PH1-03 — common density -/

/-- One positive lower density before every clock above the threshold. -/
theorem common_density : CommonClockDensity := common_positive_density

/-- The separately named depth-eleven formula at one paid coarse level. -/
theorem depthEleven_density :
    ∃ m : ℕ, 2 ≤ m ∧
      Density.kappa * Analytic.mixingError m < persistentRootScore / 2 ∧
      EveryClockDensityBound (Density.secondElevenDensity persistentRootScore m) :=
  depthEleven_common_density

/-! ### PH1-08 — the numerical clock -/

/-- The reference threshold lies strictly below the printed rational clock. -/
theorem numerical_clock : criticalClock < 10431 / 1000 := criticalClock_lt_numerical

/-! ### PH1-06 — every admissible fixed target -/

/-- Every positive target not divisible by three has its own positive density. -/
theorem every_admissible_target {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ d : ℝ, 0 < d ∧ Density.TargetBound n d :=
  admissibleTarget_elementaryDensity hn h3

/-- The same targets also carry the accepted depth-eleven formula. -/
theorem every_admissible_target_depthEleven {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ (W : ℝ) (m : ℕ), 0 < W ∧ 2 ≤ m ∧
      Density.TargetBound n (Density.secondElevenDensity W m) :=
  admissibleTarget_depthElevenDensity hn h3

/-- The exact obstruction: positive density holds precisely off the multiples of three. -/
theorem target_criterion (target : ℕ) (htarget : 0 < target) (c : ℝ)
    (hc : criticalClock < c) :
    0 < lowerNaturalDensity (goodTarget target c) ↔ ¬ 3 ∣ target :=
  Density.targetCriterion target htarget c hc

/-- Some actual canonical root has a positive singleton score and its own constant. -/
theorem individual_root :
    ∃ r ∈ seedRootPool survivalSeedSize
      (seedConductor survivalSeedSize (seedStartupIndex survivalSeedSize (by rfl))),
      ∃ W : ℝ, Density.SmallScore W ∧
        W ≤ persistentSeedMark survivalSeedSize (by rfl) r / r ∧
        ∃ d : ℝ, Density.TargetBound r d :=
  positive_individual_root

/-! ### PH1-07 — vanishing clock loss -/

/-- Convergence to one survives a positive antitone loss tending to zero. -/
theorem common_vanishing_clock :
    ∃ d : ℝ, 0 < d ∧ ∃ η : ℕ → ℝ,
      (∀ x, 0 < η x) ∧ Antitone η ∧ Tendsto η atTop (𝓝 0) ∧
      d ≤ lowerNaturalDensity {x : ℕ | 0 < x ∧
        ReachesWithin x 1 ((criticalClock + η x) * Real.log x)} :=
  Review.vanishing_clock_common_density

/-- Each admissible target keeps its own constant under a vanishing loss. -/
theorem target_vanishing_clock {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ d : ℝ, 0 < d ∧ ∃ η : ℕ → ℝ,
      (∀ x, 0 < η x) ∧ Antitone η ∧ Tendsto η atTop (𝓝 0) ∧
      d ≤ lowerNaturalDensity {x : ℕ | 0 < x ∧
        ReachesWithin x n ((criticalClock + η x) * Real.log x)} :=
  admissibleTarget_vanishingClock hn h3

/-! ### PH1-08 — the fixed-level fractional density -/

/-- The canonical score carries the order-three-halves formula at a paid level. -/
theorem fractional_density :
    ∃ m : ℕ, 2 ≤ m ∧
      EveryClockDensityBound
        (Density.fractionalElevenDensity persistentRootScore m) :=
  Density.exists_canonicalFractionalDensity

/-- Every admissible fixed target carries the fractional formula too. -/
theorem every_admissible_target_fractional {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ (W : ℝ) (m : ℕ), 0 < W ∧ 2 ≤ m ∧
      Density.TargetBound n (Density.fractionalElevenDensity W m) :=
  Density.admissibleTarget_fractionalElevenDensity hn h3

end WordCertDensity.Release.PhaseOne
