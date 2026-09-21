/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Review.DiagonalClock
import WordCertDensity.Sources.TargetPool

/-! # Positive density and vanishing clock loss for every admissible fixed target

Every positive target not divisible by three carries a target-dependent positive
lower density before every clock above the threshold, in both the elementary and
the separately named depth-eleven forms, and each such constant is retained
under an unspecified vanishing clock loss.

The constants are target-dependent and existential. No target-uniform constant
is claimed, no target is assumed to reach one, and no optimised recipe is used.
-/

namespace WordCertDensity.Release

open Filter
open scoped Topology

/-- Every admissible target has a positive elementary density before every larger clock. -/
theorem admissibleTarget_elementaryDensity {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ d : ℝ, 0 < d ∧ Density.TargetBound n d := by
  obtain ⟨W, hWpos, hWle, hsrc⟩ := Sources.admissibleTargetSources hn h3
  obtain ⟨m, hm, hpaid⟩ := Density.exists_coarseLevel hWpos
  have hbound := Density.elementaryDensity n W ⟨hWpos, hWle⟩ hsrc m hm hpaid
  exact ⟨_, hbound.1, hbound⟩

/-- Every admissible target also carries the accepted depth-eleven formula. -/
theorem admissibleTarget_depthElevenDensity {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ (W : ℝ) (m : ℕ), 0 < W ∧ 2 ≤ m ∧
      Density.TargetBound n (Density.secondElevenDensity W m) := by
  obtain ⟨W, hWpos, _, hsrc⟩ := Sources.admissibleTargetSources hn h3
  obtain ⟨m, hm, hpaid⟩ := Density.exists_coarseLevel hWpos
  exact ⟨W, m, hWpos, hm, Density.secondElevenDensity_target n W hWpos hsrc m hm hpaid⟩

/-- Each admissible target keeps its own constant under a vanishing clock loss. -/
theorem admissibleTarget_vanishingClock {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ d : ℝ, 0 < d ∧ ∃ η : ℕ → ℝ, (∀ x, 0 < η x) ∧ Antitone η ∧
      Tendsto η atTop (𝓝 0) ∧
      d ≤ lowerNaturalDensity {x : ℕ | 0 < x ∧
        ReachesWithin x n ((criticalClock + η x) * Real.log x)} := by
  obtain ⟨d, hd, hbound⟩ := admissibleTarget_elementaryDensity hn h3
  exact ⟨d, hd, Review.vanishingClock_of_bound n d hbound⟩

/-- The depth-eleven target constant is likewise retained under a vanishing loss. -/
theorem admissibleTarget_depthEleven_vanishingClock {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ (W : ℝ) (m : ℕ), 0 < W ∧ 2 ≤ m ∧
      0 < Density.secondElevenDensity W m ∧
      ∃ η : ℕ → ℝ, (∀ x, 0 < η x) ∧ Antitone η ∧ Tendsto η atTop (𝓝 0) ∧
        Density.secondElevenDensity W m ≤ lowerNaturalDensity {x : ℕ | 0 < x ∧
          ReachesWithin x n ((criticalClock + η x) * Real.log x)} := by
  obtain ⟨W, m, hWpos, hm, hbound⟩ := admissibleTarget_depthElevenDensity hn h3
  exact ⟨W, m, hWpos, hm, hbound.1, Review.vanishingClock_of_bound n _ hbound⟩

end WordCertDensity.Release
