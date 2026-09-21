/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Density.Diagonal
import WordCertDensity.Release.Analytic

/-! # A vanishing unspecified clock loss with the same positive density constant -/

namespace WordCertDensity.Review

open Filter
open scoped Topology

/-- A common target density bound survives a nonincreasing positive clock loss tending to zero. -/
theorem vanishingClock_of_bound (target : ℕ) (d : ℝ) (hd : Density.TargetBound target d) :
    ∃ η : ℕ → ℝ, (∀ x, 0 < η x) ∧ Antitone η ∧ Tendsto η atTop (𝓝 0) ∧
      d ≤ lowerNaturalDensity {x : ℕ | 0 < x ∧
        ReachesWithin x target ((criticalClock+η x)*Real.log x)} := by
  let loss : ℕ → ℝ := fun j => 1/((j : ℝ)+1)
  have hpos (j : ℕ) : 0 < loss j := by dsimp [loss]; positivity
  have hanti : Antitone loss := by
    intro i j hij
    apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (i : ℝ)+1)
    exact_mod_cast Nat.add_le_add_right hij 1
  let A : ℕ → Set ℕ := fun j => goodTarget target (criticalClock+loss j)
  have hA : Antitone A := fun i j hij =>
    goodTarget_mono target (add_le_add (le_refl criticalClock) (hanti hij))
  have hbound (j : ℕ) : d ≤ lowerNaturalDensity (A j) :=
    hd.2 _ (lt_add_of_pos_right _ (hpos j))
  obtain ⟨k, hk, hkt, hden⟩ := lowerNaturalDensity_diagonal A d hA hbound
  refine ⟨fun x => loss (k x), fun x => hpos (k x), hanti.comp_monotone hk,
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hkt, ?_⟩
  exact hden

/-- One positive density of convergent integers has an unspecified vanishing loss above the clock threshold. -/
theorem vanishing_clock_common_density :
    ∃ d : ℝ, 0 < d ∧ ∃ η : ℕ → ℝ,
      (∀ x, 0 < η x) ∧ Antitone η ∧ Tendsto η atTop (𝓝 0) ∧
      d ≤ lowerNaturalDensity {x : ℕ | 0 < x ∧
        ReachesWithin x 1 ((criticalClock+η x)*Real.log x)} := by
  obtain ⟨d, hd, hclock⟩ := Release.common_positive_density
  exact ⟨d, hd, vanishingClock_of_bound 1 d ⟨hd, hclock⟩⟩

/-- The depth-eleven density constant is retained unchanged under a vanishing clock loss. -/
theorem depthEleven_vanishing_clock :
    ∃ m : ℕ, 2 ≤ m ∧
      Density.kappa * Analytic.mixingError m < Construction.persistentRootScore/2 ∧
      0 < Density.secondElevenDensity Construction.persistentRootScore m ∧
      ∃ η : ℕ → ℝ, (∀ x, 0 < η x) ∧ Antitone η ∧ Tendsto η atTop (𝓝 0) ∧
        Density.secondElevenDensity Construction.persistentRootScore m ≤
          lowerNaturalDensity {x : ℕ | 0 < x ∧
            ReachesWithin x 1 ((criticalClock+η x)*Real.log x)} := by
  obtain ⟨m, hm, hpaid, hd⟩ := Release.depthEleven_common_density
  exact ⟨m, hm, hpaid, hd.1, vanishingClock_of_bound 1 _ hd⟩

end WordCertDensity.Review
