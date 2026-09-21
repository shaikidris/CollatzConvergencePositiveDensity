/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Density.Elementary
import WordCertDensity.Sources.Main
import WordCertDensity.Construction.SeedScoreDomain
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # One positive density for every clock above the reference ratio -/

namespace WordCertDensity

open Filter
open scoped Topology

namespace Density

/-- The actual certified mixing envelope tends to zero on the natural levels. -/
theorem mixingError_tendsto : Tendsto Analytic.mixingError atTop (𝓝 0) := by
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 6)).comp
    tendsto_natCast_atTop_atTop
  have hmajor : Tendsto (fun m : ℕ =>
      (Analytic.mixingCoefficient : ℝ) * (m : ℝ) ^ (-6 : ℝ)) atTop (𝓝 0) := by
    simpa using hp.const_mul (Analytic.mixingCoefficient : ℝ)
  apply squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact (Analytic.mixingError_pos hm).le
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact Analytic.mixingError_le_order6 hm

/-- One coarse level pays the mixing debit for a fixed positive score, before any clock. -/
theorem exists_coarseLevel {W : ℝ} (hW : 0 < W) :
    ∃ m : ℕ, 2 ≤ m ∧ kappa * Analytic.mixingError m < W / 2 := by
  have hlim : Tendsto (fun m => kappa * Analytic.mixingError m) atTop (𝓝 0) := by
    simpa using mixingError_tendsto.const_mul kappa
  have hpaid := hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < W / 2))
  exact ((eventually_ge_atTop (2 : ℕ)).and hpaid).exists

/-- The actual persistent allocation score lies in the elementary density domain. -/
theorem canonicalSmallScore : SmallScore Construction.persistentRootScore := by
  refine ⟨Construction.persistentRootScore_domain.1, ?_⟩
  have hp : (2 : ℝ) ^ (27 : ℕ) ≤ 2 ^ (4096 : ℕ) :=
    pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hi := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 ^ (27 : ℕ)) hp
  have hscore := Construction.persistentRootScore_domain.2.le
  rw [← one_div] at hscore
  exact (hscore.trans hi).trans
    (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 27) (by positivity))

/-- Every paid coarse level gives the specified common bound for actual Collatz convergence. -/
theorem canonicalElementaryDensity (m : ℕ) (hm : 2 ≤ m)
    (hpaid : kappa * Analytic.mixingError m < Construction.persistentRootScore / 2) :
    EveryClockDensityBound (4 * Construction.persistentRootScore / (25 * (2 : ℝ) ^ m)) :=
  elementaryDensity 1 Construction.persistentRootScore canonicalSmallScore
    Sources.canonicalSources m hm hpaid

end Density

/-- One positive lower natural-density constant works for every fixed ordinary clock
strictly above 3/log(4/3), with all canonical analytic and source inputs discharged. -/
theorem collatz_common_positive_density : CommonClockDensity := by
  obtain ⟨m, hm, hpaid⟩ := Density.exists_coarseLevel
    Construction.persistentRootScore_domain.1
  exact (Density.canonicalElementaryDensity m hm hpaid).common

end WordCertDensity
