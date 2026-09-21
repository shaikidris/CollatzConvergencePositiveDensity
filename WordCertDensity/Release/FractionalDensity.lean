/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Release.FanFractionalEleven
import WordCertDensity.Release.FanEleven
import WordCertDensity.Density.ThreeBranchSources
import WordCertDensity.Release.TargetDensity

/-! # A fixed-level fractional density from the accepted depth-eleven ceiling

The three-branch mass is a maximum, so its order-three-halves branch alone
already gives a positive fixed-level mass once the accepted depth-eleven
fractional fan ceiling is supplied. Radial conversion then turns that mass into
a positive lower density before every clock above the threshold.

Every certified input is a depth at most eleven. The variance and maximum
inputs are deliberately conservative: only the fractional branch is used, so
loosening them cannot destroy positivity.
-/

namespace WordCertDensity.Density

open Filter
open scoped Topology

/-- The fan variance is dominated by the accepted depth-eleven energy ceiling. -/
theorem fan_variance_le_energyEleven (m : ℕ) :
    Reference.mean m (fun r => (Reference.fan m r - (8 / 9 : ℝ)) ^ 2) ≤
      Reference.fanEnergyElevenCeiling m := by
  have hexp : (fun r => (Reference.fan m r - (8 / 9 : ℝ)) ^ 2) =
      fun r => Reference.fan m r ^ 2 - ((16 / 9) * Reference.fan m r - 64 / 81) := by
    funext r
    ring
  rw [hexp, Reference.mean_sub, Reference.mean_sub, Reference.mean_mul,
    Reference.mean_const, Reference.mean_fan]
  have h := Reference.fan_second_le_elevenCeiling m
  norm_num
  linarith

/-- A paid coarse level leaves a strictly positive residual score. -/
theorem residual_pos {W : ℝ} {m : ℕ} (hW : 0 < W)
    (hpaid : kappa * Analytic.mixingError m < W / 2) : 0 < residual W m :=
  lt_max_iff.mpr (Or.inl (by linarith))

/-- The order-three-halves branch of the three-branch mass at a paid level. -/
noncomputable def fractionalElevenMass (W : ℝ) (m : ℕ) : ℝ :=
  residual W m ^ 3 /
    ((2 * Real.log 2) ^ 2 * Reference.fanFractionalElevenCeiling m ^ 2)

/-- Positive scores give a positive fractional mass. -/
theorem fractionalElevenMass_pos {W : ℝ} {m : ℕ} (hW : 0 < W)
    (hpaid : kappa * Analytic.mixingError m < W / 2) :
    0 < fractionalElevenMass W m := by
  have hr := residual_pos hW hpaid
  have hB := Reference.fanFractionalElevenCeiling_pos m
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_pos (pow_pos hr 3)
    (mul_pos (pow_pos (by linarith) 2) (pow_pos hB 2))

/-- Every strict sub-bound of the fractional mass is present at all large cutoffs. -/
theorem fractionalEleven_shellMass (target : ℕ) (W : ℝ) (hW : SmallScore W)
    (hsrc : Sources.AllScaleSources target W) (c : ℝ) (hc : criticalClock < c)
    (m : ℕ) (hm : 2 ≤ m) (u : ℝ) (hu : 0 ≤ u) (hlt : u < fractionalElevenMass W m) :
    Counting.ShellMass (goodTarget target c) u := by
  intro Λ hΛ
  have hV := Reference.fanEnergyElevenCeiling_pos m
  have hB := Reference.fanFractionalElevenCeiling_pos m
  have hS : 0 < Reference.fanMaximum m + 1 :=
    lt_of_le_of_lt (Reference.fanMaximum_nonneg m) (by linarith)
  have hmass : u < Counting.threeBranchMass (8 / 9)
      (Reference.fanEnergyElevenCeiling m) (Reference.fanMaximum m + 1)
      (Reference.fanFractionalElevenCeiling m) (2 * Real.log 2) (residual W m) := by
    refine hlt.trans_le ?_
    unfold Counting.threeBranchMass fractionalElevenMass
    exact le_max_right _ _
  obtain ⟨A, a, R, hR, hfin⟩ := threeBranch_sources target W hW hsrc c hc m hm
    (Reference.fanEnergyElevenCeiling m) (Reference.fanMaximum m + 1)
    (Reference.fanFractionalElevenCeiling m) hV hS hB
    (fan_variance_le_energyEleven m)
    (fun r => by linarith [Reference.fan_le_maximum m r])
    (Reference.fan_fractional_le_elevenCeiling m) u hu hmass Λ hΛ
  filter_upwards [hfin, eventually_gt_atTop (0 : ℝ)] with X hX hpos
  refine ⟨A X, a X, ?_, hX.2.2.le⟩
  intro x hx
  obtain ⟨ho, hG, hlo, hhi, hn, hw⟩ := hX.1 x hx
  exact ⟨ho, hG, hlo, hhi.trans (mul_lt_mul_of_pos_right hX.2.1 hpos), hn, hw⟩

/-- A strict sub-bound clipped to the radial conversion domain. -/
noncomputable def fractionalElevenRadialMass (W : ℝ) (m : ℕ) : ℝ :=
  min (fractionalElevenMass W m / 2) (Real.log (3 / 2) / 2)

/-- The separately named depth-eleven fractional density formula. -/
noncomputable def fractionalElevenDensity (W : ℝ) (m : ℕ) : ℝ :=
  Counting.radial (fractionalElevenRadialMass W m)

/-- Actual all-scale sources give the fractional formula at every larger clock. -/
theorem fractionalElevenDensity_target (target : ℕ) (W : ℝ) (hW : SmallScore W)
    (hsrc : Sources.AllScaleSources target W) (m : ℕ) (hm : 2 ≤ m)
    (hpaid : kappa * Analytic.mixingError m < W / 2) :
    TargetBound target (fractionalElevenDensity W m) := by
  have hp := fractionalElevenMass_pos hW.1 hpaid
  have hl : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  have hpos : 0 < fractionalElevenRadialMass W m := lt_min (half_pos hp) (half_pos hl)
  have hlt : fractionalElevenRadialMass W m < fractionalElevenMass W m :=
    (min_le_left _ _).trans_lt (by linarith)
  refine ⟨Counting.radial_pos hpos, ?_⟩
  intro c hc
  exact Counting.radialConversion (goodTarget target c) _
    (goodTarget_dyadicallyClosed hc) hpos.le (min_le_right _ _)
    (fractionalEleven_shellMass target W hW hsrc c hc m hm _ hpos.le hlt)

/-- The canonical score gives a positive fractional density before every clock. -/
theorem exists_canonicalFractionalDensity :
    ∃ m : ℕ, 2 ≤ m ∧
      EveryClockDensityBound
        (fractionalElevenDensity Construction.persistentRootScore m) := by
  obtain ⟨m, hm, hpaid⟩ := exists_coarseLevel Construction.persistentRootScore_domain.1
  exact ⟨m, hm, fractionalElevenDensity_target 1 Construction.persistentRootScore
    canonicalSmallScore Sources.canonicalSources m hm hpaid⟩

/-- Every admissible fixed target also carries the fractional formula. -/
theorem admissibleTarget_fractionalElevenDensity {n : ℕ} (hn : 0 < n) (h3 : ¬ 3 ∣ n) :
    ∃ (W : ℝ) (m : ℕ), 0 < W ∧ 2 ≤ m ∧
      TargetBound n (fractionalElevenDensity W m) := by
  obtain ⟨W, hWpos, hWle, hsrc⟩ := Sources.admissibleTargetSources hn h3
  obtain ⟨m, hm, hpaid⟩ := exists_coarseLevel hWpos
  exact ⟨W, m, hWpos, hm,
    fractionalElevenDensity_target n W ⟨hWpos, hWle⟩ hsrc m hm hpaid⟩

end WordCertDensity.Density
