/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Release.FanEleven
import WordCertDensity.Counting.CoarseSources

/-! # Fixed-level second-moment mass and its harmonic limit -/

namespace WordCertDensity.Density

open Filter
open scoped Topology

/-- A fixed-score mass ceiling, separate from the manuscript optimizers. -/
noncomputable def secondElevenMass (W : ℝ) (m : ℕ) : ℝ :=
  (W / 2) ^ 2 / ((2 * Real.log 2) * Reference.fanEnergyElevenCeiling m)

/-- Every positive score has a positive second-moment mass ceiling. -/
theorem secondElevenMass_pos {W : ℝ} (hW : 0 < W) (m : ℕ) :
    0 < secondElevenMass W m := by
  unfold secondElevenMass
  exact div_pos (sq_pos_of_pos (half_pos hW))
    (mul_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
      (Reference.fanEnergyElevenCeiling_pos m))

/-- The finite harmonic denominator converges at each fixed coarse level. -/
theorem secondElevenMass_tendsto (W : ℝ) (m : ℕ) {R : ℝ → ℝ}
    (hR : Tendsto R atTop (𝓝 16)) :
    Tendsto (fun X : ℝ => (W / 2) ^ 2 /
      (((3 : ℝ) ^ m / X + Real.log (R X) / 2) * Reference.fanEnergyElevenCeiling m))
      atTop (𝓝 (secondElevenMass W m)) := by
  have hden : (2 * Real.log 2) * Reference.fanEnergyElevenCeiling m ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
      (Reference.fanEnergyElevenCeiling_pos m))
  exact tendsto_const_nhds.div
    ((Counting.fixed_harmonic_coefficient_tendsto m hR).mul_const _) hden

end WordCertDensity.Density
