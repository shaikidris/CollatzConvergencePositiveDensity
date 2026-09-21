/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Counting.RadialLimits
import Mathlib.Tactic.Linarith

/-! # Nonlinear radial conversion from actual shell mass to lower natural density -/

@[expose] public section

namespace WordCertDensity.Counting

open Filter
open scoped Topology

/-- The manuscript's nonlinear conversion of harmonic mass into ordinary natural density. -/
noncomputable def radial (u : ℝ) : ℝ := (32 / 225) * (Real.exp (2 * u) - 1)

/-- The radial conversion retains the printed linear consequence. -/
theorem radial_ge_linear (u : ℝ) : 64 * u / 225 ≤ radial u := by
  have h := Real.add_one_le_exp (2 * u)
  dsimp [radial]
  nlinarith

/-- Nonnegative mass gives a nonnegative radial bound. -/
theorem radial_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ radial u :=
  (by positivity : 0 ≤ 64 * u / 225).trans (radial_ge_linear u)

/-- Every positive mass gives a strictly positive radial bound. -/
theorem radial_pos {u : ℝ} (hu : 0 < u) : 0 < radial u :=
  (by positivity : 0 < 64 * u / 225).trans_le (radial_ge_linear u)

/-- Actual all-scale shell mass in a dyadically closed set gives the full nonlinear density bound. -/
theorem radialConversion (G : Set ℕ) (u : ℝ) (hclosed : DyadicallyClosed G)
    (hu : 0 ≤ u) (huu : u ≤ Real.log (3 / 2) / 2) (h : ShellMass G u) :
    radial u ≤ lowerNaturalDensity G := by
  by_cases hu0 : u = 0
  · simpa [radial, hu0] using lowerNaturalDensity_nonneg G
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hE : 1 < Real.exp (2 * u) := by
    simpa using Real.exp_lt_exp.mpr (by linarith : 0 < 2 * u)
  have hEu : Real.exp (2 * u) ≤ 3 / 2 := by
    have he := Real.exp_le_exp.mpr (by linarith : 2 * u ≤ Real.log (3 / 2))
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)] at he
  have ht : Tendsto (fun s : ℝ => (s - 1) * (32 / 225))
      (𝓝[<] (Real.exp (2 * u))) (𝓝 ((Real.exp (2 * u) - 1) * (32 / 225))) :=
    ((continuous_id.sub continuous_const).mul continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hbound : (Real.exp (2 * u) - 1) * (32 / 225) ≤ lowerNaturalDensity G := by
    apply le_of_tendsto ht
    have hlow : ∀ᶠ s : ℝ in 𝓝[<] (Real.exp (2 * u)), 1 < s :=
      mem_nhdsWithin_of_mem_nhds (lt_mem_nhds hE)
    have hhigh : ∀ᶠ s : ℝ in 𝓝[<] (Real.exp (2 * u)), s < Real.exp (2 * u) :=
      self_mem_nhdsWithin
    filter_upwards [hlow, hhigh] with s hs hse
    have hlog := Real.log_lt_log (by linarith : 0 < s) hse
    rw [Real.log_exp] at hlog
    exact inner_radial_density h hclosed hs (hse.le.trans hEu) (by linarith)
  simpa only [radial, mul_comm] using hbound

end WordCertDensity.Counting
