/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.Survival
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Numerical guards for the survival deficit

These are the exact logarithmic, exponential and rational comparisons used by
the summable-deficit proof.
-/

@[expose] public section

namespace WordCertDensity.Construction

/-- The logarithmic rate pays the reciprocal 504 used in the integral bound. -/
theorem survival_log_rate_lower :
    (1 / 504 : ℝ) < Real.log survivalDeficitRate := by
  have h := Real.lt_log_one_add_of_pos (x := (1 / 503 : ℝ)) (by norm_num)
  norm_num [survivalDeficitRate] at h ⊢
  linarith

/-- The rational exponential-integral factor has the printed upper bound. -/
theorem survival_integral_factor_lt :
    1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
        2 / survivalDeficitExponent ^ 3 < 227 / 2000 := by
  norm_num [survivalDeficitExponent]

/-- The elementary Taylor lower bound proves the required exponential guard. -/
theorem survival_exp_guard : 2920 < Real.exp survivalDeficitExponent := by
  have h8 := Real.sum_le_exp_of_nonneg (x := (8 : ℝ)) (by norm_num) 17
  have hsmall := Real.add_one_le_exp (-1 / 64 : ℝ)
  have hrat : (2920 : ℝ) <
      (∑ k ∈ Finset.range 17, (8 : ℝ) ^ k / k.factorial) * (63 / 64 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have hprod :
      (∑ k ∈ Finset.range 17, (8 : ℝ) ^ k / k.factorial) * (63 / 64 : ℝ) ≤
        Real.exp 8 * Real.exp (-1 / 64) := by
    apply mul_le_mul h8
    · norm_num at hsmall ⊢
      exact hsmall
    · norm_num
    · exact Real.exp_nonneg 8
  calc
    (2920 : ℝ) <
        (∑ k ∈ Finset.range 17, (8 : ℝ) ^ k / k.factorial) * (63 / 64 : ℝ) := hrat
    _ ≤ Real.exp 8 * Real.exp (-1 / 64) := hprod
    _ = Real.exp survivalDeficitExponent := by
      rw [← Real.exp_add]
      congr 1
      norm_num [survivalDeficitExponent]

/-- The final rational loss budget is strictly below one twenty-fifth. -/
theorem survival_rational_budget :
    (2 / 2920 : ℝ) * (1 + 504 * (227 / 2000)) = 14551 / 365000 ∧
      (14551 / 365000 : ℝ) < 1 / 25 := by
  norm_num

end WordCertDensity.Construction
