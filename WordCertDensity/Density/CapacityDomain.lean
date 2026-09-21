/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Density.Elementary
import WordCertDensity.Counting.CapacityMassDomain

/-! # The manuscript score range lies strictly inside the radial capacity domain -/

namespace WordCertDensity.Density

/-- Dividing the full score by the exact fan mean still leaves strict radial room. -/
theorem smallScore_capacity_domain {W : ℝ} (hW : SmallScore W) :
    W/(8/9 : ℝ) < Real.log (3/2)/2 ∧ Real.log (3/2)/2 < (2*Real.log 2)/2 := by
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3/2)
  norm_num at hlog
  have hscore : W/(8/9 : ℝ) < 1/8 := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 8/9)).2
    exact hW.2.trans_lt (by norm_num)
  have hcmp := Real.log_lt_log (by norm_num : (0 : ℝ) < 3/2)
    (by norm_num : (3/2 : ℝ) < 2)
  constructor <;> linarith

/-- The marked score remaining after the coarse mixing charge. -/
noncomputable def residual (W : ℝ) (m : ℕ) : ℝ :=
  max (W - kappa * Analytic.mixingError m) 0

/-- The actual residual lies between zero and the given score. -/
theorem residual_domain {W : ℝ} (hW : 0 ≤ W) {m : ℕ} (hm : 2 ≤ m) :
    0 ≤ residual W m ∧ residual W m ≤ W := by
  have hk : 0 ≤ kappa := by unfold kappa; positivity
  have he := (Analytic.mixingError_pos (show 1 ≤ m by omega)).le
  exact ⟨le_max_right _ _, max_le (sub_le_self _ (mul_nonneg hk he)) hW⟩

/-- The small score is strictly below total marked capacity. -/
theorem smallScore_paid {W : ℝ} (hW : SmallScore W) :
    W ≤ (8/9 : ℝ)*(2*Real.log 2) := by
  have h := smallScore_capacity_domain hW
  have hd : W/(8/9 : ℝ) < 2*Real.log 2 := by
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hp := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 8/9)).1 hd
  nlinarith

end WordCertDensity.Density
