/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.StartupSearch

/-! # Numerical lower bounds for the exact startup residual -/

namespace WordCertDensity.Construction

/-- The retained integer rate denominator fits below its stated binary bound. -/
theorem startupRateDenominator_lt : startupRateDenominator < 2 ^ 1575 := by
  calc
    _ < 2 ^ 11 * (2 ^ 17) ^ 92 := by
      unfold startupRateDenominator
      gcongr <;> norm_num
    _ = _ := by rw [← pow_mul, ← pow_add]

/-- The common residual denominator, before any cancellation, has the
manuscript's binary bound for every index, including zero. -/
theorem startupResidual_denominator_lt (n : ℕ) :
    25 * startupRateDenominator ^ n * (startupRateDenominator - startupRateNumerator) ^ 4 <
      2 ^ (1575 * n + 6305) := by
  have hdpos : 0 < startupRateDenominator := startupRate_integers.1.trans startupRate_integers.2
  have hepos : 0 < startupRateDenominator - startupRateNumerator :=
    Nat.sub_pos_of_lt startupRate_integers.2
  have hd := startupRateDenominator_lt.le
  have he : startupRateDenominator - startupRateNumerator ≤ 2 ^ 1575 :=
    (Nat.sub_le _ _).trans hd
  calc
    _ < 2 ^ 5 * startupRateDenominator ^ n *
        (startupRateDenominator - startupRateNumerator) ^ 4 :=
      Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_right (by norm_num : 25 < 2 ^ 5) (Nat.pow_pos hdpos))
        (Nat.pow_pos hepos)
    _ ≤ 2 ^ 5 * (2 ^ 1575) ^ n * (2 ^ 1575) ^ 4 := by gcongr
    _ = _ := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      omega

/-- The generic integer residual lower bound specialized to the actual rate. -/
theorem startup_residual_integer_lower (t n : ℕ)
    (hpos : 0 < (24 / 25 : ℝ) - (2 : ℝ) ^ t * seedVariationTail n) :
    1 / (25 * (startupRateDenominator : ℝ) ^ n *
      ((startupRateDenominator - startupRateNumerator : ℕ) : ℝ) ^ 4) ≤
      (24 / 25 : ℝ) - (2 : ℝ) ^ t * seedVariationTail n := by
  rw [seedVariationTail_exact, seedVariationRate_fraction] at hpos ⊢
  exact cubicTail_residual_lower t n _ _ startupRate_integers.2 hpos

/-- Literal sharp binary denominator consequence of R.denominator. -/
theorem startup_residual_binary_lower (t n : ℕ)
    (hpos : 0 < (24 / 25 : ℝ) - (2 : ℝ) ^ t * seedVariationTail n) :
    ((2 : ℝ) ^ (1575 * n + 6305))⁻¹ <
      (24 / 25 : ℝ) - (2 : ℝ) ^ t * seedVariationTail n := by
  have hdpos : 0 < startupRateDenominator := startupRate_integers.1.trans startupRate_integers.2
  have hepos := Nat.sub_pos_of_lt startupRate_integers.2
  have hdenpos : (0 : ℝ) < 25 * (startupRateDenominator : ℝ) ^ n *
      ((startupRateDenominator - startupRateNumerator : ℕ) : ℝ) ^ 4 := by positivity
  have hden : 25 * (startupRateDenominator : ℝ) ^ n *
      ((startupRateDenominator - startupRateNumerator : ℕ) : ℝ) ^ 4 <
      (2 : ℝ) ^ (1575 * n + 6305) := by exact_mod_cast startupResidual_denominator_lt n
  have h := one_div_lt_one_div_of_lt hdenpos hden
  rw [one_div] at h
  exact h.trans_le (startup_residual_integer_lower t n hpos)

/-- The weaker retained residual bound remains available for later comparisons. -/
theorem startup_residual_retained_lower (t n : ℕ)
    (hpos : 0 < (24 / 25 : ℝ) - (2 : ℝ) ^ t * seedVariationTail n) :
    ((2 : ℝ) ^ (1575 * n + 7324))⁻¹ <
      (24 / 25 : ℝ) - (2 : ℝ) ^ t * seedVariationTail n := by
  have hp : (2 : ℝ) ^ (1575 * n + 6305) < (2 : ℝ) ^ (1575 * n + 7324) :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  have h := one_div_lt_one_div_of_lt (by positivity) hp
  simp only [one_div] at h
  exact h.trans (startup_residual_binary_lower t n hpos)

/-- The whole residual at the computable least startup; no rounding or
reduced-denominator replacement is made. -/
noncomputable def startupResidual (t : ℕ) (ht : 25637 ≤ t) : ℝ :=
  24 / 25 - (2 : ℝ) ^ t * seedVariationTail (startupIndex t ht)

/-- Both numerical bounds hold for the selected residual without a positivity premise. -/
theorem startupResidual_bounds (t : ℕ) (ht : 25637 ≤ t) :
    ((2 : ℝ) ^ (1575 * startupIndex t ht + 7324))⁻¹ < startupResidual t ht ∧
    ((2 : ℝ) ^ (1575 * startupIndex t ht + 6305))⁻¹ < startupResidual t ht :=
  ⟨startup_residual_retained_lower t _ (startupIndex_residual_pos t ht),
    startup_residual_binary_lower t _ (startupIndex_residual_pos t ht)⟩

end WordCertDensity.Construction
