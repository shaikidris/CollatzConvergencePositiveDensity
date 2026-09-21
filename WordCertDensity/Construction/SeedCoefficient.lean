/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedIdentity
import WordCertDensity.Construction.SeedPolynomial

/-! # Order-92 seed increments with the actual analytic coefficient -/

namespace WordCertDensity.Construction

/-- The actual canonical coefficient exceeds the binary guard used by the seed argument. -/
theorem seed_mixingCoefficient_lower : (2 : ℝ) ^ 25637 < Analytic.mixingCoefficient := by
  have hC : (1 : ℝ) ≤ Analytic.primitiveCoefficient := by
    exact_mod_cast Analytic.one_le_primitiveCoefficient
  have hD : (20 : ℝ) ^ 6409 ≤ Analytic.tailCoefficient := by
    simpa only [Analytic.tailCoefficient, one_mul] using
      mul_le_mul_of_nonneg_right hC (show (0 : ℝ) ≤ 20 ^ 6409 by positivity)
  have hp : (16 : ℝ) ^ 6409 ≤ 20 ^ 6409 :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) 6409
  have he : (2 : ℝ) ^ 25637 = 2 * (16 : ℝ) ^ 6409 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_succ']
  rw [he, Analytic.mixingCoefficient_eq]
  calc
    _ ≤ 2 * Analytic.tailCoefficient :=
      mul_le_mul_of_nonneg_left (hp.trans hD) (by norm_num)
    _ < _ := lt_add_of_pos_right _ (by norm_num)

/-- The retained seed-failure coefficient is absorbed by the actual mixing coefficient. -/
theorem seedFailureConstant_lt_mixingCoefficient :
    seedFailureConstant < Analytic.mixingCoefficient := by
  exact seedFailureConstant_lt_two_pow.trans
    ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by decide : (8838 : ℕ) ≤ 25637)).trans_lt seed_mixingCoefficient_lower)

/-- Actual seed failure has order 92 with the canonical coefficient, not an arbitrary input. -/
theorem seedWords_failure_mixingCoefficient {b : ℕ} (hb : 32 ^ 5 ≤ b) :
    1 - Reference.stoppingMass (seedWords b) ≤
      Analytic.mixingCoefficient * (b : ℝ) ^ (-92 : ℝ) := by
  exact (seedWords_failure_polynomial hb).trans
    (mul_le_mul_of_nonneg_right seedFailureConstant_lt_mixingCoefficient.le (by positivity))

/-- The raw physical increment retains two distinct order-92 marker costs and its seed deficit. -/
theorem physicalSeedMark_increment_order92 {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (n : ℕ) :
    |physicalSeedMark b (n + 1) root - physicalSeedMark b n root| ≤
      (2 / 3 : ℝ) * seedCapacity b n *
        (Analytic.mixingCoefficient * (seedNextMarker (seedSize b n) : ℝ) ^ (-92 : ℝ) +
          Analytic.mixingCoefficient * (seedSize b n / 4 : ℕ) ^ (-92 : ℝ) +
          1 - Reference.stoppingMass (seedWords (seedSize b n))) := by
  have hB := hb.trans (seedSize_ge b n)
  have hg := seedIncrement_marker_guards (show 8 ≤ seedSize b n by omega)
  have hc : 0 ≤ seedCapacity b n := (seedTagBudget_nonneg b n).trans (seedTagBudget_le_capacity b n)
  apply (physicalSeedMark_increment_le hb hr n).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hc)
  have hk := Analytic.mixingError_le_order92 hg.2.2
  have hl := Analytic.mixingError_le_order92 hg.1
  linarith

/-- All three increment costs have a common actual coefficient while their depths stay explicit. -/
theorem physicalSeedMark_increment_absorbed {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (n : ℕ) :
    |physicalSeedMark b (n + 1) root - physicalSeedMark b n root| ≤
      (2 / 3 : ℝ) * seedCapacity b n * Analytic.mixingCoefficient *
        ((seedNextMarker (seedSize b n) : ℝ) ^ (-92 : ℝ) +
          (seedSize b n / 4 : ℕ) ^ (-92 : ℝ) + (seedSize b n : ℝ) ^ (-92 : ℝ)) := by
  have hc : 0 ≤ seedCapacity b n := (seedTagBudget_nonneg b n).trans (seedTagBudget_le_capacity b n)
  have hf := seedWords_failure_mixingCoefficient (hb.trans (seedSize_ge b n))
  apply (physicalSeedMark_increment_order92 hb hr n).trans
  calc
    _ ≤ (2 / 3 : ℝ) * seedCapacity b n *
        (Analytic.mixingCoefficient * (seedNextMarker (seedSize b n) : ℝ) ^ (-92 : ℝ) +
          Analytic.mixingCoefficient * (seedSize b n / 4 : ℕ) ^ (-92 : ℝ) +
          Analytic.mixingCoefficient * (seedSize b n : ℝ) ^ (-92 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hc)
      linarith
    _ = _ := by ring

end WordCertDensity.Construction
