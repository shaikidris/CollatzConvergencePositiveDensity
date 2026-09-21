/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.GeometricTail
public import Mathlib.Algebra.BigOperators.Field

/-! # Exact cyclic recurrence and finite initialization tail -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- The original positive-letter cyclic convolution, prior to rounding. -/
noncomputable def cyclicSum (g : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑' a : ℕ, (2 : ℝ) ^ (-((a + 1 : ℕ) : ℤ)) * g (i + a + 1)

/-- The printed inverse binary coefficient is the half-power coefficient. -/
theorem cyclicCoefficient_eq (a : ℕ) :
    (2 : ℝ) ^ (-((a + 1 : ℕ) : ℤ)) = (1 / 2 : ℝ) ^ a / 2 := by
  rw [zpow_neg, zpow_natCast, pow_succ, one_div_pow]
  simp only [mul_inv_rev, div_eq_mul_inv, one_mul]
  ring

/-- Identify the literal convolution with the geometric series used to bound its tail. -/
theorem cyclicSum_eq_weightedSeries (g : ℕ → ℝ) (i : ℕ) :
    cyclicSum g i = weightedSeries (1 / 2) (fun a => g (i + a + 1)) / 2 := by
  simp only [cyclicSum, cyclicCoefficient_eq, weightedSeries, ← tsum_div_const]
  apply tsum_congr
  intro a
  ring

/-- The cyclic recurrence is exact for every bounded nonnegative input. -/
theorem cyclicSum_recurrence {g : ℕ → ℝ} {M : ℝ}
    (hg : ∀ a, 0 ≤ g a ∧ g a ≤ M) (i : ℕ) :
    cyclicSum g i = (g (i + 1) + cyclicSum g (i + 1)) / 2 := by
  have hs := weightedSeries_summable (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) (fun a => hg (i + a + 1))
  have h := hs.tsum_eq_zero_add
  have ht : (∑' a : ℕ, (1 / 2 : ℝ) ^ (a + 1) * g (i + (a + 1) + 1)) =
      weightedSeries (1 / 2) (fun a => g (i + 1 + a + 1)) / 2 := by
    simp only [weightedSeries, ← tsum_div_const, pow_succ]
    apply tsum_congr
    intro a
    rw [show i + (a + 1) + 1 = i + 1 + a + 1 by omega]
    ring
  simp only [pow_zero, one_mul, Nat.add_zero, ht] at h
  simp only [cyclicSum_eq_weightedSeries]
  unfold weightedSeries at h ⊢
  linarith

/-- Truncating at zero loses at most M times the exact inverse binary power. -/
theorem cyclicSum_tail_le {g : ℕ → ℝ} {M : ℝ}
    (hg : ∀ a, 0 ≤ g a ∧ g a ≤ M) (T : ℕ) :
    cyclicSum g 0 ≤
      (∑ a ∈ Finset.range T, (2 : ℝ) ^ (-((a + 1 : ℕ) : ℤ)) * g (a + 1)) +
        M / (2 : ℝ) ^ T := by
  have h := weightedSeries_tail_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) (fun a => hg (a + 1)) T
  have h' := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
  rw [cyclicSum_eq_weightedSeries]
  simp only [Nat.zero_add]
  refine h'.trans_eq ?_
  rw [add_div, Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    rw [cyclicCoefficient_eq]
    ring
  · rw [one_div_pow]
    ring


/-- Periodicity of the input is retained exactly by the complete convolution. -/
theorem cyclicSum_periodic {g : ℕ → ℝ} {p : ℕ} (hg : ∀ i, g (i + p) = g i) (i : ℕ) :
    cyclicSum g (i + p) = cyclicSum g i := by
  unfold cyclicSum
  apply tsum_congr
  intro a
  rw [show i + p + a + 1 = (i + a + 1) + p by omega, hg]

end WordCertDensity.Certificates
