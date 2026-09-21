/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Exact geometric truncation bounds for certificate recursions -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- The complete geometric series with its actual bounded entries. -/
noncomputable def weightedSeries (q : ℝ) (g : ℕ → ℝ) : ℝ := ∑' a, q ^ a * g a

/-- A bounded nonnegative input gives an absolutely summable geometric series. -/
theorem weightedSeries_summable {q M : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    {g : ℕ → ℝ} (hg : ∀ a, 0 ≤ g a ∧ g a ≤ M) :
    Summable (fun a => q ^ a * g a) := by
  exact Summable.of_nonneg_of_le
    (fun a => mul_nonneg (pow_nonneg hq _) (hg a).1)
    (fun a => mul_le_mul_of_nonneg_left (hg a).2 (pow_nonneg hq _))
    ((hasSum_geometric_of_lt_one hq hq1).summable.mul_right M)

/-- The constant input bounds the full geometric expectation. -/
theorem weightedSeries_le {q M : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    {g : ℕ → ℝ} (hg : ∀ a, 0 ≤ g a ∧ g a ≤ M) :
    weightedSeries q g ≤ M / (1 - q) := by
  have h := (weightedSeries_summable hq hq1 hg).tsum_le_tsum
    (fun a => mul_le_mul_of_nonneg_left (hg a).2 (pow_nonneg hq _))
    ((hasSum_geometric_of_lt_one hq hq1).summable.mul_right M)
  rw [tsum_mul_right, (hasSum_geometric_of_lt_one hq hq1).tsum_eq] at h
  simpa only [weightedSeries, div_eq_mul_inv, mul_comm] using h

/-- The exact remainder separates its geometric scale from its original shifted entries. -/
theorem weightedSeries_split {q M : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    {g : ℕ → ℝ} (hg : ∀ a, 0 ≤ g a ∧ g a ≤ M) (T : ℕ) :
    weightedSeries q g = (∑ a ∈ Finset.range T, q ^ a * g a) +
      q ^ T * weightedSeries q (fun a => g (a + T)) := by
  have h := (weightedSeries_summable hq hq1 hg).sum_add_tsum_nat_add T
  rw [weightedSeries, ← h]
  congr 1
  simp only [weightedSeries, ← tsum_mul_left, pow_add]
  apply tsum_congr
  intro a
  ring

/-- Every finite truncation has a certified geometric initialization tail. -/
theorem weightedSeries_tail_le {q M : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    {g : ℕ → ℝ} (hg : ∀ a, 0 ≤ g a ∧ g a ≤ M) (T : ℕ) :
    weightedSeries q g ≤ (∑ a ∈ Finset.range T, q ^ a * g a) +
      q ^ T * (M / (1 - q)) := by
  rw [weightedSeries_split hq hq1 hg T]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (weightedSeries_le hq hq1 (fun a => hg (a + T))) (pow_nonneg hq T))

end WordCertDensity.Certificates
