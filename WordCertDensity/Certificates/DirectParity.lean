/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.ReferenceRecursion
public import Mathlib.Tactic.FieldSimp

/-! # Independent direct parity truncation before integer rounding -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Clearing a finite quarter-weighted sum gives the algorithm's integer-power head. -/
theorem quarterSeries_head (g : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (1 / 4 : ℝ) ^ j * g j) =
      (∑ j ∈ Finset.range (n + 1), (4 : ℝ) ^ (n - j) * g j) / (4 : ℝ) ^ n := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_sub₀ (4 : ℝ) (by norm_num) (Nat.le_of_lt_succ (Finset.mem_range.mp hj)),
    one_div_pow]
  field_simp

/-- The independent parity algorithm retains exactly the printed positive tail and scale. -/
theorem directParityTail (g : ℕ → ℝ) (M : ℝ) (e J : ℕ)
    (_he : 1 ≤ e) (hJ : 1 ≤ J) (hg : ∀ i, 0 ≤ g i ∧ g i ≤ M) :
    (3 * (2 : ℝ) ^ (-(e : ℤ)) * ∑' j : ℕ, (4 : ℝ) ^ (-(j : ℤ)) * g j) ≤
      (3 * (∑ j ∈ Finset.range J, (4 : ℝ) ^ (J - 1 - j) * g j) + M) /
        (2 : ℝ) ^ (e + 2 * J - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)
  have h := weightedSeries_tail_le (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1) hg (n + 1)
  have h' := mul_le_mul_of_nonneg_left h
    (by rw [zpow_neg, zpow_natCast]; positivity : 0 ≤ 3 * (2 : ℝ) ^ (-(e : ℤ)))
  have hs : (∑' j : ℕ, (4 : ℝ) ^ (-(j : ℤ)) * g j) = weightedSeries (1 / 4) g := by
    unfold weightedSeries
    apply tsum_congr
    intro j
    rw [zpow_neg, zpow_natCast, one_div_pow]
    simp only [one_div]
  rw [hs]
  refine h'.trans_eq ?_
  rw [quarterSeries_head]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [show e + 2 * (n + 1) - 2 = e + 2 * n by omega,
    pow_add (2 : ℝ) e (2 * n), pow_mul (2 : ℝ) 2 n,
    zpow_neg, zpow_natCast]
  norm_num
  simp only [one_div_pow, pow_succ]
  field_simp

end WordCertDensity.Certificates
