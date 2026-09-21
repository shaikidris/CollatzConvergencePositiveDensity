/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.ExactLowLevels
import WordCertDensity.Certificates.DirectParity
import WordCertDensity.Certificates.CyclicUpper

/-! # Actual density bounds for the independent parity evaluator -/

namespace WordCertDensity.Certificates

/-- The explicit fan formula follows the direct evaluator's forward affine iteration. -/
theorem fanMap_step (n j : ℕ) (x : ZMod (3 ^ n)) :
    Reference.fanMap n (j + 1) x = 4 * Reference.fanMap n j x + 1 := by
  have ho : (4 ^ (j + 1) - 1) / 3 = 4 * ((4 ^ j - 1) / 3) + 1 := by
    rw [← Roots.value_eq_quotient, Roots.value_succ, ← Roots.value_eq_quotient]
  simp only [Reference.fanMap]
  rw [ho]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
  ring

/-- The fan coset has the exact original parity series with incoming valuation 1. -/
theorem density_fan_series (n : ℕ) (x : ZMod (3 ^ n)) :
    Reference.density (n + 1) (Reference.fanEmbedding n x) =
      3 * (2 : ℝ) ^ (-(1 : ℤ)) * ∑' j : ℕ, (4 : ℝ) ^ (-(j : ℤ)) *
        Reference.density n (Reference.fanMap n j x) := by
  rw [Reference.density_fanEmbedding, Reference.fan, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro j
  norm_num [Reference.marker]
  ring

/-- The even coset has the exact original parity series with incoming valuation 2. -/
theorem density_even_series (n : ℕ) (x : ZMod (3 ^ n)) :
    Reference.density (n + 1) (Reference.evenEmbedding n x) =
      3 * (2 : ℝ) ^ (-(2 : ℤ)) * ∑' j : ℕ, (4 : ℝ) ^ (-(j : ℤ)) *
        Reference.density n (Reference.fanMap n j x) := by
  rw [Reference.density_evenEmbedding, Reference.fan, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro j
  norm_num [Reference.marker]
  ring

/-- A pointwise upper sequence can replace the finite head without changing the paid tail. -/
theorem direct_bound_of_upper_sequence (g f : ℕ → ℝ) (M : ℝ) (e J : ℕ)
    (he : 1 ≤ e) (hJ : 1 ≤ J) (hg : ∀ j, 0 ≤ g j)
    (hf : ∀ j, f j ≤ M) (hgf : ∀ j, g j ≤ f j) :
    (3 * (2 : ℝ) ^ (-(e : ℤ)) * ∑' j : ℕ, (4 : ℝ) ^ (-(j : ℤ)) * g j) ≤
      (3 * (∑ j ∈ Finset.range J, (4 : ℝ) ^ (J - 1 - j) * f j) + M) /
        (2 : ℝ) ^ (e + 2 * J - 2) := by
  have ht := directParityTail g M e J he hJ (fun j => ⟨hg j, (hgf j).trans (hf j)⟩)
  have hs : (∑ j ∈ Finset.range J, (4 : ℝ) ^ (J - 1 - j) * g j) ≤
      ∑ j ∈ Finset.range J, (4 : ℝ) ^ (J - 1 - j) * f j :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hgf j) (by positivity))
  exact ht.trans (div_le_div_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 3)) le_rfl)
    (by positivity))

/-- The direct fan-coset evaluator bounds actual density from an upper previous-level array. -/
theorem density_fan_direct_upper (n : ℕ) (f : ZMod (3 ^ n) → ℝ) (M : ℝ)
    (hf : ∀ y, f y ≤ M) (hupper : ∀ y, Reference.density n y ≤ f y)
    (x : ZMod (3 ^ n)) (J : ℕ) (hJ : 1 ≤ J) :
    Reference.density (n + 1) (Reference.fanEmbedding n x) ≤
      (3 * (∑ j ∈ Finset.range J, (4 : ℝ) ^ (J - 1 - j) *
        f (Reference.fanMap n j x)) + M) / (2 : ℝ) ^ (1 + 2 * J - 2) := by
  rw [density_fan_series]
  exact direct_bound_of_upper_sequence _ _ M 1 J (by decide) hJ
    (fun j => Reference.density_nonneg n _) (fun j => hf _) (fun j => hupper _)

/-- The direct even-coset evaluator bounds actual density from an upper previous-level array. -/
theorem density_even_direct_upper (n : ℕ) (f : ZMod (3 ^ n) → ℝ) (M : ℝ)
    (hf : ∀ y, f y ≤ M) (hupper : ∀ y, Reference.density n y ≤ f y)
    (x : ZMod (3 ^ n)) (J : ℕ) (hJ : 1 ≤ J) :
    Reference.density (n + 1) (Reference.evenEmbedding n x) ≤
      (3 * (∑ j ∈ Finset.range J, (4 : ℝ) ^ (J - 1 - j) *
        f (Reference.fanMap n j x)) + M) / (2 : ℝ) ^ (2 + 2 * J - 2) := by
  rw [density_even_series]
  exact direct_bound_of_upper_sequence _ _ M 2 J (by decide) hJ
    (fun j => Reference.density_nonneg n _) (fun j => hf _) (fun j => hupper _)

end WordCertDensity.Certificates
