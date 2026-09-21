/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.SecondCapacity
import WordCertDensity.Counting.Harmonic
import WordCertDensity.Release.FanEleven

/-! # Explicit second-moment bounds on actual finite odd source families -/

namespace WordCertDensity.Counting
open scoped BigOperators

/-- Actual physical sources obey the second-moment bound with the finite modulus boundary. -/
theorem physical_fan_second_capacity (m : ℕ) (X R : ℝ) (S : Finset ℕ) (a : ℕ → ℝ)
    (hX : 0 < X) (hR : 1 < R)
    (hdata : ∀ x ∈ S, Odd x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) < R * X ∧
      0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹) :
    (∑ x ∈ S, a x * Reference.fan m (x : ZMod (3 ^ m))) ^ 2 ≤
      (∑ x ∈ S, a x) *
        (((3 : ℝ) ^ m / X + Real.log R / 2) * Reference.fanEnergyElevenCeiling m) := by
  have hT : 0 ≤ (3 : ℝ) ^ m / X + Real.log R / 2 :=
    add_nonneg (div_nonneg (by positivity) hX.le)
      (div_nonneg (Real.log_nonneg hR.le) (by norm_num))
  have ht := odd_harmonic_test (3 ^ m) X R S a (by positivity)
    ((by decide : Odd (3 : ℕ)).pow (n := m)) hX hR hdata
    (fun r => Reference.fan m r ^ 2) (fun r => sq_nonneg _)
  have he : (∑ x ∈ S, a x * Reference.fan m (x : ZMod (3 ^ m)) ^ 2) ≤
      ((3 : ℝ) ^ m / X + Real.log R / 2) *
        Reference.mean m (fun r => Reference.fan m r ^ 2) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Reference.mean] using ht
  have hbound := he.trans (mul_le_mul_of_nonneg_left
    (Reference.fan_second_le_elevenCeiling m) hT)
  exact (weighted_second_mass S a (fun x => Reference.fan m (x : ZMod (3 ^ m)))
    (fun x hx => (hdata x hx).2.2.2.1)).trans
      (mul_le_mul_of_nonneg_left hbound
        (Finset.sum_nonneg (fun x hx => (hdata x hx).2.2.2.1)))

/-- A marked-mass guarantee yields explicit occupied mass for the same physical sources. -/
theorem physical_fan_mass_lower (m : ℕ) (X R p : ℝ) (S : Finset ℕ) (a : ℕ → ℝ)
    (hX : 0 < X) (hR : 1 < R) (hp : 0 ≤ p)
    (hdata : ∀ x ∈ S, Odd x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) < R * X ∧
      0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹)
    (hmarked : p ≤ ∑ x ∈ S, a x * Reference.fan m (x : ZMod (3 ^ m))) :
    p ^ 2 / (((3 : ℝ) ^ m / X + Real.log R / 2) *
      Reference.fanEnergyElevenCeiling m) ≤ ∑ x ∈ S, a x := by
  have hT : 0 < (3 : ℝ) ^ m / X + Real.log R / 2 :=
    add_pos_of_pos_of_nonneg (div_pos (by positivity) hX)
      (div_nonneg (Real.log_nonneg hR.le) (by norm_num))
  apply (div_le_iff₀ (mul_pos hT (Reference.fanEnergyElevenCeiling_pos m))).2
  have hmark0 : 0 ≤ ∑ x ∈ S, a x * Reference.fan m (x : ZMod (3 ^ m)) :=
    Finset.sum_nonneg (fun x hx => mul_nonneg (hdata x hx).2.2.2.1
      (Reference.fan_nonneg _ _))
  have hc := physical_fan_second_capacity m X R S a hX hR hdata
  nlinarith

end WordCertDensity.Counting
