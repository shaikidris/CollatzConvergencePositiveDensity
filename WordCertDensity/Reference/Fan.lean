/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.FanMap
import WordCertDensity.Transfer.LetterCap
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The convergent affine fan of the actual reference marker

The original coefficients and marker are retained literally. Summability uses
the elementary all-level marker cap; no finite certificate is assumed.
-/

namespace WordCertDensity.Reference

/-- The actual nonnegative series used after physical compression. -/
noncomputable def fan (m : ℕ) (x : ZMod (3^m)) : ℝ :=
  ∑' j : ℕ, (4 : ℝ)^(-(j : ℤ))*marker m (fanMap m j x)

/-- The printed integer-exponent coefficient is the geometric quarter power. -/
theorem fanCoefficient_eq (j : ℕ) : (4 : ℝ)^(-(j : ℤ)) = (1/4 : ℝ)^j := by
  simp [zpow_neg, zpow_natCast, one_div, inv_pow]

/-- All fan coefficients have total mass four thirds. -/
theorem fanCoefficient_hasSum : HasSum (fun j : ℕ => (4 : ℝ)^(-(j : ℤ))) (4/3) := by
  simp_rw [fanCoefficient_eq]
  convert! hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/4)
    (by norm_num : (1/4 : ℝ) < 1) using 1
  norm_num

/-- The complete marker fan is summable at every residue and level. -/
theorem fan_summable (m : ℕ) (x : ZMod (3^m)) :
    Summable (fun j : ℕ => (4 : ℝ)^(-(j : ℤ))*marker m (fanMap m j x)) := by
  exact Summable.of_nonneg_of_le
    (fun j => mul_nonneg (by positivity) (marker_nonneg m _))
    (fun j => mul_le_mul_of_nonneg_left (marker_le_two_pow m _) (by positivity))
    (fanCoefficient_hasSum.summable.mul_right ((2/3 : ℝ)*2^m))

/-- Every fan value is nonnegative. -/
theorem fan_nonneg (m : ℕ) (x : ZMod (3^m)) : 0 ≤ fan m x :=
  tsum_nonneg fun j => mul_nonneg (by positivity) (marker_nonneg m _)

/-- Finite subfamilies retain at most the complete nonnegative fan. -/
theorem fan_finite_le (m : ℕ) (x : ZMod (3^m)) (s : Finset ℕ) :
    (∑ j ∈ s, (4 : ℝ)^(-(j : ℤ))*marker m (fanMap m j x)) ≤ fan m x :=
  (fan_summable m x).sum_le_tsum s
    (fun j _ => mul_nonneg (by positivity) (marker_nonneg m _))

/-- A full-group mean commutes with a pointwise summable series on its finite group. -/
theorem mean_tsum (m : ℕ) (f : ℕ → ZMod (3^m) → ℝ)
    (hf : ∀ x, Summable (fun j => f j x)) :
    mean m (fun x => ∑' j, f j x) = ∑' j, mean m (f j) := by
  have hs := Summable.tsum_finsetSum (s := Finset.univ) (fun x _ => hf x)
  simp only [mean, ← hs, tsum_div_const]

/-- The exact fan mean is eight ninths on the full group at every level. -/
theorem mean_fan (m : ℕ) : mean m (fan m) = 8/9 := by
  unfold fan
  rw [mean_tsum m _ (fan_summable m)]
  simp_rw [mean_mul, mean_fanMap, mean_marker]
  rw [tsum_mul_right, fanCoefficient_hasSum.tsum_eq]
  norm_num

/-- At level zero the one-point fan has value eight ninths. -/
theorem fan_zero (x : ZMod (3^0)) : fan 0 x = 8/9 := by
  simp only [fan, marker_zero, tsum_mul_right, fanCoefficient_hasSum.tsum_eq]
  norm_num

end WordCertDensity.Reference
