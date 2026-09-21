/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Moments

/-! # Integer square bounds certify the actual fractional reference moment -/

@[expose] public section

namespace WordCertDensity.Certificates

open scoped Classical

/-- The fractional power at three halves, including the zero boundary. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add_of_nonneg hx (by norm_num) (by norm_num), Real.rpow_one,
    ← Real.sqrt_eq_rpow]

/-- Any integer square upper enclosure suffices; no square-root algorithm is trusted. -/
theorem integer_rpow_upper (z r : ℕ) (h : z ≤ r ^ 2) :
    (z : ℝ) ^ (3 / 2 : ℝ) ≤ (z : ℝ) * r := by
  rw [rpow_three_halves (Nat.cast_nonneg z)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg z)
  apply (Real.sqrt_le_left (Nat.cast_nonneg r)).mpr
  exact_mod_cast h

/-- Positive scaling and an upper integer array preserve the fractional inequality. -/
theorem scaled_fractional_upper {S x : ℝ} (hS : 0 < S) (hx : 0 ≤ x)
    (z r : ℕ) (hz : S * x ≤ z) (hr : z ≤ r ^ 2) :
    S ^ (3 / 2 : ℝ) * x ^ (3 / 2 : ℝ) ≤ (z : ℝ) * r := by
  rw [← Real.mul_rpow hS.le hx]
  exact (Real.rpow_le_rpow (mul_nonneg hS.le hx) hz (by norm_num)).trans
    (integer_rpow_upper z r hr)

/-- Full-group certificate at every natural binary precision, including odd precisions. -/
theorem integerFractionalCertificate (d t : ℕ) (z r : ZMod (3 ^ d) → ℕ)
    (hz : ∀ x, (2 : ℝ) ^ t * Reference.density d x ≤ z x)
    (hr : ∀ x, z x ≤ r x ^ 2) :
    Reference.moment (3 / 2) d ≤
      (∑ x, (z x : ℝ) * r x) /
        ((3 : ℝ) ^ d * (2 : ℝ) ^ ((3 / 2 : ℝ) * t)) := by
  have hscale : ((2 : ℝ) ^ t) ^ (3 / 2 : ℝ) =
      (2 : ℝ) ^ ((3 / 2 : ℝ) * t) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm (t : ℝ)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    scaled_fractional_upper (pow_pos (by norm_num : (0 : ℝ) < 2) t)
      (Reference.density_nonneg d x) (z x) (r x) (hz x) (hr x))
  rw [hscale, ← Finset.mul_sum] at hs
  have hQ : 0 < (3 : ℝ) ^ d := pow_pos (by norm_num) d
  have hK : 0 < (2 : ℝ) ^ ((3 / 2 : ℝ) * t) := Real.rpow_pos_of_pos (by norm_num) _
  unfold Reference.moment Reference.mean
  apply (div_le_div_iff₀ hQ (mul_pos hQ hK)).mpr
  convert mul_le_mul_of_nonneg_left hs hQ.le using 1 <;> ring

end WordCertDensity.Certificates
