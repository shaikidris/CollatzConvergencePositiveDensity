/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LayerInduction
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

/-! # Elementary power ratios for the actual layer comparisons -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- Bernoulli's inequality controls the loss from removing a nonnegative
distance from the current layer. -/
theorem layer_power_drop_lower (B : ℕ) {x y : ℝ} (hx : 0 < x)
    (hyx : y ≤ x) :
    (1 - (B : ℝ) * y / x) * x ^ B ≤ (x - y) ^ B := by
  have hratio : y / x ≤ 1 := (div_le_one hx).mpr hyx
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(y / x) by linarith) B
  have hb' : 1 - (B : ℝ) * y / x ≤ (1 - y / x) ^ B := by
    simpa only [mul_neg, ← sub_eq_add_neg, ← mul_div_assoc] using hb
  have he : (1 - y / x) * x = x - y := by field_simp
  calc
    _ ≤ (1 - y / x) ^ B * x ^ B := mul_le_mul_of_nonneg_right hb' (by positivity)
    _ = _ := by rw [← mul_pow, he]

/-- The short-exit ratio has the printed one-plus-d/8 distortion. -/
theorem layer_power_short_ratio (B : ℕ) {x y d : ℝ} (hx : 0 < x)
    (hyx : y ≤ x) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hsmall : (B : ℝ) * y / x ≤ d / 32) :
    x ^ B ≤ (1 + d / 8) * (x - y) ^ B := by
  have hfactor : (1 : ℝ) ≤ (1 + d / 8) * (1 - d / 32) := by nlinarith
  have hbound : 1 ≤ (1 + d / 8) * (1 - (B : ℝ) * y / x) :=
    hfactor.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  calc
    _ ≤ ((1 + d / 8) * (1 - (B : ℝ) * y / x)) * x ^ B := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hbound (by positivity : 0 ≤ x ^ B)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (layer_power_drop_lower B hx hyx) (by positivity)

/-- The white one-step contraction still loses at least half of d after
weighting when B/x is at most d/8. -/
theorem layer_power_white_ratio (B : ℕ) {x d : ℝ} (hx : 1 ≤ x)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hsmall : (B : ℝ) / x ≤ d / 8) :
    (1 - d) * x ^ B ≤ (1 - d / 2) * (x - 1) ^ B := by
  have hp := layer_power_drop_lower B (by linarith : 0 < x) hx
  simp only [mul_one] at hp
  have hbase : 1 - d ≤ (1 - d / 2) * (1 - d / 8) := by nlinarith
  have hfactor : 1 - d ≤ (1 - d / 2) * (1 - (B : ℝ) / x) :=
    hbase.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  calc
    _ ≤ ((1 - d / 2) * (1 - (B : ℝ) / x)) * x ^ B :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hp (by linarith)

end WordCertDensity.LocalPrimitive
