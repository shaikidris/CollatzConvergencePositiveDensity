/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.FanIdentity
import WordCertDensity.Roots.Basic

/-! # Exact one-step recurrence for the complete affine fan -/

namespace WordCertDensity.Reference

/-- Increasing the fan index applies the same affine successor to its input. -/
theorem fanMap_succ (m j : ℕ) (x : ZMod (3 ^ m)) :
    fanMap m (j + 1) x = fanMap m j (4 * x + 1) := by
  have ho : (4 ^ (j + 1) - 1) / 3 = 4 ^ j + (4 ^ j - 1) / 3 := by
    rw [← Roots.value_eq_quotient, Roots.value_succ, ← Roots.value_eq_quotient]
    have h := Roots.three_mul_value_add_one j
    omega
  simp only [fanMap]
  rw [ho]
  simp only [pow_succ, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- The infinite fan solves its exact affine recurrence, before any finite approximation. -/
theorem fan_recurrence (m : ℕ) (x : ZMod (3 ^ m)) :
    fan m x = marker m x + (1 / 4 : ℝ) * fan m (4 * x + 1) := by
  have h := (fan_summable m x).tsum_eq_zero_add
  have ht : (∑' j : ℕ, (4 : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) *
      marker m (fanMap m (j + 1) x)) = (1 / 4 : ℝ) * fan m (4 * x + 1) := by
    rw [fan, ← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [fanCoefficient_eq, fanCoefficient_eq, fanMap_succ, pow_succ]
    ring
  change fan m x = _ at h
  simpa only [Nat.cast_zero, neg_zero, zpow_zero, one_mul, fanMap_zero, ht] using h

end WordCertDensity.Reference
