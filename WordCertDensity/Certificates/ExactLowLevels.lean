/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.FanRecurrence
import WordCertDensity.Reference.FanCoset
import Mathlib.Tactic.FinCases

/-! # Exact low-level reference density, derived from the complete fan -/

namespace WordCertDensity.Reference

/-- Binary multiplication is injective on every ternary group, including level zero. -/
theorem two_mul_injective (q : ℕ) :
    Function.Injective (fun x : ZMod (3 ^ q) => 2 * x) := by
  intro x y h
  have hh := congrArg (fun z => inverseTwoPow q 1 * z) h
  have hc := two_pow_mul_inverseTwoPow q 1
  norm_num only [pow_one] at hc
  linear_combination hh - (x - y) * hc

/-- The exact numerator determines the odd-coset embedding uniquely. -/
theorem fanEmbedding_eq_of_double (m : ℕ) (x : ZMod (3 ^ m))
    (y : ZMod (3 ^ (m + 1))) (hy : 2 * y = 1 + 3 * (x.val : ZMod (3 ^ (m + 1)))) :
    fanEmbedding m x = y := by
  apply two_mul_injective (m + 1)
  exact (two_mul_fanEmbedding m x).trans hy.symm

/-- The same numerator determines the even-coset embedding uniquely. -/
theorem evenEmbedding_eq_of_four (m : ℕ) (x : ZMod (3 ^ m))
    (y : ZMod (3 ^ (m + 1))) (hy : 4 * y = 1 + 3 * (x.val : ZMod (3 ^ (m + 1)))) :
    evenEmbedding m x = y := by
  apply two_mul_injective (m + 1)
  apply two_mul_injective (m + 1)
  have h1 := two_mul_evenEmbedding m x
  have h2 := two_mul_fanEmbedding m x
  linear_combination (2 : ZMod (3 ^ (m + 1))) * h1 + h2 - hy

/-- The actual level-one density has values zero, one and two on its three residues. -/
theorem density_one_values : density 1 0 = 0 ∧ density 1 1 = 1 ∧ density 1 2 = 2 := by
  have hz := density_zero_coset 0 0 (by simp)
  have he := density_evenEmbedding 0 (0 : ZMod (3 ^ 0))
  have ho := density_fanEmbedding 0 (0 : ZMod (3 ^ 0))
  rw [evenEmbedding_eq_of_four 0 0 1 (by decide), fan_zero] at he
  rw [fanEmbedding_eq_of_double 0 0 2 (by decide), fan_zero] at ho
  exact ⟨hz, by norm_num at he; exact he, by norm_num at ho; exact ho⟩

/-- Solve the exact three-point fan recurrence without any finite approximation. -/
theorem fan_one_values : fan 1 0 = 16 / 63 ∧ fan 1 1 = 64 / 63 ∧ fan 1 2 = 88 / 63 := by
  obtain ⟨d0, d1, d2⟩ := density_one_values
  have h0 := fan_recurrence 1 0
  have h1 := fan_recurrence 1 1
  have h2 := fan_recurrence 1 2
  rw [show (4 : ZMod (3 ^ 1)) * 0 + 1 = 1 by decide, marker, d0] at h0
  rw [show (4 : ZMod (3 ^ 1)) * 1 + 1 = 2 by decide, marker, d1] at h1
  rw [show (4 : ZMod (3 ^ 1)) * 2 + 1 = 0 by decide, marker, d2] at h2
  exact ⟨by linarith, by linarith, by linarith⟩

/-- The complete depth-two seed vector is an identity about the original reference law. -/
theorem density_two_vector (x : ZMod (3 ^ 2)) : density 2 x =
    (([0, 8/7, 16/7, 0, 11/7, 4/7, 0, 2/7, 22/7] : List ℝ)[x.val]?.getD 0) := by
  obtain ⟨f0, f1, f2⟩ := fan_one_values
  have h5 := density_fanEmbedding 1 (0 : ZMod (3 ^ 1))
  rw [fanEmbedding_eq_of_double 1 0 5 (by decide), f0] at h5
  have h2 := density_fanEmbedding 1 (1 : ZMod (3 ^ 1))
  rw [fanEmbedding_eq_of_double 1 1 2 (by decide), f1] at h2
  have h8 := density_fanEmbedding 1 (2 : ZMod (3 ^ 1))
  rw [fanEmbedding_eq_of_double 1 2 8 (by decide), f2] at h8
  have h7 := density_evenEmbedding 1 (0 : ZMod (3 ^ 1))
  rw [evenEmbedding_eq_of_four 1 0 7 (by decide), f0] at h7
  have h1 := density_evenEmbedding 1 (1 : ZMod (3 ^ 1))
  rw [evenEmbedding_eq_of_four 1 1 1 (by decide), f1] at h1
  have h4 := density_evenEmbedding 1 (2 : ZMod (3 ^ 1))
  rw [evenEmbedding_eq_of_four 1 2 4 (by decide), f2] at h4
  have h0 := density_zero_coset 1 0 (by simp)
  have h3 := density_zero_coset 1 3 (by
    simpa only [map_ofNat] using (show (3 : ZMod (3 ^ 1)) = 0 by decide))
  have h6 := density_zero_coset 1 6 (by
    simpa only [map_ofNat] using (show (6 : ZMod (3 ^ 1)) = 0 by decide))
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8
  fin_cases x
  · change density 2 0 = 0
    exact h0
  · change density 2 1 = 8/7
    exact h1
  · change density 2 2 = 16/7
    exact h2
  · change density 2 3 = 0
    exact h3
  · change density 2 4 = 11/7
    exact h4
  · change density 2 5 = 4/7
    exact h5
  · change density 2 6 = 0
    exact h6
  · change density 2 7 = 2/7
    exact h7
  · change density 2 8 = 22/7
    exact h8

end WordCertDensity.Reference
