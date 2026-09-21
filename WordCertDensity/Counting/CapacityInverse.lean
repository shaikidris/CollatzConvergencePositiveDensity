/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # The stable smaller-root formula for finite capacity inversion -/

namespace WordCertDensity.Counting

/-- Rationalized smaller root; the capacity application has constant term equal to squared mass. -/
noncomputable def capacitySmallRoot (A B C : ℝ) : ℝ :=
  2*C/(B+Real.sqrt (B^2-4*A*C))

/-- Zero residual has zero inverse, including the totalized zero-denominator case. -/
theorem capacitySmallRoot_zero (A B : ℝ) : capacitySmallRoot A B 0 = 0 := by
  simp [capacitySmallRoot]

/-- On a real discriminant the rationalized formula is the smaller quadratic root. -/
theorem capacitySmallRoot_eq {A B C : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hD : 0 ≤ B^2-4*A*C) :
    capacitySmallRoot A B C = (B-Real.sqrt (B^2-4*A*C))/(2*A) := by
  have hd : 0 < B+Real.sqrt (B^2-4*A*C) := add_pos_of_pos_of_nonneg hB (Real.sqrt_nonneg _)
  apply (div_eq_div_iff hd.ne' (by positivity : (2*A : ℝ) ≠ 0)).2
  nlinarith [Real.sq_sqrt hD]

/-- Nonnegative residual and a positive linear coefficient give a nonnegative inverse. -/
theorem capacitySmallRoot_nonneg {A B C : ℝ} (hB : 0 < B) (hC : 0 ≤ C) :
    0 ≤ capacitySmallRoot A B C := by
  exact div_nonneg (by positivity) (add_nonneg hB.le (Real.sqrt_nonneg _))

/-- Every point with nonpositive quadratic value lies above the smaller root. -/
theorem capacitySmallRoot_le {A B C x : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hD : 0 ≤ B^2-4*A*C) (hx : A*x^2-B*x+C ≤ 0) :
    capacitySmallRoot A B C ≤ x := by
  rw [capacitySmallRoot_eq hA hB hD]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*A)).2
  have he : (B-2*A*x)^2 ≤ B^2-4*A*C := by nlinarith
  have hs := Real.sq_sqrt hD
  have hn := Real.sqrt_nonneg (B^2-4*A*C)
  nlinarith

end WordCertDensity.Counting
