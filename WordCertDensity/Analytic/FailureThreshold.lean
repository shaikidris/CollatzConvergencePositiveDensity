/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.HeadScalars
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Chernoff parameters for short and long intervals -/

@[expose] public section

namespace WordCertDensity
namespace Head

/-- The short-interval Chernoff parameter, retaining its square-root length improvement. -/
noncomputable def shortDeviation (v L r : ℝ) : ℝ :=
  v * Real.log 2 * L + (v * Real.log 2 / 2) * Real.sqrt (r * L)

/-- The long-interval Chernoff parameter pays for the quadratic interval count. -/
noncomputable def longDeviation (v L : ℝ) : ℝ := (v * Real.log 2 + 2) * L

/-- Every short-interval parameter is strictly positive at positive logarithmic scale. -/
theorem shortDeviation_pos {v L r : ℝ} (hv : 0 < v) (hL : 0 < L) :
    0 < shortDeviation v L r := by
  have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold shortDeviation
  positivity

/-- Every long-interval parameter is strictly positive at positive logarithmic scale. -/
theorem longDeviation_pos {v L : ℝ} (hv : 0 ≤ v) (hL : 0 < L) :
    0 < longDeviation v L := by
  have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold longDeviation
  positivity

/-- For r<=L the exact Chernoff threshold fits the manuscript's typicality corridor. -/
theorem short_chernoff_threshold {v L r : ℝ} (hv : 80 ≤ v) (hL : 0 < L)
    (hr : 0 ≤ r) (hrL : r ≤ L) :
    2 * Real.sqrt (r * shortDeviation v L r) + shortDeviation v L r / Real.log 2 ≤
      v * (Real.sqrt (r * L) + L) := by
  have hv0 : 0 ≤ v := by linarith
  have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hroot : Real.sqrt (r * L) ≤ L := Real.sqrt_le_iff.mpr
    ⟨hL.le, by nlinarith [mul_le_mul_of_nonneg_right hrL hL.le]⟩
  have hz : shortDeviation v L r ≤ (3 / 2 : ℝ) * (v * Real.log 2) * L := by
    have hm := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ v * Real.log 2 / 2)
    unfold shortDeviation
    nlinarith only [hm]
  have hvh : 24 * Real.log 2 ≤ v := by linarith [log_two_upper]
  have hquad : (3 / 2 : ℝ) * (v * Real.log 2) ≤ v ^ 2 / 16 := by
    nlinarith only [mul_le_mul_of_nonneg_left hvh hv0]
  have hz' := hz.trans (mul_le_mul_of_nonneg_right hquad hL.le)
  have hs : Real.sqrt (r * shortDeviation v L r) ≤ (v / 4) * Real.sqrt (r * L) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      r * shortDeviation v L r ≤ r * ((v ^ 2 / 16) * L) :=
        mul_le_mul_of_nonneg_left hz' hr
      _ = ((v / 4) * Real.sqrt (r * L)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hr hL.le)]
        ring
  have hd : shortDeviation v L r / Real.log 2 = v * L + (v / 2) * Real.sqrt (r * L) := by
    unfold shortDeviation
    field_simp [hh.ne']
  rw [hd]
  nlinarith only [hs]

/-- For r>=L the exact Chernoff threshold also fits the same corridor. -/
theorem long_chernoff_threshold {v L r : ℝ} (hv : 80 ≤ v) (hL : 0 < L)
    (hLr : L ≤ r) :
    2 * Real.sqrt (r * longDeviation v L) + longDeviation v L / Real.log 2 ≤
      v * (Real.sqrt (r * L) + L) := by
  have hv0 : 0 ≤ v := by linarith
  have hr : 0 ≤ r := by linarith
  have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : (2 : ℝ) / Real.log 2 ≤ 3 := by
    apply (div_le_iff₀ hh).mpr
    linarith [log_two_lower]
  have hpoly : v * Real.log 2 + 2 ≤ ((v - 3) / 2) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left log_two_upper.le hv0
    nlinarith [sq_nonneg (v - 80)]
  have hcroot : Real.sqrt (v * Real.log 2 + 2) ≤ (v - 3) / 2 :=
    Real.sqrt_le_iff.mpr ⟨by linarith, hpoly⟩
  have hc : 2 * Real.sqrt (v * Real.log 2 + 2) + 2 / Real.log 2 ≤ v := by linarith
  have hroot : L ≤ Real.sqrt (r * L) := by
    nlinarith [Real.sq_sqrt (mul_nonneg hr hL.le), Real.sqrt_nonneg (r * L),
      mul_le_mul_of_nonneg_right hLr hL.le]
  have he : r * longDeviation v L = (r * L) * (v * Real.log 2 + 2) := by
    unfold longDeviation
    ring
  have hd : longDeviation v L / Real.log 2 = (v + 2 / Real.log 2) * L := by
    unfold longDeviation
    field_simp [hh.ne']
  rw [he, Real.sqrt_mul (mul_nonneg hr hL.le), hd]
  have hca := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (r * L))
  have hla := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ (2 : ℝ) / Real.log 2)
  nlinarith only [hca, hla]

end Head
end WordCertDensity
