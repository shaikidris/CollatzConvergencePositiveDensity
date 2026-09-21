/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Analytic.NearbyMixing

/-!
# Positivity and geometric contraction of the width envelope

Every exponent is below minus eight throughout the original width range.
The logarithmic denominator only improves the decay as scale increases.
-/

namespace WordCertDensity.Analytic

/-- All four envelope powers decay faster than the eighth inverse power. -/
theorem mixing_exponents_lt {v : ℝ} (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) :
    -6407 + Real.log 2 * v ^ 2 / 2 < -8 ∧
      1 - v * Real.log 2 < -8 ∧ -(v * Real.log 2) < -8 ∧
        -(v * Real.log 2) - 1 < -8 := by
  have hlog : Real.log 2 ≤ (69315 / 100000 : ℝ) :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hsq : v ^ 2 ≤ (679 / 5 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by linarith) (by norm_num)).mpr hv'
  have hu := mul_le_mul hlog hsq (sq_nonneg v) (by norm_num : (0 : ℝ) ≤ 69315 / 100000)
  have hl := mul_le_mul hv Head.log_two_lower.le (by norm_num : (0 : ℝ) ≤ 693 / 1000)
    (by linarith : 0 ≤ v)
  constructor
  · nlinarith only [hu]
  · constructor <;> [nlinarith only [hl]; constructor <;> nlinarith only [hl]]

/-- The envelope is strictly positive at every scale larger than one. -/
theorem mixingEnvelope_pos {v x : ℝ} (hv : 80 ≤ v) (hx : 1 < x) :
    0 < mixingEnvelope v x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hv0 : 0 < v := by linarith
  have hD := tailCoefficient_pos
  unfold mixingEnvelope Head.failureEnvelope
  positivity

private theorem envelope_le_of_power_le {v x y t : ℝ}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hx : 1 < x) (hxy : x ≤ y)
    (hp : ∀ e : ℝ, e ≤ -8 → y ^ e ≤ t * x ^ e) :
    mixingEnvelope v y ≤ t * mixingEnvelope v x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogxy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hq : 0 < v * Real.log 2 := mul_pos (by linarith) (Real.log_pos (by norm_num))
  have hden : 0 < (v * Real.log 2) ^ 2 * Real.log x := mul_pos (sq_pos_of_pos hq) hlog
  have hcoeff : 16 / ((v * Real.log 2) ^ 2 * Real.log y) ≤
      16 / ((v * Real.log 2) ^ 2 * Real.log x) :=
    div_le_div_of_nonneg_left (by norm_num) hden
      (mul_le_mul_of_nonneg_left hlogxy (sq_nonneg _))
  obtain ⟨hA, hB, hC, hD⟩ := mixing_exponents_lt hv hv'
  have hmain := mul_le_mul_of_nonneg_left (hp _ hA.le)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) tailCoefficient_pos.le)
  have hshort := mul_le_mul hcoeff (hp _ hB.le) (Real.rpow_nonneg hy0.le _)
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 16) hden.le)
  have hsecond := hp _ hC.le
  have hthird := hp _ hD.le
  unfold mixingEnvelope Head.failureEnvelope
  nlinarith only [hmain, hshort, hsecond, hthird]

/-- Increasing scale decreases the envelope, on its natural positive-log domain. -/
theorem mixingEnvelope_antitone {v x y : ℝ} (hv : 80 ≤ v) (hv' : v ≤ 679 / 5)
    (hx : 1 < x) (hxy : x ≤ y) : mixingEnvelope v y ≤ mixingEnvelope v x := by
  have h := envelope_le_of_power_le hv hv' hx hxy (t := 1) (fun e he => by
    simpa using Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x) hxy
      (by linarith : e ≤ 0))
  simpa using h

/-- Geometric scaling pays at most the eighth inverse power, for every permitted width. -/
theorem mixingEnvelope_mul_le {v x t : ℝ} (hv : 80 ≤ v) (hv' : v ≤ 679 / 5)
    (hx : 1 < x) (ht : 1 ≤ t) :
    mixingEnvelope v (t * x) ≤ t ^ (-8 : ℝ) * mixingEnvelope v x := by
  have hx0 : 0 < x := by linarith
  apply envelope_le_of_power_le hv hv' hx (by nlinarith)
  intro e he
  rw [Real.mul_rpow (by linarith : 0 ≤ t) hx0.le]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht he)
    (Real.rpow_nonneg hx0.le e)

/-- Doubling the envelope after an 11/10 jump strictly decreases it (M.contraction). -/
theorem mixingEnvelope_contraction {v x : ℝ} (hv : 80 ≤ v) (hv' : v ≤ 679 / 5)
    (hx : 1 < x) : 2 * mixingEnvelope v ((11 / 10 : ℝ) * x) < mixingEnvelope v x := by
  have h := mul_le_mul_of_nonneg_left (mixingEnvelope_mul_le hv hv' hx
    (by norm_num : (1 : ℝ) ≤ 11 / 10)) (by norm_num : (0 : ℝ) ≤ 2)
  have hrate : 2 * (11 / 10 : ℝ) ^ (-8 : ℝ) < 1 := by norm_num
  have hpos := mixingEnvelope_pos hv hx
  nlinarith only [h, mul_lt_mul_of_pos_right hrate hpos]

end WordCertDensity.Analytic
