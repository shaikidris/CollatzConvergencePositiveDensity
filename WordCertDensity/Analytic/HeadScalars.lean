/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

Head-selection and scalar arguments adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The original LICENSE
and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
This version uses the local positive valuation words and the full manuscript width range.
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Common scalar margins for every permitted head width

The cutoff is literally 2^80 and the width range is 80 through 679/5.
The estimates below are independent of the primitive-decay coefficient.
-/

@[expose] public section

namespace WordCertDensity
namespace Head

/-- The binary displacement of one ternary digit. -/
noncomputable def logRatio : ℝ := Real.log 3 / Real.log 2

/-- The first-crossing threshold at width v and ambient depth n. -/
noncomputable def gateLevel (v : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * logRatio - v ^ 2 * Real.log (n : ℝ)

/-- The lower binary logarithm guard used by the head margins. -/
theorem log_two_lower : (693 / 1000 : ℝ) < Real.log 2 :=
  (by norm_num : (693 / 1000 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9

/-- The upper binary logarithm guard used by the head margins. -/
theorem log_two_upper : Real.log 2 < (347 / 500 : ℝ) :=
  Real.log_two_lt_d9.trans (by norm_num : (0.6931471808 : ℝ) < 347 / 500)

/-- The ternary-to-binary logarithm ratio is strictly larger than one. -/
theorem one_lt_logRatio : 1 < logRatio := by
  apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  simpa using Real.log_lt_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) < 3)

/-- The exact integer comparison 3^5<2^8 bounds the logarithm ratio. -/
theorem logRatio_lt_eight_fifths : logRatio < 8 / 5 := by
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3 ^ 5)
    (by norm_num : (3 : ℝ) ^ 5 < 2 ^ 8)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

/-- The decay logarithm has the stated strict lower bound. -/
theorem log_four_thirds_lower : (2 / 7 : ℝ) < Real.log (4 / 3 : ℝ) := by
  have h := Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1 / 3)
  norm_num at h
  exact h

/-- The decay logarithm has the stated strict upper bound. -/
theorem log_four_thirds_upper : Real.log (4 / 3 : ℝ) < (1 / 3 : ℝ) := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    (by norm_num : (4 / 3 : ℝ) ≠ 1)
  norm_num at h
  exact h

/-- A square-root bound sufficient for the common finite cutoff. -/
theorem log_le_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ Real.sqrt x := by
  have h := Real.log_le_sub_one_of_pos (div_pos (Real.sqrt_pos.mpr hx) (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_div (Real.sqrt_pos.mpr hx).ne' (by norm_num), Real.log_sqrt hx.le] at h
  have htwo : Real.log 2 ≤ 1 := by linarith [log_two_upper]
  linarith

/-- A coefficient bounded by a multiple of sqrt(x) pays the same multiple of x. -/
theorem mul_log_le {a b x : ℝ} (ha : 0 ≤ a) (hx : 0 < x)
    (hab : a ≤ b * Real.sqrt x) : a * Real.log x ≤ b * x := by
  calc
    a * Real.log x ≤ a * Real.sqrt x := mul_le_mul_of_nonneg_left (log_le_sqrt hx) ha
    _ ≤ (b * Real.sqrt x) * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hab (Real.sqrt_nonneg x)
    _ = b * x := by rw [mul_assoc, Real.mul_self_sqrt hx.le]

/-- Both logarithmic budgets hold at one cutoff for the entire permitted width interval. -/
theorem common_margins {v : ℝ} {n : ℕ} (hv : 80 ≤ v) (hv' : v ≤ 679 / 5)
    (hn : 2 ^ 80 ≤ n) :
    4 < Real.log (n : ℝ) ∧
      ((3 / 2 : ℝ) * v ^ 2 + v) * Real.log (n : ℝ) ≤ (3 / 200 : ℝ) * n ∧
      ((5 / 2 : ℝ) * v ^ 2 + v) * Real.log (n : ℝ) ≤ (3 / 10 : ℝ) * n := by
  have hnreal : (2 : ℝ) ^ 80 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnreal
  have hroot : (2 : ℝ) ^ 40 ≤ Real.sqrt (n : ℝ) := by
    nlinarith only [Real.sq_sqrt hnpos.le, Real.sqrt_nonneg (n : ℝ), hnreal]
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ 80) hnreal
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hv0 : 0 ≤ v := by linarith
  have hv136 : v ≤ 136 := by linarith
  have hv2 : v ^ 2 ≤ (136 : ℝ) ^ 2 :=
    by simpa only [pow_two] using mul_self_le_mul_self hv0 hv136
  have hfirst : (3 / 2 : ℝ) * v ^ 2 + v ≤ (3 / 200 : ℝ) * Real.sqrt (n : ℝ) := by
    nlinarith
  have hsecond : (5 / 2 : ℝ) * v ^ 2 + v ≤ (3 / 10 : ℝ) * Real.sqrt (n : ℝ) := by
    nlinarith
  exact ⟨by linarith [log_two_lower],
    mul_log_le (by positivity) hnpos hfirst, mul_log_le (by positivity) hnpos hsecond⟩

/-- Completing a square pays a square-root term against any positive linear cost. -/
theorem young_sqrt {a b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    a * Real.sqrt x - b * x ≤ a ^ 2 / (4 * b) := by
  rw [le_div_iff₀ (by positivity : 0 < 4 * b)]
  have hsq := sq_nonneg (a - 2 * b * Real.sqrt x)
  have hsqrt := Real.sq_sqrt hx
  ring_nf at hsq ⊢
  nlinarith

/-- The square-root payment with the exact index coefficient used by head selection. -/
theorem young_index {v L s : ℝ} (hL : 0 < L) (hs : 0 ≤ s) :
    v * Real.sqrt (s * L) ≤ s / 10 + (5 / 2 : ℝ) * v ^ 2 * L := by
  have h := young_sqrt (a := v) (b := 1 / (10 * L)) (x := s * L)
    (by positivity) (mul_nonneg hs hL.le)
  calc
    v * Real.sqrt (s * L) ≤ (1 / (10 * L)) * (s * L) +
        v ^ 2 / (4 * (1 / (10 * L))) := by linarith
    _ = s / 10 + (5 / 2 : ℝ) * v ^ 2 * L := by field_simp [hL.ne']; ring

/-- A typical singleton fits the entire overshoot window. -/
theorem singleton_error_le {v L : ℝ} (hv : 17 ≤ v) (hL : 4 ≤ L) :
    2 + v * (Real.sqrt L + L) ≤ 2 * v * L := by
  have hsqrt : Real.sqrt L ≤ L / 2 := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ L), Real.sqrt_nonneg L]
  have hmul := mul_le_mul_of_nonneg_left hsqrt (by linarith : 0 ≤ v)
  nlinarith

end Head
end WordCertDensity
