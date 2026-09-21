/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.StoppedExpectation
public import WordCertDensity.Reference.PrefixWeight
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact means of the actual stopped law

Perturb the geometric letter weights while keeping the prefix-free family
fixed. Its perturbed mass is at most one. The mean logarithmic correction
therefore has a local maximum at the original law. A scalar derivative gives
the exact valuation/depth mean identity; no differentiation of a series or
optional-stopping premise is used.
-/

@[expose] public section

namespace WordCertDensity.Construction

open Filter
open scoped Classical Topology

private noncomputable def logTilt (q : ℝ) (w : ValuationWord) : ℝ :=
  (w.total : ℝ) * Real.log (2 * q) + (w.length : ℝ) * Real.log ((1 - q) / q)

private theorem tilted_weight {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (w : ValuationWord) :
    (1 / (2 : ℝ) ^ w.total) * Real.exp (logTilt q w) =
      Reference.prefixWeight (Reference.biasedLetter q) w := by
  have hr : 0 < (1 - q) / q := div_pos (sub_pos.mpr hq1) hq0
  rw [Reference.prefixWeight_biased, logTilt, Real.exp_add, Real.exp_nat_mul,
    Real.exp_nat_mul, Real.exp_log (mul_pos (by norm_num) hq0), Real.exp_log hr, mul_pow]
  calc
    (1 / (2 : ℝ) ^ w.total) *
        ((2 ^ w.total * q ^ w.total) * ((1 - q) / q) ^ w.length) =
      ((1 / (2 : ℝ) ^ w.total) * 2 ^ w.total) *
        (((1 - q) / q) ^ w.length * q ^ w.total) := by ring
    _ = _ := by rw [one_div, inv_mul_cancel₀ (by positivity), one_mul]

private theorem summable_stopped_logTilt (q : ℝ) :
    Summable (fun w => (stoppedPMF w).toReal * logTilt q w) := by
  have h := (summable_stopped_total.mul_right (Real.log (2 * q))).add
    (summable_stopped_depth.mul_right (Real.log ((1 - q) / q)))
  apply h.congr
  intro w
  dsimp [logTilt]
  ring

private theorem expectation_logTilt (q : ℝ) :
    stoppedExpectation (logTilt q) =
      stoppedExpectation (fun w => w.total) * Real.log (2 * q) +
        stoppedExpectation (fun w => w.length) * Real.log ((1 - q) / q) := by
  have hA := summable_stopped_total.mul_right (Real.log (2 * q))
  have hd := summable_stopped_depth.mul_right (Real.log ((1 - q) / q))
  calc
    stoppedExpectation (logTilt q) = ∑' w,
        (((stoppedPMF w).toReal * (w.total : ℝ)) * Real.log (2 * q) +
          ((stoppedPMF w).toReal * (w.length : ℝ)) * Real.log ((1 - q) / q)) := by
      apply tsum_congr
      intro w
      dsimp [logTilt]
      ring
    _ = _ := by rw [hA.tsum_add hd, tsum_mul_right, tsum_mul_right]; rfl

private theorem expectation_logTilt_nonpos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    stoppedExpectation (logTilt q) ≤ 0 := by
  have hw : Summable (fun w => (stoppedPMF w).toReal) :=
    ENNReal.summable_toReal (by rw [stoppedPMF.tsum_coe]; exact ENNReal.one_ne_top)
  have hs : Summable (fun w => (stoppedPMF w).toReal * (1 + logTilt q w)) := by
    apply (hw.add (summable_stopped_logTilt q)).congr
    intro w
    ring
  have hbound : ∀ V : Finset ValuationWord,
      (∑ w ∈ V, (stoppedPMF w).toReal * (1 + logTilt q w)) ≤ 1 := by
    intro V
    have hf : (V.filter FirstCrossing : Set ValuationWord).Pairwise
        (fun u v => ¬ u <+: v) := by
      intro u hu v hv hne hprefix
      exact hne (firstCrossing_prefix_eq (Finset.mem_filter.mp hu).2
        (Finset.mem_filter.mp hv).2 hprefix)
    refine (le_trans ?_ (Reference.biased_prefixWeight_sum_le_one hq0 hq1 _ hf))
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro w _
    by_cases hwc : FirstCrossing w
    · rw [if_pos hwc, stoppedPMF_toReal hwc, ← tilted_weight hq0 hq1 w]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [add_comm] using Real.add_one_le_exp (logTilt q w)) (by positivity)
    · simp [hwc, stoppedPMF_apply_of_not_firstCrossing hwc]
  have h := hs.tsum_le_of_sum_le hbound
  have he : (∑' w, (stoppedPMF w).toReal * (1 + logTilt q w)) =
      1 + stoppedExpectation (logTilt q) := by
    calc
      (∑' w, (stoppedPMF w).toReal * (1 + logTilt q w)) =
          (∑' w, (stoppedPMF w).toReal * 1) + stoppedExpectation (logTilt q) := by
        simp_rw [mul_add]
        exact (hw.mul_right 1).tsum_add (summable_stopped_logTilt q)
      _ = _ := by rw [← stoppedExpectation, stoppedExpectation_const]
  rw [he] at h
  linarith

/-- The actual stopped total valuation has mean twice the actual stopping depth. -/
theorem stoppedExpectation_total_eq_two_depth :
    stoppedExpectation (fun w => w.total) =
      2 * stoppedExpectation (fun w => w.length) := by
  let A := stoppedExpectation (fun w => w.total)
  let d := stoppedExpectation (fun w => w.length)
  let f := fun q : ℝ => A * Real.log (2 * q) + d * Real.log ((1 - q) / q)
  have hmax : IsLocalMax f (1 / 2) := by
    change ∀ᶠ q in 𝓝 (1 / 2 : ℝ), f q ≤ f (1 / 2)
    filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)] with q hq
    have h := expectation_logTilt_nonpos hq.1 hq.2
    rw [expectation_logTilt] at h
    have hzero : f (1 / 2) = 0 := by norm_num [f]
    rw [hzero]
    exact h
  have hfirst : HasDerivAt (fun q : ℝ => Real.log (2 * q)) 2 (1 / 2) := by
    have h := ((hasDerivAt_id (1 / 2 : ℝ)).const_mul 2).log (by norm_num)
    norm_num at h
    exact h
  have hsecond : HasDerivAt (fun q : ℝ => Real.log ((1 - q) / q)) (-4) (1 / 2) := by
    have hdiv := ((hasDerivAt_const (1 / 2 : ℝ) 1).sub
      (hasDerivAt_id (1 / 2 : ℝ))).div (hasDerivAt_id (1 / 2 : ℝ)) (by norm_num)
    have h := hdiv.log (by norm_num)
    norm_num at h
    exact h
  have h := hmax.hasDerivAt_eq_zero ((hfirst.const_mul A).add (hsecond.const_mul d))
  change A = 2 * d
  linarith

/-- The mean ordinary cost is exactly three times the mean stopped depth. -/
theorem stoppedExpectation_cost_eq_three_depth :
    stoppedExpectation (fun w => w.ordinaryCost) =
      3 * stoppedExpectation (fun w => w.length) := by
  rw [stoppedExpectation_cost, stoppedExpectation_total_eq_two_depth]
  ring

/-- The exact displacement mean is the mean increment times the stopped depth. -/
theorem stoppedExpectation_displacement_eq_depth :
    stoppedExpectation displacement =
      (2 - Head.logRatio) * stoppedExpectation (fun w => w.length) := by
  rw [stoppedExpectation_displacement, stoppedExpectation_total_eq_two_depth]
  ring

/-- The actual mean stopped depth is strictly positive. -/
theorem stoppedExpectation_depth_pos : 0 < stoppedExpectation (fun w => w.length) := by
  have h := stoppedExpectation_displacement_lower
  rw [stoppedExpectation_displacement_eq_depth] at h
  have hpos : 0 < 2 - Head.logRatio := by linarith [Head.logRatio_lt_eight_fifths]
  by_contra hd
  have hn := mul_nonpos_of_nonneg_of_nonpos hpos.le (le_of_not_gt hd)
  linarith

/-- The reference displacement increment times log two is exactly log(4/3). -/
theorem log_two_mul_mean_increment :
    Real.log 2 * (2 - Head.logRatio) = Real.log (4 / 3 : ℝ) := by
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (by linarith [Head.log_two_lower])
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [Head.logRatio, Real.log_div (by norm_num) (by norm_num), h4]
  field_simp

/-- The actual stopped ordinary-clock ratio is the manuscript's threshold coefficient. -/
theorem stoppedExpectation_clock_ratio :
    stoppedExpectation (fun w => w.ordinaryCost) /
      (Real.log 2 * stoppedExpectation displacement) = 3 / Real.log (4 / 3 : ℝ) := by
  rw [stoppedExpectation_cost_eq_three_depth, stoppedExpectation_displacement_eq_depth,
    ← mul_assoc, log_two_mul_mean_increment]
  have hd := stoppedExpectation_depth_pos.ne'
  field_simp

end WordCertDensity.Construction
