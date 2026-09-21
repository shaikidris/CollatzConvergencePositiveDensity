/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.StoppedExpectation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit centered stopped-block moments

The original stopped law gives a common quadratic MGF bound for every
observable dominated in absolute value by twice the ordinary cost. The
parameter interval includes both signs. A global exponential remainder
estimate applies even though the costs are unbounded.
-/

@[expose] public section

namespace WordCertDensity.Construction

open scoped ENNReal

/-- Center an observable by its expectation under the original stopped law. -/
noncomputable def stoppedCentered (F : ValuationWord → ℝ) (w : ValuationWord) : ℝ :=
  F w - stoppedExpectation F

/-- A common explicit quadratic MGF coefficient for displacement and ordinary cost. -/
noncomputable def stoppedQuadraticBound : ℝ :=
  128000000 * Real.exp (stoppedMomentBound / 2) * stoppedMomentBound

/-- The common coefficient is finite and strictly positive. -/
theorem stoppedQuadraticBound_pos : 0 < stoppedQuadraticBound := by
  unfold stoppedQuadraticBound
  positivity [stoppedMomentBound_pos]

private theorem summable_weights : Summable (fun w => (stoppedPMF w).toReal) :=
  ENNReal.summable_toReal (by rw [stoppedPMF.tsum_coe]; exact ENNReal.one_ne_top)

private theorem sum_weights : (∑' w, (stoppedPMF w).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun _ => PMF.apply_ne_top _ _), stoppedPMF.tsum_coe]
  rfl

private theorem cost_exp_bound (w : ValuationWord) :
    (w.ordinaryCost : ℝ) ≤ 1000 * Real.exp ((1 / 1000 : ℝ) * w.ordinaryCost) := by
  have h := Real.add_one_le_exp ((1 / 1000 : ℝ) * w.ordinaryCost)
  linarith

/-- A cost-dominated observable has a uniform bound on the absolute value of its mean. -/
theorem abs_stoppedExpectation_le {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) :
    |stoppedExpectation F| ≤ 2000 * stoppedMomentBound := by
  have h := tsum_of_norm_bounded (summable_stopped_expMoment.mul_left 2000).hasSum
    (f := fun w => (stoppedPMF w).toReal * F w) (fun w => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      have hb : |F w| ≤ 2000 * Real.exp ((1 / 1000 : ℝ) * w.ordinaryCost) := by
        linarith [hF w, cost_exp_bound w]
      have hp := mul_le_mul_of_nonneg_left hb
        (ENNReal.toReal_nonneg : 0 ≤ (stoppedPMF w).toReal)
      nlinarith)
  rw [Real.norm_eq_abs, tsum_mul_left] at h
  exact h.trans (mul_le_mul_of_nonneg_left stopped_expMoment_le (by norm_num))

/-- Centering preserves absolute integrability. -/
theorem summable_stopped_centered {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) :
    Summable (fun w => (stoppedPMF w).toReal * stoppedCentered F w) := by
  have hf := summable_stopped_of_abs_le_cost (by norm_num : (0 : ℝ) ≤ 2) hF
  have hc := summable_weights.mul_right (stoppedExpectation F)
  apply (hf.sub hc).congr
  intro w
  simp [stoppedCentered, mul_sub]

/-- The actual centered observable has mean zero. -/
theorem stoppedExpectation_centered {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) :
    stoppedExpectation (stoppedCentered F) = 0 := by
  have hf := summable_stopped_of_abs_le_cost (by norm_num : (0 : ℝ) ≤ 2) hF
  have hc := summable_weights.mul_right (stoppedExpectation F)
  change (∑' w, (stoppedPMF w).toReal * (F w - stoppedExpectation F)) = 0
  simp only [mul_sub]
  rw [hf.tsum_sub hc, tsum_mul_right, sum_weights, one_mul]
  exact sub_self (stoppedExpectation F)

private theorem centered_abs_le {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) (w : ValuationWord) :
    |stoppedCentered F w| ≤ 2 * w.ordinaryCost + 2000 * stoppedMomentBound :=
  (abs_sub (F w) (stoppedExpectation F)).trans
    (add_le_add (hF w) (abs_stoppedExpectation_le hF))

private theorem centered_exp_dom {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) (w : ValuationWord) :
    Real.exp (|stoppedCentered F w| / 4000) ≤
      Real.exp (stoppedMomentBound / 2) *
        Real.exp ((1 / 1000 : ℝ) * w.ordinaryCost) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hR : (0 : ℝ) ≤ w.ordinaryCost := Nat.cast_nonneg _
  linarith [centered_abs_le hF w]

/-- The centered absolute exponential moment is summable at a fixed parameter. -/
theorem summable_stopped_centered_abs_exp {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) :
    Summable (fun w => (stoppedPMF w).toReal *
      Real.exp (|stoppedCentered F w| / 4000)) := by
  apply summable_stopped_of_abs_le_exp
  intro w
  rw [abs_of_pos (Real.exp_pos _)]
  exact centered_exp_dom hF w

/-- The centered absolute exponential moment has a common explicit majorant. -/
theorem stopped_centered_abs_exp_le {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) :
    stoppedExpectation (fun w => Real.exp (|stoppedCentered F w| / 4000)) ≤
      Real.exp (stoppedMomentBound / 2) * stoppedMomentBound := by
  have h := Summable.tsum_le_tsum (fun w => by
    have hp := mul_le_mul_of_nonneg_left (centered_exp_dom hF w)
      (ENNReal.toReal_nonneg : 0 ≤ (stoppedPMF w).toReal)
    nlinarith) (summable_stopped_centered_abs_exp hF)
      (summable_stopped_expMoment.mul_left (Real.exp (stoppedMomentBound / 2)))
  rw [tsum_mul_left] at h
  exact h.trans (mul_le_mul_of_nonneg_left stopped_expMoment_le (Real.exp_pos _).le)

/-- Both parameter signs give an integrable centered MGF on a fixed closed interval. -/
theorem summable_stopped_centered_exp {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) {t : ℝ} (ht : |t| ≤ 1 / 8000) :
    Summable (fun w => (stoppedPMF w).toReal * Real.exp (t * stoppedCentered F w)) := by
  apply summable_stopped_of_abs_le_exp
  intro w
  rw [abs_of_pos (Real.exp_pos _)]
  refine le_trans (Real.exp_le_exp.mpr ?_) (centered_exp_dom hF w)
  calc
    t * stoppedCentered F w ≤ |t * stoppedCentered F w| := le_abs_self _
    _ = |t| * |stoppedCentered F w| := abs_mul _ _
    _ ≤ (1 / 8000 : ℝ) * |stoppedCentered F w| :=
      mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    _ ≤ |stoppedCentered F w| / 4000 := by nlinarith [abs_nonneg (stoppedCentered F w)]

private theorem exp_remainder_global (x : ℝ) :
    |Real.exp x - (1 + x)| ≤ x ^ 2 * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
  have he : Complex.exp (x : ℂ) -
      (∑ m ∈ Finset.range 2, (x : ℂ) ^ m / (m.factorial : ℂ)) =
      ((Real.exp x - (1 + x) : ℝ) : ℂ) := by
    simp [Finset.sum_range_succ, Complex.ofReal_exp]
  rw [he] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

private theorem exp_quadratic_majorant {t : ℝ} (ht : |t| ≤ 1 / 8000) (z : ℝ) :
    Real.exp (t * z) ≤ 1 + t * z +
      128000000 * t ^ 2 * Real.exp (|z| / 4000) := by
  have hp := Real.pow_div_factorial_le_exp (|z| / 8000)
    (by positivity : (0 : ℝ) ≤ |z| / 8000) 2
  rw [div_pow, sq_abs] at hp
  norm_num at hp
  have hp' : z ^ 2 ≤ 128000000 * Real.exp (|z| / 8000) := by nlinarith
  have he : Real.exp |t * z| ≤ Real.exp (|z| / 8000) := by
    apply Real.exp_le_exp.mpr
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_right ht (abs_nonneg z)
    linarith
  have hprod : z ^ 2 * Real.exp |t * z| ≤
      128000000 * Real.exp (|z| / 4000) := by
    calc
      _ ≤ (128000000 * Real.exp (|z| / 8000)) * Real.exp (|z| / 8000) :=
        mul_le_mul hp' he (Real.exp_pos _).le (by positivity)
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have h := mul_le_mul_of_nonneg_left hprod (sq_nonneg t)
  have hr := (le_abs_self (Real.exp (t * z) - (1 + t * z))).trans
    (exp_remainder_global (t * z))
  nlinarith

/-- The original centered MGF has a common quadratic bound for both signs. -/
theorem stopped_centered_exp_le {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) {t : ℝ} (ht : |t| ≤ 1 / 8000) :
    stoppedExpectation (fun w => Real.exp (t * stoppedCentered F w)) ≤
      Real.exp (stoppedQuadraticBound * t ^ 2) := by
  have hlin := (summable_stopped_centered hF).mul_left t
  have hquad := (summable_stopped_centered_abs_exp hF).mul_left (128000000 * t ^ 2)
  have h := Summable.tsum_le_tsum (fun w => by
    have hp := mul_le_mul_of_nonneg_left (exp_quadratic_majorant ht (stoppedCentered F w))
      (ENNReal.toReal_nonneg : 0 ≤ (stoppedPMF w).toReal)
    nlinarith) (summable_stopped_centered_exp hF ht) ((summable_weights.add hlin).add hquad)
  rw [(summable_weights.add hlin).tsum_add hquad, summable_weights.tsum_add hlin,
    tsum_mul_left, tsum_mul_left, sum_weights] at h
  change stoppedExpectation (fun w => Real.exp (t * stoppedCentered F w)) ≤
    1 + t * stoppedExpectation (stoppedCentered F) +
      128000000 * t ^ 2 *
        stoppedExpectation (fun w => Real.exp (|stoppedCentered F w| / 4000)) at h
  rw [stoppedExpectation_centered hF, mul_zero, add_zero] at h
  have hm := mul_le_mul_of_nonneg_left (stopped_centered_abs_exp_le hF)
    (by positivity : 0 ≤ 128000000 * t ^ 2)
  have hfinal : stoppedExpectation (fun w => Real.exp (t * stoppedCentered F w)) ≤
      1 + stoppedQuadraticBound * t ^ 2 := by
    unfold stoppedQuadraticBound
    nlinarith
  exact hfinal.trans (by linarith [Real.add_one_le_exp (stoppedQuadraticBound * t ^ 2)])

/-- The quadratic bound in the nonnegative-moment form consumed by exponential Markov. -/
theorem stopped_centered_exp_ennreal_le {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) {t : ℝ} (ht : |t| ≤ 1 / 8000) :
    (∑' w, stoppedPMF w * ENNReal.ofReal (Real.exp (t * stoppedCentered F w))) ≤
      ENNReal.ofReal (Real.exp (stoppedQuadraticBound * t ^ 2)) := by
  have heq : (∑' w, stoppedPMF w * ENNReal.ofReal (Real.exp (t * stoppedCentered F w))) =
      ENNReal.ofReal (stoppedExpectation (fun w => Real.exp (t * stoppedCentered F w))) := by
    unfold stoppedExpectation
    rw [ENNReal.ofReal_tsum_of_nonneg
      (fun w => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
      (summable_stopped_centered_exp hF ht)]
    apply tsum_congr
    intro w
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (stopped_centered_exp_le hF ht)

/-- The displacement coordinate satisfies the same two-sided centered MGF estimate. -/
theorem stopped_displacement_centered_exp_le {t : ℝ} (ht : |t| ≤ 1 / 8000) :
    (∑' w, stoppedPMF w * ENNReal.ofReal
      (Real.exp (t * stoppedCentered displacement w))) ≤
      ENNReal.ofReal (Real.exp (stoppedQuadraticBound * t ^ 2)) :=
  stopped_centered_exp_ennreal_le abs_displacement_le_cost ht

/-- The ordinary-cost coordinate uses the identical coefficient and parameter interval. -/
theorem stopped_cost_centered_exp_le {t : ℝ} (ht : |t| ≤ 1 / 8000) :
    (∑' w, stoppedPMF w * ENNReal.ofReal
      (Real.exp (t * stoppedCentered (fun v => v.ordinaryCost) w))) ≤
      ENNReal.ofReal (Real.exp (stoppedQuadraticBound * t ^ 2)) := by
  apply stopped_centered_exp_ennreal_le (ht := ht)
  intro w
  rw [abs_of_nonneg (Nat.cast_nonneg w.ordinaryCost : (0 : ℝ) ≤ w.ordinaryCost)]
  have hR : (0 : ℝ) ≤ w.ordinaryCost := Nat.cast_nonneg _
  linarith

end WordCertDensity.Construction
