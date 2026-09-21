/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingMoment

/-! # Vertical tails on the original common word horizon -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The actual post-crossing height exceeds a natural threshold. -/
def longCrossingVerticalEvent (s p Y : ℕ) (w : ValuationWord) : Prop :=
  ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧
    Y < ValuationWord.total (w.take (2 * ((i : ℕ) + 1 + p))) - s

/-- Markov's inequality applied directly to the actual stopped height.
There is no conditioning on the crossing index or the realized height. -/
theorem longCrossingVertical_probability_le_power (L s p Y : ℕ)
    (hL : s / 2 + 1 + p ≤ L) :
    Gated.probability (Reference.wordPMF (2 * L)) (longCrossingVerticalEvent s p Y) ≤
      (4 : ℝ) ^ (p + 1) / (4 / 3 : ℝ) ^ Y := by
  let μ := Reference.wordPMF (2 * L)
  have hmass : (∑' w, if longCrossingVerticalEvent s p Y w then μ w else 0) *
      ENNReal.ofReal ((4 / 3 : ℝ) ^ Y) ≤ horizonPostPassageMoment L s p := by
    rw [← ENNReal.tsum_mul_right]
    apply ENNReal.tsum_le_tsum
    intro w
    by_cases hw : longCrossingVerticalEvent s p Y w
    · rw [if_pos hw]
      rcases hw with ⟨i, hi, hheight⟩
      apply mul_le_mul_right
      calc
        ENNReal.ofReal ((4 / 3 : ℝ) ^ Y) ≤ ENNReal.ofReal ((4 / 3 : ℝ) ^
            (ValuationWord.total (w.take (2 * ((i : ℕ) + 1 + p))) - s)) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num) hheight.le)
        _ = (if horizonTailEvent s 0 i w then
            ENNReal.ofReal ((4 / 3 : ℝ) ^
              (ValuationWord.total (w.take (2 * ((i : ℕ) + 1 + p))) - s)) else 0) := by
          rw [if_pos hi]
        _ ≤ _ := ENNReal.le_tsum i
    · simp [hw]
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (hmass.trans (horizonPostPassageMoment_le L s p hL))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at hr
  exact (le_div_iff₀ (by positivity)).mpr hr

/-- The numerical power ratio in E.5, with the printed `A ≥ 32` guard. -/
theorem longCrossing_power_ratio_le (A p : ℕ) (hA : 32 ≤ A) :
    (4 : ℝ) ^ (p + 1) / (4 / 3 : ℝ) ^ (A * (p + 1)) ≤
      4 / ((A : ℝ) * ((p : ℝ) + 1) ^ 2) := by
  have hAr : (32 : ℝ) ≤ A := by exact_mod_cast hA
  have hAp : (0 : ℝ) < A := by linarith
  have hr : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hlog : (1 / 4 : ℝ) ≤ Real.log (4 / 3) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at h
    exact h
  have hlog4 : Real.log 4 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have heq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [heq]
    linarith
  have hexponent : ((p + 1 : ℕ) : ℝ) * Real.log 4 -
      ((A * (p + 1) : ℕ) : ℝ) * Real.log (4 / 3) ≤
        -((A : ℝ) * ((p : ℝ) + 1) / 8) := by
    push_cast
    have h₁ := mul_le_mul_of_nonneg_left hlog4 hr.le
    have h₂ := mul_le_mul_of_nonneg_left hlog (mul_pos hAp hr).le
    have h₃ := mul_nonneg (sub_nonneg.mpr hAr) hr.le
    nlinarith
  have hexp : (A : ℝ) * ((p : ℝ) + 1) ^ 2 / 4 ≤
      Real.exp ((A : ℝ) * ((p : ℝ) + 1) / 8) := by
    have h := Real.pow_div_factorial_le_exp ((A : ℝ) * ((p : ℝ) + 1) / 8)
      (show 0 ≤ (A : ℝ) * ((p : ℝ) + 1) / 8 by positivity) 2
    norm_num at h
    have hmul := mul_nonneg (mul_nonneg hAp.le (sub_nonneg.mpr hAr))
      (sq_nonneg ((p : ℝ) + 1))
    nlinarith
  calc
    _ = Real.exp (((p + 1 : ℕ) : ℝ) * Real.log 4 -
        ((A * (p + 1) : ℕ) : ℝ) * Real.log (4 / 3)) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 4),
        Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    _ ≤ Real.exp (-((A : ℝ) * ((p : ℝ) + 1) / 8)) :=
      Real.exp_le_exp.mpr hexponent
    _ ≤ 4 / ((A : ℝ) * ((p : ℝ) + 1) ^ 2) := by
      rw [Real.exp_neg]
      calc
        _ ≤ 1 / ((A : ℝ) * ((p : ℝ) + 1) ^ 2 / 4) := by
          simpa only [one_div] using
            one_div_le_one_div_of_le (by positivity) hexp
        _ = _ := by rw [one_div_div]

/-- The literal vertical rectangle-error estimate of Appendix E.5. -/
theorem longCrossingVertical_probability_le (L s p A : ℕ)
    (hL : s / 2 + 1 + p ≤ L) (hA : 32 ≤ A) :
    Gated.probability (Reference.wordPMF (2 * L))
        (longCrossingVerticalEvent s p (A * (p + 1))) ≤
      4 / ((A : ℝ) * ((p : ℝ) + 1) ^ 2) :=
  (longCrossingVertical_probability_le_power L s p (A * (p + 1)) hL).trans
    (longCrossing_power_ratio_le A p hA)

end WordCertDensity.LocalPrimitive
