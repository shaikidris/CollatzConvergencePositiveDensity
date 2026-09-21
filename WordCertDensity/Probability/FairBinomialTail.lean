/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Probability.FairBinomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Sharp fair-binomial exponential tails

The exact centered MGF is a power of cosh. The global cosh majorant and
exponential Markov give both non-strict Hoeffding tails, with optimization
only at a positive trial count. Natural-cutoff forms serve the two timeout
probabilities without changing either endpoint.
-/

@[expose] public section

namespace WordCertDensity.Probability

open scoped Classical ENNReal

/-- A fair count minus half the number of trials. -/
noncomputable def fairCenteredCount (n k : ℕ) : ℝ := (k : ℝ) - (n : ℝ) / 2

private theorem centered_succ_success (n k : ℕ) :
    fairCenteredCount (n + 1) (k + 1) = fairCenteredCount n k + 1 / 2 := by
  simp only [fairCenteredCount, Nat.cast_add, Nat.cast_one]
  ring

private theorem centered_succ_failure (n k : ℕ) :
    fairCenteredCount (n + 1) k = fairCenteredCount n k - 1 / 2 := by
  simp only [fairCenteredCount, Nat.cast_add, Nat.cast_one]
  ring

private theorem shifted_moment (n : ℕ) (t b : ℝ) :
    (∑' k, fairBinomial n k * ENNReal.ofReal (Real.exp (t * fairCenteredCount n k + b))) =
      ENNReal.ofReal (Real.exp b) *
        (∑' k, fairBinomial n k * ENNReal.ofReal (Real.exp (t * fairCenteredCount n k))) := by
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  ac_rfl

private theorem fair_cosh_coefficient (t : ℝ) :
    (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (t / 2)) +
        (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(t / 2))) =
      ENNReal.ofReal (Real.cosh (t / 2)) := by
  rw [Real.cosh_eq, ENNReal.ofReal_div_of_pos (by norm_num),
    ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
  simp only [div_eq_mul_inv, one_mul]
  ring

/-- The original fair-binomial centered MGF is exactly cosh(t/2) to the trial count. -/
theorem fairBinomial_centeredExpMoment (n : ℕ) (t : ℝ) :
    (∑' k, fairBinomial n k * ENNReal.ofReal (Real.exp (t * fairCenteredCount n k))) =
      ENNReal.ofReal (Real.cosh (t / 2)) ^ n := by
  induction n with
  | zero => simp [fairBinomial, PMF.pure_apply, fairCenteredCount]
  | succ n ih =>
      rw [fairBinomial_sum_succ]
      have hs (k : ℕ) : t * fairCenteredCount (n + 1) (k + 1) =
          t * fairCenteredCount n k + t / 2 := by
        rw [centered_succ_success]
        ring
      have hf (k : ℕ) : t * fairCenteredCount (n + 1) k =
          t * fairCenteredCount n k + (-(t / 2)) := by
        rw [centered_succ_failure]
        ring
      simp_rw [hs, hf, shifted_moment, ih]
      calc
        _ = ((1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (t / 2)) +
            (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(t / 2)))) *
            ENNReal.ofReal (Real.cosh (t / 2)) ^ n := by ring
        _ = _ := by rw [fair_cosh_coefficient, pow_succ']

/-- The sharp quadratic MGF bound holds for every real parameter and every trial count. -/
theorem fairBinomial_centeredExpMoment_le (n : ℕ) (t : ℝ) :
    (∑' k, fairBinomial n k * ENNReal.ofReal (Real.exp (t * fairCenteredCount n k))) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * (t ^ 2 / 8))) := by
  rw [fairBinomial_centeredExpMoment]
  have hc : Real.cosh (t / 2) ≤ Real.exp (t ^ 2 / 8) := by
    calc
      _ ≤ Real.exp ((t / 2) ^ 2 / 2) := Real.cosh_le_exp_half_sq (t / 2)
      _ = _ := by congr 1; ring
  have h := pow_le_pow_left' (ENNReal.ofReal_le_ofReal hc) n
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul] at h
  exact h

private theorem optimal_exponent (n : ℕ) (hn : 0 < n) (a : ℝ) :
    -(4 * a / n) * a + (n : ℝ) * ((4 * a / n) ^ 2 / 8) = -2 * a ^ 2 / n := by
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hn)
  field_simp
  ring

/-- The non-strict upper centered tail has Hoeffding's exponent, including zero deviation. -/
theorem fairBinomial_centeredUpperTail_le (n : ℕ) (hn : 0 < n) {a : ℝ} (ha : 0 ≤ a) :
    Gated.probability (fairBinomial n) (fun k => a ≤ fairCenteredCount n k) ≤
      Real.exp (-2 * a ^ 2 / n) := by
  have ht : 0 ≤ 4 * a / (n : ℝ) := by positivity
  have h := Gated.probability_le_exp (fairBinomial n) (fairCenteredCount n)
    (cutoff := a) ht (fairBinomial_centeredExpMoment_le n (4 * a / n))
  rw [optimal_exponent n hn a] at h
  exact h

/-- The non-strict lower centered tail has exactly the same sharp exponent. -/
theorem fairBinomial_centeredLowerTail_le (n : ℕ) (hn : 0 < n) {a : ℝ} (ha : 0 ≤ a) :
    Gated.probability (fairBinomial n) (fun k => fairCenteredCount n k ≤ -a) ≤
      Real.exp (-2 * a ^ 2 / n) := by
  have ht : 0 ≤ 4 * a / (n : ℝ) := by positivity
  have hm : (∑' k, fairBinomial n k * ENNReal.ofReal
        (Real.exp ((4 * a / n) * (-fairCenteredCount n k)))) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * ((4 * a / n) ^ 2 / 8))) := by
    simpa only [mul_neg, neg_mul, neg_sq] using
      fairBinomial_centeredExpMoment_le n (-(4 * a / n))
  have h := Gated.probability_le_exp (fairBinomial n) (fun k => -fairCenteredCount n k)
    (cutoff := a) ht hm
  rw [optimal_exponent n hn a] at h
  simpa only [le_neg] using h

/-- A natural upper cutoff retains its exact distance above the binomial midpoint. -/
theorem fairBinomial_upperTail_le (n N : ℕ) (hn : 0 < n) (hN : (n : ℝ) / 2 ≤ N) :
    Gated.probability (fairBinomial n) (fun k => N ≤ k) ≤
      Real.exp (-2 * ((N : ℝ) - (n : ℝ) / 2) ^ 2 / n) := by
  simpa [fairCenteredCount] using fairBinomial_centeredUpperTail_le n hn (sub_nonneg.mpr hN)

/-- A natural lower cutoff retains its exact distance below the binomial midpoint. -/
theorem fairBinomial_lowerTail_le (n N : ℕ) (hn : 0 < n) (hN : (N : ℝ) ≤ (n : ℝ) / 2) :
    Gated.probability (fairBinomial n) (fun k => k ≤ N) ≤
      Real.exp (-2 * ((n : ℝ) / 2 - (N : ℝ)) ^ 2 / n) := by
  simpa [fairCenteredCount, neg_sub] using
    fairBinomial_centeredLowerTail_le n hn (sub_nonneg.mpr hN)

end WordCertDensity.Probability
