/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The independent-list moment induction is adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The original LICENSE
and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
This version uses the actual local word law and the full-pole F16 estimates.
-/
module

public import WordCertDensity.Reference.Words
public import WordCertDensity.Reference.GeometricMoment
public import WordCertDensity.Probability.ExponentialMarkov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Centered moments of the actual independent valuation words

Centering uses real subtraction. ENNReal expectations factor under the
original iid law, including the empty word and every negative parameter.
-/

@[expose] public section

namespace WordCertDensity
namespace ValuationWord

/-- Sum of the centered positive valuations K-2, with real subtraction. -/
def centeredTotal (w : ValuationWord) : ℝ := (w.total : ℝ) - 2 * (w.length : ℝ)

/-- The empty word has zero centered sum. -/
@[simp] theorem centeredTotal_nil : centeredTotal [] = 0 := by simp [centeredTotal, total]

/-- Adding a positive valuation adds its centered value. -/
@[simp] theorem centeredTotal_cons (a : ℕ+) (w : ValuationWord) :
    centeredTotal (a :: w) = ((a : ℕ) : ℝ) - 2 + centeredTotal w := by
  simp [centeredTotal, total]
  ring

/-- Independent concatenation adds the centered sums. -/
theorem centeredTotal_append (u v : ValuationWord) :
    centeredTotal (u ++ v) = centeredTotal u + centeredTotal v := by
  simp [centeredTotal]
  ring

end ValuationWord

namespace Reference

open scoped ENNReal

private theorem exp_centeredTotal_cons (s : ℝ) (a : ℕ+) (w : ValuationWord) :
    ENNReal.ofReal (Real.exp (s * ValuationWord.centeredTotal (a :: w))) =
      ENNReal.ofReal (Real.exp (s * (((a : ℕ) : ℝ) - 2))) *
        ENNReal.ofReal (Real.exp (s * ValuationWord.centeredTotal w)) := by
  rw [ValuationWord.centeredTotal_cons, mul_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- The exact independent-word moment is the corresponding single-letter moment power. -/
theorem word_centeredExpMoment (n : ℕ) {s : ℝ} (hs : s < Real.log 2) :
    (∑' w, wordPMF n w * ENNReal.ofReal (Real.exp (s * ValuationWord.centeredTotal w))) =
      ENNReal.ofReal (centeredExpMoment s) ^ n := by
  induction n with
  | zero => simp [wordPMF, PMF.pure_apply]
  | succ n ih =>
      rw [wordPMF, PMFMoment.sum_bind]
      simp_rw [PMFMoment.sum_map, exp_centeredTotal_cons]
      have hin (a : ℕ+) :
          (∑' w, wordPMF n w *
            (ENNReal.ofReal (Real.exp (s * (((a : ℕ) : ℝ) - 2))) *
              ENNReal.ofReal (Real.exp (s * ValuationWord.centeredTotal w)))) =
          ENNReal.ofReal (Real.exp (s * (((a : ℕ) : ℝ) - 2))) *
            ENNReal.ofReal (centeredExpMoment s) ^ n := by
        calc
          _ = ENNReal.ofReal (Real.exp (s * (((a : ℕ) : ℝ) - 2))) *
              ∑' w, wordPMF n w * ENNReal.ofReal (Real.exp (s * ValuationWord.centeredTotal w)) := by
            rw [← ENNReal.tsum_mul_left]
            apply tsum_congr
            intro w
            ac_rfl
          _ = _ := by rw [ih]
      simp_rw [hin, ← mul_assoc]
      rw [ENNReal.tsum_mul_right, centeredExpMoment_ennreal hs, pow_succ']

/-- The positive word moment retains the exact geometric pole denominator. -/
theorem word_centeredExpMoment_le (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < Real.log 2) :
    (∑' w, wordPMF n w * ENNReal.ofReal (Real.exp (s * ValuationWord.centeredTotal w))) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * (s ^ 2 / (1 - (Real.log 2)⁻¹ * s)))) := by
  rw [word_centeredExpMoment n hs]
  have h := pow_le_pow_left' (ENNReal.ofReal_le_ofReal (centeredExpMoment_le_exp hs0 hs)) n
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul] at h
  exact h

/-- Every negative parameter has the smaller quadratic word-moment exponent. -/
theorem word_centeredExpMoment_neg_le (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    (∑' w, wordPMF n w * ENNReal.ofReal (Real.exp ((-s) * ValuationWord.centeredTotal w))) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) * s ^ 2)) := by
  rw [word_centeredExpMoment n (by linarith [GeometricLog.log_two_pos] : -s < Real.log 2)]
  have h := pow_le_pow_left' (ENNReal.ofReal_le_ofReal (centeredExpMoment_neg_le_exp hs)) n
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul] at h
  exact h

/-- Exponential Markov for the original word's positive centered tail. -/
theorem word_upperTail_le (n : ℕ) {s cutoff : ℝ} (hs0 : 0 ≤ s) (hs : s < Real.log 2) :
    Gated.probability (wordPMF n) (fun w => cutoff ≤ ValuationWord.centeredTotal w) ≤
      Real.exp (-s * cutoff + (n : ℝ) * (s ^ 2 / (1 - (Real.log 2)⁻¹ * s))) :=
  Gated.probability_le_exp (wordPMF n) ValuationWord.centeredTotal hs0
    (word_centeredExpMoment_le n hs0 hs)

/-- Exponential Markov for the original word's negative centered tail. -/
theorem word_lowerTail_le (n : ℕ) {s cutoff : ℝ} (hs : 0 ≤ s) :
    Gated.probability (wordPMF n) (fun w => ValuationWord.centeredTotal w ≤ -cutoff) ≤
      Real.exp (-s * cutoff + (n : ℝ) * s ^ 2) := by
  have h := Gated.probability_le_exp (wordPMF n) (fun w => -ValuationWord.centeredTotal w)
    (cutoff := cutoff) hs (by simpa only [mul_neg, neg_mul] using word_centeredExpMoment_neg_le n hs)
  simpa only [le_neg] using h

end Reference
end WordCertDensity
