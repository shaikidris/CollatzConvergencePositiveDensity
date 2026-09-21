/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.FailureThreshold
public import WordCertDensity.Analytic.IntervalTail
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Length-sensitive failure probabilities of actual intervals -/

@[expose] public section

namespace WordCertDensity
namespace Head

/-- Strict failure of the typicality inequality on the half-open interval [i,j). -/
def intervalFailure (v : ℝ) (n i j : ℕ) (w : ValuationWord) : Prop :=
  v * (Real.sqrt (((j - i : ℕ) : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ)) <
    |(intervalSum w i j : ℝ) - 2 * ((j - i : ℕ) : ℝ)|

/-- A certified threshold comparison turns the actual Chernoff bound into strict failure control. -/
theorem intervalFailure_le_exp {v z : ℝ} {n i j : ℕ} (hij : i < j) (hjn : j ≤ n)
    (hz : 0 < z)
    (hcut : 2 * Real.sqrt (((j - i : ℕ) : ℝ) * z) + z / Real.log 2 ≤
      v * (Real.sqrt (((j - i : ℕ) : ℝ) * Real.log (n : ℝ)) + Real.log (n : ℝ))) :
    Gated.probability (Reference.wordPMF n) (intervalFailure v n i j) ≤ 2 * Real.exp (-z) := by
  apply le_trans _ (interval_absTail_le hij hjn hz)
  apply Gated.probability_mono_on_support
  intro w _ hw
  exact hcut.trans (le_of_lt hw)

/-- The short-interval bound retains the square-root length factor needed for the sum. -/
theorem intervalFailure_short {v : ℝ} {n i j : ℕ} (hv : 80 ≤ v) (hn : 1 < n)
    (hij : i < j) (hjn : j ≤ n) (hr : ((j - i : ℕ) : ℝ) ≤ Real.log (n : ℝ)) :
    Gated.probability (Reference.wordPMF n) (intervalFailure v n i j) ≤
      2 * (n : ℝ) ^ (-(v * Real.log 2)) *
        Real.exp (-(v * Real.log 2 / 2) * Real.sqrt (((j - i : ℕ) : ℝ) * Real.log (n : ℝ))) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have h := intervalFailure_le_exp hij hjn
    (shortDeviation_pos (by linarith : 0 < v) hL)
    (short_chernoff_threshold hv hL (Nat.cast_nonneg (j - i)) hr)
  have he : Real.exp (-shortDeviation v (Real.log (n : ℝ)) ((j - i : ℕ) : ℝ)) =
      (n : ℝ) ^ (-(v * Real.log 2)) *
        Real.exp (-(v * Real.log 2 / 2) * Real.sqrt (((j - i : ℕ) : ℝ) * Real.log (n : ℝ))) := by
    rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < n)]
    unfold shortDeviation
    rw [neg_add, Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  rw [he] at h
  simpa only [mul_assoc] using h

/-- The long-interval bound pays for all n(n+1)/2 candidate intervals. -/
theorem intervalFailure_long {v : ℝ} {n i j : ℕ} (hv : 80 ≤ v) (hn : 1 < n)
    (hij : i < j) (hjn : j ≤ n) (hr : Real.log (n : ℝ) ≤ ((j - i : ℕ) : ℝ)) :
    Gated.probability (Reference.wordPMF n) (intervalFailure v n i j) ≤
      2 * (n : ℝ) ^ (-(v * Real.log 2) - 2) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have h := intervalFailure_le_exp hij hjn
    (longDeviation_pos (by linarith : 0 ≤ v) hL) (long_chernoff_threshold hv hL hr)
  have he : Real.exp (-longDeviation v (Real.log (n : ℝ))) =
      (n : ℝ) ^ (-(v * Real.log 2) - 2) := by
    rw [Real.rpow_def_of_pos (by linarith : (0 : ℝ) < n)]
    unfold longDeviation
    congr 1
    ring
  rw [he] at h
  exact h

end Head
end WordCertDensity
