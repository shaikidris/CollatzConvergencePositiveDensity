/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalTrials
import WordCertDensity.Reference.WaitingTime
import WordCertDensity.Probability.FairBinomialTail

/-! # Original-law terminal endpoint probabilities

The two signed geometric deviations correspond to the exact binomial trial
counts, including both strict endpoint shifts. Each original probability is
bounded by exp(-b/64000), uniformly over the permitted barrier shift.
-/

namespace WordCertDensity.Construction

open Probability

/-- The lower geometric deviation has exactly the lower binomial cutoff in N.coin. -/
theorem terminalLower_coin {b : ℕ} (hb : 200 ≤ b) :
    Gated.probability (Reference.wordPMF (terminalLow b))
        (fun w => 2 * (terminalPrecision b : ℤ) ≤ (w.total : ℤ) - 2 * terminalLow b) =
      Gated.probability (fairBinomial (terminalLowerTrials b))
        (fun k => k ≤ terminalLow b - 1) := by
  have hg := terminalEndpoint_guards hb
  calc
    _ = Gated.probability (Reference.wordPMF (terminalLow b))
        (fun w => 2 * terminalLow b + 2 * terminalPrecision b ≤ w.total) := by
      apply Gated.probability_congr_on_support
      intro w _
      omega
    _ = _ := Reference.word_total_ge_binomial_probability _ _ hg.1 (by omega)

/-- The strict upper geometric deviation retains the L-1 trial shift in N.coin. -/
theorem terminalUpper_coin {b : ℕ} (hb : 200 ≤ b) :
    Gated.probability (Reference.wordPMF (terminalHigh b))
        (fun w => (w.total : ℤ) - 2 * terminalHigh b < -2 * (terminalPrecision b : ℤ)) =
      Gated.probability (fairBinomial (terminalUpperTrials b))
        (fun k => terminalHigh b ≤ k) := by
  have hg := terminalEndpoint_guards hb
  calc
    _ = Gated.probability (Reference.wordPMF (terminalHigh b))
        (fun w => w.total < 2 * terminalHigh b - 2 * terminalPrecision b) := by
      apply Gated.probability_congr_on_support
      intro w _
      omega
    _ = _ := Reference.word_total_lt_binomial_probability _ _ (by omega)

/-- The lower endpoint tail has the manuscript's exponential bound. -/
theorem terminalLower_tail {b : ℕ} (hb : 200 ≤ b) :
    Gated.probability (Reference.wordPMF (terminalLow b))
        (fun w => 2 * (terminalPrecision b : ℤ) ≤ (w.total : ℤ) - 2 * terminalLow b) ≤
      Real.exp (-(b : ℝ) / 64000) := by
  rw [terminalLower_coin hb]
  have hg := terminalTrials_bounds hb
  have hd := (terminalTrials_distances hb).1
  have hcut : ((terminalLow b - 1 : ℕ) : ℝ) ≤ (terminalLowerTrials b : ℝ) / 2 := by
    have he : (0 : ℝ) ≤ terminalPrecision b := Nat.cast_nonneg _
    linarith
  have h := fairBinomial_lowerTail_le _ _ hg.1 hcut
  rw [hd] at h
  exact h.trans (terminalTail_exponent hb hg.1 (by omega))

/-- The upper endpoint tail has the same bound despite its strict total cutoff. -/
theorem terminalUpper_tail {b : ℕ} (hb : 200 ≤ b) :
    Gated.probability (Reference.wordPMF (terminalHigh b))
        (fun w => (w.total : ℤ) - 2 * terminalHigh b < -2 * (terminalPrecision b : ℤ)) ≤
      Real.exp (-(b : ℝ) / 64000) := by
  rw [terminalUpper_coin hb]
  have hg := terminalTrials_bounds hb
  have hd := (terminalTrials_distances hb).2
  have hcut : (terminalUpperTrials b : ℝ) / 2 ≤ terminalHigh b := by
    have he : (0 : ℝ) ≤ terminalPrecision b := Nat.cast_nonneg _
    linarith
  have h := fairBinomial_upperTail_le _ _ hg.2.1 hcut
  rw [hd] at h
  exact h.trans (terminalTail_exponent hb hg.2.1 hg.2.2.2)

end WordCertDensity.Construction
