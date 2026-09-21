/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalRadius

/-! # Exact trial counts for the two terminal endpoint tails

The natural subtractions retain the strict waiting-time shifts. Both trial
counts are positive and at most 16b/5; their deviations are exactly e+1/2.
-/

namespace WordCertDensity.Construction

/-- Trials for failure of the required lower-endpoint miss. -/
def terminalLowerTrials (b : ℕ) : ℕ :=
  2 * terminalLow b + 2 * terminalPrecision b - 1

/-- Trials for failure to hit the barrier by the upper endpoint. -/
def terminalUpperTrials (b : ℕ) : ℕ :=
  2 * terminalHigh b - 2 * terminalPrecision b - 1

/-- The endpoint depths and the strict upper waiting cutoff are positive. -/
theorem terminalEndpoint_guards {b : ℕ} (hb : 200 ≤ b) :
    0 < terminalLow b ∧ 0 < terminalHigh b ∧
      2 * terminalPrecision b + 1 < 2 * terminalHigh b := by
  unfold terminalLow terminalHigh terminalWidth terminalPrecision
  omega

/-- Both integer trial counts are positive with the common printed upper bound. -/
theorem terminalTrials_bounds {b : ℕ} (hb : 200 ≤ b) :
    0 < terminalLowerTrials b ∧ 0 < terminalUpperTrials b ∧
      terminalLowerTrials b ≤ b ∧ 5 * terminalUpperTrials b ≤ 16 * b := by
  unfold terminalLowerTrials terminalUpperTrials terminalLow terminalHigh
    terminalWidth terminalPrecision
  omega

/-- Cleared identities preserve both one-trial waiting-time shifts. -/
theorem terminalTrials_balance {b : ℕ} (hb : 200 ≤ b) :
    terminalLowerTrials b + 1 = 2 * terminalLow b + 2 * terminalPrecision b ∧
      terminalUpperTrials b + 2 * terminalPrecision b + 1 = 2 * terminalHigh b := by
  have hg := terminalEndpoint_guards hb
  unfold terminalLowerTrials terminalUpperTrials
  omega

/-- Both cutoffs are exactly e+1/2 from their respective binomial means. -/
theorem terminalTrials_distances {b : ℕ} (hb : 200 ≤ b) :
    (terminalLowerTrials b : ℝ) / 2 - (terminalLow b - 1 : ℕ) =
        (terminalPrecision b : ℝ) + 1 / 2 ∧
      (terminalHigh b : ℝ) - (terminalUpperTrials b : ℝ) / 2 =
        (terminalPrecision b : ℝ) + 1 / 2 := by
  have hg := terminalEndpoint_guards hb
  have hl : (terminalLowerTrials b : ℝ) + 1 =
      2 * (terminalLow b : ℝ) + 2 * terminalPrecision b := by
    exact_mod_cast (terminalTrials_balance hb).1
  have hh : (terminalUpperTrials b : ℝ) + 2 * terminalPrecision b + 1 =
      2 * (terminalHigh b : ℝ) := by
    exact_mod_cast (terminalTrials_balance hb).2
  have hpred : ((terminalLow b - 1 : ℕ) : ℝ) = (terminalLow b : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ terminalLow b)]
    norm_num
  rw [hpred]
  constructor <;> linarith

/-- The common trial bound and the exact floor precision give the printed exponent. -/
theorem terminalTail_exponent {b n : ℕ} (hb : 200 ≤ b) (hn : 0 < n)
    (hnb : 5 * n ≤ 16 * b) :
    Real.exp (-2 * ((terminalPrecision b : ℝ) + 1 / 2) ^ 2 / n) ≤
      Real.exp (-(b : ℝ) / 64000) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hnB : (5 : ℝ) * n ≤ 16 * b := by exact_mod_cast hnb
  have he := terminalPrecision_lower hb
  have hsq : ((b : ℝ) / 200) ^ 2 ≤ ((terminalPrecision b : ℝ) + 1 / 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hprod := mul_le_mul_of_nonneg_left hnB hbR
  apply Real.exp_le_exp.mpr
  have h : (b : ℝ) / 64000 ≤ 2 * ((terminalPrecision b : ℝ) + 1 / 2) ^ 2 / n := by
    apply (le_div_iff₀ hnR).mpr
    nlinarith
  simpa only [neg_div, neg_mul] using neg_le_neg h

end WordCertDensity.Construction
