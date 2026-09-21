/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Probability.ExponentialMarkov
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Fair binomial counts in the original PMF event interface

Independent fair Boolean increments define the count law. Its exact atoms
are the usual binomial coefficients times two to the negative trial count.
The upper-tail recurrence is the interface to positive geometric waiting times.
-/

@[expose] public section

namespace WordCertDensity.Probability

open scoped Classical ENNReal

/-- A fair Boolean trial. -/
noncomputable def fairBit : PMF Bool := PMF.ofFintype (fun _ => (1 / 2 : ℝ≥0∞)) (by
  norm_num
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

/-- Both outcomes of a fair trial have mass one half. -/
theorem fairBit_apply (b : Bool) : fairBit b = (1 / 2 : ℝ≥0∞) := by
  simp [fairBit, PMF.ofFintype_apply]

/-- The number of successes in independent fair trials. -/
noncomputable def fairBinomial : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | n + 1 => fairBit.bind (fun b => if b then (fairBinomial n).map Nat.succ else fairBinomial n)

/-- Zero trials have deterministic count zero. -/
theorem fairBinomial_zero : fairBinomial 0 = PMF.pure 0 := rfl

/-- Every nonnegative observable obeys the independent fair-increment recurrence. -/
theorem fairBinomial_sum_succ (n : ℕ) (H : ℕ → ℝ≥0∞) :
    (∑' k, fairBinomial (n + 1) k * H k) =
      (1 / 2 : ℝ≥0∞) * (∑' k, fairBinomial n k * H (k + 1)) +
        (1 / 2 : ℝ≥0∞) * (∑' k, fairBinomial n k * H k) := by
  rw [fairBinomial, PMFMoment.sum_bind, tsum_fintype, Fintype.sum_bool]
  change (1 / 2 : ℝ≥0∞) * (∑' k, ((fairBinomial n).map Nat.succ) k * H k) +
    (1 / 2 : ℝ≥0∞) * (∑' k, fairBinomial n k * H k) = _
  rw [PMFMoment.sum_map]

/-- Zero successes requires a failure in the last fair trial. -/
theorem fairBinomial_succ_zero (n : ℕ) :
    fairBinomial (n + 1) 0 = (1 / 2 : ℝ≥0∞) * fairBinomial n 0 := by
  simp [fairBinomial, PMF.bind_apply, tsum_fintype, fairBit_apply, PMF.map_apply]

/-- Positive success counts obey the two-term Pascal recurrence. -/
theorem fairBinomial_succ_succ (n k : ℕ) :
    fairBinomial (n + 1) (k + 1) =
      (1 / 2 : ℝ≥0∞) * fairBinomial n k + (1 / 2 : ℝ≥0∞) * fairBinomial n (k + 1) := by
  simp [fairBinomial, PMF.bind_apply, tsum_fintype, fairBit_apply, PMF.map_apply]

/-- The count law has exactly the standard fair-binomial atoms at every natural index. -/
theorem fairBinomial_apply (n k : ℕ) :
    fairBinomial n k = (n.choose k : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ n := by
  induction n generalizing k with
  | zero => cases k <;> simp [fairBinomial, PMF.pure_apply]
  | succ n ih =>
      cases k with
      | zero => rw [fairBinomial_succ_zero, ih]; simp [pow_succ, mul_comm]
      | succ k =>
          rw [fairBinomial_succ_succ, ih, ih, Nat.choose_succ_succ, Nat.cast_add, pow_succ]
          ring

/-- Upper count-event mass before conversion to real probabilities. -/
noncomputable def fairBinomialUpperMass (n N : ℕ) : ℝ≥0∞ :=
  ∑' k, fairBinomial n k * if N ≤ k then 1 else 0

/-- A zero success target is always met. -/
theorem fairBinomialUpperMass_zero (n : ℕ) : fairBinomialUpperMass n 0 = 1 := by
  simp [fairBinomialUpperMass, PMF.tsum_coe]

/-- No positive success target is met in zero trials. -/
theorem fairBinomialUpperMass_zero_trials (N : ℕ) : fairBinomialUpperMass 0 (N + 1) = 0 := by
  simp [fairBinomialUpperMass, fairBinomial, PMF.pure_apply]
  intro i hi
  omega

/-- The binomial upper tail splits according to the final fair trial. -/
theorem fairBinomialUpperMass_succ_succ (n N : ℕ) :
    fairBinomialUpperMass (n + 1) (N + 1) =
      (1 / 2 : ℝ≥0∞) * fairBinomialUpperMass n N +
        (1 / 2 : ℝ≥0∞) * fairBinomialUpperMass n (N + 1) := by
  unfold fairBinomialUpperMass
  rw [fairBinomial_sum_succ]
  simp only [Nat.add_le_add_iff_right]

/-- Conversion preserves the literal original binomial upper-tail probability. -/
theorem fairBinomialUpperMass_toReal (n N : ℕ) :
    (fairBinomialUpperMass n N).toReal =
      Gated.probability (fairBinomial n) (fun k => N ≤ k) := by
  unfold fairBinomialUpperMass Gated.probability
  congr 1
  apply tsum_congr
  intro k
  by_cases h : N ≤ k <;> simp [h]

end WordCertDensity.Probability
