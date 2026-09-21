/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Words
public import WordCertDensity.Probability.FairBinomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Positive geometric waiting times and fair binomial counts

The CDF for total positive valuations and the binomial upper tail satisfy
identical recurrences. This proves the exact waiting-time identity under
the original word law, including zero depth and the strict endpoint shifts.
-/

@[expose] public section

namespace WordCertDensity.Reference

open scoped Classical ENNReal
open Probability

/-- Original probability mass for completing n positive waiting times by trial m. -/
noncomputable def waitingMass (n m : ℕ) : ℝ≥0∞ :=
  ∑' w, wordPMF n w * if w.total ≤ m then 1 else 0

/-- The waiting CDF converts to the literal original word-total probability. -/
theorem waitingMass_toReal (n m : ℕ) :
    (waitingMass n m).toReal = Gated.probability (wordPMF n) (fun w => w.total ≤ m) := by
  unfold waitingMass Gated.probability
  congr 1
  apply tsum_congr
  intro w
  by_cases h : w.total ≤ m <;> simp [h]

/-- Completing zero positive waiting times takes zero trials. -/
theorem waitingMass_zero (m : ℕ) : waitingMass 0 m = 1 := by
  simp [waitingMass, wordPMF, PMF.pure_apply, ValuationWord.total]

private theorem geometricNat_zero : geometricNat 0 = (1 / 2 : ℝ≥0∞) := by
  change ENNReal.ofReal ((1 / 2 : ℝ) ^ (0 + 1)) = _
  norm_num [ENNReal.ofReal_div_of_pos]

private theorem geometricNat_succ (k : ℕ) :
    geometricNat (k + 1) = (1 / 2 : ℝ≥0∞) * geometricNat k := by
  change ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1 + 1)) =
    (1 / 2 : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1))
  rw [pow_succ, ENNReal.ofReal_mul (by positivity)]
  norm_num [mul_comm, ENNReal.ofReal_div_of_pos]

private theorem waitingMass_succ_eq (n m : ℕ) :
    waitingMass (n + 1) m = ∑' k : ℕ, geometricNat k *
      ∑' w, wordPMF n w * if k + 1 + w.total ≤ m then 1 else 0 := by
  unfold waitingMass
  rw [wordPMF, PMFMoment.sum_bind]
  simp_rw [PMFMoment.sum_map]
  rw [geometricLetter, PMFMoment.sum_map]
  rfl

/-- A positive number of positive waiting times cannot fit in zero trials. -/
theorem waitingMass_succ_zero (n : ℕ) : waitingMass (n + 1) 0 = 0 := by
  rw [waitingMass_succ_eq]
  apply ENNReal.tsum_eq_zero.mpr
  intro k
  have hz : (∑' w, wordPMF n w * if k + 1 + w.total ≤ 0 then 1 else 0) = 0 := by
    apply ENNReal.tsum_eq_zero.mpr
    intro w
    have h : ¬ k + 1 + w.total ≤ 0 := by omega
    simp [h]
  rw [hz, mul_zero]

/-- The waiting CDF obeys the same fair success/failure recurrence as the binomial tail. -/
theorem waitingMass_succ_succ (n m : ℕ) :
    waitingMass (n + 1) (m + 1) =
      (1 / 2 : ℝ≥0∞) * waitingMass n m + (1 / 2 : ℝ≥0∞) * waitingMass (n + 1) m := by
  rw [waitingMass_succ_eq, tsum_eq_zero_add' ENNReal.summable]
  have hfirst : geometricNat 0 *
      (∑' w, wordPMF n w * if 0 + 1 + w.total ≤ m + 1 then 1 else 0) =
        (1 / 2 : ℝ≥0∞) * waitingMass n m := by
    rw [geometricNat_zero]
    congr 1
    apply tsum_congr
    intro w
    have h : 0 + 1 + w.total ≤ m + 1 ↔ w.total ≤ m := by omega
    simp only [h]
  have htail : (∑' k : ℕ, geometricNat (k + 1) *
      ∑' w, wordPMF n w * if k + 1 + 1 + w.total ≤ m + 1 then 1 else 0) =
        (1 / 2 : ℝ≥0∞) * waitingMass (n + 1) m := by
    rw [waitingMass_succ_eq, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro k
    have hs : (∑' w, wordPMF n w * if k + 1 + 1 + w.total ≤ m + 1 then 1 else 0) =
        ∑' w, wordPMF n w * if k + 1 + w.total ≤ m then 1 else 0 := by
      apply tsum_congr
      intro w
      have h : k + 1 + 1 + w.total ≤ m + 1 ↔ k + 1 + w.total ≤ m := by omega
      simp only [h]
    rw [geometricNat_succ, hs, mul_assoc]
  rw [hfirst, htail]

/-- The n-th success is by trial m exactly when those trials contain at least n successes. -/
theorem waitingMass_eq_binomial (n m : ℕ) : waitingMass n m = fairBinomialUpperMass m n := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rw [waitingMass_zero, fairBinomialUpperMass_zero]
      | succ n => rw [waitingMass_succ_zero, fairBinomialUpperMass_zero_trials]
  | succ m ih =>
      cases n with
      | zero => rw [waitingMass_zero, fairBinomialUpperMass_zero]
      | succ n => rw [waitingMass_succ_succ, fairBinomialUpperMass_succ_succ, ih, ih]

/-- The CDF identity as equality of original real event probabilities. -/
theorem word_total_le_binomial_probability (n m : ℕ) :
    Gated.probability (wordPMF n) (fun w => w.total ≤ m) =
      Gated.probability (fairBinomial m) (fun k => n ≤ k) := by
  rw [← waitingMass_toReal, waitingMass_eq_binomial, fairBinomialUpperMass_toReal]

/-- A strict total cutoff L corresponds to L-1 fair trials, with no shift in the success target. -/
theorem word_total_lt_binomial_probability (n L : ℕ) (hL : 0 < L) :
    Gated.probability (wordPMF n) (fun w => w.total < L) =
      Gated.probability (fairBinomial (L - 1)) (fun k => n ≤ k) := by
  rw [← word_total_le_binomial_probability]
  apply Gated.probability_congr_on_support
  intro w _
  omega

private theorem probability_not {α : Type*} (p : PMF α) (G : α → Prop) :
    Gated.probability p (fun a => ¬ G a) = 1 - Gated.probability p G := by
  let A : ℝ≥0∞ := ∑' a, if G a then p a else 0
  let B : ℝ≥0∞ := ∑' a, if ¬ G a then p a else 0
  have h : A + B = 1 := by
    dsimp [A, B]
    rw [← ENNReal.tsum_add]
    calc
      _ = ∑' a, p a := by
        apply tsum_congr
        intro a
        by_cases ha : G a <;> simp [ha]
      _ = 1 := p.tsum_coe
  have hA : A.toReal = Gated.probability p G := by
    apply congrArg ENNReal.toReal
    apply tsum_congr
    intro a
    by_cases ha : G a <;> simp [ha]
  have hB : B.toReal = Gated.probability p (fun a => ¬ G a) := by
    dsimp [B, Gated.probability]
    congr 1
    apply tsum_congr
    intro a
    by_cases ha : G a <;> simp [ha]
  have hfin : A + B ≠ ⊤ := by rw [h]; simp
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mp hfin).1 (ENNReal.add_ne_top.mp hfin).2,
    ENNReal.toReal_one, hA, hB] at hr
  linarith

/-- The complementary total tail keeps both essential E-1 and n-1 shifts. -/
theorem word_total_ge_binomial_probability (n E : ℕ) (hn : 0 < n) (hE : 0 < E) :
    Gated.probability (wordPMF n) (fun w => E ≤ w.total) =
      Gated.probability (fairBinomial (E - 1)) (fun k => k ≤ n - 1) := by
  have hleft : Gated.probability (wordPMF n) (fun w => E ≤ w.total) =
      1 - Gated.probability (wordPMF n) (fun w => w.total < E) := by
    rw [← probability_not]
    apply Gated.probability_congr_on_support
    intro w _
    omega
  have hright : Gated.probability (fairBinomial (E - 1)) (fun k => k ≤ n - 1) =
      1 - Gated.probability (fairBinomial (E - 1)) (fun k => n ≤ k) := by
    rw [← probability_not]
    apply Gated.probability_congr_on_support
    intro k _
    omega
  rw [hleft, hright, word_total_lt_binomial_probability n E hE]

end WordCertDensity.Reference
