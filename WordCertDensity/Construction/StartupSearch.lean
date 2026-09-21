/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.StartupEndpoint
import WordCertDensity.Construction.ResidualArithmetic
import Mathlib.Data.Nat.Find

/-! # Computable least startup and its exact positive residual -/

namespace WordCertDensity.Construction

/-- Canonical numerator of the retained variation rate. -/
def startupRateNumerator : ℕ := 2013 * 100000 ^ 92

/-- Canonical denominator of the retained variation rate. -/
def startupRateDenominator : ℕ := 2000 * 100999 ^ 92

/-- The canonical integer rate is strictly between zero and one. -/
theorem startupRate_integers :
    0 < startupRateNumerator ∧ startupRateNumerator < startupRateDenominator := by
  norm_num [startupRateNumerator, startupRateDenominator]

/-- Exact identity between the analytic rate and its integer recipe. -/
theorem seedVariationRate_fraction :
    seedVariationRate = (startupRateNumerator : ℝ) / startupRateDenominator := by
  norm_num [seedVariationRate, seedTagGrowth, seedScheduleRate,
    startupRateNumerator, startupRateDenominator]

/-- A decidable integer test for positive startup residual. -/
def startupAccept (t n : ℕ) : Prop :=
  25 * (2 ^ t * startupRateNumerator ^ n *
    cubicTailNumerator n startupRateNumerator startupRateDenominator) <
  24 * (startupRateDenominator ^ n * (startupRateDenominator - startupRateNumerator) ^ 4)

instance (t n : ℕ) : Decidable (startupAccept t n) :=
  inferInstanceAs (Decidable (_ < _))

/-- The integer test is equivalent to positivity of the actual analytic residual. -/
theorem startupAccept_iff (t n : ℕ) :
    startupAccept t n ↔ 0 < (24 / 25 : ℝ) - (2 : ℝ) ^ t * seedVariationTail n := by
  let A := 2 ^ t * startupRateNumerator ^ n *
    cubicTailNumerator n startupRateNumerator startupRateDenominator
  let B := startupRateDenominator ^ n * (startupRateDenominator - startupRateNumerator) ^ 4
  have hd := startupRate_integers
  have hBn : 0 < B := Nat.mul_pos (Nat.pow_pos (hd.1.trans hd.2))
    (Nat.pow_pos (Nat.sub_pos_of_lt hd.2))
  have hB : (0 : ℝ) < B := by exact_mod_cast hBn
  have hid : (2 : ℝ) ^ t * seedVariationTail n = (A : ℝ) / B := by
    rw [seedVariationTail_exact, seedVariationRate_fraction,
      cubicTailFormula_integer n _ _ hd.2]
    dsimp [A, B]
    push_cast
    ring
  rw [hid]
  change 25 * A < 24 * B ↔ _
  constructor
  · intro h
    have hr : (25 : ℝ) * A < 24 * B := by exact_mod_cast h
    have hdiv : (A : ℝ) / B < 24 / 25 := (div_lt_iff₀ hB).mpr (by linarith)
    linarith
  · intro h
    have hdiv : (A : ℝ) / B < 24 / 25 := by linarith
    have hr := (div_lt_iff₀ hB).mp hdiv
    exact_mod_cast (show (25 : ℝ) * A < 24 * B by linarith)

/-- Every index below sixteen fails, even with the weaker multiplier guard t≥32. -/
theorem startup_small_index_fails {t n : ℕ} (ht : 32 ≤ t) (hn : n < 16) :
    ¬ startupAccept t n := by
  have hr : (1 / 4 : ℝ) < seedVariationRate := by linarith [seedVariationRate_bounds.1]
  have hp := pow_lt_pow_left₀ hr (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (16 : ℕ) ≠ 0)
  have hterm : (4913 / 4294967296 : ℝ) < seedVariationTerm 16 := by
    norm_num [seedVariationTerm] at hp ⊢
    linarith
  have htail : seedVariationTerm 16 ≤ seedVariationTail n := by
    have h := seedVariationTail_step 16
    have hnonneg := seedVariationTail_nonneg 17
    have hmono := seedVariationTail_strictAnti hn
    linarith
  have hpow : (4294967296 : ℝ) ≤ (2 : ℝ) ^ t := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ht
    norm_num at h
    exact h
  have hmass := mul_le_mul hpow htail (seedVariationTerm_pos 16).le (by positivity)
  have hlarge : 1 < (2 : ℝ) ^ t * seedVariationTail n := by nlinarith
  rw [startupAccept_iff]
  linarith

/-- A successful integer test occurs by the explicit search endpoint. -/
theorem exists_startupAccept {t : ℕ} (ht : 25637 ≤ t) : ∃ n, startupAccept t n :=
  ⟨startupFixedIndex t - 1, (startupAccept_iff _ _).mpr (startupFixedIndex_residual_pos ht)⟩

/-- Computable least successful integer test; its existence proof is erased. -/
def startupIndex (t : ℕ) (ht : 25637 ≤ t) : ℕ := Nat.find (exists_startupAccept ht)

/-- The selected startup has positive actual residual. -/
theorem startupIndex_residual_pos (t : ℕ) (ht : 25637 ≤ t) :
    0 < (24 / 25 : ℝ) - (2 : ℝ) ^ t * seedVariationTail (startupIndex t ht) :=
  (startupAccept_iff _ _).mp (Nat.find_spec (exists_startupAccept ht))

/-- The least successful index lies in the manuscript's finite search interval. -/
theorem startupIndex_bounds (t : ℕ) (ht : 25637 ≤ t) :
    16 ≤ startupIndex t ht ∧ startupIndex t ht ≤ startupFixedIndex t - 1 := by
  constructor
  · by_contra h
    exact startup_small_index_fails (n := startupIndex t ht) (by omega : 32 ≤ t) (by omega)
      (Nat.find_spec (exists_startupAccept ht))
  · exact Nat.find_min' (exists_startupAccept ht)
      ((startupAccept_iff _ _).mpr (startupFixedIndex_residual_pos ht))

/-- Every earlier index has nonpositive actual residual. -/
theorem startupIndex_minimal (t : ℕ) (ht : 25637 ≤ t) {n : ℕ}
    (hn : n < startupIndex t ht) :
    (24 / 25 : ℝ) - (2 : ℝ) ^ t * seedVariationTail n ≤ 0 := by
  have h := Nat.find_min (exists_startupAccept ht) hn
  rw [startupAccept_iff] at h
  exact le_of_not_gt h

end WordCertDensity.Construction
