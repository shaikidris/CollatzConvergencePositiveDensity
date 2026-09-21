/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ExactVariationTail
import Mathlib.Data.Nat.Log

/-! # Exact scalar guards for the bounded variation startup search -/

namespace WordCertDensity.Construction

/-- The hundred-step decay bound, using a small rational intermediate to avoid
expanding the original rate to exponent 9200. -/
theorem seedVariationRate_hundred :
    seedVariationRate ^ 100 < ((2 : ℝ) ^ 131)⁻¹ := by
  have hr : seedVariationRate < (10083 / 25000 : ℝ) := by
    norm_num [seedVariationRate, seedTagGrowth, seedScheduleRate]
  have hp := pow_lt_pow_left₀ hr (seedVariationRate_contracts.1.le)
    (by norm_num : (100 : ℕ) ≠ 0)
  have hq : (10083 / 25000 : ℝ) ^ 100 < ((2 : ℝ) ^ 131)⁻¹ := by norm_num
  exact hp.trans hq

/-- The hundred-step comparison applies to every positive exponent. -/
theorem seedVariationRate_power_hundred {n : ℕ} (hn : 0 < n) :
    (seedVariationRate ^ n) ^ 100 < (((2 : ℝ) ^ 131)⁻¹) ^ n := by
  have h := pow_lt_pow_left₀ seedVariationRate_hundred
    (pow_nonneg seedVariationRate_contracts.1.le 100) hn.ne'
  simpa only [← pow_mul, Nat.mul_comm] using h

private theorem startup_log_budget {k : ℕ} (hk : 14 ≤ k) :
    1500 * (k + 1) + 107650 ≤ 24 * 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    nlinarith

/-- Integer ceiling log at t+1 equals floor log at t plus one. -/
theorem startup_clog_eq {t : ℕ} (ht : 0 < t) :
    Nat.clog 2 (t + 1) = Nat.log 2 t + 1 := by
  apply Nat.le_antisymm
  · apply Nat.clog_le_of_le_pow
    exact Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) t)
  · have h := (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mpr
      (Nat.lt_succ_of_le (Nat.pow_log_le_self 2 ht.ne'))
    exact Nat.succ_le_of_lt h

/-- The logarithmic overhead fits into the retained linear search budget. -/
theorem startup_clock_budget {t : ℕ} (ht : 25637 ≤ t) :
    1500 * Nat.clog 2 (t + 1) + 107650 ≤ 24 * t := by
  have htpos : 0 < t := by omega
  have hk : 14 ≤ Nat.log 2 t := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have h := startup_log_budget hk
  have hp := Nat.pow_log_le_self 2 htpos.ne'
  rw [startup_clog_eq htpos]
  omega

/-- The exact integer ceiling defining the fixed startup-search endpoint. -/
def startupFixedIndex (t : ℕ) : ℕ :=
  (100 * (t + 3 * Nat.clog 2 (t + 1) + 214) + 130) / 131

/-- Cleared-integer form of R.searchguard, together with the lower ceiling
inequality needed to pay the exponential budget at the search endpoint. -/
theorem startupFixedIndex_guards {t : ℕ} (ht : 25637 ≤ t) :
    17 ≤ startupFixedIndex t ∧
    131 * startupFixedIndex t ≤ 100 * t + 300 * Nat.clog 2 (t + 1) + 21530 ∧
    5 * startupFixedIndex t ≤ 4 * t ∧
    100 * (t + 3 * Nat.clog 2 (t + 1) + 214) ≤ 131 * startupFixedIndex t := by
  have h := startup_clock_budget ht
  unfold startupFixedIndex
  omega

end WordCertDensity.Construction
