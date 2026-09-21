/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.StartupGuards

/-! # Positive residual at the explicit startup-search endpoint -/

namespace WordCertDensity.Construction

/-- The exact hundred-step guard gives a real-exponent bound at each positive
integer, without restricting the integer to multiples of one hundred. -/
theorem seedVariationRate_rpow_bound {n : ℕ} (hn : 0 < n) :
    seedVariationRate ^ n < (2 : ℝ) ^ (-131 * (n : ℝ) / 100) := by
  apply (pow_lt_pow_iff_left₀ (pow_nonneg seedVariationRate_contracts.1.le n)
    (Real.rpow_nonneg (by norm_num) _) (by norm_num : (100 : ℕ) ≠ 0)).mp
  have hid : ((2 : ℝ) ^ (-131 * (n : ℝ) / 100)) ^ (100 : ℕ) =
      (((2 : ℝ) ^ 131)⁻¹) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num only [Nat.cast_ofNat]
    rw [show (-131 * (n : ℝ) / 100) * (100 : ℝ) = -(131 * (n : ℝ)) by ring]
    rw [Real.rpow_neg (by norm_num), Real.rpow_mul (by norm_num), Real.rpow_natCast]
    norm_num only [Real.rpow_ofNat, inv_pow]
    simp only [one_div, inv_pow]
  rw [hid]
  exact seedVariationRate_power_hundred hn

/-- The lower ceiling inequality pays the full exponential startup budget. -/
theorem startup_exponential_budget {t L N : ℕ} (hN : 0 < N)
    (hbudget : 100 * (t + 3 * L + 214) ≤ 131 * N) :
    (2 : ℝ) ^ (t + 3 * L) * seedVariationRate ^ N < ((2 : ℝ) ^ 214)⁻¹ := by
  have hr := seedVariationRate_rpow_bound hN
  have hb : (100 : ℝ) * (t + 3 * L + 214) ≤ 131 * N := by exact_mod_cast hbudget
  calc
    _ < (2 : ℝ) ^ (t + 3 * L) * (2 : ℝ) ^ (-131 * (N : ℝ) / 100) :=
      mul_lt_mul_of_pos_left hr (by positivity)
    _ = (2 : ℝ) ^ ((t : ℝ) + 3 * L - 131 * N / 100) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    _ ≤ (2 : ℝ) ^ (-214 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = _ := by rw [Real.rpow_neg (by norm_num)]; norm_num only [Real.rpow_ofNat]

/-- Literal R.searchendpoint: the tail one stage before the fixed index
already lies below the retained tiny rational budget. -/
theorem startupFixedIndex_tail_budget {t : ℕ} (ht : 25637 ≤ t) :
    (2 : ℝ) ^ t * seedVariationTail (startupFixedIndex t - 1) <
      (64 / 25 : ℝ) * ((2 : ℝ) ^ 214)⁻¹ := by
  let N := startupFixedIndex t
  let L := Nat.clog 2 (t + 1)
  have hg := startupFixedIndex_guards ht
  have hN : 17 ≤ N := hg.1
  have hNpos : 0 < N := by omega
  have hb := startup_exponential_budget hNpos hg.2.2.2
  have htL : t ≤ 2 ^ L := by
    have h := Nat.le_pow_clog (by norm_num : 1 < 2) (t + 1)
    dsimp [L]
    omega
  have hNr : (5 : ℝ) * N ≤ 4 * t := by exact_mod_cast hg.2.2.1
  have htLr : (t : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast htL
  have hNbound : (N : ℝ) ≤ (4 / 5 : ℝ) * (2 : ℝ) ^ L := by linarith
  have hc := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ N) hNbound 3
  have hc' : (N : ℝ) ^ 3 ≤ (64 / 125 : ℝ) * (2 : ℝ) ^ (3 * L) := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm, show (4 / 5 : ℝ) ^ 3 = 64 / 125 by norm_num]
      using hc
  have hr := seedVariationRate_bounds
  have hp : 0 < seedVariationRate ^ (N - 1) := pow_pos seedVariationRate_contracts.1 _
  have heq : seedVariationRate ^ N = seedVariationRate ^ (N - 1) * seedVariationRate := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ N)]
  have hprev : seedVariationRate ^ (N - 1) < (5 / 2 : ℝ) * seedVariationRate ^ N := by
    rw [heq]
    nlinarith [mul_pos hp (sub_pos.mpr hr.1)]
  have htail := cubicTailFormula_lt_twice (n := N - 1) (by omega)
    seedVariationRate_contracts.1 hr.2.le
  rw [← seedVariationTail_exact] at htail
  have hcast : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ N))
  rw [hcast] at htail
  have hproduct := mul_lt_mul_of_le_of_lt_of_pos_of_nonneg hc' hprev
    (by positivity : (0 : ℝ) < (N : ℝ) ^ 3)
    (mul_nonneg (by norm_num) (pow_nonneg seedVariationRate_contracts.1.le N))
  have hscaled := mul_lt_mul_of_pos_left hproduct (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ t)
  have hfirst := mul_lt_mul_of_pos_left htail (by positivity : (0 : ℝ) < (2 : ℝ) ^ t)
  have hlast := mul_lt_mul_of_pos_left hb (by norm_num : (0 : ℝ) < 64 / 25)
  have hid : (2 : ℝ) ^ (t + 3 * L) = (2 : ℝ) ^ t * (2 : ℝ) ^ (3 * L) := pow_add _ _ _
  rw [hid] at hlast
  change (2 : ℝ) ^ t * seedVariationTail (N - 1) < _
  nlinarith

/-- The fixed endpoint is a valid positive-residual candidate. -/
theorem startupFixedIndex_residual_pos {t : ℕ} (ht : 25637 ≤ t) :
    0 < (24 / 25 : ℝ) - (2 : ℝ) ^ t * seedVariationTail (startupFixedIndex t - 1) := by
  have h := startupFixedIndex_tail_budget ht
  have hsmall : (64 / 25 : ℝ) * ((2 : ℝ) ^ 214)⁻¹ < 24 / 25 := by norm_num
  linarith

end WordCertDensity.Construction
