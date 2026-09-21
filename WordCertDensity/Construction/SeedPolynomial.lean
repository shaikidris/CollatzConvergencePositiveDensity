/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.SeedFailure

/-! # The retained polynomial envelope for seed failure -/

@[expose] public section

namespace WordCertDensity.Construction

/-- The manuscript's retained degree-465 exponential-series coefficient. -/
noncomputable def seedFailureConstant : ℝ := 8 * (Nat.factorial 465 : ℝ) * 576 ^ 465

/-- A single exponential-series term bounds negative exponential decay by a reciprocal power. -/
theorem exp_neg_le_factorial_div {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.exp (-x) ≤ (Nat.factorial k : ℝ) / x ^ k := by
  have hf : (0 : ℝ) < Nat.factorial k := by exact_mod_cast Nat.factorial_pos k
  have h := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp x hx.le k)
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-x)).le
  rw [mul_assoc, mul_comm (Nat.factorial k : ℝ), ← mul_assoc,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] at hm
  exact (le_div_iff₀ (pow_pos hx k)).mpr (by simpa only [mul_comm] using hm)

/-- Degree 465 gives exactly the decay exponent -92 after the retained linear prefactor. -/
theorem seed_exponential_polynomial {b : ℝ} (hb : 1 ≤ b) :
    8 * b * Real.exp (-(b ^ (1 / 5 : ℝ) / 576)) ≤ seedFailureConstant * b ^ (-92 : ℝ) := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hx : 0 < b ^ (1 / 5 : ℝ) / 576 := by positivity
  have h := exp_neg_le_factorial_div hx 465
  have hp : (b ^ (1 / 5 : ℝ) / 576) ^ 465 = b ^ (93 : ℕ) / 576 ^ 465 := by
    rw [div_pow, ← Real.rpow_mul_natCast hbpos.le,
      show (1 / 5 : ℝ) * (465 : ℕ) = (93 : ℕ) by norm_num, Real.rpow_natCast]
  rw [hp] at h
  calc
    _ ≤ 8 * b * ((Nat.factorial 465 : ℝ) / (b ^ (93 : ℕ) / 576 ^ 465)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = seedFailureConstant * b ^ (-92 : ℝ) := by
      rw [Real.rpow_neg hbpos.le, show (92 : ℝ) = (92 : ℕ) by norm_num, Real.rpow_natCast]
      unfold seedFailureConstant
      field_simp

/-- The printed looser exponential envelope is dominated by the retained polynomial coefficient. -/
theorem seed_printed_exponential_le {b : ℝ} (hb : 1 ≤ b) :
    2 * Real.exp (-(b ^ (1 / 5 : ℝ) / (2333 / 100))) ≤ seedFailureConstant * b ^ (-92 : ℝ) := by
  have he : Real.exp (-(b ^ (1 / 5 : ℝ) / (2333 / 100))) ≤
      Real.exp (-(b ^ (1 / 5 : ℝ) / 576)) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
  have h := mul_le_mul he (show (2 : ℝ) ≤ 8 * b by linarith)
    (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos _).le
  have h' : 2 * Real.exp (-(b ^ (1 / 5 : ℝ) / (2333 / 100))) ≤
      8 * b * Real.exp (-(b ^ (1 / 5 : ℝ) / 576)) := by
    simpa only [mul_comm] using h
  exact h'.trans (seed_exponential_polynomial hb)

/-- The actual finite seed failure satisfies the retained S92 times b^-92 bound. -/
theorem seedWords_failure_polynomial {b : ℕ} (hb : 32 ^ 5 ≤ b) :
    1 - Reference.stoppingMass (seedWords b) ≤ seedFailureConstant * (b : ℝ) ^ (-92 : ℝ) := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have he : 2 * Real.exp (-((b : ℝ) ^ (1 / 5 : ℝ) / (4 + 3 / 512))) ≤
      2 * Real.exp (-((b : ℝ) ^ (1 / 5 : ℝ) / (2333 / 100))) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
  exact (seedWords_failure_power_le hb).trans (he.trans (seed_printed_exponential_le hb1))

/-- The retained coefficient fits strictly below the printed binary ceiling. -/
theorem seedFailureConstant_lt_two_pow : seedFailureConstant < (2 : ℝ) ^ 8838 := by
  have hfactorial (k : ℕ) : (Nat.factorial k : ℝ) ≤ (k : ℝ) ^ k := by
    exact_mod_cast Nat.factorial_le_pow k
  have hf0 := hfactorial 465
  have hf : (Nat.factorial 465 : ℝ) < (512 : ℝ) ^ 465 :=
    hf0.trans_lt (pow_lt_pow_left₀ (by norm_num : (465 : ℝ) < 512)
      (by norm_num) (by decide : (465 : ℕ) ≠ 0))
  have hg : (576 : ℝ) ^ 465 ≤ (1024 : ℝ) ^ 465 :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) 465
  calc
    seedFailureConstant < (8 * (512 : ℝ) ^ 465) * 576 ^ 465 :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hf (by norm_num)) (by positivity)
    _ ≤ (8 * (512 : ℝ) ^ 465) * 1024 ^ 465 :=
      mul_le_mul_of_nonneg_left hg (by positivity)
    _ = (2 : ℝ) ^ 8838 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, show (512 : ℝ) = 2 ^ 9 by norm_num,
        show (1024 : ℝ) = 2 ^ 10 by norm_num, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]

end WordCertDensity.Construction
