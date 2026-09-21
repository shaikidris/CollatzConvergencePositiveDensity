/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.StartupResidual
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # The actual seed budget, startup and uniform future-mark control -/

namespace WordCertDensity.Construction

/-- Exact natural recipe for F_b, retaining the upstream primitive coefficient. -/
noncomputable def seedVariationBudget (b : ℕ) : ℕ :=
  2 ^ 467 * b * 16 ^ b * (2 * Analytic.primitiveCoefficient * 20 ^ 6409 + 3)

/-- The integer recipe agrees with the coefficient in the physical variation bound. -/
theorem seedVariationBudget_cast (b : ℕ) :
    (seedVariationBudget b : ℝ) = seedVariationCoefficient b := by
  unfold seedVariationBudget seedVariationCoefficient
  rw [Analytic.mixingCoefficient_eq_natCast]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, add_assoc,
    show (2 : ℝ) + 1 = 3 by norm_num]

/-- The literal ceiling-log startup multiplier exponent. -/
noncomputable def seedStartupExponent (b : ℕ) : ℕ := Nat.clog 2 (seedVariationBudget b)

/-- Agreement with the ceiling-log definition in R.variationdata. -/
theorem seedStartupExponent_eq (b : ℕ) :
    seedStartupExponent b = ⌈Real.logb 2 (seedVariationCoefficient b)⌉₊ := by
  rw [← seedVariationBudget_cast]
  simpa only [Nat.cast_ofNat, seedStartupExponent] using
    (Real.natCeil_logb_natCast 2 (seedVariationBudget b)).symm

/-- The dyadic multiplier dominates the actual variation coefficient. -/
theorem seedStartupExponent_covers (b : ℕ) :
    seedVariationCoefficient b ≤ (2 : ℝ) ^ seedStartupExponent b := by
  rw [← seedVariationBudget_cast]
  exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (seedVariationBudget b)

/-- The actual budget exponent is at least four times the seed depth. -/
theorem seedStartupExponent_depth {b : ℕ} (hb : 1 ≤ b) :
    4 * b ≤ seedStartupExponent b := by
  have hpow : 2 ^ (4 * b) ≤ seedVariationBudget b := by
    rw [pow_mul]
    norm_num only [show (2 : ℕ) ^ 4 = 16 by norm_num]
    unfold seedVariationBudget
    have hc : 1 ≤ 2 * Analytic.primitiveCoefficient * 20 ^ 6409 + 3 := by omega
    have htwo : 1 ≤ (2 : ℕ) ^ 467 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
    calc
      16 ^ b = 1 * 1 * 16 ^ b * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right (16 ^ b) (Nat.mul_le_mul htwo hb)) hc
  exact (Nat.le_log_of_pow_le (by norm_num) hpow).trans (Nat.log_le_clog _ _)

/-- Every permitted seed depth meets the scalar startup guard. -/
theorem seedStartupExponent_guard {b : ℕ} (hb : 32 ^ 5 ≤ b) :
    25637 ≤ seedStartupExponent b := by
  have h := seedStartupExponent_depth (b := b) (by omega)
  omega

/-- The actual seed's least startup, specialized from the integer search. -/
noncomputable def seedStartupIndex (b : ℕ) (hb : 32 ^ 5 ≤ b) : ℕ :=
  startupIndex (seedStartupExponent b) (seedStartupExponent_guard hb)

/-- The whole positive residual for the actual seed coefficient. -/
noncomputable def seedStartupResidual (b : ℕ) (hb : 32 ^ 5 ≤ b) : ℝ :=
  startupResidual (seedStartupExponent b) (seedStartupExponent_guard hb)

/-- The actual seed has positive residual and the specified bounded startup. -/
theorem seedStartup_spec (b : ℕ) (hb : 32 ^ 5 ≤ b) :
    16 ≤ seedStartupIndex b hb ∧
    seedStartupIndex b hb ≤ startupFixedIndex (seedStartupExponent b) - 1 ∧
    0 < seedStartupResidual b hb := by
  have h := startupIndex_bounds (seedStartupExponent b) (seedStartupExponent_guard hb)
  exact ⟨h.1, h.2, startupIndex_residual_pos _ _⟩

/-- Every later physical mark is within the paid variation budget, uniformly
over all roots satisfying the original height guard. -/
theorem physicalSeedMark_startup_tail {b root j : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (hj : seedStartupIndex b hb ≤ j) :
    |physicalSeedMark b j root - physicalSeedMark b (seedStartupIndex b hb) root| ≤
      24 / 25 - seedStartupResidual b hb := by
  calc
    _ ≤ seedVariationCoefficient b * seedVariationTail (seedStartupIndex b hb) :=
      physicalSeedMark_finite_tail hb hr hj
    _ ≤ (2 : ℝ) ^ seedStartupExponent b * seedVariationTail (seedStartupIndex b hb) :=
      mul_le_mul_of_nonneg_right (seedStartupExponent_covers b) (seedVariationTail_nonneg _)
    _ = _ := by unfold seedStartupResidual startupResidual seedStartupIndex; ring

/-- The limiting physical mark obeys the same actual startup budget. -/
theorem physicalSeedLimit_startup_tail {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) :
    |physicalSeedLimit b root - physicalSeedMark b (seedStartupIndex b hb) root| ≤
      24 / 25 - seedStartupResidual b hb := by
  calc
    _ ≤ seedVariationCoefficient b * seedVariationTail (seedStartupIndex b hb) :=
      physicalSeedMark_limit_tail hb hr
    _ ≤ (2 : ℝ) ^ seedStartupExponent b * seedVariationTail (seedStartupIndex b hb) :=
      mul_le_mul_of_nonneg_right (seedStartupExponent_covers b) (seedVariationTail_nonneg _)
    _ = _ := by unfold seedStartupResidual startupResidual seedStartupIndex; ring

end WordCertDensity.Construction
