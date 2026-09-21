/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.Parameters
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Scalar payment of the repeated-entry bound by the fixed recipe -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

set_option maxHeartbeats 20000

/-- The geometric entry factor is bounded by its elementary exponential. -/
theorem entry_factor_le_exp (K r : ℕ) :
    Real.exp (K : ℝ) * (3 / 4 : ℝ) ^ r ≤ Real.exp ((K : ℝ) - (r : ℝ) / 4) := by
  have hq : (3 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by
    have h := Real.add_one_le_exp (-(1 / 4 : ℝ))
    linarith
  calc
    _ ≤ Real.exp (K : ℝ) * Real.exp (-(1 / 4 : ℝ)) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hq _) (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

/-- An elementary exponential dominates the printed delta denominator. -/
theorem deltaDenom_le_exp (B : ℕ) :
    (localPrimitiveDeltaDenom B : ℝ) ≤ Real.exp (16 * ((B : ℝ) + 1)) := by
  have he : (16 : ℝ) ≤ Real.exp 16 := by
    have h := Real.add_one_le_exp (16 : ℝ)
    linarith
  have hp : (16 : ℝ) * 10 ^ B ≤ Real.exp 16 ^ (B + 1) := by
    induction B with
    | zero => simpa using he
    | succ B ih =>
        rw [pow_succ (10 : ℝ), ← mul_assoc, pow_succ (Real.exp 16)]
        exact mul_le_mul ih (by linarith) (by positivity) (by positivity)
  unfold localPrimitiveDeltaDenom
  push_cast
  rw [← Real.exp_nat_mul] at hp
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hp

/-- The recipe pays the full repeated-entry event bound by delta. -/
theorem entry_recipe_le_delta (B : ℕ) :
    Real.exp (localPrimitiveK B : ℝ) * (3 / 4 : ℝ) ^ (localPrimitiveR B - 1) ≤
      1 / (localPrimitiveDeltaDenom B : ℝ) := by
  unfold localPrimitiveR
  rw [Nat.add_sub_cancel]
  generalize localPrimitiveK B = k
  have h := entry_factor_le_exp k (4 * (k + 16 * (B + 1)))
  have hex : (k : ℝ) -
      ((4 * (k + 16 * (B + 1)) : ℕ) : ℝ) / 4 =
      -(16 * ((B : ℝ) + 1)) := by push_cast; ring
  rw [hex] at h
  apply h.trans
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by exact_mod_cast localPrimitiveDeltaDenom_pos B)
    (deltaDenom_le_exp B)

end WordCertDensity.LocalPrimitive
