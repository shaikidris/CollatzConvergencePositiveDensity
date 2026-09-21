/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.Parameters
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

/-! # Paying the predictable-mark moment with the fixed Appendix E recipe -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped ENNReal

/-- The exact quarter-mark moment has its elementary exponential bound. -/
theorem quarterMarkMoment_le_exp {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1) (k : ℕ) :
    (((1 / 4 : ℝ≥0∞) * ENNReal.ofReal (1 - 2 * ε ^ 2) + 3 / 4) ^ k).toReal ≤
      Real.exp (-(ε ^ 2 * (k : ℝ) / 2)) := by
  have hb : ((1 / 4 : ℝ≥0∞) * ENNReal.ofReal (1 - 2 * ε ^ 2) + 3 / 4).toReal =
      1 - ε ^ 2 / 2 := by
    rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith)]
    norm_num
    ring
  rw [ENNReal.toReal_pow, hb]
  calc
    _ ≤ Real.exp (-(ε ^ 2 / 2)) ^ k := by
      apply pow_le_pow_left₀ (by nlinarith [sq_nonneg ε])
      have he := Real.add_one_le_exp (-(ε ^ 2 / 2))
      linarith
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- A simple exponential lower bound pays the printed delta denominator. -/
theorem deltaDenom_le_exp_eight (B : ℕ) :
    (localPrimitiveDeltaDenom B : ℝ) ≤ Real.exp (8 * ((B : ℝ) + 1)) := by
  have he : (16 : ℝ) ≤ Real.exp 8 := by
    have h := Real.add_one_le_exp (4 : ℝ)
    rw [show (8 : ℝ) = 4 + 4 by norm_num, Real.exp_add]
    nlinarith
  have hp : (16 : ℝ) * 10 ^ B ≤ Real.exp 8 ^ (B + 1) := by
    induction B with
    | zero => simpa using he
    | succ B ih =>
        rw [pow_succ (10 : ℝ), ← mul_assoc, pow_succ (Real.exp 8)]
        exact mul_le_mul ih (by linarith) (by positivity) (by positivity)
  unfold localPrimitiveDeltaDenom
  push_cast
  rw [← Real.exp_nat_mul] at hp
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hp

/-- The manuscript's epsilon and K make the exact mark moment at most delta. -/
theorem postExit_recipe_moment_le_delta (B : ℕ) :
    (((1 / 4 : ℝ≥0∞) * ENNReal.ofReal (1 - 2 * (1 / (2 : ℝ) ^ 78) ^ 2) + 3 / 4) ^
      localPrimitiveK B).toReal ≤ 1 / (localPrimitiveDeltaDenom B : ℝ) := by
  have hm := quarterMarkMoment_le_exp
    (ε := 1 / (2 : ℝ) ^ 78) (by norm_num) (localPrimitiveK B)
  have hex : (1 / (2 : ℝ) ^ 78) ^ 2 * (localPrimitiveK B : ℝ) / 2 =
      8 * ((B : ℝ) + 1) := by
    unfold localPrimitiveK
    push_cast
    norm_num
    ring
  rw [hex] at hm
  apply hm.trans
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by exact_mod_cast localPrimitiveDeltaDenom_pos B)
    (deltaDenom_le_exp_eight B)

end WordCertDensity.LocalPrimitive
