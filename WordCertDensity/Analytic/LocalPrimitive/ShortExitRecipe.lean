/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LayerRatios
public import WordCertDensity.Analytic.LocalPrimitive.Parameters
public import WordCertDensity.Analytic.LocalPrimitive.Majorant
import Mathlib.Tactic

/-! # Fixed-recipe bounds for every possible short first-passage time -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The exact pair loss agrees with the denominator used by the recipe. -/
theorem localPairLoss_eq_invDDenom :
    pairLoss localEpsilon = 1 / (localPrimitiveDDenom : ℝ) := by
  norm_num [pairLoss, localEpsilon, localPrimitiveDDenom]

/-- Every short first passage leaves ample distance and has the printed
relative-time bound, including the zero-depth case whose first passage is one. -/
theorem short_exit_recipe_bounds (B m s q : ℕ) (hB : 0 < B)
    (hm : localPrimitiveM B ≤ m)
    (hs : (s : ℝ) ≤ (m : ℝ) / (localPrimitiveEtaDenom B : ℝ))
    (hq : q ≤ s / 2 + 1) :
    q < m ∧ 2 * q ≤ m ∧ 8 * B * localPrimitiveDDenom ≤ m - q ∧
      32 * B * localPrimitiveDDenom * q ≤ m := by
  have hden : (0 : ℝ) < localPrimitiveEtaDenom B := by
    exact_mod_cast localPrimitiveEtaDenom_pos hB
  have hsN : s * localPrimitiveEtaDenom B ≤ m := by
    exact_mod_cast (le_div_iff₀ hden).mp hs
  have hmN := (localPrimitiveM_ge_entropy B).trans hm
  let X := B * localPrimitiveDDenom
  have hX : 1 ≤ X := Nat.mul_pos hB localPrimitiveDDenom_pos
  have hsX : 32 * X * s ≤ m := by
    simpa [X, localPrimitiveEtaDenom, mul_assoc, mul_comm, mul_left_comm] using hsN
  have hmX : 64 * X ≤ m := by simpa [X, mul_assoc] using hmN
  have hq2 : 2 * q ≤ s + 2 := by omega
  have htime : 32 * X * q ≤ m := by nlinarith
  have hhalf : 2 * q ≤ m := by nlinarith
  have hrem : 8 * X ≤ m - q := by omega
  refine ⟨by omega, hhalf, ?_, ?_⟩
  · simpa [X, mul_assoc] using hrem
  · simpa [X, mul_assoc] using htime

/-- The actual short stop meets the scalar power-ratio hypothesis. -/
theorem short_exit_recipe_relative (B m s q : ℕ) (hB : 0 < B)
    (hm : localPrimitiveM B ≤ m)
    (hs : (s : ℝ) ≤ (m : ℝ) / (localPrimitiveEtaDenom B : ℝ))
    (hq : q ≤ s / 2 + 1) :
    (B : ℝ) * q / m ≤ pairLoss localEpsilon / 32 := by
  have hb := (short_exit_recipe_bounds B m s q hB hm hs hq).2.2.2
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (localPrimitiveM_pos B).trans_le hm
  have hden : (0 : ℝ) < localPrimitiveDDenom := by exact_mod_cast localPrimitiveDDenom_pos
  have hb' : (32 : ℝ) * B * localPrimitiveDDenom * q ≤ m := by exact_mod_cast hb
  rw [localPairLoss_eq_invDDenom]
  apply (div_le_iff₀ hmpos).mpr
  have he : 1 / (localPrimitiveDDenom : ℝ) / 32 * m =
      (m : ℝ) / (32 * localPrimitiveDDenom) := by ring
  rw [he]
  apply (le_div_iff₀ (show (0 : ℝ) < 32 * localPrimitiveDDenom by positivity)).mpr
  nlinarith [hb']

end WordCertDensity.LocalPrimitive
