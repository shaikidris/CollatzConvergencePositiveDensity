/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.ShortExitRecipe
import Mathlib.Tactic

/-! # Actual layer-weight distortion at short exits and white states -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The fixed local pair loss lies in the unit interval. -/
theorem localPairLoss_mem_unitInterval :
    0 ≤ pairLoss localEpsilon ∧ pairLoss localEpsilon ≤ 1 := by
  unfold pairLoss
  constructor
  · positivity
  · nlinarith [localEpsilon_guard, sq_nonneg localEpsilon]

/-- Every actual short passage has the printed layer-weight distortion. -/
theorem short_exit_weight_ratio (B m s q : ℕ) (hB : 0 < B)
    (hm : localPrimitiveM B ≤ m)
    (hs : (s : ℝ) ≤ (m : ℝ) / (localPrimitiveEtaDenom B : ℝ))
    (hq : q ≤ s / 2 + 1) :
    layerWeight B m ≤ (1 + pairLoss localEpsilon / 8) * layerWeight B (m - q) := by
  have hb := short_exit_recipe_bounds B m s q hB hm hs hq
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (localPrimitiveM_pos B).trans_le hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hr1 : (1 : ℝ) ≤ (m - q : ℕ) := by exact_mod_cast (show 1 ≤ m - q by omega)
  have hd := localPairLoss_mem_unitInterval
  have hratio := layer_power_short_ratio B hmpos
    (show (q : ℝ) ≤ m by exact_mod_cast hb.1.le) hd.1 hd.2
    (short_exit_recipe_relative B m s q hB hm hs hq)
  change (max (m : ℝ) 1) ^ B ≤
    (1 + pairLoss localEpsilon / 8) * (max ((m - q : ℕ) : ℝ) 1) ^ B
  rw [max_eq_left hm1, max_eq_left hr1, Nat.cast_sub hb.1.le]
  exact hratio

/-- A sufficiently distant white state retains half the pair loss after
the one-step change in the actual layer weight. -/
theorem white_layer_weight_ratio (B r : ℕ) (hr : 2 ≤ r)
    (hlarge : 8 * B * localPrimitiveDDenom ≤ r) :
    (1 - pairLoss localEpsilon) * layerWeight B r ≤
      (1 - pairLoss localEpsilon / 2) * layerWeight B (r - 1) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hrem1 : (1 : ℝ) ≤ (r - 1 : ℕ) := by exact_mod_cast (show 1 ≤ r - 1 by omega)
  have hden : (0 : ℝ) < localPrimitiveDDenom := by exact_mod_cast localPrimitiveDDenom_pos
  have hl : (8 : ℝ) * B * localPrimitiveDDenom ≤ r := by exact_mod_cast hlarge
  have hsmall : (B : ℝ) / r ≤ pairLoss localEpsilon / 8 := by
    rw [localPairLoss_eq_invDDenom]
    rw [show 1 / (localPrimitiveDDenom : ℝ) / 8 = 1 / (8 * localPrimitiveDDenom) by ring]
    apply (div_le_div_iff₀ hrpos (by positivity : (0 : ℝ) < 8 * localPrimitiveDDenom)).mpr
    nlinarith
  have hd := localPairLoss_mem_unitInterval
  have hp := layer_power_white_ratio B hr1 hd.1 hd.2 hsmall
  change (1 - pairLoss localEpsilon) * (max (r : ℝ) 1) ^ B ≤
    (1 - pairLoss localEpsilon / 2) * (max ((r - 1 : ℕ) : ℝ) 1) ^ B
  rw [max_eq_left hr1, max_eq_left hrem1, Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one]
  exact hp

end WordCertDensity.LocalPrimitive
