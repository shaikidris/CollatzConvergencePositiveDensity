/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.TerminalTail
public import WordCertDensity.Analytic.LocalPrimitive.Parameters
public import WordCertDensity.Analytic.LocalPrimitive.LayerInduction
import Mathlib.Tactic

/-! # Terminal-event payment under the fixed layer threshold -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The printed threshold supplies the window and minimum-size guards for
the original terminal probability estimate. -/
theorem terminal_recipe_probability_le (s m B L : ℕ) (hs : 0 < s)
    (hm : localPrimitiveM B ≤ m) (hsize : 5 * s ≤ 16 * m)
    (hL : s / 2 + 1 ≤ L) :
    Gated.probability (Reference.wordPMF (2 * L))
      (terminalPassageEvent s m (localPrimitiveP B)) ≤ Real.exp (-(m : ℝ) / 640) := by
  have hfloor := (localPrimitiveM_ge_floor B).trans hm
  have hwindow := (localPrimitiveM_ge_horizon B).trans hm
  exact terminalPassage_probability_le s m (localPrimitiveP B) L hs (by omega)
    hsize (by omega) hL

/-- The actual original-law terminal event, weighted by the layer weight,
costs at most one quarter under the fixed manuscript threshold. -/
theorem terminal_recipe_payment_le_quarter (s m B L : ℕ) (hs : 0 < s)
    (hm : localPrimitiveM B ≤ m) (hsize : 5 * s ≤ 16 * m)
    (hL : s / 2 + 1 ≤ L) :
    layerWeight B m * Gated.probability (Reference.wordPMF (2 * L))
      (terminalPassageEvent s m (localPrimitiveP B)) ≤ 1 / 4 := by
  have htail := (localPrimitiveM_ge_tail B).trans hm
  have htail' : (2560 * ((B : ℝ) + 1)) ^ 2 ≤ (m : ℝ) := by exact_mod_cast htail
  exact (mul_le_mul_of_nonneg_left
    (terminal_recipe_probability_le s m B L hs hm hsize hL)
    (layerWeight_pos B m).le).trans (terminalPayment_le_quarter htail')

end WordCertDensity.LocalPrimitive
