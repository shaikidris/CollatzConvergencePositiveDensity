/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.ShortExitWeights
public import WordCertDensity.Analytic.LocalPrimitive.LayerBridge
import Mathlib.Tactic

/-! # Weighted white-state contraction for the actual integer potential -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The actual white potential retains half the local pair loss after
weighting; the future bound is the literal preceding-layer hypothesis. -/
theorem phaseRemainingPotential_white_half_loss (B n N r : ℕ) (ξ : ZMod (3 ^ n))
    (l : ℤ) (hr : 2 ≤ r) (hrN : r ≤ N) (D : ℝ) (hD : 0 ≤ D)
    (hlarge : 8 * B * localPrimitiveDDenom ≤ r)
    (hfuture : ∀ l', layerWeight B (r - 1) *
      phaseRemainingPotential n ξ N (r - 1) l' ≤ D)
    (hwhite : phaseWhiteAtInt n ξ (N - r) l) :
    layerWeight B r * phaseRemainingPotential n ξ N r l ≤
      D * (1 - pairLoss localEpsilon / 2) := by
  have hk := phaseRemainingPotential_white_weighted_le B n N r ξ l (by omega) hrN D hfuture hwhite
  have hw := white_layer_weight_ratio B r hr hlarge
  have hp := layerWeight_pos B (r - 1)
  calc
    _ ≤ layerWeight B r * ((1 - pairLoss localEpsilon) * D / layerWeight B (r - 1)) :=
      mul_le_mul_of_nonneg_left hk (layerWeight_pos B r).le
    _ = D * ((1 - pairLoss localEpsilon) * layerWeight B r) / layerWeight B (r - 1) := by ring
    _ ≤ D * ((1 - pairLoss localEpsilon / 2) * layerWeight B (r - 1)) /
        layerWeight B (r - 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw hD) hp.le
    _ = _ := by field_simp

/-- At a short white exit, all required future layers belong to the previous
layer bound and the fixed recipe supplies the remaining-distance guard. -/
theorem short_white_exit_weighted_le (B n N m s q : ℕ) (ξ : ZMod (3 ^ n))
    (l : ℤ) (hB : 0 < B) (hm : localPrimitiveM B ≤ m) (hmN : m ≤ N)
    (hs : (s : ℝ) ≤ (m : ℝ) / (localPrimitiveEtaDenom B : ℝ))
    (hq : q ≤ s / 2 + 1) (hqpos : 0 < q) (D : ℝ) (hD : 0 ≤ D)
    (hfuture : ∀ r, r < m → ∀ l', layerWeight B r * phaseRemainingPotential n ξ N r l' ≤ D)
    (hwhite : phaseWhiteAtInt n ξ (N - (m - q)) l) :
    layerWeight B (m - q) * phaseRemainingPotential n ξ N (m - q) l ≤
      D * (1 - pairLoss localEpsilon / 2) := by
  have hb := short_exit_recipe_bounds B m s q hB hm hs hq
  have hDpos := localPrimitiveDDenom_pos
  have hbase : 8 ≤ 8 * B * localPrimitiveDDenom := by nlinarith
  apply phaseRemainingPotential_white_half_loss B n N (m - q) ξ l
    (by omega) (by omega) D hD hb.2.2.1
  · exact hfuture (m - q - 1) (by omega)
  · exact hwhite

end WordCertDensity.LocalPrimitive
