/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.TerminalRecipe
public import WordCertDensity.Analytic.LocalPrimitive.WhiteExit
import Mathlib.Tactic

/-! # The terminal tail's size condition from actual selected triangles -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The proved primitive triangle margin supplies the terminal tail's
vertical-size condition at every actual point of a selected triangle. -/
theorem selected_triangle_depth_size {n a j : ℕ} (hn : 0 < n) (ha : 2 * a < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (top l : ℤ)
    (hsel : isSelectedPhaseTriangle n ξ a top)
    (hstart : inPhaseTriangleIntMul n ξ a top j l) :
    5 * (top - l).toNat ≤ 16 * (n / 2 - j) := by
  have hmargin := firstPassageExit_before_terminal n a j
    (5 * ((top - l).toNat / 16) + 9) (top - l).toNat top l ξ
    hsel hstart rfl le_rfl hn ha hξ
  omega

/-- The weighted terminal event is paid from the actual selected triangle,
with its vertical-size premise derived rather than assumed. -/
theorem selected_triangle_terminal_payment {n a j : ℕ} (hn : 0 < n) (ha : 2 * a < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (top l : ℤ)
    (hsel : isSelectedPhaseTriangle n ξ a top)
    (hstart : inPhaseTriangleIntMul n ξ a top j l) (B L : ℕ)
    (hs : 0 < (top - l).toNat) (hm : localPrimitiveM B ≤ n / 2 - j)
    (hL : (top - l).toNat / 2 + 1 ≤ L) :
    layerWeight B (n / 2 - j) * Gated.probability (Reference.wordPMF (2 * L))
      (terminalPassageEvent (top - l).toNat (n / 2 - j) (localPrimitiveP B)) ≤ 1 / 4 :=
  terminal_recipe_payment_le_quarter _ _ B L hs hm
    (selected_triangle_depth_size hn ha ξ hξ top l hsel hstart) hL

end WordCertDensity.LocalPrimitive
