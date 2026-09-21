/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.TerminalGeometry
public import WordCertDensity.Analytic.LocalPrimitive.PostExitBound
import Mathlib.Tactic

/-! # Actual long-exit geometric and numerical adapters -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The fixed M and the long-depth inequality supply the square-root guard
required by the original-law large-triangle estimate. -/
theorem long_depth_sqrt_guard (B m s : ℕ) (hB : 0 < B)
    (hm : localPrimitiveM B ≤ m)
    (hlong : (m : ℝ) / (localPrimitiveEtaDenom B : ℝ) < (s : ℝ)) :
    (localPrimitiveZ B : ℝ) ≤ Real.sqrt s := by
  have hden : (0 : ℝ) < localPrimitiveEtaDenom B := by
    exact_mod_cast localPrimitiveEtaDenom_pos hB
  have hguard : (localPrimitiveZ B : ℝ) ^ 2 * (localPrimitiveEtaDenom B : ℝ) ≤ m := by
    exact_mod_cast (localPrimitiveM_ge_terminal B).trans hm
  have hdepth := (div_lt_iff₀ hden).mp hlong
  apply Real.le_sqrt_of_sq_le
  nlinarith

/-- All E-L4 admissibility premises follow from the actual selected triangle
and the long-depth branch of the fixed layer recipe. -/
theorem selected_triangle_long_admissible {n a j : ℕ} (hn : 0 < n) (ha : 2 * a < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (top l : ℤ)
    (hsel : isSelectedPhaseTriangle n ξ a top)
    (hstart : inPhaseTriangleIntMul n ξ a top j l) (B : ℕ) (hB : 0 < B)
    (hm : localPrimitiveM B ≤ n / 2 - j)
    (hlong : ((n / 2 - j : ℕ) : ℝ) / (localPrimitiveEtaDenom B : ℝ) < (top - l).toNat) :
    longCrossingAdmissible n ξ a j top l B (localPrimitiveA B)
      (localPrimitiveH B) (localPrimitiveP B) (localPrimitiveZ B) := by
  exact ⟨hn, hξ, ha, hsel, hstart, hB, localPrimitiveP_pos B, rfl, rfl, rfl,
    long_depth_sqrt_guard B _ _ hB hm hlong⟩

/-- The actual long triangle pays the post-exit expectation at the exact
local epsilon and in the coefficient form consumed by LayerEstimates. -/
theorem selected_triangle_long_postexit {n a j : ℕ} (hn : 0 < n) (ha : 2 * a < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (top l : ℤ)
    (hsel : isSelectedPhaseTriangle n ξ a top)
    (hstart : inPhaseTriangleIntMul n ξ a top j l) (B L : ℕ) (hB : 0 < B)
    (hm : localPrimitiveM B ≤ n / 2 - j)
    (hlong : ((n / 2 - j : ℕ) : ℝ) / (localPrimitiveEtaDenom B : ℝ) < (top - l).toNat)
    (hL : (top - l).toNat / 2 + 1 + localPrimitiveP B ≤ L) :
    (postPassageProductMoment n ξ (top - l).toNat j l B L
      (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2))).toReal ≤ 1 / (4 * (10 : ℝ) ^ B) := by
  have he := postExit_product_le_four_delta hn ξ hξ a j top l B L
    (selected_triangle_long_admissible hn ha ξ hξ top l hsel hstart B hB hm hlong) hL
  have hε : localEpsilon = 1 / (2 : ℝ) ^ 78 := by simp [localEpsilon]
  rw [hε]
  convert he using 1
  unfold localPrimitiveDeltaDenom
  push_cast
  ring

end WordCertDensity.LocalPrimitive
