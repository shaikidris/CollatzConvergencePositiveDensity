/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PostPassageProductBound
public import WordCertDensity.Analytic.LocalPrimitive.PostExitRecipe
import Mathlib.Tactic

/-! # Original-law post-exit product with the fixed manuscript coefficient -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- Unused future samples do not change the original stopped product moment. -/
theorem postPassageProductMoment_horizon (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (B L L' : ℕ) (z : ℝ≥0∞)
    (hL : s / 2 + 1 + localPrimitiveP B ≤ L) (hLL' : L ≤ L') :
    postPassageProductMoment n ξ s j l B L z =
      postPassageProductMoment n ξ s j l B L' z := by
  have hlen : ∀ u ∈ passagePrefixFamily s, u.length ≤ 2 * L := by
    intro u hu
    have := passagePrefixFamily_length s u hu
    omega
  have hlen' : ∀ u ∈ passagePrefixFamily s, u.length ≤ 2 * L' := by
    intro u hu
    have := hlen u hu
    omega
  unfold postPassageProductMoment
  let F : ValuationWord → ValuationWord → ℝ≥0∞ := fun u v =>
    whiteWindowProduct (extendedPhaseWhite n ξ) z (localPrimitiveP B)
      (j + u.length / 2) (l + u.total) v
  rw [countableStoppedMoment_factor _ _ F hlen,
    countableStoppedMoment_factor _ _ F hlen']
  dsimp [F]
  apply tsum_congr
  intro u
  congr 1
  obtain ⟨i, hi, _⟩ := u.property
  have hidx := i.isLt
  have hr : 2 * L - (u : ValuationWord).length = 2 * (L - ((i : ℕ) + 1)) := by omega
  have hr' : 2 * L' - (u : ValuationWord).length = 2 * (L' - ((i : ℕ) + 1)) := by omega
  rw [hr, hr']
  exact (whiteWindowProduct_moment_horizon (extendedPhaseWhite n ξ) z
    (localPrimitiveP B) (L - ((i : ℕ) + 1)) _ _ (by omega)).symm.trans
      (whiteWindowProduct_moment_horizon (extendedPhaseWhite n ξ) z
        (localPrimitiveP B) (L' - ((i : ℕ) + 1)) _ _ (by omega))

/-- Exact predictable moments give a slightly stronger three-delta bound
for the original post-exit product on the manuscript's window horizon. -/
theorem postExit_product_lt_three_delta {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (a j : ℕ) (top l : ℤ) (B L : ℕ)
    (hadm : longCrossingAdmissible n ξ a j top l B (localPrimitiveA B)
      (localPrimitiveH B) (localPrimitiveP B) (localPrimitiveZ B))
    (hL : (top - l).toNat / 2 + 1 + localPrimitiveP B ≤ L) :
    (postPassageProductMoment n ξ (top - l).toNat j l B L
      (ENNReal.ofReal (1 - 2 * (1 / (2 : ℝ) ^ 78) ^ 2))).toReal <
        3 / (localPrimitiveDeltaDenom B : ℝ) := by
  have hz : ENNReal.ofReal (1 - 2 * (1 / (2 : ℝ) ^ 78) ^ 2) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (1 / (2 : ℝ) ^ 78)]
  have hm := postPassageProductMoment_toReal_lt hn ξ hξ a j top l B
    (L + localPrimitiveK B + n / 2) hz hadm (by omega)
  rw [← postPassageProductMoment_horizon n ξ (top - l).toNat j l B L
    (L + localPrimitiveK B + n / 2) _ hL (by omega)] at hm
  calc
    _ < _ := hm
    _ ≤ 2 / (localPrimitiveDeltaDenom B : ℝ) +
        1 / (localPrimitiveDeltaDenom B : ℝ) :=
      add_le_add le_rfl (postExit_recipe_moment_le_delta B)
    _ = _ := by ring

/-- Appendix E.postexit on the original word law with its printed four-delta
coefficient and no assumed white-visit or predictable-mark estimate. -/
theorem postExit_product_le_four_delta {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (a j : ℕ) (top l : ℤ) (B L : ℕ)
    (hadm : longCrossingAdmissible n ξ a j top l B (localPrimitiveA B)
      (localPrimitiveH B) (localPrimitiveP B) (localPrimitiveZ B))
    (hL : (top - l).toNat / 2 + 1 + localPrimitiveP B ≤ L) :
    (postPassageProductMoment n ξ (top - l).toNat j l B L
      (ENNReal.ofReal (1 - 2 * (1 / (2 : ℝ) ^ 78) ^ 2))).toReal ≤
        4 / (localPrimitiveDeltaDenom B : ℝ) := by
  apply (postExit_product_lt_three_delta hn ξ hξ a j top l B L hadm hL).le.trans
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

end WordCertDensity.LocalPrimitive
