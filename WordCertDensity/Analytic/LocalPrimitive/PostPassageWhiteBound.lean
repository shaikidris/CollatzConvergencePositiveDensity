/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PostPassageShortage
public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingBounds
import Mathlib.Tactic

/-! # Combining the original-law white shortage and large-triangle bounds -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- Real-probability form of the original-law shortage bound outside the union. -/
theorem postPassage_shortage_outside_union_probability_le {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (s j : ℕ) (l : ℤ) (B L : ℕ)
    (hL : s / 2 + 1 + localPrimitiveP B + (8 * n + 8) ≤ L) :
    Gated.probability (Reference.wordPMF (2 * L))
      (fun w => postPassageShortageEvent n ξ s j l B w ∧
        ¬ longCrossingLargeUnionEvent n ξ s j l (localPrimitiveH B) (localPrimitiveP B) w) ≤
      1 / (localPrimitiveDeltaDenom B : ℝ) := by
  have hm := postPassage_shortage_outside_union_mass_le hn ξ hξ s j l B L hL
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
  rw [ENNReal.toReal_ofReal (by positivity)] at hr
  convert hr using 1
  unfold Gated.probability
  congr 1
  apply tsum_congr
  intro w
  by_cases hw : postPassageShortageEvent n ξ s j l B w ∧
      ¬ longCrossingLargeUnionEvent n ξ s j l (localPrimitiveH B) (localPrimitiveP B) w
  · simp [hw]
  · simp [hw]

/-- Under E-L4's actual geometric admissibility conditions, fewer than K
white states in the post-passage P-window has original probability below 2 delta. -/
theorem postPassage_white_shortage_probability_lt {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (a j : ℕ) (top l : ℤ) (B L : ℕ)
    (hadm : longCrossingAdmissible n ξ a j top l B (localPrimitiveA B)
      (localPrimitiveH B) (localPrimitiveP B) (localPrimitiveZ B))
    (hL : (top - l).toNat / 2 + 1 + localPrimitiveP B + (8 * n + 8) ≤ L) :
    Gated.probability (Reference.wordPMF (2 * L))
      (postPassageShortageEvent n ξ (top - l).toNat j l B) <
        2 / (localPrimitiveDeltaDenom B : ℝ) := by
  let S := postPassageShortageEvent n ξ (top - l).toNat j l B
  let U := longCrossingLargeUnionEvent n ξ (top - l).toNat j l
    (localPrimitiveH B) (localPrimitiveP B)
  have hsub := Gated.probability_mono_on_support (Reference.wordPMF (2 * L))
    S (fun w => U w ∨ (S w ∧ ¬ U w)) (by
      intro w _ hs
      by_cases hu : U w
      · exact Or.inl hu
      · exact Or.inr ⟨hs, hu⟩)
  have hunion := Gated.probability_or_le (Reference.wordPMF (2 * L)) U
    (fun w => S w ∧ ¬ U w)
  have hsmall := postPassage_shortage_outside_union_probability_le hn ξ hξ
    (top - l).toNat j l B L hL
  have hlarge := longCrossing_union_target n ξ a j top l B (localPrimitiveA B)
    (localPrimitiveH B) (localPrimitiveP B) (localPrimitiveZ B) hadm L (by omega)
  have hden : (localPrimitiveDeltaDenom B : ℝ) = 16 * (10 : ℝ) ^ B := by
    simp [localPrimitiveDeltaDenom]
  change Gated.probability _ S < _
  change Gated.probability _ U < _ at hlarge
  change Gated.probability _ (fun w => S w ∧ ¬ U w) ≤ _ at hsmall
  rw [← hden] at hlarge
  calc
    _ ≤ _ := hsub.trans hunion
    _ < 1 / (localPrimitiveDeltaDenom B : ℝ) +
        1 / (localPrimitiveDeltaDenom B : ℝ) := add_lt_add_of_lt_of_le hlarge hsmall
    _ = _ := by ring

end WordCertDensity.LocalPrimitive
