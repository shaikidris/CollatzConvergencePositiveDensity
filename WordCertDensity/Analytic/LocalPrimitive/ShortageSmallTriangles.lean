/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryDurationRecipe
public import WordCertDensity.Analytic.LocalPrimitive.EntryProbability
public import WordCertDensity.Analytic.LocalPrimitive.EntryRecipe
import Mathlib.Tactic

/-! # Original-law white shortage outside large selected triangles -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The fixed entry bound is at most delta in the native event-mass codomain. -/
theorem entry_recipe_mass_le_delta (B : ℕ) :
    ENNReal.ofReal (Real.exp (localPrimitiveK B : ℝ)) *
      (3 / 4 : ℝ≥0∞) ^ (localPrimitiveR B - 1) ≤
        ENNReal.ofReal (1 / (localPrimitiveDeltaDenom B : ℝ)) := by
  have h := ENNReal.ofReal_le_ofReal (entry_recipe_le_delta B)
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow (by norm_num)] at h
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)] at h
  norm_num at h ⊢
  exact h

/-- The fixed-recipe shortage and small-triangle event is paid by the
repeated-entry bound, uniformly in the starting lattice state. -/
theorem shortage_small_triangles_mass_le {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (j : ℕ) (l : ℤ) (B Q : ℕ)
    (hQ : localPrimitiveP B + (8 * n + 8) ≤ Q) :
    (∑' w : ValuationWord,
      if (2 * localPrimitiveP B ≤ w.length ∧
        sampledWhiteStateCount n ξ j l w (localPrimitiveP B) < localPrimitiveK B ∧
        ∀ s, s < localPrimitiveP B → entryWordBlack n ξ j l w s →
          phaseTriangleLogSize n (entryWordTriangle hn ξ hξ j l w s).1
            (entryWordTriangle hn ξ hξ j l w s).2 ξ <
              (localPrimitiveH B * (s + 1) ^ 4 : ℕ))
      then Reference.wordPMF (2 * Q) w else 0) ≤
      ENNReal.ofReal (Real.exp (localPrimitiveK B : ℝ)) *
        (3 / 4 : ℝ≥0∞) ^ (localPrimitiveR B - 1) := by
  apply le_trans _ (entry_white_shortage_mass_le hn ξ hξ j l
    (localPrimitiveR B - 1) (localPrimitiveP B) (localPrimitiveP B) Q
    (localPrimitiveK B) le_rfl hQ)
  apply ENNReal.tsum_le_tsum
  intro w
  split_ifs with h he
  · exact le_rfl
  · obtain ⟨t, ht, hentry⟩ := recipe_entry_of_shortage_small_triangles
      hn ξ hξ j l w B h.1 h.2.1 h.2.2
    exact False.elim (he ⟨⟨t, ht.le, hentry⟩, h.2.1⟩)
  · exact zero_le
  · exact le_rfl

end WordCertDensity.LocalPrimitive
