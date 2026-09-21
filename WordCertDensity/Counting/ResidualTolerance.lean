/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.MassTolerance

/-! # Positive residuals and fixed losses for strict nonnegative mass targets -/

namespace WordCertDensity.Counting

/-- Zero marked residual supplies no positive mass through any retained branch. -/
theorem threeBranchMass_zero (μ V S B T : ℝ) : threeBranchMass μ V S B T 0 = 0 := by
  simp [threeBranchMass, capacitySmallRoot]

/-- A strict nonnegative target forces the marked residual to be positive. -/
theorem threeBranchMass_residual_pos {μ V S B T p u : ℝ} (hp : 0 ≤ p)
    (hu : 0 ≤ u) (hlt : u < threeBranchMass μ V S B T p) : 0 < p := by
  by_contra hn
  have he : p = 0 := le_antisymm (le_of_not_gt hn) hp
  rw [he, threeBranchMass_zero] at hlt
  exact (not_lt_of_ge hu) hlt

/-- The positive tolerance may be chosen below the actual residual, so no clipping remains. -/
theorem threeBranchMass_unclipped_tolerance {μ V S B T p u : ℝ}
    (hμ : 0 < μ) (hV : 0 < V) (hB : 0 < B) (hT : 0 < T)
    (hp : 0 ≤ p) (hu : 0 ≤ u) (hlt : u < threeBranchMass μ V S B T p) :
    ∃ η : ℝ, 0 < η ∧ η < p ∧ u < threeBranchMass μ V S B T (p-η) := by
  obtain ⟨η, hη, he⟩ := threeBranchMass_positive_tolerance hμ hV hB hT hp hlt
  have hsmall : η < p := by
    by_contra hn
    have hz : max (p-η) 0 = 0 := max_eq_right (by linarith [le_of_not_gt hn])
    rw [hz, threeBranchMass_zero] at he
    exact (not_lt_of_ge hu) he
  exact ⟨η, hη, hsmall, by simpa only [max_eq_left (by linarith : 0 ≤ p-η)] using he⟩

/-- A raw score after mixing admits one fixed positive loss with a positive remaining mark. -/
theorem threeBranchMass_raw_tolerance {μ V S B T W E u : ℝ}
    (hμ : 0 < μ) (hV : 0 < V) (hB : 0 < B) (hT : 0 < T)
    (hu : 0 ≤ u) (hlt : u < threeBranchMass μ V S B T (max (W-E) 0)) :
    ∃ η : ℝ, 0 < η ∧ 0 < W-E-η ∧ u < threeBranchMass μ V S B T (W-E-η) := by
  have hp := threeBranchMass_residual_pos (le_max_right (W-E) 0) hu hlt
  have hraw : 0 < W-E := by
    by_contra hn
    rw [max_eq_right (le_of_not_gt hn)] at hp
    exact (lt_irrefl 0) hp
  rw [max_eq_left hraw.le] at hlt
  obtain ⟨η, hη, hsmall, he⟩ := threeBranchMass_unclipped_tolerance
    hμ hV hB hT hraw.le hu hlt
  exact ⟨η, hη, sub_pos.mpr hsmall, he⟩

end WordCertDensity.Counting
