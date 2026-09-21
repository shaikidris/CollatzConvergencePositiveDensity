/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.MassLimit

/-! # One positive marked tolerance before the large-scale limit -/

namespace WordCertDensity.Counting

open Filter
open scoped Topology

/-- Every strict mass target tolerates one fixed positive loss in marked mass. -/
theorem threeBranchMass_positive_tolerance {μ V S B T p u : ℝ}
    (hμ : 0 < μ) (hV : 0 < V) (hB : 0 < B) (hT : 0 < T) (hp : 0 ≤ p)
    (hu : u < threeBranchMass μ V S B T p) :
    ∃ η : ℝ, 0 < η ∧ u < threeBranchMass μ V S B T (max (p-η) 0) := by
  have ha : Tendsto (fun η : ℝ => max (p-η) 0) (𝓝 0) (𝓝 p) := by
    have h : Tendsto (fun η : ℝ => max (p-η) 0) (𝓝 0) (𝓝 (max (p-0) 0)) :=
      (tendsto_const_nhds.sub tendsto_id).max tendsto_const_nhds
    simpa only [sub_zero, max_eq_left hp] using h
  have he := threeBranchMass_eventually_gt hμ hV hB hT hp hu tendsto_const_nhds ha
  obtain ⟨δ, hδ, heδ⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ/2, by positivity, heδ ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < δ/2)]
  linarith

/-- Fix the positive tolerance first; arbitrary convergent finite capacities then suffice. -/
theorem threeBranchMass_fixed_tolerance {μ V S B T p u : ℝ}
    (hμ : 0 < μ) (hV : 0 < V) (hB : 0 < B) (hT : 0 < T) (hp : 0 ≤ p)
    (hu : u < threeBranchMass μ V S B T p) :
    ∃ η : ℝ, 0 < η ∧ ∀ {α : Type*} (l : Filter α) (t a : α → ℝ),
      Tendsto t l (𝓝 T) → Tendsto a l (𝓝 (max (p-η) 0)) →
      ∀ᶠ x in l, u < threeBranchMass μ V S B (t x) (a x) := by
  obtain ⟨η, hη, htarget⟩ := threeBranchMass_positive_tolerance hμ hV hB hT hp hu
  refine ⟨η, hη, ?_⟩
  intro α l t a ht ha
  exact threeBranchMass_eventually_gt hμ hV hB hT (le_max_right _ _) htarget ht ha

end WordCertDensity.Counting
